// This software is in the public domain.

#include <cstdlib>
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <cstdint>
#include <cctype>
#include <cassert>
#include <string>


#ifdef __linux__

#include <sys/mman.h>
#define ATTR_NORETURN __attribute((noreturn))

#else

#define ATTR_NORETURN
#pragma warning(disable : 4996)
#define mmap(addr, length, prot, flags, fd, offset) (std::malloc(length))
#define munmap(addr, size) (std::free(addr))
#endif

namespace minilisp {
ATTR_NORETURN void error(const char *fmt, ...) {
    std::va_list ap;
    va_start(ap, fmt);
    std::vfprintf(stderr, fmt, ap);
	std::fprintf(stderr, "\n");
    va_end(ap);
	std::exit(1);
}

//======================================================================
// Lisp objects
//======================================================================

// The Lisp object type
enum {
    // Regular objects visible from the user
    TINT = 1,
    TCELL,
    TSYMBOL,
    TPRIMITIVE,
    TFUNCTION,
    TMACRO,
    TENV,
    // The marker that indicates the object has been moved to other location by GC. The new location
    // can be found at the forwarding pointer. Only the functions to do garbage collection set and
    // handle the object of this type. Other functions will never see the object of this type.
    TMOVED,
    // Const objects. They are statically allocated and will never be managed by GC.
    TTRUE,
    TNIL,
    TDOT,
    TCPAREN,
};

// Typedef for the primitive function
struct Obj;
class Context;
typedef struct Obj *Primitive(Context& context, struct Obj **env, struct Obj **args);

// The object type
typedef struct Obj {
    // The first word of the object represents the type of the object. Any code that handles object
    // needs to check its type first, then access the following union members.
    int type;

    // The total size of the object, including "type" field, this field, the contents, and the
    // padding at the end of the object.
    int size;

    // Object values.
    union {
        // Int
        int value;
        // Cell
        struct {
            struct Obj *car;
            struct Obj *cdr;
        };
        // Symbol
        char name[1];
        // Primitive
        Primitive *fn;
        // Function or Macro
        struct {
            struct Obj *params;
            struct Obj *body;
            struct Obj *env;
        };
        // Environment frame. This is a linked list of association lists
        // containing the mapping from symbols to their value.
        struct {
            struct Obj *vars;
            struct Obj *up;
        };
        // Forwarding pointer
        void *moved;
    };
} Obj;

// Constants
Obj TrueV = Obj{ TTRUE };
Obj NilV = Obj{ TNIL };
Obj DotV = Obj{ TDOT };
Obj CparenV = Obj{ TCPAREN };

Obj *True = &TrueV;
Obj *Nil = &NilV;
Obj *Dot = &DotV;
Obj *Cparen = &CparenV;

namespace {
	bool getEnvFlag(const char *name);
	void *alloc_semispace();
}

struct Context {
	// The list containing all symbols. Such data structure is traditionally called the "obarray", but I
	// avoid using it as a variable name as this is not an array but a list.
	Obj *Symbols;
	// The pointer pointing to the beginning of the current heap
	void *memory;

	// The pointer pointing to the beginning of the old heap
	void *from_space;

	// The number of bytes allocated from the heap
	size_t mem_nused = 0;

	// Flags to debug GC
	bool gc_running = false;
	bool debug_gc = false;
	bool always_gc = false;
	// Cheney's algorithm uses two pointers to keep track of GC status. At first both pointers point to
	// the beginning of the to-space. As GC progresses, they are moved towards the end of the
	// to-space. The objects before "scan1" are the objects that are fully copied. The objects between
	// "scan1" and "scan2" have already been copied, but may contain pointers to the from-space. "scan2"
	// points to the beginning of the free space.
	Obj *scan1;
	Obj *scan2;


	void* root;

	explicit Context()
	: Symbols(nullptr), memory(nullptr), from_space(nullptr),
	  mem_nused(0), gc_running(false), debug_gc(false),
	  always_gc(false), scan1(nullptr), scan2(nullptr),
	  root(nullptr) {
		// Debug flags
		this->debug_gc = getEnvFlag("MINILISP_DEBUG_GC");
		this->always_gc = getEnvFlag("MINILISP_ALWAYS_GC");
		// Memory allocation
		this->memory = alloc_semispace();
		this->Symbols = Nil;
	}
};


//======================================================================
// Memory management
//======================================================================

// The size of the heap in byte
constexpr int MEMORY_SIZE = 65536;

void gc(Context& context);

// Currently we are using Cheney's copying GC algorithm, with which the available memory is split
// into two halves and all objects are moved from one half to another every time GC is invoked. That
// means the address of the object keeps changing. If you take the address of an object and keep it
// in a C variable, dereferencing it could cause SEGV because the address becomes invalid after GC
// runs.
//
// In order to deal with that, all access from C to Lisp objects will go through two levels of
// pointer dereferences. The C local variable is pointing to a pointer on the C stack, and the
// pointer is pointing to the Lisp object. GC is aware of the pointers in the stack and updates
// their contents with the objects' new addresses when GC happens.
//
// The following is a macro to reserve the area in the C stack for the pointers. The contents of
// this area are considered to be GC root.
//
// Be careful not to bypass the two levels of pointer indirections. If you create a direct pointer
// to an object, it'll cause a subtle bug. Such code would work in most cases but fails with SEGV if
// GC happens during the execution of the code. Any code that allocates memory may invoke GC.

#define ROOT_END ((void *)-1)

#define ADD_ROOT(size)                          \
    void *root_ADD_ROOT_[size + 2];             \
    root_ADD_ROOT_[0] = context.root;                   \
    for (int i = 1; i <= size; i++)             \
        root_ADD_ROOT_[i] = NULL;               \
    root_ADD_ROOT_[size + 1] = ROOT_END;        \
    context.root = root_ADD_ROOT_

#define DEFINE1(var1)                           \
    ADD_ROOT(1);                                \
    Obj **var1 = (Obj **)(root_ADD_ROOT_ + 1)

#define DEFINE2(var1, var2)                     \
    ADD_ROOT(2);                                \
    Obj **var1 = (Obj **)(root_ADD_ROOT_ + 1);  \
    Obj **var2 = (Obj **)(root_ADD_ROOT_ + 2)

#define DEFINE3(var1, var2, var3)               \
    ADD_ROOT(3);                                \
    Obj **var1 = (Obj **)(root_ADD_ROOT_ + 1);  \
    Obj **var2 = (Obj **)(root_ADD_ROOT_ + 2);  \
    Obj **var3 = (Obj **)(root_ADD_ROOT_ + 3)

#define DEFINE4(var1, var2, var3, var4)         \
    ADD_ROOT(4);                                \
    Obj **var1 = (Obj **)(root_ADD_ROOT_ + 1);  \
    Obj **var2 = (Obj **)(root_ADD_ROOT_ + 2);  \
    Obj **var3 = (Obj **)(root_ADD_ROOT_ + 3);  \
    Obj **var4 = (Obj **)(root_ADD_ROOT_ + 4)

// Round up the given value to a multiple of size. Size must be a power of 2. It adds size - 1
// first, then zero-ing the least significant bits to make the result a multiple of size. I know
// these bit operations may look a little bit tricky, but it's efficient and thus frequently used.
inline size_t roundup(size_t var, size_t size) {
    return (var + size - 1) & ~(size - 1);
}

// Allocates memory block. This may start GC if we don't have enough memory.
Obj *alloc(Context& context, int type, size_t size) {
    // The object must be large enough to contain a pointer for the forwarding pointer. Make it
    // larger if it's smaller than that.
    size = roundup(size, sizeof(void *));

    // Add the size of the type tag and size fields.
    size += offsetof(Obj, value);

    // Round up the object size to the nearest alignment boundary, so that the next object will be
    // allocated at the proper alignment boundary. Currently we align the object at the same
    // boundary as the pointer.
    size = roundup(size, sizeof(void *));

    // If the debug flag is on, allocate a new memory space to force all the existing objects to
    // move to new addresses, to invalidate the old addresses. By doing this the GC behavior becomes
    // more predictable and repeatable. If there's a memory bug that the C variable has a direct
    // reference to a Lisp object, the pointer will become invalid by this GC call. Dereferencing
    // that will immediately cause SEGV.
    if (context.always_gc && !context.gc_running)
        gc(context);

    // Otherwise, run GC only when the available memory is not large enough.
    if (!context.always_gc && MEMORY_SIZE < context.mem_nused + size)
        gc(context);

    // Terminate the program if we couldn't satisfy the memory request. This can happen if the
    // requested size was too large or the from-space was filled with too many live objects.
    if (MEMORY_SIZE < context.mem_nused + size)
        error("Memory exhausted");

    // Allocate the object.
    Obj *obj = reinterpret_cast<Obj*>((unsigned char*)context.memory + context.mem_nused);
    obj->type = type;
    obj->size = size;
	context.mem_nused += size;
    return obj;
}

//======================================================================
// Garbage collector
//======================================================================

// Moves one object from the from-space to the to-space. Returns the object's new address. If the
// object has already been moved, does nothing but just returns the new address.
inline Obj *forward(Context& context, Obj *obj) {
    // If the object's address is not in the from-space, the object is not managed by GC nor it
    // has already been moved to the to-space.
    ptrdiff_t offset = (uint8_t *)obj - (uint8_t *)context.from_space;
    if (offset < 0 || MEMORY_SIZE <= offset)
        return obj;

    // The pointer is pointing to the from-space, but the object there was a tombstone. Follow the
    // forwarding pointer to find the new location of the object.
    if (obj->type == TMOVED)
        return reinterpret_cast<Obj*>(obj->moved);

    // Otherwise, the object has not been moved yet. Move it.
    Obj *newloc = context.scan2;
    std::memcpy(newloc, obj, obj->size);
	context.scan2 = (Obj *)((uint8_t *)context.scan2 + obj->size);

    // Put a tombstone at the location where the object used to occupy, so that the following call
    // of forward() can find the object's new location.
    obj->type = TMOVED;
    obj->moved = newloc;
    return newloc;
}

// Copies the root objects.
void forward_root_objects(Context& context) {
	context.Symbols = forward(context, context.Symbols);
    for (void **frame = reinterpret_cast<void**>(context.root); frame; frame = *(void ***)frame)
        for (int i = 1; frame[i] != ROOT_END; i++)
            if (frame[i])
                frame[i] = forward(context, reinterpret_cast<Obj*>(frame[i]));
}

// Implements Cheney's copying garbage collection algorithm.
// http://en.wikipedia.org/wiki/Cheney%27s_algorithm
void gc(Context& context) {
    assert(!context.gc_running);
	context.gc_running = true;

    // Allocate a new semi-space.
	context.from_space = context.memory;
	context.memory = alloc_semispace();

    // Initialize the two pointers for GC. Initially they point to the beginning of the to-space.
	context.scan1 = context.scan2 = reinterpret_cast<Obj*>(context.memory);

    // Copy the GC root objects first. This moves the pointer scan2.
    forward_root_objects(context);

    // Copy the objects referenced by the GC root objects located between scan1 and scan2. Once it's
    // finished, all live objects (i.e. objects reachable from the root) will have been copied to
    // the to-space.
    while (context.scan1 < context.scan2) {
        switch (context.scan1->type) {
        case TINT:
        case TSYMBOL:
        case TPRIMITIVE:
            // Any of the above types does not contain a pointer to a GC-managed object.
            break;
        case TCELL:
            context.scan1->car = forward(context, context.scan1->car);
            context.scan1->cdr = forward(context, context.scan1->cdr);
            break;
        case TFUNCTION:
        case TMACRO:
            context.scan1->params = forward(context, context.scan1->params);
            context.scan1->body = forward(context, context.scan1->body);
            context.scan1->env = forward(context, context.scan1->env);
            break;
        case TENV:
            context.scan1->vars = forward(context, context.scan1->vars);
            context.scan1->up = forward(context, context.scan1->up);
            break;
        default:
            error("Bug: copy: unknown type %d", context.scan1->type);
        }
		context.scan1 = (Obj *)((uint8_t *)context.scan1 + context.scan1->size);
    }

    // Finish up GC.
    munmap(context.from_space, MEMORY_SIZE);
    size_t old_nused = context.mem_nused;
	context.mem_nused = (size_t)((uint8_t *)context.scan1 - (uint8_t *)context.memory);
    if (context.debug_gc)
		std::fprintf(stderr, "GC: %zu bytes out of %zu bytes copied.\n", context.mem_nused, old_nused);
	context.gc_running = false;
}

//======================================================================
// Constructors
//======================================================================

Obj *make_int(Context& context, int value) {
    Obj *r = alloc(context, TINT, sizeof(int));
    r->value = value;
    return r;
}

Obj *cons(Context& context, Obj **car, Obj **cdr) {
    Obj *cell = alloc(context, TCELL, sizeof(Obj *) * 2);
    cell->car = *car;
    cell->cdr = *cdr;
    return cell;
}

Obj *make_symbol(Context& context, const char *name) {
    Obj *sym = alloc(context, TSYMBOL, strlen(name) + 1);
	std::strcpy(sym->name, name);
    return sym;
}

Obj *make_primitive(Context& context, Primitive *fn) {
    Obj *r = alloc(context, TPRIMITIVE, sizeof(Primitive *));
    r->fn = fn;
    return r;
}

Obj *make_function(Context& context, Obj **env, int type, Obj **params, Obj **body) {
    assert(type == TFUNCTION || type == TMACRO);
    Obj *r = alloc(context, type, sizeof(Obj *) * 3);
    r->params = *params;
    r->body = *body;
    r->env = *env;
    return r;
}

Obj *make_env(Context& context, Obj **vars, Obj **up) {
    Obj *r = alloc(context, TENV, sizeof(Obj *) * 2);
    r->vars = *vars;
    r->up = *up;
    return r;
}

// Returns ((x . y) . a)
Obj *acons(Context& context, Obj **x, Obj **y, Obj **a) {
    DEFINE1(cell);
    *cell = cons(context, x, y);
    return cons(context, cell, a);
}

//======================================================================
// Parser
//
// This is a hand-written recursive-descendent parser.
//======================================================================

constexpr int SYMBOL_MAX_LEN = 200;
constexpr char symbol_chars[] = "~!@#$%^&*-_=+:/?<>";

template<typename ScannerT>
Obj *read_expr(ScannerT& scanner, Context& context);

// Destructively reverses the given list.
Obj *reverse(Obj *p) {
    Obj *ret = Nil;
    while (p != Nil) {
        Obj *head = p;
        p = p->cdr;
        head->cdr = ret;
        ret = head;
    }
    return ret;
}

// ScannerT requires:
// int peek()
// int get()
struct FileScanner {
	FILE* input;
	bool close;

	explicit FileScanner(FILE* input, bool close) : input(input), close(close) {}
	explicit FileScanner() : input(stdin), close(false){}
	~FileScanner() { if (close) fclose(input); }
	int read() { return fgetc(input); }
	int peek() {
		int c = fgetc(input);
		ungetc(c, input);
		return c;
	}
};
struct TextScanner {
	std::string input;
	int pos;

	explicit TextScanner(const std::string& input) : input(input), pos(0){}
	int read() {
		if (pos >= static_cast<int>(input.size())) {
			return EOF;
		}
		char c = input[pos];
		pos++;
		return static_cast<int>(c);
	}
	int peek() {
		if (pos >= static_cast<int>(input.size())) {
			return EOF;
		}
		return static_cast<int>(input[pos]);
	}
};

// Skips the input until newline is found. Newline is one of \r, \r\n or \n.
template<typename ScannerT>
void skip_line(ScannerT& scanner) {
    for (;;) {
        int c = scanner.read();
        if (c == EOF || c == '\n')
            return;
        if (c == '\r') {
            if (scanner.peek() == '\n')
				scanner.read();
            return;
        }
    }
}

// Reads a list. Note that '(' has already been read.
template<typename ScannerT>
Obj *read_list(ScannerT& scanner, Context& context) {
    DEFINE3(obj, head, last);
    *head = Nil;
    for (;;) {
        *obj = read_expr(scanner, context);
        if (!*obj)
            error("Unclosed parenthesis");
        if (*obj == Cparen)
            return reverse(*head);
        if (*obj == Dot) {
            *last = read_expr(scanner, context);
            if (read_expr(scanner, context) != Cparen)
                error("Closed parenthesis expected after dot");
            Obj *ret = reverse(*head);
            (*head)->cdr = *last;
            return ret;
        }
        *head = cons(context, obj, head);
    }
}

// May create a new symbol. If there's a symbol with the same name, it will not create a new symbol
// but return the existing one.
Obj *intern(Context& context, const char *name) {
    for (Obj *p = context.Symbols; p != Nil; p = p->cdr)
        if (std::strcmp(name, p->car->name) == 0)
            return p->car;
    DEFINE1(sym);
    *sym = make_symbol(context, name);
	context.Symbols = cons(context, sym, &context.Symbols);
    return *sym;
}

// Reader marcro ' (single quote). It reads an expression and returns (quote <expr>).
template<typename ScannerT>
Obj *read_quote(ScannerT& scanner, Context& context) {
    DEFINE2(sym, tmp);
    *sym = intern(context, "quote");
    *tmp = read_expr(scanner, context);
    *tmp = cons(context, tmp, &Nil);
    *tmp = cons(context, sym, tmp);
    return *tmp;
}

template<typename ScannerT>
int read_number(ScannerT& scanner, int val) {
    while (std::isdigit(scanner.peek()))
        val = val * 10 + (scanner.read() - '0');
    return val;
}

template<typename ScannerT>
Obj *read_symbol(ScannerT& scanner, Context& context, char c) {
    char buf[SYMBOL_MAX_LEN + 1];
    buf[0] = c;
    int len = 1;
    while (std::isalnum(scanner.peek()) || std::strchr(symbol_chars, scanner.peek())) {
        if (SYMBOL_MAX_LEN <= len)
            error("Symbol name too long");
        buf[len++] = scanner.read();
    }
    buf[len] = '\0';
    return intern(context, buf);
}

template<typename ScannerT>
Obj *read_expr(ScannerT& scanner, Context& context) {
    for (;;) {
		int c = scanner.read();
        if (c == ' ' || c == '\n' || c == '\r' || c == '\t')
            continue;
        if (c == EOF)
            return NULL;
        if (c == ';') {
            skip_line(scanner);
            continue;
        }
        if (c == '(')
            return read_list(scanner, context);
        if (c == ')')
            return Cparen;
        if (c == '.')
            return Dot;
        if (c == '\'')
            return read_quote(scanner, context);
        if (std::isdigit(c))
            return make_int(context, read_number(scanner, c - '0'));
        if (c == '-' && std::isdigit(scanner.peek()))
            return make_int(context, -read_number(scanner, 0));
        if (std::isalpha(c) || std::strchr(symbol_chars, c))
            return read_symbol(scanner, context, c);
        error("Don't know how to handle %c", c);
    }
}

// Prints the given object.
void print(Obj *obj) {
    switch (obj->type) {
    case TCELL:
        std::printf("(");
        for (;;) {
            print(obj->car);
            if (obj->cdr == Nil)
                break;
            if (obj->cdr->type != TCELL) {
				std::printf(" . ");
                print(obj->cdr);
                break;
            }
			std::printf(" ");
            obj = obj->cdr;
        }
		std::printf(")");
        return;

#define CASE(type, ...)                         \
    case type:                                  \
        std::printf(__VA_ARGS__);                    \
        return
    CASE(TINT, "%d", obj->value);
    CASE(TSYMBOL, "%s", obj->name);
    CASE(TPRIMITIVE, "<primitive>");
    CASE(TFUNCTION, "<function>");
    CASE(TMACRO, "<macro>");
    CASE(TMOVED, "<moved>");
    CASE(TTRUE, "t");
    CASE(TNIL, "()");
#undef CASE
    default:
        error("Bug: print: Unknown tag type: %d", obj->type);
    }
}

// Returns the length of the given list. -1 if it's not a proper list.
int length(Obj *list) {
    int len = 0;
    for (; list->type == TCELL; list = list->cdr)
        len++;
    return list == Nil ? len : -1;
}

//======================================================================
// Evaluator
//======================================================================

Obj *eval(Context& context, Obj **env, Obj **obj);

void add_variable(Context& context, Obj **env, Obj **sym, Obj **val) {
    DEFINE2(vars, tmp);
    *vars = (*env)->vars;
    *tmp = acons(context, sym, val, vars);
    (*env)->vars = *tmp;
}

void add_primitive(Context& context, Obj **env, const char *name, Primitive *fn) {
	DEFINE2(sym, prim);
	*sym = intern(context, name);
	*prim = make_primitive(context, fn);
	add_variable(context, env, sym, prim);
}

// Returns a newly created environment frame.
Obj *push_env(Context& context, Obj **env, Obj **vars, Obj **vals) {
    DEFINE3(map, sym, val);
    *map = Nil;
    for (; (*vars)->type == TCELL; *vars = (*vars)->cdr, *vals = (*vals)->cdr) {
        if ((*vals)->type != TCELL)
            error("Cannot apply function: number of argument does not match");
        *sym = (*vars)->car;
        *val = (*vals)->car;
        *map = acons(context, sym, val, map);
    }
    if (*vars != Nil)
        *map = acons(context, vars, vals, map);
    return make_env(context, map, env);
}

// Evaluates the list elements from head and returns the last return value.
Obj *progn(Context& context, Obj **env, Obj **list) {
    DEFINE2(lp, r);
    for (*lp = *list; *lp != Nil; *lp = (*lp)->cdr) {
        *r = (*lp)->car;
        *r = eval(context, env, r);
    }
    return *r;
}

// Evaluates all the list elements and returns their return values as a new list.
Obj *eval_list(Context& context, Obj **env, Obj **list) {
    DEFINE4(head, lp, expr, result);
    *head = Nil;
    for (lp = list; *lp != Nil; *lp = (*lp)->cdr) {
        *expr = (*lp)->car;
        *result = eval(context, env, expr);
        *head = cons(context, result, head);
    }
    return reverse(*head);
}

bool is_list(Obj *obj) {
    return obj == Nil || obj->type == TCELL;
}

Obj *apply_func(Context& context, Obj **env, Obj **fn, Obj **args) {
    DEFINE3(params, newenv, body);
    *params = (*fn)->params;
    *newenv = (*fn)->env;
    *newenv = push_env(context, newenv, params, args);
    *body = (*fn)->body;
    return progn(context, newenv, body);
}

// Apply fn with args.
Obj *apply(Context& context, Obj **env, Obj **fn, Obj **args) {
    if (!is_list(*args))
        error("argument must be a list");
    if ((*fn)->type == TPRIMITIVE)
        return (*fn)->fn(context, env, args);
    if ((*fn)->type == TFUNCTION) {
        DEFINE1(eargs);
        *eargs = eval_list(context, env, args);
        return apply_func(context, env, fn, eargs);
    }
    error("not supported");
}

// Searches for a variable by symbol. Returns null if not found.
Obj *find(Obj **env, Obj *sym) {
    for (Obj *p = *env; p != Nil; p = p->up) {
        for (Obj *cell = p->vars; cell != Nil; cell = cell->cdr) {
            Obj *bind = cell->car;
            if (sym == bind->car)
                return bind;
        }
    }
    return NULL;
}

// Expands the given macro application form.
Obj *macroexpand(Context& context, Obj **env, Obj **obj) {
    if ((*obj)->type != TCELL || (*obj)->car->type != TSYMBOL)
        return *obj;
    DEFINE3(bind, macro, args);
    *bind = find(env, (*obj)->car);
    if (!*bind || (*bind)->cdr->type != TMACRO)
        return *obj;
    *macro = (*bind)->cdr;
    *args = (*obj)->cdr;
    return apply_func(context, env, macro, args);
}

// Evaluates the S expression.
Obj *eval(Context& context, Obj **env, Obj **obj) {
    switch ((*obj)->type) {
    case TINT:
    case TPRIMITIVE:
    case TFUNCTION:
    case TTRUE:
    case TNIL:
        // Self-evaluating objects
        return *obj;
    case TSYMBOL: {
        // Variable
        Obj *bind = find(env, *obj);
        if (!bind)
            error("Undefined symbol: %s", (*obj)->name);
        return bind->cdr;
    }
    case TCELL: {
        // Function application form
        DEFINE3(fn, expanded, args);
        *expanded = macroexpand(context, env, obj);
        if (*expanded != *obj)
            return eval(context, env, expanded);
        *fn = (*obj)->car;
        *fn = eval(context, env, fn);
        *args = (*obj)->cdr;
        if ((*fn)->type != TPRIMITIVE && (*fn)->type != TFUNCTION)
            error("The head of a list must be a function");
        return apply(context, env, fn, args);
    }
    default:
        error("Bug: eval: Unknown tag type: %d", (*obj)->type);
    }
}

namespace {
//======================================================================
// Primitive functions and special forms
//======================================================================

// 'expr
Obj *prim_quote(Context& context, Obj **env, Obj **list) {
    if (length(*list) != 1)
        error("Malformed quote");
    return (*list)->car;
}

// (cons expr expr)
Obj *prim_cons(Context& context, Obj **env, Obj **list) {
    if (length(*list) != 2)
        error("Malformed cons");
    Obj *cell = eval_list(context, env, list);
    cell->cdr = cell->cdr->car;
    return cell;
}

// (car <cell>)
Obj *prim_car(Context& context, Obj **env, Obj **list) {
    Obj *args = eval_list(context, env, list);
    if (args->car->type != TCELL || args->cdr != Nil)
        error("Malformed car");
    return args->car->car;
}

// (cdr <cell>)
Obj *prim_cdr(Context& context, Obj **env, Obj **list) {
    Obj *args = eval_list(context, env, list);
    if (args->car->type != TCELL || args->cdr != Nil)
        error("Malformed cdr");
    return args->car->cdr;
}

// (setq <symbol> expr)
Obj *prim_setq(Context& context, Obj **env, Obj **list) {
    if (length(*list) != 2 || (*list)->car->type != TSYMBOL)
        error("Malformed setq");
    DEFINE2(bind, value);
    *bind = find(env, (*list)->car);
    if (!*bind)
        error("Unbound variable %s", (*list)->car->name);
    *value = (*list)->cdr->car;
    *value = eval(context, env, value);
    (*bind)->cdr = *value;
    return *value;
}

// (setcar <cell> expr)
Obj *prim_setcar(Context& context, Obj **env, Obj **list) {
    DEFINE1(args);
    *args = eval_list(context, env, list);
    if (length(*args) != 2 || (*args)->car->type != TCELL)
        error("Malformed setcar");
    (*args)->car->car = (*args)->cdr->car;
    return (*args)->car;
}

// (while cond expr ...)
Obj *prim_while(Context& context, Obj **env, Obj **list) {
    if (length(*list) < 2)
        error("Malformed while");
    DEFINE2(cond, exprs);
    *cond = (*list)->car;
    while (eval(context, env, cond) != Nil) {
        *exprs = (*list)->cdr;
        eval_list(context, env, exprs);
    }
    return Nil;
}

// (gensym)
Obj *prim_gensym(Context& context, Obj **env, Obj **list) {
  static int count = 0;
  char buf[10];
  snprintf(buf, sizeof(buf), "G__%d", count++);
  return make_symbol(context, buf);
}

// (+ <integer> ...)
Obj *prim_plus(Context& context, Obj **env, Obj **list) {
    int sum = 0;
    for (Obj *args = eval_list(context, env, list); args != Nil; args = args->cdr) {
        if (args->car->type != TINT)
            error("+ takes only numbers");
        sum += args->car->value;
    }
    return make_int(context, sum);
}

// (- <integer> ...)
Obj *prim_minus(Context& context, Obj **env, Obj **list) {
    Obj *args = eval_list(context, env, list);
    for (Obj *p = args; p != Nil; p = p->cdr)
        if (p->car->type != TINT)
            error("- takes only numbers");
    if (args->cdr == Nil)
        return make_int(context, -args->car->value);
    int r = args->car->value;
    for (Obj *p = args->cdr; p != Nil; p = p->cdr)
        r -= p->car->value;
    return make_int(context, r);
}

// (< <integer> <integer>)
Obj *prim_lt(Context& context, Obj **env, Obj **list) {
    Obj *args = eval_list(context, env, list);
    if (length(args) != 2)
        error("malformed <");
    Obj *x = args->car;
    Obj *y = args->cdr->car;
    if (x->type != TINT || y->type != TINT)
        error("< takes only numbers");
    return x->value < y->value ? True : Nil;
}

Obj *handle_function(Context& context, Obj **env, Obj **list, int type) {
    if ((*list)->type != TCELL || !is_list((*list)->car) || (*list)->cdr->type != TCELL)
        error("Malformed lambda");
    Obj *p = (*list)->car;
    for (; p->type == TCELL; p = p->cdr)
        if (p->car->type != TSYMBOL)
            error("Parameter must be a symbol");
    if (p != Nil && p->type != TSYMBOL)
        error("Parameter must be a symbol");
    DEFINE2(params, body);
    *params = (*list)->car;
    *body = (*list)->cdr;
    return make_function(context, env, type, params, body);
}

// (lambda (<symbol> ...) expr ...)
Obj *prim_lambda(Context& context, Obj **env, Obj **list) {
    return handle_function(context, env, list, TFUNCTION);
}

Obj *handle_defun(Context& context, Obj **env, Obj **list, int type) {
    if ((*list)->car->type != TSYMBOL || (*list)->cdr->type != TCELL)
        error("Malformed defun");
    DEFINE3(fn, sym, rest);
    *sym = (*list)->car;
    *rest = (*list)->cdr;
    *fn = handle_function(context, env, rest, type);
    add_variable(context, env, sym, fn);
    return *fn;
}

// (defun <symbol> (<symbol> ...) expr ...)
Obj *prim_defun(Context& context, Obj **env, Obj **list) {
    return handle_defun(context, env, list, TFUNCTION);
}

// (define <symbol> expr)
Obj *prim_define(Context& context, Obj **env, Obj **list) {
    if (length(*list) != 2 || (*list)->car->type != TSYMBOL)
        error("Malformed define");
    DEFINE2(sym, value);
    *sym = (*list)->car;
    *value = (*list)->cdr->car;
    *value = eval(context, env, value);
    add_variable(context, env, sym, value);
    return *value;
}

// (defmacro <symbol> (<symbol> ...) expr ...)
Obj *prim_defmacro(Context& context, Obj **env, Obj **list) {
    return handle_defun(context, env, list, TMACRO);
}

// (macroexpand expr)
Obj *prim_macroexpand(Context& context, Obj **env, Obj **list) {
    if (length(*list) != 1)
        error("Malformed macroexpand");
    DEFINE1(body);
    *body = (*list)->car;
    return macroexpand(context, env, body);
}

// (println expr)
Obj *prim_println(Context& context, Obj **env, Obj **list) {
    DEFINE1(tmp);
    *tmp = (*list)->car;
    print(eval(context, env, tmp));
    std::printf("\n");
    return Nil;
}

// (if expr expr expr ...)
Obj *prim_if(Context& context, Obj **env, Obj **list) {
    if (length(*list) < 2)
        error("Malformed if");
    DEFINE3(cond, then, els);
    *cond = (*list)->car;
    *cond = eval(context, env, cond);
    if (*cond != Nil) {
        *then = (*list)->cdr->car;
        return eval(context, env, then);
    }
    *els = (*list)->cdr->cdr;
    return *els == Nil ? Nil : progn(context, env, els);
}

// (= <integer> <integer>)
Obj *prim_num_eq(Context& context, Obj **env, Obj **list) {
    if (length(*list) != 2)
        error("Malformed =");
    Obj *values = eval_list(context, env, list);
    Obj *x = values->car;
    Obj *y = values->cdr->car;
    if (x->type != TINT || y->type != TINT)
        error("= only takes numbers");
    return x->value == y->value ? True : Nil;
}

// (eq expr expr)
Obj *prim_eq(Context& context, Obj **env, Obj **list) {
    if (length(*list) != 2)
        error("Malformed eq");
    Obj *values = eval_list(context, env, list);
    return values->car == values->cdr->car ? True : Nil;
}

void define_constants(Context& context, Obj **env) {
    DEFINE1(sym);
    *sym = intern(context, "t");
    add_variable(context, env, sym, &True);
}

void define_primitives(Context& context, Obj **env) {
    add_primitive(context, env, "quote", prim_quote);
    add_primitive(context, env, "cons", prim_cons);
    add_primitive(context, env, "car", prim_car);
    add_primitive(context, env, "cdr", prim_cdr);
    add_primitive(context, env, "setq", prim_setq);
    add_primitive(context, env, "setcar", prim_setcar);
    add_primitive(context, env, "while", prim_while);
    add_primitive(context, env, "gensym", prim_gensym);
    add_primitive(context, env, "+", prim_plus);
    add_primitive(context, env, "-", prim_minus);
    add_primitive(context, env, "<", prim_lt);
    add_primitive(context, env, "define", prim_define);
    add_primitive(context, env, "defun", prim_defun);
    add_primitive(context, env, "defmacro", prim_defmacro);
    add_primitive(context, env, "macroexpand", prim_macroexpand);
    add_primitive(context, env, "lambda", prim_lambda);
    add_primitive(context, env, "if", prim_if);
    add_primitive(context, env, "=", prim_num_eq);
    add_primitive(context, env, "eq", prim_eq);
    add_primitive(context, env, "println", prim_println);
}

// Returns true if the environment variable is defined and not the empty string.
bool getEnvFlag(const char *name) {
	char *val = std::getenv(name);
	return val && val[0];
}

void *alloc_semispace() {
	return mmap(NULL, MEMORY_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
}
}
}

//======================================================================
// Entry point
//======================================================================


int main(int argc, char **argv) {
	using namespace minilisp;
	Context context;

	// Constants and primitives
    DEFINE3(env, expr, obj);
    *env = make_env(context, &Nil, &Nil);
    define_constants(context, env);
    define_primitives(context, env);

	TextScanner ts("(println 1)");
	*obj = read_expr(ts, context);
	print(eval(context, env, obj));
	std::printf("\n");

    // The main loop
	FileScanner fs;
    for (;;) {
        *expr = read_expr(fs, context);
        if (!*expr)
            return 0;
        if (*expr == Cparen)
            error("Stray close parenthesis");
        if (*expr == Dot)
            error("Stray dot");
        print(eval(context, env, expr));
        std::printf("\n");
    }
}
