/* -------------------------------------------------------------------------- */

version (X86) {} else {static assert(0);};
version (D_InlineAsm_X86) {} else {static assert(0);};

import Std_;
import core.internal.hash : hash_of_ = hashOf;

import Misc_ = miscellaneous : MpDec_ = MpDec;
import Rt_ = runtime;
import Lang_ = language;
import X86_ = x86generator;

/* -------------------------------------------------------------------------- */

// TODO: find out why -inline breaks the code
// TODO: make sure all value allocations are through valigned_malloc
// TODO: unittests for Namespaceº
// TODO: use something other than Arrayº for AST forms
// TODO: to-source should not be a method, it should be a global function
// TODO: optimise Atreeº iteration
// TODO: HtreeRootº needs payload packed towards the start of the structure

/*
	value types
	¯¯¯¯¯¯¯¯¯¯¯
	a value consists of a size_t[4] structure, containing pointers and
	arbitrary data.

	all values must conform one of the following layouts:
	    _________        _________        _________        _________
	1. [  Funcº  ]   2. [  Funcº  ]   3. [  Funcº  ]   4. [  Funcº  ]
	   [  data   ]      [ pointer ]      [ pointer ]      [ pointer ]
	   [  data   ]      [  data   ]      [ pointer ]      [ pointer ]
	   [  data   ]      [  data   ]      [  data   ]      [ pointer ]
	    ¯¯¯¯¯¯¯¯¯        ¯¯¯¯¯¯¯¯¯        ¯¯¯¯¯¯¯¯¯        ¯¯¯¯¯¯¯¯¯
	i.e. pointers are packed towards the start of the structure.
	this allows for more efficient GC tracing techniques.

	however, 'data' can safely contain pointers to manually-managed memory.

	note that pointers to GC-allocated memory may be modified during collection
	cycles by a compacting GC implementation.
*/

/* note: extern(C) funcs need to be defined as templates to mangle their name */

/* -- generic value type -- */

alias Funcº = extern(C) Valº function(size_t, Valº, ...);

struct Valº {
	/* Valº.init is the nil value
	nil is the only logically false value */
	Funcº Func;
	private size_t[3] PadØ;
	enum PtrCount = 0;

	invariant {
		/* only nil should have a null Func */
		assert(Func !is null || this is this.init);
	};

	bool opCast(Tº : bool)() {return this !is this.init;};
	auto opCast(Tº : Valº)() inout {return *(cast(inout(Tº)*) &this);};

	extern(C) Valº voke(Tsº...)(Tsº Vals) if (allSatisfy_!(IsVal, Tsº)) {
		/* run through apply() to ensure stack alignment */
		static if (Vals.length > 0) {
			return apply((cast(Valº*) &Vals[0])[0 .. Vals.length]);
		} else {
			return apply([]);
		};
	};
	Valº voke(string Name)() {
		enum X = CtfeAtomº(Name);
		return voke(cast(Valº) X);
	};

	Valº voke_u(Tsº...)(Tsº Vals) if (allSatisfy_!(IsVal, Tsº)) {
		/* only for functions which don't require stack alignment */
		return Func(1 + Vals.length, this, Vals);
	};
	Valº voke_u(string Name)() {
		enum X = CtfeAtomº(Name);
		return voke_u(cast(Valº) X);
	};

	/* the main transition from D code to luaphole code */
	Valº apply(Valº[] Vals) {
		/* return Func(1 + Vals.length, this, Vals...) */

		void* ValsStart = Vals.ptr;
		void* ValsEnd = Vals.ptr + Vals.length;
		size_t ArgC = 1 + Vals.length;

		/* aligned memory for return value */
		Valº[2] RetMem;
		size_t RetPtr = (cast(size_t) &RetMem[1]) & X86_.ValignMask;
		assert((RetPtr & 0xf) == 0);

		asm {
			mov EBX, ESP;
			and ESP, X86_.ValignMask; /* align stack for SSE */

			/* push params */
			mov EAX, ValsStart;
			mov ECX, ValsEnd;
			Loop1:; /* while (end > start) */
			cmp ECX, EAX;
			jle Break1;
			sub ECX, 4;
			push dword ptr [ECX];
			jmp Loop1;
			Break1:;

			/* push this */
			mov EAX, this; /* start */
			mov ECX, EAX; /* end */
			add ECX, this.sizeof; /* end */
			Loop2:; /* while (end > start) */
			cmp ECX, EAX;
			jle Break2;
			sub ECX, 4;
			push dword ptr [ECX];
			jmp Loop2;
			Break2:;

			push ArgC;
			push RetPtr;
			/* call this.Func */
			mov EAX, this + Func.offsetof;
			call [EAX];

			mov ESP, EBX;
		};

		return *(cast(Valº*) RetPtr);
	};

	unittest {
		enum A = Valº(null, cast(void*[]) [5, 6, 7000005]);
		enum B = Valº(cast(Funcº) -1, cast(void*[]) [0, 0, 1]);
	
		extern(C) Valº f(size_t ArgC, Valº Self, Valº X, Valº Y) {
			assert(ArgC == 3);
			assert(Self is Valº(cast(Funcº) &f));
			assert(X is A);
			assert(Y is B);
			return B;
		};
		auto F = Valº(cast(Funcº) &f);
		assert(F.apply([A, B]) is B);
	};
};

/* useful as a sentinel */
enum InvalidVal = Valº(cast(Funcº) size_t.max);

Valº bool_val(bool X) {
	enum NonNil = CtfeAtomº(`t`);
	return X ? NonNil : Valº.init;
};

alias IsVal(Tº) = Alias_!(is(Tº : Valº) && Tº.sizeof == Valº.sizeof);
unittest {
	static assert(IsVal!Valº);
	static assert(!IsVal!(size_t[4]));

	struct Aº {size_t[4] X;};
	static assert(!IsVal!Aº);

	struct Bº {
		@property Valº V() {return Valº.init;};
		alias V this;
	};
	static assert(!IsVal!Bº);

	struct Cº {
		size_t[4] X;
		@property Valº V() {return Valº.init;};
		alias V this;
	};
	static assert(!IsVal!Cº);
};

mixin template ValSubType(size_t PadLen = 0) {
	size_t[PadLen] PadØ;

	alias BaseØ this;
	@property auto ref BaseØ()() inout {return *(cast(inout Valº*) &this);};

	//static assert(is(typeof(this) : Valº));
	static assert(this.sizeof == Valº.sizeof);

	invariant {
		alias b = Misc_.bytes_of;
		assert(this.Func !is null || b(this) == b(Valº.init));
	};

	static if (__traits(compiles, {enum size_t X = PtrCount;})) {
		static assert(ordered_(0, PtrCount, 3));
	} else static if (__traits(compiles, {
		size_t X = PtrCount(typeof(this).init);
	})) {
		invariant {
			// might cause reentrant loop
			// assert(ordered_(0, PtrCount(this), 3));
		};
	} else {
		static assert(0);
	};
};

auto maybe(Tº)(Tº V) {return Maybeº!Tº(V);};

struct Maybeº(Tº) if (is(Tº : Valº) && is(Tº == Unqual_!Tº)) {
	private Valº Val;
	alias Get this;

	this(Tº V) {Val = V;};

	@property auto ref Get() inout in {
		assert(NonNil);
	} body {
		return *(cast(inout Tº*) &Val);
	};

	@property bool NonNil() const {
		return Val !is Val.init;
	};
};

template dispatch_methods(Tº) if (IsVal!Tº) {
	/*
	finds methods in Tº of the form
		@(`foo`) Valº bar() {…};
	and creates a dispatch function that maps Atomº(`foo`) to &bar
	*/
	enum dispatch_methods = cast(Funcº) &disp;

	static extern(C) Valº disp(size_t ArgC, Tº Self, Atomº Key) in {
		assert(ArgC == 2,
			`attempt to invoke `~Tº.stringof~` with `~(ArgC-1).to_!string~
			` parameters (expected 1)`
		);
		assert(is_atom(Key));
	} body {
		debug (dispatch) {
			if (Key.Txt != `dump`) { 
				writeln_(`meth.disp.: `, Tº.stringof, `.`, Key.Txt);
			};
		};

		/* dispatch on Key */
		if (auto Method = *(cast(CtfeAtomº*) &Key) in DispatchTbl) {
			return (*Method)(ArgC, Self);
		};

		debug (dispatch) {
			writeln_(`method does not exist: `, Tº.stringof, `.`, Key.Txt);
		};
		return Valº.init;
	};

	/* dispatch table constructed at compile time */
	immutable DispatchTbl = ({
		alias Forwarderº = extern(C) Valº function(size_t, Tº);
		alias Tblº = Misc_.StaticHashTblº!(
			CtfeAtomº, Forwarderº, //CtfeAtomº.init,
			X => X.toHash, (X, Y) => X is Y
		);

		return Tblº.From!(({
			Tblº.Pairº[] Pairs;
			foreach (Idx; aliasSeqOf_!(iota_(DynamicNames.length))) {
				Pairs ~= Tblº.Pairº(
					CtfeAtomº(DynamicNames[Idx]),
					&f!(Idx, DynamicNames[Idx])
				);
			};
			return Pairs;
		})());
	})();

	/* forwarder */
	extern(C) static Valº f(size_t Idx, string DynName)(size_t ArgC, Tº Self) {
		enum StaticName = __traits(identifier, StaticSyms[Idx]);

		static if (IsVokeable!(StaticSyms[Idx])) {
			/* ? */
			auto X = cast() Self;
			X.Func = cast(Funcº) &StaticSyms[Idx];
			return X;

		} else static if (arity_!(StaticSyms[Idx]) == 0) {
			/* ? */
			return __traits(getMember, Self, StaticName)();

		} else {
			static assert(
				`invalid signature for dynamic method '`~StaticName~`'`
			);
		};
	};

	/* --- --- */

	alias StaticSyms = Filter_!(IsDynMethod,
		staticMap_!(SymOf, __traits(allMembers, Tº))
	);
	alias DynamicNames = staticMap_!(DynNameFor, StaticSyms);

	static assert(StaticSyms.length == DynamicNames.length);

	static enum IsDynMethod(Sym...) = DynNameFor!(Sym[0]) != ``;

	template SymOf(string Name) {
		static if (__traits(compiles, __traits(getMember, Tº, Name))) {
			alias SymOf = Alias_!(__traits(getMember, Tº, Name));
		} else {
			enum Placeholder = 0;
			alias SymOf = Placeholder;
		};
	};

	static template DynNameFor(Sym...) {
		static if (__traits(compiles, __traits(getAttributes, Sym[0]))) {
			alias Attrs = AliasSeq_!(__traits(getAttributes, Sym[0]));
			static if (Attrs.length == 1 && is(typeof(Attrs[0]) == string)) {
				enum DynNameFor = Attrs[0];
			} else {
				enum DynNameFor = ``;
			};
		} else {
			enum DynNameFor = ``;
		};
	};

	template IsVokeable(alias X) {
		static if (
			functionLinkage_!X == `C` &&
			__traits(isStaticFunction, X) &&
			is(typeof(X) Pº == function) &&
			is(Pº[0] == size_t)
		) {
			enum IsVokeable = true;
		} else {
			enum IsVokeable = false;
		};
	};

	/* dispatch table (constructed once at runtime) */
	/+struct S {
		static immutable Funcº[Atomº] DispatchTbl;
		__gshared static this() {
			foreach (Idx, DynName; DynamicNames) {
				DispatchTbl[Atomº(DynName)] = cast(Funcº) &f!(Idx, DynName);
			};
			DispatchTbl.rehash;
		};
	};+/
};

debug string dump_val(Valº V) {
	if (V is V.init) {return `.n`;};
	auto R = V.voke!`dump`;
	if (is_utf8(R)) {
		return (cast(Utf8º) R).Txt;
	};
	import std.format;
	return format(`;\?VAL(%08x)\;`, cast(size_t) V.Func);
};

/* --- closure --- */

struct Closureº {
	Funcº Func;
	Valº* Upvals;
	Rt_.RuntimeStateº* Runtime;
	enum PtrCount = 1;
	mixin ValSubType!1;
};

struct FuncInfoº {
	string Name;
};

/* -- atom type -- */

struct Atomº {
	Funcº Func = &atom_trampoline;
	union {
		char[size_t.sizeof * 2] ShortStr;
		struct {
			immutable(char)* LongStr;
			size_t LongStrHash;
		};
		size_t[2] Payload;
	};
	size_t Len;

	alias PtrCount = (typeof(this) X) => (X.IsShort ? 0 : 1);
	mixin ValSubType;

	invariant {
		if (Len > ShortStr.length) {
			assert(LongStrHash == hash_of_(LongStr[0 .. Len]));
		};
	};

	this(string Src) out (A) {
		assert(A.InternalTxt == Src);
		if (!A.IsShort) {
			assert(hash_of_(Src) == A.toHash);
		};
	} body {
		Len = Src.length;
		Payload = [0, 0];
		if (Src.length <= ShortStr.length) {
			ShortStr[0 .. Src.length] = Src;
		} else {
			LongStr = Src.ptr;
			LongStrHash = hash_of_(Src);
		};
	};

	size_t toHash() const @trusted pure nothrow {
		return IsShort ? hash_of_short_atom(Payload) : LongStrHash;
	};

	@property char[] Txt() const {return InternalTxt.dup;};
	private @property const(char)[] InternalTxt() const {
		if (IsShort) {
			return ShortStr[0 .. Len];
		} else {
			return LongStr[0 .. Len];
		};
	};

	@property bool IsShort() const @safe pure nothrow {
		/* note: this returns false when Len==0, but it doesn't matter */
		return !((Len - 1) & ~0b111);
		//return !(((Len - 8) >> 3) ^ 0x1FFFFFFF);
	};
	unittest {
		immutable char[1000] Src;
		foreach (size_t X; 0 .. Src.length) {
			auto A = Atomº(Src[0 .. X]);
			if (A.Len == 0) {continue;};
			assert(A.IsShort == (A.Len <= ShortStr.length));
		};
	};

	bool opEquals()(in auto ref typeof(this) A) const {
		if (/* these fields must be identical */
			Func !is A.Func ||
			Payload[1] != A.Payload[1] ||
			Len != A.Len
		) {return false;};

		if (Payload[0] == A.Payload[0]) {return true;};
		if (IsShort) {return false;};
		return LongStr[0 .. Len] == A.LongStr[0 .. Len];
	};

	version (none) @(`to-source`) auto to_utf8_source() {
		return utf8(`:`~Txt.assumeUnique_);
	};

	@(`to-hash`) auto to_hash_integer() {
		return Int64º(toHash);
	};

	@(`=`) static extern(C) Valº equals(size_t ArgC, Atomº Self, Atomº X) in {
		assert(ArgC == 2);
	} body {
		return bool_val(Self == X);
	};

	debug @(`dump`) auto dump() {
		return Utf8º((':'~InternalTxt).assumeUnique_);
	};
};

bool is_atom(Valº V) @trusted pure nothrow @nogc {
	return V.Func is Atomº.init.Func;
};

unittest {
	assert(Atomº(``) == Atomº(``));
	assert(Atomº(``).toHash == Atomº(``).toHash);
	assert(Atomº(`x`) == Atomº(`x`));
	assert(Atomº(`x`).toHash == Atomº(`x`).toHash);
	assert(Atomº(`x`) != Atomº(`y`));
	assert(Atomº(`x`).toHash != Atomº(`y`).toHash);
	assert(Atomº(`asdfghja`).IsShort);
	assert(!Atomº(`asdfghjaw`).IsShort);
	assert(Atomº(`asdfghjawww`).toHash);
	auto S = randomUUID_().toString;
	assert(Atomº(S) == Atomº(S));
	assert(Atomº(S).toHash == Atomº(S).toHash);
	assert(Atomº(S) != Atomº(randomUUID_().toString));
	assert(Atomº(S).toHash != Atomº(randomUUID_().toString).toHash);
};

private struct CtfeAtomº {
	Funcº Func = &atom_trampoline;
	size_t[2] Payload;
	size_t Len;

	alias Val this;
	@property auto ref Val()() inout {return *(cast(inout Valº*) &this);};
	static assert(this.sizeof == Valº.sizeof);

	this(string Src) in {
		assert(Src.length <= 2 * size_t.sizeof,
			`cannot create a long atom at compile-time`
		);
	} body {
		Len = Src.length;
		ubyte[2 * size_t.sizeof] X;
		X[0 .. Len] = cast(const ubyte[]) Src;
		Payload[0] = X[0] | (X[1] << 8) | (X[2] << 16) | (X[3] << 24);
		Payload[1] = X[4] | (X[5] << 8) | (X[6] << 16) | (X[7] << 24);
	};

	size_t toHash() const @safe pure nothrow {
		return hash_of_short_atom(Payload);
	};
};

private size_t hash_of_short_atom(size_t[2] Xs) @safe pure nothrow {
	return hash_of_(Xs[1], hash_of_(Xs[0]));
	/+static size_t mix(size_t X) @safe pure nothrow @nogc {
		enum M = 0x5bd1e995;
		X ^= X >> 13;
		X *= M;
		X ^= X >> 15;
		return X;
	};
	return mix(rol_!7(Xs[0])) + mix(Xs[1]);+/
};

/* forwarder for the atom dispatcher.
avoids cyclic dependency between `dispatch_methods` and `CtfeAtomº` */
private extern(C) Valº atom_trampoline(size_t, Valº, ...) {
	/* to be overwritten with a JMP */
	asm {naked; int 3; di 0xffffffff;};
};
shared static this() {
	/* patch the trampoline with the real jump target */
	uint Target = cast(uint) dispatch_methods!Atomº;
	Target -= (cast(uint) &atom_trampoline) + 5;

	auto Code = (cast(ubyte*) &atom_trampoline)[0 .. 5];
	//assert(Code == X86_.Op1.Break~x"ffffffff");

	uint PrevAccess = Misc_.set_page_access(Code, Misc_.PageAllAccess);
	Code[0] = X86_.Op1.JmpI4;
	Code[1 .. 5] = Misc_.bytes_of(Target);
	version (Windows) Misc_.set_page_access(Code, PrevAccess);
};

/* -- ns -- */

struct Namespaceº {
	Funcº Func = dispatch_methods!(typeof(this));
	private Implº O;
	enum PtrCount = 0;
	mixin ValSubType!2;

	private static class Implº {
		Symbolº Sym; /* the NS's own name */
		Maybeº!Namespaceº Parent;
		Entryº[Atomº] NameTbl;
		struct Entryº {
			Valº Val;
			Valº[Atomº] AttribTbl;
		};
		bool IsolateSubSyms; /* sub-symbols have this NS as their root */
	};

	invariant {
		assert(O);
		assert(&O.Sym);
	};

	this(
		string Name,
		Maybeº!(typeof(this)) Parent = Maybeº!(typeof(this)).init,
		Flag_!q{IsolateSubSyms} Iso = No_.IsolateSubSyms
	) {
		O = new Implº;
		O.IsolateSubSyms = Iso;
		O.Parent = Parent;
		O.IsolateSubSyms = Iso;
		O.Sym = Parent.NonNil ? Symbolº(Name, Parent.SelfSym) : Symbolº(Name);
	};

	@property bool HasParent() const {return O.Parent.NonNil;};

	@property auto SelfSym() inout {return O.Sym;};

	void define(string Name, Valº Val) {
		define(Atomº(Name), null, Val);
	};
	void define(string Name, Valº[Atomº] Attr, Valº Val) {
		define(Atomº(Name), Attr, Val);
	};
	void define(Atomº Name, Valº[Atomº] AttribTbl, Valº Val) {
		enforce_(Name.Txt != ``, `attempt to define empty symbol`);
		enforce_(Name.Txt != O.Sym.Name, `attempt to redefine symbol`);
		enforce_(Name !in O.NameTbl, `attempt to redefine symbol`);
		O.NameTbl[Name] = O.Entryº(Val, AttribTbl.dup);
	};

	auto query(Symbolº Sym) {
		struct Rº {
			Valº Ns;
			Symbolº Sym;
			Valº[Atomº] AttribTbl;
			Valº Val;
		};

		if (auto X = Atomº(Sym.Name) in O.NameTbl) {
			if (!Sym.HasParent || Sym.Parent == O.Sym) {
				auto P = O.IsolateSubSyms ? Symbolº(O.Sym.Name) : O.Sym;
				Rº R = {
					Ns : this,
					Sym : Symbolº(Sym.Name, P),
					AttribTbl : X.AttribTbl,
					Val : X.Val
				};
				return Nullable_!Rº(R);
			};
		};

		if (
			Sym.Name == O.Sym.Name &&
			(!Sym.HasParent || (HasParent && Sym.Parent == O.Parent.O.Sym))
		) {
			/* symbol refers to this NS */
			Rº R = {
				Ns : this,
				Sym : Sym,
				Val : this
			};
			return Nullable_!Rº(R);
		};

		if (HasParent) {
			return O.Parent.query(Sym);
		};

		return Nullable_!Rº.init;
	};

	@(`root`) Valº get_root_ns() {
		auto Ns = this;
		while (Ns.HasParent) {Ns = Ns.O.Parent;};
		return Ns;
	};

	@(`at`) static extern(C) Valº ns_get(
		size_t ArgC, typeof(this) Self, Symbolº Sym, Valº Else
	) in {
		assert(ordered_(2, ArgC, 3));
	} body {
		if (is_atom(cast(Valº) Sym)) {
			Sym = Symbolº((cast(Atomº) Sym).Txt.assumeUnique_);
		} else {
			assert(is_symbol(Sym));
		};
	
		auto Q = Self.query(Sym);
		if (Q.isNull) {
			if (ArgC == 3) {return Else;};
			throw new Exception(`reference to undefined symbol`);
		};
		return Q.Val;
	};
	
	@(`def`) static extern(C) Valº ns_define(
		size_t ArgC, typeof(this) Self, Atomº Name, Htableº AttribDict, Valº Val
	) in {
		assert(ArgC == 4);
		assert(is_atom(Name));
		assert(AttribDict is Valº.init || is_htable(AttribDict));
	} body {
		Self.define(
			Name,
			AttribDict !is Valº.init ? AttribDict.O : null,
			Val
		);
		return Valº.init;
	};

	debug @(`dump`) auto dump() {
		return Utf8º(dump_val(SelfSym));
	};
};

bool is_namespace(Valº V) {return V.Func is Namespaceº.init.Func;};

/* -- symbol type -- */

struct Symbolº {
	/*
		symbols represent qualified and unqualified names.
		unqualified:
			`bar` -> symbol(`bar`)
		qualified:
			`foo:bar` -> symbol(`bar`, symbol(`foo`))
	*/
	Funcº Func = dispatch_methods!(typeof(this));
	NullableRef_!Symbolº Parent = null;
	Ptr1stº!(immutable char) Name;
	enum PtrCount = 2;
	mixin ValSubType;

	invariant {
		assert(Name != ``);
	};

	this(string N) {
		enforce_(N != ``, `symbol cannot be empty`);
		Name = N;
	};

	this(string N, typeof(this) P) {
		this(N, Nullable_!(typeof(this))(P));
	};

	this(string N, Nullable_!(typeof(this)) P) {
		this(N);
		if (!P.isNull) {
			/* this casting business is to avoid triggering invariants on
			uninitialised memory */
			void* Ptr = Rt_.valigned_malloc!Symbolº(null, 1);
			*(cast(ubyte[Symbolº.sizeof]*) Ptr) = Misc_.bytes_of(P.get);
			Parent.bind(cast(Symbolº*) Ptr);
		};
	};

	@property bool HasParent() const {return !Parent.isNull;};

	bool opEquals()(in auto ref typeof(this) A) const {
		if (A.Name != Name) {return false;};
		if (A.HasParent != HasParent) {return false;};
		if (HasParent) {return A.Parent == Parent;};
		return true;
	};

	version (none) @(`to-source`) Utf8º to_source() {
		return (!HasParent ? Utf8º.init : Parent.to_source~`:`)~Name;
	};

	debug @(`dump`) auto dump() {
		return Utf8º(HasParent ? dump_val(Parent)~`:`~Name : Name);
	};
};

bool is_symbol(Valº V) {
	return V.Func is Symbolº.init.Func;
};

version (none) unittest {
	auto f(Symbolº Sym) {
		return cast(Utf8º) Sym.voke((`to-source`));
	};
	assert(f(Symbolº(`bar`)) == `bar`.utf8);
	assert(f(Symbolº(`foo`, Symbolº(`bar`))) == `bar:foo`.utf8);
	assert(f(Symbolº(`foo`, Symbolº(`bar`, Symbolº(`z`)))) == `z:bar:foo`.utf8);
};

/* -- invocation type -- */

struct Invocationº {
	Funcº Func = dispatch_methods!(typeof(this));
	Valº* InvokeePtr;
	Ptr1stº!Valº Params;
	enum PtrCount = 2;
	mixin ValSubType;

	invariant {assert(InvokeePtr);};

	this()(Valº V, Valº[] Xs) {
		this(V, Xs.stride_(1));
	};

	this(Tº)(Valº Vokee, Tº Xs) if (
		isForwardRange_!Tº && is(ElementType_!Tº : Valº)
	) out {
		assert(*InvokeePtr is Vokee);
		assert(Params.length == walkLength_(Xs.save));
	} body {
		size_t Len = 1 + walkLength_(Xs.save);
		Valº* Elems = Rt_.valigned_malloc!Valº(null, Len);
		Elems[0] = Vokee;
		copy_(Xs.save, Elems[1 .. Len]);
		InvokeePtr = Elems;
		Params = Elems[1 .. Len];
	};

	@(`invokee`) @property auto Invokee() {return *InvokeePtr;};

	@(`params`) @property auto Tail() {return Csliceº(Params[]);};

	debug @(`dump`) auto dump() {
		return Utf8º(dump_val(*InvokeePtr)~dump_val(Csliceº(Params[])));
	};
};

bool is_invocation(Valº V) {
	return V.Func is Invocationº.init.Func;
};

/* -- basic array slice type -- */

struct Csliceº {
	/* contiguous slice (aligned) */
	Funcº Func = dispatch_methods!(typeof(this));
	union {
		Ptr1stº!Valº Elems;
		struct {
			Valº* Ptr;
			size_t Len;
		};
	};
	enum PtrCount = 1;
	mixin ValSubType!1;

	invariant {
		assert(X86_.is_valigned(cast(size_t) Elems.ptr));
	};

	this(Valº[] Xs) {
		Elems = Xs;
	};

	alias from = of;
	static auto of(Valº[] Xs...) {
		auto New = alloc(Xs.length);
		New[] = Xs[];
		return typeof(this)(New);
	};

	@(`front?`) auto nonempty() {
		return bool_val(Elems != []);
	};

	@(`front`) auto front() {
		return Elems[0];
	};

	@(`next`) auto next() {
		return typeof(this)(Elems[1 .. $]);
	};

	@(`len`) auto length() {
		return Int64º(Len);
	};

	@(`dup`) auto duplicate() {
		Valº[] New = alloc(Len);
		New[] = Elems[];
		return typeof(this)(New);
	};

	@(`at`) static extern(C) Valº at(
		size_t ArgC, typeof(this) Self, Valº IdxV
	) in {
		assert(ArgC == 2);
	} body {
		ptrdiff_t Idx = val_to_ptrdiff_t(IdxV);
		if (Idx < 0) {Idx += Self.Elems.length;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx, Self.Elems.length));
		};
		return Self.Elems[Idx];
	};

	@(`slic`) static extern(C) typeof(this) slice(
		size_t ArgC, typeof(this) Self, Valº V1, Valº V2
	) in {
		assert(ArgC.among_(2, 3));
	} out (X) {
		assert(X.Len <= Self.Len);
	} body {
		size_t Len = Self.Elems.length;
		if (ArgC == 2) {return slice(3, Self, V1, Int64º(Len));};

		ptrdiff_t Idx1 = val_to_ptrdiff_t(V1);
		ptrdiff_t Idx2 = val_to_ptrdiff_t(V2);
		if (Idx1 < 0) {Idx1 += Len;};
		if (Idx2 < 0) {Idx2 += Len;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx1, Idx2, Len));
		};
		return typeof(this)(Self.Elems[Idx1 .. Idx2]);
	};

	private static Valº[] alloc(size_t Len) {
		return Rt_.valigned_malloc!Valº(null, Len)[0 .. Len];
	};

	debug @(`dump`) auto dump() {
		return Utf8º(`(`~Elems[].map_!(X => dump_val(X)).join_(` `)~`)`);
	};
};

bool is_cslice(Valº V) {
	return V.Func is Csliceº.init.Func;
};

unittest {
	auto A = Csliceº.of(
		Atomº(`foo`), Decimalº(66),
		Atomº(`bar`), Utf8º(`words`),
	);
	assert((cast(Int64º) A.voke!`len`) == (cast(Csliceº) A).Len);
	assert((cast(Int64º) A.voke!`len`) == Decimalº(4));

	auto B = A.voke!`slic`.voke(Int64º(2));
	assert((cast(Int64º) B.voke!`len`) == (cast(Csliceº) B).Len);
	assert((cast(Int64º) B.voke!`len`) == Decimalº(2));
};

/* -- basic dict type -- */

struct Htableº {
	Funcº Func = dispatch_methods!(typeof(this));
	Valº[Atomº] O;
	enum PtrCount = 1;
	mixin ValSubType!2;

	this(Valº[Atomº] X) {
		O = X;
	};

	@(`dup`) auto duplicate() {
		return typeof(this)(O.dup);
	};

	@(`len`) auto length() {
		return Int64º(O.length);
	};

	@(`at`) static extern(C) Valº at(
		size_t ArgC, typeof(this) Self, Atomº Key
	) in {
		assert(ArgC == 2);
		assert(is_atom(Key));
	} body {
		if (auto X = Key in Self.O) {return *X;};
		throw new RangeError_;
	};

	@(`asoc`) static extern(C) typeof(this) asoc(
		size_t ArgC, typeof(this) Self, Atomº Key, Valº Val
	) in {
		assert(ArgC == 3);
		assert(is_atom(Key));
	} body {
		auto NewTbl = Self.O.dup;
		NewTbl[Key] = Val;
		return typeof(this)(NewTbl);
	};
};

bool is_htable(Valº V) {
	return V.Func is Htableº.init.Func;
};

/* -- utf8 string type -- */

struct Utf8º {
	Funcº Func = dispatch_methods!(typeof(this));
	Ptr1stº!(immutable char) Txt;
	size_t Len; /* number of codepoints */
	enum PtrCount = 1;
	mixin ValSubType;

	invariant {
		assert(Len == Txt[].count_);
	};

	this(string Src) {
		Txt = Src;
		Len = Src.count_;
	};

	auto opBinary(string Op : `~`)(string X) const {
		return typeof(this)(Txt~X);
	};

	bool opEquals()(in auto ref typeof(this) X) const {
		return X.Txt == Txt;
	};

	@(`len`) auto len_integer() const {
		return Int64º(Len);
	};

	@(`at`)	static extern(C) auto read_codepoint(
		size_t ArgC, Utf8º Self, Valº IdxV
	) in {
		assert(ArgC == 2);
	} body {
		ptrdiff_t Idx = val_to_ptrdiff_t(IdxV);
		if (Idx < 0) {Idx += Self.Len;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx, Self.Len));
		};
		size_t ReadIdx = toUTFindex_(Self.Txt, Idx);
		{
			auto SubStr = Self.Txt[ReadIdx .. $];
			return Int64º(decode_(SubStr));
		};
	};

	@(`slic`) static extern(C) auto slice(
		size_t ArgC, Utf8º Self, Valº V1, Valº V2
	) in {
		assert(ArgC == 3);
	} body {
		ptrdiff_t Idx1 = val_to_ptrdiff_t(V1);
		ptrdiff_t Idx2 = val_to_ptrdiff_t(V2);
		if (Idx1 < 0) {Idx1 += Self.Len;};
		if (Idx2 < 0) {Idx2 += Self.Len;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx1, Idx2, Self.Len));
		};
		size_t Start = toUTFindex_(Self.Txt, Idx1);
		size_t End = Start + toUTFindex_(Self.Txt[Start .. $], Idx2 - Idx1);
		return typeof(this)(Self.Txt[Start .. End]);
	};

	debug @(`dump`) auto dump() {
		return Utf8º('`'~Txt~'`');
	};
};

bool is_utf8(Valº V) {
	return V.Func is Utf8º.init.Func;
};

/* -- numeric types -- */

bool is_number(Valº V) {
	return is_int64(V) || is_decimal(V);
};

struct Int64º {
	Funcº Func = dispatch_methods!(typeof(this));
	size_t Hash;
	long Num;

	enum PtrCount = 0;
	mixin ValSubType;

	invariant {
		assert(Hash == hash_of_(Num));
	};

	this(long X) pure @safe nothrow {
		Num = X;
		Hash = hash_of_(X);
	};

	string toString() const {
		return Num.to_!string;
	};

	size_t toHash() const {
		return Hash;
	};

	bool opEquals()(in auto ref typeof(this) A) const {
		return Num == A.Num;
	};
	bool opEquals(in long A) const {
		return Num == A;
	};

	auto opCast(Tº)() inout {
		return cast(inout Tº) (* cast(Valº*) &this);
	};
	long opCast(Tº : long)() const {
		return Num;
	};

	typeof(this) opBinary(string Op)(in typeof(this) A) const {
		return typeof(this)(mixin(`Num `~Op~` A.Num`));
	};

	typeof(this) opUnary(string Op : `-`)() const {
		return typeof(this)(-Num);
	};

	@property typeof(this) Abs() const {
		return typeof(this)((Num ^ (Num >> 63)) - (Num >> 63));
	};

	auto opBinary(string Op)(in typeof(this) A) const if (
		Op.among_(`+`, `-`, `*`, `/`, `^^`)
	) {
		return typeof(this)(mixin(`Num `~Op~` A.Num`));
	};

	@(`=`) static extern(C) Valº equals_number(
		size_t ArgC, typeof(this) Self, Valº A
	) in {
		assert(ArgC == 2);
	} body {
		return bool_val(
			is_int64(A) ? (cast(typeof(this)) A) == Self :
			is_decimal(A) ? (cast(Decimalº) A) == Self :
			false
		);
	};

	@(`to-hash`) auto to_hash_integer() const {
		return typeof(this)(toHash);
	};
};

bool is_int64(Valº V) {
	return V.Func is Int64º.init.Func;
};

unittest {
	assert(Int64º(0).Abs == Int64º(0));
	assert(Int64º(1).Abs == Int64º(1));
	assert(Int64º(2).Abs == Int64º(2));
	assert(Int64º(-1).Abs == Int64º(1));
	assert(Int64º(-2).Abs == Int64º(2));
	assert(Int64º(long.max).Abs == Int64º(long.max));
	assert(
		Int64º(0xf000ffff_ffffffffL).Abs ==
		Int64º(-0xf000ffff_ffffffffL)
	);
	assert(Int64º(long.min + 1).Abs == Int64º(long.max));
	assert(Int64º(long.min).Abs == Int64º(long.min)); /* overflow */
};

unittest {
	foreach (X; [
		Int64º(0), Int64º(1), Int64º(2), -Int64º(1), -Int64º(2),
		Int64º(long.max), -Int64º(long.max), -Int64º(long.max - 1),
	]) {
		assert(X == X);
		assert(X.toHash == X.toHash);
		if (X.Num != 0) {
			assert(X != -X);
			assert(X.toHash != (-X).toHash);
		};
	};
};

struct Decimalº {
	Funcº Func = dispatch_methods!(typeof(this));
	immutable(DynDecº)* Num;
	size_t Hash;
	BitFlags_!(MpDec_.Statusº) Status;

	enum PtrCount = 1;
	mixin ValSubType;

	invariant {
		assert(Num);
		assert(Num.IsReduced);
	};

	private this(DynDecº* X, typeof(Status) S = MpDec_.Statusº.init) {
		Status &= S;
		MpDec_.qreduce(X, X, &MpDec_.Ctx, &Status);
		Num = X.assume_unique();
		Hash = Num.toHash;
	};

	this(Tº)(Tº Src) if (!isSigned_!Tº) {
		ulong Mag = Src;
		auto X = new DynDecº(0);
		MpDec_.qadd_u64(X, X, Mag, &MpDec_.Ctx, &Status);
		this(X);
	};

	this(Tº)(Tº Src) if (isSigned_!Tº) {
		long N = Src;
		auto X = new DynDecº(0);
		MpDec_.qadd_i64(X, X, N, &MpDec_.Ctx, &Status);
		this(X);
	};

	this(immutable(DynDecº)* X) in {
		assert(X.IsReduced);
	} body {
		Num = X;
		Hash = X.toHash;
	};

	static @property auto Infinity() {
		auto X = new DynDecº(0);
		MpDec_.setspecial(X, MpDec_.Flagº.Pos, MpDec_.Flagº.Inf);
		return typeof(this)(X);
	};

	static @property auto NaN() {
		auto X = new DynDecº(0);
		MpDec_.setspecial(X, MpDec_.Flagº.Pos, MpDec_.Flagº.NaN);
		return typeof(this)(X);
	};

	@property auto Abs() const {
		auto X = new DynDecº(0);
		typeof(Status) S;
		MpDec_.qabs(X, Num, &MpDec_.Ctx, &S);
		return typeof(this)(X, S);
	};

	auto opCast(Tº)() inout {
		return cast(inout Tº) (* cast(Valº*) &this);
	};
	long opCast(Tº : long)() const {
		auto X = DynDecº(0);
		typeof(Status) S;
		MpDec_.qtrunc(&X, Num, &MpDec_.Ctx, &S);
		assert(S == S.init);
		return MpDec_.qget_i64!long(&X, &S);
	};

	bool opEquals()(in auto ref typeof(this) A) const {
		if (Hash != A.Hash) {return false;};
		if (Num is A.Num) {return true;};
		return MpDec_.cmp_total!int(Num, A.Num) == 0;
	};

	bool opEquals()(in auto ref Int64º A) const {
		uint S;
		long B = MpDec_.qget_i64!long(Num, &S);
		return !S && A.Num == B;
	};

	auto opUnary(string Op : `-`)() const {
		auto X = new DynDecº(0);
		typeof(Status) S;
		MpDec_.qcopy_negate(X, Num, &S);
		return typeof(this)(X, S);
	};

	private alias BinOpTbl = Alias_!([
		`+` : `qadd`,
		`-` : `qsub`,
		`*` : `qmul`,
		`/` : `qdiv`,
		`^^` : `qpow`,
	]);
	auto opBinary(string Op)(typeof(this) A) const if (!!(Op in BinOpTbl)) {
		auto X = new DynDecº(0);
		typeof(Status) S;
		mixin(`MpDec_.`~BinOpTbl[Op]~`(X, Num, A.Num, &MpDec_.Ctx, &S);`);
		return typeof(this)(X, S);
	};

	string toString() const {
		return Num.toString;
	};

	@(`=`) static extern(C) Valº equals_number(
		size_t ArgC, typeof(this) Self, Valº A
	) in {
		assert(ArgC == 2);
	} body {
		return bool_val(
			is_decimal(A) ? Self == cast(typeof(this)) A :
			is_int64(A) ? Self == cast(Int64º) A :
			false
		);
	};

	@(`cmpr`) static extern(C) auto cmp(
		size_t ArgC, typeof(this) Self, Valº A
	) in {
		assert(ArgC == 2);
		assert(is_decimal(A));
	} out (X) {
		assert(ordered_(-1, cast(long) X, 1));
	} body {
		return Int64º(MpDec_.cmp_total!int(Self.Num, (cast(Decimalº) A).Num));
	};

	@(`to-hash`) auto to_hash_integer() const {
		return Int64º(Hash);
	};

	/* construct from components of numeric literal */
	static typeof(this) from_lit(
		byte Sign, in dchar[] IntChrs, in dchar[] FracChrs, uint Radix
	) in {
		assert(Radix >= 2);
	} body {
		typeof(Status) S;
		auto X = new DynDecº(0);
		/* temporary numbers */
		auto A = DynDecº(0);
		auto B = DynDecº(0);

		void add_digit(uint Di, int Exp) {
			/* X += Digit * Radix^^Exp; */
			MpDec_.qset_u32(&A, Radix, &MpDec_.Ctx, &S); /* A <- Radix */
			MpDec_.qset_i32(&B, Exp, &MpDec_.Ctx, &S); /* B <- Exp */
			MpDec_.qpow(&A, &A, &B, &MpDec_.Ctx, &S); /* A ^^= B */
			MpDec_.qmul_u32(&A, &A, Di, &MpDec_.Ctx, &S); /* A *= Digit */
			MpDec_.qadd(X, X, &A, &MpDec_.Ctx, &S); /* X += A */
		};

		foreach (Idx, Chr; FracChrs) {
			auto Src = (&Chr)[0 .. 1];
			int Exp = -(Idx + 1);
			add_digit(parse_!uint(Src, Radix), Exp);
			enforce_(Src == []);
		};

		foreach (Idx, Chr; IntChrs) {
			auto Src = (&Chr)[0 .. 1];
			uint Exp = IntChrs.length - (Idx + 1);
			add_digit(parse_!uint(Src, Radix), Exp);
			enforce_(Src == []);
		};

		if (Sign < 0) {MpDec_.set_negative(X);};

		return typeof(this)(X, S);
	};

	static typeof(this) from_bytes(Tº)(Tº Src) if (
		isInputRange_!Tº && is(ElementType_!Tº == ubyte)
	) out (X) {
		assert(X.Num);
	} body {
		return typeof(this)([DynDecº.from_bytes(Src)].ptr);
	};

	debug @(`dump`) auto dump() {
		return Utf8º(toString.translate_(['.' : ',']));
	};
};

bool is_decimal(Valº V) {
	return V.Func is Decimalº.init.Func;
};

// NOTE: the current setup may exhibit poor data locality
// because the descriptor and coefficient are allocated on different heaps
struct DynDecº {
	private MpDec_.Decº Descriptor;

	invariant {
		assert(MpDec_.isstatic!int(&this));
		assert(!MpDec_.isstatic_data!int(&this));
		assert(!MpDec_.isconst_data!int(&this));
		auto De = &Descriptor;
		assert(cast(void*) &this is cast(void*) De);
		assert(De.Len);
		assert(De.Len <= De.Alloc);
		assert(De.Len <= De.Digits);
		assert(De.Digits < 0x1000);
		assert(De.Data);
	};

	/* create */
	this(int Z) in {
		assert(Z == 0);
	} out {
		assert(MpDec_.iszero!int(&this));
	} body {
		Descriptor.Alloc = MpDec_.MinAlloc;
		Descriptor.Data = MpDec_.alloc!(uint*)(Descriptor.Alloc, uint.sizeof);
		MpDec_.set_static(&this);
		MpDec_.zerocoeff(&this);
	};

	private this(MpDec_.Decº De) {
		Descriptor = De;
	};

	~this() {
		assert(&this !is null);
		MpDec_.del(&this);
	};

	/* make immutable */
	auto assume_unique() {
		return cast(immutable) &this;
	};

	/* hash of all the value components */
	/* be sure to mpd_reduce() before calculating hash */
	size_t toHash() immutable {
		enum BufSz = 64;
		static auto buffer(Tº)(Tº Src) {
			ubyte[BufSz] Buf;
			copy_(Src, Buf[]);
			return Buf;
		};
		return to_bytes()
			.chunks_(BufSz)
			.map_!buffer
			.fold_!((Acc, Buf) => hash_of_(Buf, Acc))(size_t(0))
		;
	};

	/* serialise into a hashable byte sequence */
	auto to_bytes() immutable {
		alias Fº = MpDec_.Flagº;

		auto De = cast() Descriptor;
		De.Flags &= BitFlags_!Fº(Fº.Pos, Fº.Neg, Fº.Inf, Fº.NaN, Fº.SNaN);
		De.Alloc = 0;
		auto Co = De.Data[0 .. De.Len];
		De.Data = null;

		return only_(Misc_.arr_tuple(Misc_.bytes_of(De)).expand)
			.chain_(cast(ubyte[]) Co)
		;
	};

	static auto from_bytes(Tº)(Tº Srcª) if (
		isInputRange_!Tº && is(ElementType_!Tº == ubyte)
	) {
		InputRange_!ubyte Src = inputRangeObject_(Srcª);

		/* copy descriptor */
		MpDec_.Decº De;
		enforce_(copy_(
			Src.take_(De.sizeof),
			Misc_.bslic_of(&De)
		).length == 0);
		assert(De !is De.init);
		assert(De.Data is null);
		assert(De.Alloc == 0);

		/* copy coefficient */
		De.Alloc = max_(De.Len, MpDec_.MinAlloc);
		De.Data = MpDec_.calloc!(uint*)(De.Alloc, uint.sizeof);
		assert(De.Data);
		enforce_(copy_(
			Src.take_(De.Len * uint.sizeof),
			cast(ubyte[]) (De.Data[0 .. De.Len])
		).length == 0);

		MpDec_.set_static(&De);
		return typeof(this)(De);
	};

	string toString() const {
		char* Str;
		size_t Len = MpDec_.to_sci_size!size_t(&Str, &this, 0);
		assert(Str);
		scope(exit) {MpDec_.free(Str);};
		return Str[0 .. Len].idup;
	};

	@property bool IsReduced() immutable {
		uint S;
		auto Xm = typeof(cast() this)(0);
		MpDec_.qreduce(&Xm, &this, &MpDec_.Ctx, &S);
		auto X = Xm.assume_unique;
		return X.toHash == toHash && opCmp(*X) == 0;
	};

	@property auto Coeff() immutable {
		return Descriptor.Data[0 .. Descriptor.Len];
	};

	int opCmp(immutable ref typeof(this) X) immutable {
		/* cmp_total seems to have a bug, where it sometimes returns 1 for
		identical operands, so test for identical first */
		if (equal_(to_bytes, X.to_bytes)) {return 0;};
		return MpDec_.cmp_total!int(&X, &this);
	};
};

unittest {
	auto X = DynDecº(0);
	assert(MpDec_.iszero!int(&X));
	immutable ImmX = X.assume_unique();
	assert(MpDec_.iszero!int(ImmX));
};

unittest {
	Decimalº X;

	X = Decimalº(0);
	assert(X.to_!string == `0`);

	X = Decimalº(ulong.max);
	assert(X.to_!string == ulong.max.to_!string);

	X = Decimalº.from_lit(1, `50`d, `44411`d, 10);
	assert(X.to_!string == `50.44411`);

	X = Decimalº.from_lit(-1, `12345678901234567`d, `09876`d, 10);
	assert(X.to_!string == `-12345678901234567.09876`);
	assert((-X).to_!string == `12345678901234567.09876`);

	X = Decimalº.from_lit(-1, `deadbeef`d, `0`d, 16);
	assert(X.to_!string == `-3735928559`);

	X = Decimalº.from_lit(1, `1101`d, `0011`d, 2);
	assert(X.to_!string == `13.1875`);

	X = Decimalº.from_lit(1, `y11zzyy`d, `11zzz`d, 36);
	assert(X.to_!string); /* probably inexact, just make sure we get anything */
};

unittest {
	Decimalº X = Decimalº.from_lit(1, `y11zzyy`d, `11zzz`d, 36);
	assert(X - X == Decimalº(0));
};

unittest {
	Decimalº X = Decimalº.from_lit(-1, `deadbeef`d, `0012f`d, 16);
	version (none) assert((cast(Int64º) X) == Int64º(-3735928559L));
};

auto val_to_size_t(Valº V) {
	if (is_int64(V)) {
		return to_!size_t(cast(long) cast(Int64º) V);
	};
	if (is_decimal(V)) {
		return to_!size_t(cast(long) cast(Decimalº) V);
	};
	assert(0);
};

auto val_to_ptrdiff_t(Valº V) {
	if (is_int64(V)) {
		return to_!ptrdiff_t(cast(long) cast(Int64º) V);
	};
	if (is_decimal(V)) {
		return to_!ptrdiff_t(cast(long) cast(Decimalº) V);
	};
	assert(0);
};

/* --- hash-tree type --- */

struct Htreeº {
	/*
	immutable hash array mapped trie
	adapted from https://github.com/clojure/.../lang/PersistentHashMap.java

	hardcoded branching factor of 5
	*/

	Funcº Func = dispatch_methods!(typeof(this));
	private HtreeRootº Root;
	private size_t TotalLeafCount;
	enum PtrCount = 1;
	mixin ValSubType;

	private this(HtreeRootº R, size_t C) {Root = R; TotalLeafCount = C;};

	@property auto Count() const {return TotalLeafCount;};

	@(`#`) @property auto CountInt64() const {
		return Int64º(Count);
	};

	@(`at`) static extern(C) Valº at(
		size_t ArgC, typeof(this) Self, Valº Key, Valº Else
	) {
		/* lookup an element by its key; return Else on failure */
		return Self.Root.visit_!(
			() => Else,
			(HtreeLeafº* X) => X.at(Key, Else),
			(immutable HtreeBranchº X) => X.at(hash_of(Key), 0, Key, Else),
		);
	};

	@(`asoc`) static extern(C) typeof(this) asoc(
		size_t ArgC, typeof(this) Self, Valº Key, Valº Val
	) out (X) {
		assert(X.Root.hasValue);
	} body {
		/* insert a leaf; overwrite if it already exists */
		return Self.Root.visit_!(
			() => typeof(this)(
				HtreeRootº(HtreeLeafº.alloc(Key, Val)),
				1
			),
			(HtreeLeafº* X) {
				if (*X is HtreeLeafº(Key, Val)) {/* no change */
					return Self;
				};
				if (keys_equal(Key, X.Key)) {/* overwrite */
					return typeof(this)(
						HtreeRootº(HtreeLeafº.alloc(Key, Val)),
						1
					);
				};
				auto New = HtreeBitmapº
					.of(hash_of(X.Key), 0, X)
					.asoc(hash_of(Key), 0, HtreeLeafº.alloc(Key, Val))
				;
				return typeof(this)(
					HtreeRootº(New),
					2
				);
			},
			(immutable HtreeBranchº X) {
				auto New = X.asoc(hash_of(Key), 0, HtreeLeafº.alloc(Key, Val));
				if (X is New) {
					return Self; /* no change */
				};
				return typeof(this)(
					cast(HtreeRootº) New,
					Self.Count + 1
				);
			},
		);
	};

	@(`disoc`) static extern(C) typeof(this) disoc(
		size_t ArgC, typeof(this) Self, Valº Key
	) {
		/* remove a k/v pair; do nothing if it doesn't exist */
		return Self.Root.visit_!(
			() => typeof(this).init,
			(HtreeLeafº* X) {
				if (keys_equal(Key, X.Key)) {
					return typeof(this).init;
				};
				return Self; /* no change */
			},
			(immutable HtreeBranchº X) {
				auto New = X.disoc(hash_of(Key), 0, Key);
				if (New.peek!(typeof(X)) && X is *New.peek!(typeof(X))) {
					return Self; /* no change */
				};
				return typeof(this)(
					cast(HtreeRootº) New,
					Self.Count - 1
				);
			},
		);
	};

	private static uint hash_of(Valº Key) {
		static assert(is(uint == size_t));
		return val_to_size_t(Key.voke!`to-hash`);
	};

	private static bool keys_equal(Valº K1, Valº K2) {
		if (K1 is K2) {return true;};
		return K1.voke!`=`.voke(K2) !is Valº.init;
	};

	debug string dump() {
		return Root.visit_!(
			() => `()`,
			(HtreeLeafº* X) => X.dump(),
			(immutable HtreeBranchº X) => (cast()X).dump(),
		);
	};
};

bool is_htree(Valº V) {
	return V.Func is Htreeº.init.Func;
};

private alias HtreeNodeº = Algebraic_!(HtreeLeafº*, immutable HtreeBranchº);
private alias HtreeRootº = HtreeNodeº;

private struct HtreeLeafº {
	/* k/v pair */
	Valº Key;
	Valº Val;

	Valº at(Valº QueryKey, Valº Else) {
		if (Htreeº.keys_equal(QueryKey, Key)) {return Val;};
		return Else;
	};

	static auto alloc(Valº Key, Valº Val) out (X) {
		assert(X !is null);
		assert(X.Key is Key);
		assert(X.Val is Val);
	} body {
		enum Len = typeof(this).sizeof / Valº.sizeof;
		auto Mem = cast(typeof(this)*) Rt_.valigned_malloc!Valº(null, Len);
		return emplace_(Mem, Key, Val);
	};

	debug string dump() {
		import std.format;
		//return format(`(#%x: %s)`, Htreeº.hash_of(Key), *cast(uint[4]*)&Val);
		return format(`('%032b: .)`, Htreeº.hash_of(Key));
	};
};

private extern(C++) abstract class HtreeBranchº {extern(D) {
	/* sub-tree; contains one or more leaves */

	/* total number of leaves contained within the subtree */
	version (none) @property size_t LeafCount() const;

	/* lookup an element; return `Else` on failure */
	Valº at(uint Hash, uint Sh, Valº Key, Valº Else) const;

	/* return a branch containing the given leaf.
	`Sh` is how many bits `Hash` should be shifted by */
	immutable(typeof(this)) asoc(uint Hash, uint Sh, HtreeLeafº*) immutable;

	/* return a node without the given key */
	//HtreeNodeº disoc(uint Hash, uint Sh, Valº Key) immutable;
	VariantN_!4 disoc(uint Hash, uint Sh, Valº Key) immutable;

	debug string dump();
};};

private extern(C++) class HtreeBitmapº : HtreeBranchº {extern(D) {
	/* bitmapped branch node */
	uint LeafBmp; /* indicates which elements are leaves */
	uint BranchBmp; /* indicates which elements are branches */
	void*[0] Nodes; /* payload: up to 32 (pointers to) leaves/branches */

	alias ImmBrº = immutable HtreeBranchº;

	invariant {
		assert(ordered_(1, Length, 32));
		foreach (Pos; 0 .. 32) {
			uint Bit = 1 << Pos;
			if (Bit & LeafBmp) {
				assert(!(Bit & BranchBmp));
				assert(cast(HtreeLeafº*) Nodes.ptr[index(Bit)]);
			};
			if (Bit & BranchBmp) {
				assert(!(Bit & LeafBmp));
				assert(cast(ImmBrº) Nodes.ptr[index(Bit)]);
			};
		};
		assert(Length > 1 || BranchBmp != 0);
	};

	static auto of(uint Hash, uint Sh, HtreeLeafº* L) in {
		assert(L);
		assert(Sh % 5 == 0);
	} out (X) {
		assert(popcnt_(X.LeafBmp) == 1);
		assert(popcnt_(X.BranchBmp) == 0);
	} body {
		auto X = alloc_instance(1);
		X.LeafBmp = bitpos(Hash >> Sh);
		X.Nodes.ptr[0] = L;
		return cast(immutable) X;
	};

	static auto of(uint Hash, uint Sh, immutable HtreeCollisionº C) in {
		assert(C);
		assert(Sh % 5 == 0);
	} out (X) {
		assert(popcnt_(X.LeafBmp) == 0);
		assert(popcnt_(X.BranchBmp) == 1);
	} body {
		auto X = alloc_instance(1);
		X.BranchBmp = bitpos(Hash >> Sh);
		X.Nodes.ptr[0] = cast(void*) C;
		return cast(immutable) X;
	};

	version (none) override @property size_t LeafCount() const {
		size_t C;
		foreach (Pos; 0 .. 32) {
			uint Bit = 1 << Pos;
			if (Bit & BranchBmp) {
				C += (cast(ImmBrº) Nodes.ptr[index(Bit)]).LeafCount;
			};
		};
		return C + popcnt_(LeafBmp);
	};

	@property size_t Length() @safe pure nothrow const {
		return popcnt_(LeafBmp|BranchBmp);
	};

	override Valº at(uint Hash, uint Sh, Valº Key, Valº Else) const in {
		assert(Sh % 5 == 0);
	} body {
		uint Bit = bitpos(Hash >> Sh);

		if (Bit & LeafBmp) {/* it's a leaf node */
			auto Leaf = cast(HtreeLeafº*) Nodes.ptr[index(Bit)];
			return Leaf.at(Key, Else);
		};

		if (Bit & BranchBmp) {/* it's a branch node */
			auto Branch = cast(ImmBrº) Nodes.ptr[index(Bit)];
			return Branch.at(Hash, Sh + 5, Key, Else);
		};

		return Else; /* not found */
	};

	override ImmBrº asoc(
		uint Hash, uint Sh, HtreeLeafº* NewLeaf
	) immutable in {
		assert(Sh % 5 == 0);
	} body {
		uint Bit = bitpos(Hash >> Sh);
		auto Idx = index(Bit);

		if (Bit & BranchBmp) {/* insert into existing branch node */
			auto Branch = cast(ImmBrº) Nodes.ptr[Idx];
			auto NewBranch = Branch.asoc(Hash, Sh + 5, NewLeaf);
			return replace_node(Bit, Idx, NewBranch);
		};

		if (Bit & LeafBmp) {/* overlaps existing leaf node */
			auto ExLeaf = cast(HtreeLeafº*) Nodes.ptr[Idx];

			if (Htreeº.keys_equal(ExLeaf.Key, NewLeaf.Key)) {
				/* replace existing leaf */
				return replace_node(Bit, Idx, NewLeaf);
			};

			uint ExHash = Htreeº.hash_of(ExLeaf.Key);
			if (Hash == ExHash) {/* hash collision */
				return replace_node(
					Bit, Idx,
					HtreeCollisionº.of(Hash, ExLeaf, NewLeaf)
				);
			};

			/* expand the leaf to a branch */
			return replace_node(
				Bit, Idx,
				typeof(this)
					.of(ExHash, Sh + 5, ExLeaf)
					.asoc(Hash, Sh + 5, NewLeaf)
			);
		};

		/* insert new leaf */
		return insert_node(Bit, Idx, NewLeaf);
	};

	override VariantN_!4 disoc(uint Hash, uint Sh, Valº Key) immutable in {
		assert(Sh % 5 == 0);
	} body {
		uint Bit = bitpos(Hash >> Sh);
		auto Idx = index(Bit);

		if (Bit & BranchBmp) {/* branch may contain key */
			auto Branch = cast(ImmBrº) Nodes.ptr[Idx];

			return VariantN_!4(cast(immutable HtreeBranchº)
				(cast(HtreeNodeº) Branch.disoc(Hash, Sh + 5, Key))
					.visit_!(
						(HtreeLeafº* X) => replace_node(Bit, Idx, X),
						(ImmBrº X) => replace_node(Bit, Idx, X)
					)
			);
		};

		if (Bit & LeafBmp) {/* leaf may contain key */
			auto Leaf = cast(HtreeLeafº*) Nodes.ptr[Idx];

			if (Htreeº.keys_equal(Key, Leaf.Key)) {
				/* remove leaf */
				return VariantN_!4(
					remove_node(Bit, Idx, ~Bit & LeafBmp, BranchBmp)
				);
			};
		};

		/* key not found */
		return VariantN_!4(this);
	};

	immutable(typeof(this)) insert_node(
		uint Bit, ubyte Idx, void* Node
	) immutable in {
		assert(Length < 32);
	} body {
		auto Len = Length;
		auto X = alloc_instance(Len + 1);
		X.LeafBmp = Bit | LeafBmp;
		X.BranchBmp = BranchBmp;

		/* copy existing payload elements */
		X.Nodes.ptr[0 .. Idx] = cast(void*[]) Nodes.ptr[0 .. Idx];
		X.Nodes.ptr[Idx + 1 .. Len + 1] = cast(void*[]) Nodes.ptr[Idx .. Len];

		X.Nodes.ptr[Idx] = Node;

		assert(X.Length == Length + 1);
		return cast(immutable) X;
	};

	immutable(typeof(this)) replace_node(Tº)(
		uint Bit, ubyte Idx, Tº Node
	) immutable {
		if (Nodes.ptr[Idx] is cast(void*) Node) {/* no change */
			return this;
		};

		auto Len = Length;
		auto X = alloc_instance(Len);

		static if (is(Tº : ImmBrº)) {
			X.LeafBmp = ~Bit & LeafBmp;
			X.BranchBmp = Bit | BranchBmp;
		} else static if (is(Tº == HtreeLeafº*)) {
			X.LeafBmp = Bit | LeafBmp;
			X.BranchBmp = ~Bit & BranchBmp;
		} else {
			static assert(0);
		};

		X.Nodes.ptr[0 .. Len] = cast(void*[]) Nodes.ptr[0 .. Len];
		X.Nodes.ptr[Idx] = cast(void*) Node;

		assert(X.Length == Length);
		return cast(immutable) X;
	};

	HtreeNodeº remove_node(
		uint Bit, ubyte Idx, uint NewLeafBmp, uint NewBranchBmp
	) immutable out (X) {
		assert(Length == 2 || X.peek!ImmBrº);
	} body {
		auto Len = Length;
		if (Len == 2) {/* 2nd-last node */
			/* return remaining node */
			auto X = Nodes.ptr[(Idx + 1) % Len];
			if (~Bit & LeafBmp) {
				return HtreeNodeº(cast(HtreeLeafº*) X);
			};
			assert(~Bit & BranchBmp);
			/* don't collapse with subbranches */
		};

		auto X = alloc_instance(Len - 1);
		X.LeafBmp = NewLeafBmp;
		X.BranchBmp = NewBranchBmp;

		/* copy remaining payload elements */
		X.Nodes.ptr[0 .. Idx] = cast(void*[]) Nodes.ptr[0 .. Idx];
		X.Nodes.ptr[Idx .. Len - 1] = cast(void*[]) Nodes.ptr[Idx + 1 .. Len];

		assert(X.Length == Length - 1);
		return HtreeNodeº(cast(ImmBrº) X);
	};

	static auto alloc_instance(size_t Len) out (X) {
		assert(X !is null);
		auto Expect = (cast(void*) X) + __traits(classInstanceSize, typeof(X));
		assert(X.Nodes.ptr is Expect);
	} body {
		enum BaseSize = __traits(classInstanceSize, typeof(this));
		enum BaseAlign = classInstanceAlignment_!(typeof(this));
		alias alloc = Rt_.aligned_malloc!(ubyte, BaseAlign);

		/* allocate new class instance */
		size_t Size = BaseSize + Len*size_t.sizeof;
		void[] Mem = alloc(null, Size)[0 .. Size];
		debug {(cast(size_t[]) Mem)[] = size_t.max;};
		return emplace_!(typeof(this))(Mem);
	};

	static uint bitpos(uint Hash) {
		return 1 << (Hash & 0b11111);
	};

	ubyte index(uint Bit) @safe pure nothrow @nogc const {
		/* `Nodes` array index of the element indicated by `Bit` */
		return cast(ubyte) popcnt_((LeafBmp|BranchBmp) & (Bit - 1));
	};

	debug override string dump() {
		string[] S = [`{`];
		foreach (Sh; 0 .. 32) {
			uint Bit = 1 << Sh;
			alias f = X => (X == '\n' ? [dchar('\n'), dchar('\t')] : [X]);
			if (Bit & LeafBmp) {
				S ~= '\t'~map_!f(
					(cast(HtreeLeafº*) Nodes.ptr[index(Bit)]).dump()~`,`
				).join_.to_!string;
			};
			if (Bit & BranchBmp) {
				S ~= '\t'~map_!f(
					(cast(HtreeBranchº) Nodes.ptr[index(Bit)]).dump()~`,`
				).join_.to_!string;
			};
		};
		S ~= `}`;
		return S.join_('\n');
	};
};};

private extern(C++) class HtreeCollisionº : HtreeBranchº {extern(D) {
	/* ? */
	uint Collision; /* the colliding hash */
	size_t Len;
	align(16) HtreeLeafº[0] Leaves;

	static assert(X86_.is_valigned(Leaves.offsetof));
	invariant {
		assert(Len >= 2);
	};

	static auto of(uint Hash, HtreeLeafº* L1, HtreeLeafº* L2) {
		auto X = alloc_instance(2, Hash);
		X.Leaves.ptr[0 .. 2] = [*L1, *L2];
		return cast(immutable) X;
	};

	version (none) override @property size_t LeafCount() const {return Len;};

	override Valº at(uint Hash, uint, Valº Key, Valº Else) const in {
		assert(Sh % 5 == 0);
	} body {
		if (Hash != Collision) {return Else;};
		auto X = find(Key);
		if (X.empty) {return Else;};
		return X.front.Val;
	};

	override immutable(HtreeBranchº) asoc(
		uint Hash, uint Sh, HtreeLeafº* NewLeaf
	) immutable in {
		assert(Sh % 5 == 0);
	} body {
		if (Hash != Collision) {/* new leaf does not collide */
			/* nest the collision in a bitmap node */
			return HtreeBitmapº
				.of(Collision, Sh, this)
				.asoc(Hash, Sh, NewLeaf)
			;
		};

		auto Idx = idx_for(NewLeaf.Key);
		if (!Idx.isNull) {/* key already exists */
			if (Leaves.ptr[Idx].Val is NewLeaf.Val) {/* val already exists */
				return this;
			};

			/* overwrite leaf */
			auto New = alloc_instance(Len, Collision, Leaves.ptr[0 .. Len]);
			New.Leaves.ptr[Idx] = *NewLeaf;
			return cast(immutable) New;
		};

		/* insert new leaf */
		auto X = alloc_instance(Len + 1, Collision);

		/* copy existing leaves */
		alias Tº = HtreeLeafº[];
		X.Leaves.ptr[0 .. Idx] = cast(Tº) Leaves.ptr[0 .. Idx];
		X.Leaves.ptr[Idx + 1 .. Len + 1] = cast(Tº) Leaves.ptr[Idx .. Len];

		X.Leaves.ptr[Idx] = *NewLeaf;

		assert(X.Len == Len + 1);
		return cast(immutable) X;
	};

	override VariantN_!4 disoc(uint Hash, uint Sh, Valº Key) immutable in {
		assert(Sh % 5 == 0);
		assert(Hash == Collision);
	} body {
		auto Idx = idx_for(Key);
		if (Idx.isNull) {return VariantN_!4(this);}; /* key not found */
		if (Len == 2) {/* 2nd-last leaf */
			return VariantN_!4(cast(HtreeLeafº*) &Leaves.ptr[(Idx + 1) % Len]);
		};

		/* remove leaf */
		auto New = alloc_instance(Len - 1, Collision);
		/* copy remaining payload elements */
		alias Tº = HtreeLeafº[];
		New.Leaves.ptr[0 .. Idx] = cast(Tº) Leaves.ptr[0 .. Idx];
		New.Leaves.ptr[Idx .. Len - 1] = cast(Tº) Leaves.ptr[Idx + 1 .. Len];

		return VariantN_!4(cast(immutable HtreeBranchº) New);
	};

	auto find(Valº Key) const out (Xª) {
		auto X = cast() Xª;
		assert(hasLength_!(typeof(X)));
		assert(X.length <= Len);
		assert(X.empty || Htreeº.keys_equal(Key, X.front.Key));
	} body {
		return Leaves.ptr[0 .. Len].find_!(
			X => Htreeº.keys_equal(X.Key, Key)
		).stride_(1);
	};

	auto idx_for(Valº Key) const out (X) {
		assert(X.isNull || X < Len);
	} body {
		size_t Idx = Len - find(Key).length;
		return Nullable_!(size_t, size_t.max)(Idx < Len ? Idx : size_t.max);
	};

	static auto alloc_instance(
		size_t Len, uint Hash, in HtreeLeafº[] Leaves = []
	) in {
		assert(Leaves.length <= Len);
	} out (X) {
		assert(X !is null);
		auto Expect = (cast(void*) X) + __traits(classInstanceSize, typeof(X));
		assert(X.Leaves.ptr is Expect);
	} body {
		/* allocate new class instance */
		enum BaseSize = __traits(classInstanceSize, typeof(this));
		size_t Size = BaseSize + Len * HtreeLeafº.sizeof;
		alias alloc = Rt_.valigned_malloc!Valº;
		void[] Mem = alloc(null, Size / Valº.sizeof)[0 .. Size];

		auto X = emplace_!(typeof(this))(Mem);
		X.Collision = Hash;
		debug X.Leaves.ptr[0 .. Len] = HtreeLeafº(InvalidVal, InvalidVal);
		X.Leaves.ptr[0 .. Leaves.length] = cast(HtreeLeafº[]) Leaves[0 .. $];
		return X;
	}; 

	debug override string dump() {
		return `<collision:`~Collision.to_!string~`>`;
	};
};};


unittest {
	auto Tr = Htreeº.init;
	assert(Tr.voke!`at`.voke(Atomº(`foo`), Atomº(`nf`)) is Atomº(`nf`));

	auto Tr2 = Tr.voke!`asoc`.voke(Atomº(`foo`), Decimalº(22));
	{
		auto x = Tr2.voke!`at`.voke(Atomº(`foo`), Atomº(`nf`));
		assert(x.is_decimal);
		assert((cast(Decimalº) x) == Decimalº(22));
	};
};

unittest {
	enum Count = 30000;
	auto Tr = Htreeº.init;
	scope Keys = new Valº[Count];
	scope Vals = new Valº[Count];

	foreach (Idx; 0 .. Count) {
		Keys[Idx] = Int64º(Idx);
		Vals[Idx] = Int64º(-Idx);
	};

	foreach (Idx; 0 .. Count) {
		assert(val_to_size_t(Tr.voke!(`#`)) == Idx);
		assert(Tr.voke_u!(`at`).voke_u(Keys[Idx], InvalidVal) is InvalidVal);

		Tr = cast(Htreeº) Tr.voke_u!`asoc`.voke_u(Keys[Idx], Vals[Idx]);
		//auto x = Tr.dump();

		assert(val_to_size_t(Tr.voke!(`#`)) == Idx + 1);
		assert(Tr.voke_u!(`at`).voke_u(Keys[Idx], InvalidVal) is Vals[Idx]);
	};

	foreach (Idx; 0 .. Count) {
		assert(val_to_size_t(Tr.voke!(`#`)) == Count - Idx);
		assert(Tr.voke_u!(`at`).voke_u(Keys[Idx], InvalidVal) is Vals[Idx]);

		Tr = cast(Htreeº) Tr.voke_u!`disoc`.voke_u(Keys[Idx]);

		assert(Tr.voke_u!(`at`).voke_u(Keys[Idx], InvalidVal) is InvalidVal);
	};

	assert(val_to_size_t(Tr.voke!(`#`)) == 0);
};

/* --- array-tree type --- */

struct Atreeº {
	/*
	better known as 'PersistentVector'.
	adapted from http://github.com/clojure/···/lang/PersistentVector.java

	hardcoded branching factor of 32
	*/

	Funcº Func = dispatch_methods!(typeof(this));
	Branchº* Root = &EmptyBranch;
	Valº* Tail = EmptyLeaf.ptr;
	auto Attr = Attrº(0, 5);
	enum PtrCount = 2;
	mixin ValSubType;

	private alias Branchº = Alias_!(void*)[32];
	private alias Leafº = Valº[32];
	private static __gshared Branchº EmptyBranch; /* (immutable) */
	private static __gshared Leafº EmptyLeaf; /* (immutable) */

	@disable this();
	private this(int) {};
	private this(typeof(Attr) A, typeof(Root) R, typeof(Tail) T) {
		Attr = A; Root = R; Tail = T;
	};

	this(Tº)(Tº Src) if (isInputRange_!Tº && is(ElementType_!Tº : Valº)) {
		/* construct atree from any value range */

		static auto alloc_copy(Xº)(ref Xº Xs) {
			auto Arr = Rt_.valigned_malloc!Valº(null, Xs.length)[0 ..Xs.length];
			copy_(Xs, Arr);
			return Arr;
		};

		static if (hasLength_!Tº) {
			/* allocate all the leaves at once */
			this = adopt(alloc_copy(Src));
			return;
		};

		static Valº[] take_copy_and_drop(ref Tº Xs) {
			/* pop up to 32 elements off the front of X
			and copy them into a new tail/leaf array */
			Valº[Leafº.length] Buf;
			size_t Len;
			while (Len < Buf.length && !Xs.empty) {
				Buf[Len++] = Xs.front;
				Xs.popFront();
			};
			auto Ys = Buf[0 .. Len];
			return alloc_copy(Ys);
		};

		/* allocate leaves one at a time */
		this = adopt(take_copy_and_drop(Src));
		while (!Src.empty) {/* insert slices until the source is depleted */
			this = overflow_tail(take_copy_and_drop(Src));
		};
	};

	static auto adopt(Valº[] Src) in {/* construct atree using slices of Src */
		assert(X86_.is_valigned(cast(size_t) Src.ptr));
	} out (R) {
		assert(R.length == Src.length);
		if (R.length) {
			assert(R.Tail is &Src[$ - R.TailLen]);
		};
		if (R.length > Leafº.length) {
			assert((cast(Valº*) R.leaf_for(0)) is Src.ptr);
		};
	} body {
		if (Src == []) {return typeof(this)(0);};

		static Valº[] take_and_drop(ref Valº[] Xs) {
			size_t N = min_(Xs.length, Leafº.length);
			Valº[] Sub = Xs[0 .. N];
			Xs = Xs[N .. $];
			return Sub;
		};

		auto Xs = Src;

		/* initialise the tail with up to 32 elems from front of Src */
		Valº[] FirstSlice = take_and_drop(Xs);
		auto R = typeof(this)(
			Attrº(FirstSlice.length, 5),
			&EmptyBranch,
			FirstSlice.ptr
		);

		while (Xs != []) {/* insert slices until the source is depleted */
			R = R.overflow_tail(take_and_drop(Xs));
		};

		return R;
	};

	@property size_t length() const {return Attr.Count;};
	alias opDollar(size_t X : 0) = length;

	Valº opIndex(size_t Idx) {
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(Idx < Attr.Count);
		};
		return (*leaf_for(Idx))[Idx & 0b11111];
	};

	AtreeSliceº opIndex() {
		return AtreeSliceº(this, 0, length);
	};

	AtreeSliceº opIndex(size_t[2] Bounds) {
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(Bounds[0], Bounds[1], length));
		};
		return AtreeSliceº(this, Bounds[0], Bounds[1]);
	};

	size_t[2] opSlice(size_t Pos)(size_t S, size_t E) {return [S, E];};

	@property size_t TailIdx() const {
		if (Attr.Count < 32) {return 0;};
		return ((Attr.Count - 1) >>> 5) << 5;
	};

	@property size_t TailLen() const {
		return Attr.Count - TailIdx;
	};



	typeof(this) opBinary(string Op : `~`)(Valº Val) {
		/* atree ~ val */

		/* room in tail? */
		if (TailLen < 32) {
			auto NewTail = extend_tail(Tail[0 .. TailLen], Val);
			return typeof(this)(
				Attrº(Attr.Count + 1, Attr.Shift),
				Root,
				NewTail.ptr
			);
		};

		/* full tail, push into tree */
		return overflow_tail(extend_tail([], Val));
	};

	private typeof(this) overflow_tail(Valº[] NewTail) in {
		assert(TailLen == Leafº.length);
		assert(NewTail.length <= Leafº.length);
	} body {
		Leafº* TailLeaf = cast(Leafº*) Tail;
		Branchº* NewRoot;
		auto NewShift = Attr.Shift;
		/* overflow root? */
		if ((Attr.Count >>> 5) > (1 << Attr.Shift)) {
			NewRoot = dup_node(Branchº.init);
			(*NewRoot)[0 .. 2] = [Root, new_path(Attr.Shift, TailLeaf)];
			NewShift += 5;
		} else {
			NewRoot = push_tail(Attr.Shift, Root, TailLeaf);
		};

		return typeof(this)(
			Attrº(Attr.Count + NewTail.length, NewShift),
			NewRoot,
			NewTail.ptr
		);
	};

	typeof(this) asoc(size_t Idx, Valº Val) {
		/* ? */
		if (Idx == Attr.Count) {
			return this~Val;
		};

		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(Idx < Attr.Count);
		};

		if (Idx >= TailIdx) {
			Idx &= 0b11111;
			auto NewTail = dup_tail(
				Tail[0 .. TailLen],
				max_(Idx + 1, TailLen)
			);
			NewTail[Idx] = Val;
			return typeof(this)(Attr, Root, NewTail.ptr);

		} else {
			return typeof(this)(
				Attr,
				cast(Branchº*) tree_asoc(Attr.Shift, Root, Idx, Val),
				Tail
			);
		};
	};

	private static void* tree_asoc(
		size_t Level, void* Node, size_t Idx, Valº Val
	) {
		if (Level == 0) {
			Leafº* Ret = dup_node(cast(Leafº*) Node);
			(*Ret)[Idx & 0b11111] = Val;
			return Ret;

		} else {
			Branchº* Ret = dup_node(cast(Branchº*) Node);
			uint SubIdx = (Idx >>> Level) & 0b11111;
			(*Ret)[SubIdx] = tree_asoc(
				Level - 5,
				(* cast(Branchº*) Node)[SubIdx],
				Idx,
				Val
			);
			return Ret;
		};
	};

	typeof(this) trunc() {
		/* ? */
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(Attr.Count > 0);
		};

		if (Attr.Count == 1) {/* last element */
			return this.init;
		};

		if (TailLen > 1) {/* just decrement the length */
			return typeof(this)(
				Attrº(Attr.Count - 1, Attr.Shift),
				Root,
				Tail
			);
		};

		/* move the last leaf to the tail position */

		auto Newtail = cast(Valº*) leaf_for(Attr.Count - 2);
		Branchº* NewRoot = cast(Branchº*) trunc_tail(Attr.Shift, Root);
		uint NewShift = Attr.Shift;
		if (NewRoot is null) {
			NewRoot = Root.init;
		};
		if (Attr.Shift > 5 && (*NewRoot)[1] is null) {
			NewRoot = cast(Branchº*) (*NewRoot)[0];
			NewShift -= 5;
		};
		return typeof(this)(
			Attrº(Attr.Count - 1, NewShift),
			NewRoot,
			Newtail
		);
	};

	private void* trunc_tail(int Level, void* Node) {
		int SubIdx = ((Attr.Count - 2) >>> Level) & 0b11111;
		if (Level > 5) {
			void* NewChild = trunc_tail(
				Level - 5, (* cast(Branchº*) Node)[SubIdx]
			);
			if (NewChild is null && SubIdx == 0) {
				return null;
			} else {
				auto Ret = dup_node(cast(Branchº*) Node);
				(*Ret)[SubIdx] = NewChild;
				return Ret;
			};
		} else if (SubIdx == 0) {
			return null;
		} else {
			auto Ret = dup_node(cast(Leafº*) Node);
			(*Ret)[SubIdx] = Valº.init;
			return Ret;
		};
	};

	private Branchº* push_tail(size_t Level, void* Parent, Leafº* TailNode) in {
		assert(Parent !is null);
		assert(Level >= 5);
	} body {
		/* if parent is (parent-of-)leaf, insert node,
		else does it map to an existing child? ->
			nodeToInsert = pushNode one more level
		else alloc new path
		return nodeToInsert placed in copy of parent */

		size_t SubIdx = ((Attr.Count - 1) >>> Level) & 0b11111;
		auto Ret = dup_node(cast(Branchº*) Parent);
		if (Level == 5) {
			(*Ret)[SubIdx] = TailNode;
			return Ret;

		} else {
			auto Child = (*Ret)[SubIdx];
			(*Ret)[SubIdx] = (Child !is null) ?
				push_tail(Level - 5, Child, TailNode)
			:
				new_path(Level - 5, TailNode)
			;
			return Ret;
		};
	};

	private static void* new_path(size_t Level, Leafº* Node) {
		if (Level == 0) {
			return Node;
		};
		auto Ret = dup_node(Branchº.init);
		(*Ret)[0] = new_path(Level - 5, Node);
		return Ret;
	};

	private inout(Leafº)* leaf_for(size_t Idx) inout in {
		assert(Idx < Attr.Count);
	} body {
		if (Idx >= TailIdx) {return cast(inout(Leafº)*) Tail;};

		auto Node = cast(Branchº*) Root;
		for (uint Level = Attr.Shift; Level > 0; Level -= 5) {
			Node = cast(Branchº*) (*Node)[(Idx >>> Level) & 0b11111];
		};
		return cast(inout(Leafº)*) Node;
	};

	private static Tº* dup_node(Tº)(Tº* Node) if (
		is(Tº == Branchº) || is(Tº == Leafº)
	) out (Copy) {
		assert(Misc_.bytes_of(*Copy) == Misc_.bytes_of(*Node));
	} body {
		enum Len = Tº.sizeof / Valº.sizeof;
		auto New = cast(Tº*) Rt_.valigned_malloc!Valº(null, Len);
		*New = *Node;
		return New;
	};

	private static Tº* dup_node(Tº)(Tº Node) if (
		is(Tº == Branchº) || is(Tº == Leafº)
	) {
		return dup_node(&Node);
	};

	private static Valº[] extend_tail(Valº[] X, Valº Elem) {
		auto New = cast(Valº*) dup_tail(X, X.length + 1);
		New[X.length] = Elem;
		return New[0 .. X.length + 1];
	};

	private static Valº[] dup_tail(Valº[] X, size_t NewLen) in {
		assert(NewLen >= X.length);
	} body {
		auto New = cast(Valº*) Rt_.valigned_malloc!Valº(null, NewLen);
		New[0 .. X.length] = X[];
		return New[0 .. NewLen];
	};
	private static auto dup_tail(Valº[] X) {
		return dup_tail(X, X.length);
	};

	private struct Attrº {
		/* 32 bits: [0] CCCCCCCCCCCCCCCCCCCCCCCCCCCC|SSSS [32]
		supports up to 4gb worth of 16-byte elements */
		private uint X;
		@property uint Count() const {return X & 0xfffffffu;};
		@property uint Shift() const {return 5 * (X >> 28);};
		this(uint C, uint S) inout in {
			assert(C < 0x10000000u);
			assert(S < 5*16);
			assert(S % 5 == 0);
		} body {
			X = C | ((S / 5) << 28);
		};

		unittest {
			auto A = immutable Attrº(600, 10);
			assert(A.Count == 600);
			assert(A.Shift == 10);
			auto B = immutable Attrº(0xfffffffu, 25);
			assert(B.Count == 0xfffffffu);
			assert(B.Shift == 25);
		};
	};

	unittest {
		/* unions can be unreliable at initialising fields */
		assert(typeof(this).init.Func !is null);
		assert(typeof(this).init.Root is &EmptyBranch);
		assert(typeof(this).init.Tail is EmptyLeaf.ptr);
		assert(typeof(this).init.Attr is Attrº(0, 5));
		auto A = typeof(this).init;
		assert(A.Func is typeof(this).init.Func);
		assert(A.Root is &EmptyBranch);
		assert(A.Tail is EmptyLeaf.ptr);
		assert(A.Attr is Attrº(0, 5));
		version (none) {/* don't try to initialise this way */
			typeof(this) B;
			assert(B.Func is typeof(this).init.Func);
			assert(B.Root is &EmptyBranch);
			assert(B.Tail is EmptyLeaf.ptr);
			assert(B.Attr is Attrº(0, 5));
		};
	};

	@(`front?`) auto nonempty() {
		return bool_val(!!length);
	};

	@(`front`) auto front() {
		return this[0];
	};

	@(`next`) auto next() {
		return this[1 .. $];
	};

	@(`len`) auto length_int64() {
		return Int64º(length);
	};

	@(`at`) static extern(C) Valº at(
		size_t ArgC, typeof(this) Self, Valº IdxV
	) in {
		assert(ArgC == 2);
	} body {
		ptrdiff_t Idx = val_to_ptrdiff_t(IdxV);
		if (Idx < 0) {Idx += Self.length;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx, Self.length));
		};
		return Self[Idx];
	};

	@(`slic`) static extern(C) Valº slice(
		size_t ArgC, typeof(this) Self, Valº V1, Valº V2
	) in {
		assert(ArgC.among_(2, 3));
	} out (X) {
		//assert(X.length <= Self.length);
	} body {
		if (ArgC == 2) {return slice(3, Self, V1, Int64º(Self.length));};

		ptrdiff_t Idx1 = val_to_ptrdiff_t(V1);
		ptrdiff_t Idx2 = val_to_ptrdiff_t(V2);
		if (Idx1 < 0) {Idx1 += Self.length;};
		if (Idx2 < 0) {Idx2 += Self.length;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx1, Idx2, Self.length));
		};
		return Self[Idx1 .. Idx2];
	};
};

struct AtreeSliceº {
	/* aka 'SubVector' */

	Funcº Func = dispatch_methods!(typeof(this));
	Atreeº* Tree = &EmptyTree;
	size_t Start;
	size_t End;
	enum PtrCount = 1;
	mixin ValSubType;

	private static __gshared Atreeº EmptyTree = Atreeº.init; /* (immutable) */

	this(typeof(Tree) Tr, typeof(Start) S, typeof(End) E) {
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(Start, End, Tr.length));
		};
		Tree = Tr; Start = S; End = E;
	};

	this(typeof(*Tree) Tr, typeof(Start) S, typeof(End) E) {
		auto New = Rt_.valigned_malloc!(typeof(*Tree))(null, 1);
		*New = Tr;
		this(New, S, E);
	};

	this(typeof(Tree) Tr, typeof(Start) S = 0) {
		this(Tr, S, Tr.length);
	};

	this(typeof(this) Slice, typeof(Start) S, typeof(End) E) {
		this(Slice.Tree, Start + S, Start + E);
	};

	@property size_t length() const {return End - Start;};

	@property bool empty() const {return Start == End;};

	@property Valº front() {return (*Tree)[Start];};

	auto ref popFront() {this = typeof(this)(Tree, Start + 1, End);};

	@property Valº back() {return (*Tree)[End - 1];};

	auto ref popBack() {this = typeof(this)(Tree, Start, End - 1);};

	@property typeof(this) save() {return this;};

	alias opDollar(size_t X : 0) = length;

	typeof(this) opIndex() {return this;};

	Valº opIndex(size_t Idx) {return (*Tree)[Start + Idx];};

	typeof(this) opIndex(size_t[2] Bounds) {
		return typeof(this)(Tree, Start + Bounds[0], Start + Bounds[1]);
	};

	size_t[2] opSlice(size_t Pos)(size_t S, size_t E) {return [S, E];};

	/+bool opEquals(typeof(this) A) {
		return equal_!((X, Y) => )(this, A);
	};+/

	typeof(this) opBinary(string Op)(Valº Val) if (Op == `~`) {
		return typeof(this)((*this.Tree)~Val, Start, End + 1);
	};

	@(`front?`) auto nonempty() {
		return bool_val(!!length);
	};

	@(`front`) auto front_val() {
		return this[0];
	};

	@(`next`) auto next() {
		return this[1 .. $];
	};

	@(`len`) auto length_int64() {
		return Int64º(length);
	};

	@(`at`) static extern(C) Valº at(
		size_t ArgC, typeof(this) Self, Valº IdxV
	) in {
		assert(ArgC == 2);
	} body {
		ptrdiff_t Idx = val_to_ptrdiff_t(IdxV);
		if (Idx < 0) {Idx += Self.length;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx, Self.length));
		};
		return Self[Idx];
	};

	@(`slic`) static extern(C) Valº slice(
		size_t ArgC, typeof(this) Self, Valº V1, Valº V2
	) in {
		assert(ArgC.among_(2, 3));
	} out (X) {
		//assert(X.length <= Self.length);
	} body {
		if (ArgC == 2) {return slice(3, Self, V1, Int64º(Self.length));};

		ptrdiff_t Idx1 = val_to_ptrdiff_t(V1);
		ptrdiff_t Idx2 = val_to_ptrdiff_t(V2);
		if (Idx1 < 0) {Idx1 += Self.length;};
		if (Idx2 < 0) {Idx2 += Self.length;};
		version (D_NoBoundsChecks) {} else {
			enforceEx_!RangeError_(ordered_(0, Idx1, Idx2, Self.length));
		};
		return Self[Idx1 .. Idx2];
	};
};

unittest {
	auto A = Atreeº.init~Valº.init~Atomº(`foo`)~Decimalº(4);
	assert(A.length == 3);
	assert(A[0] == Valº.init);
	assert(cast(Decimalº) A[2] == Decimalº(4));

	auto B = A~Atomº(`oof`);
	assert(A.length == 3);
	assert(B.length == 4);

	auto C = B.asoc(0, Atomº(`x`));
	assert(A.length == 3);
	assert(B.length == 4);
	assert(C.length == 4);
	assert(C[0] is Atomº(`x`));

	auto D = Atreeº.init;
	foreach (Idx; 0 .. 100) {
		D = D.asoc(Idx, Decimalº(Idx));
		assert(D.length == Idx + 1);
		assert(cast(Decimalº) D[Idx] == Decimalº(Idx));
		if (Idx > 0) {
			assert(cast(Decimalº) D[Idx-1] == Decimalº(Idx-1));
		};
	};

	D = D.trunc();
	assert(D.length == 99);
	assert(cast(Decimalº) D[$ - 1] == Decimalº(98));
	D = D.trunc();
	assert(D.length == 98);
	assert(cast(Decimalº) D[$ - 1] == Decimalº(97));

	auto E = Atreeº(iota_(900).map_!(X => Decimalº(X)));
	foreach (Idx; 0 .. 900) {
		assert(cast(Decimalº) E[Idx] == Decimalº(Idx));
	};

	static assert(is(ElementType_!(typeof(A[])) == Valº));
	static assert(isForwardRange_!(typeof(A[])));
	static assert(isBidirectionalRange_!(typeof(A[])));
	static assert(isRandomAccessRange_!(typeof(A[])));
	static assert(hasSlicing_!(typeof(A[])));
	auto S1 = E[];
	auto F = Atreeº(S1);
	//assert(S1 == F[]);
	//assert(E[] == F[]);

};

unittest {
	/* adopt */
	enum Len = 500;
	Valº[] Arr = Rt_.valigned_malloc!Valº(null, Len)[0 ..Len];

	auto Tree = Atreeº.adopt(Arr);
	assert(Tree.length == Arr.length);

	foreach (Idx; 0 .. Len) {
		auto LeafPtr = cast(Valº*) Tree.leaf_for(Idx);
		assert(ordered_(Arr.ptr, LeafPtr, Arr.ptr + Len));
	};
};

unittest {
	/* copy */
	auto Arr = new Valº[500];

	InputRange_!Valº Src = inputRangeObject_(Arr);
	auto Tree = Atreeº(Src);
	assert(Tree.length == Arr.length);

	foreach (Idx; 0 .. Arr.length) {
		auto LeafPtr = cast(Valº*) Tree.leaf_for(Idx);
		assert(!ordered_(Arr.ptr, LeafPtr, Arr.ptr + Arr.length));
	};
};

/* -------------------------------------------------------------------------- */

/* --- miscellaneous --- */

struct Ptr1stº(Tº) {
	/* dynamic array slice, but with the field order reversed */
	private void* PtrØ;
	private size_t LenØ;
	alias Len1stØ this;

	this()(inout Tº[] A) inout @trusted pure nothrow {
		PtrØ = cast(inout(void)*) A.ptr;
		LenØ = A.length;
	};

	@property inout(Tº)[] Len1stØ() inout @trusted pure nothrow {
		union Uº {
			Tº[] A;
			struct {
				size_t L;
				void* P;
			};
		};
		inout Uº X = {L : LenØ, P : PtrØ};
		return X.A;
	};

	@property size_t length() const @safe pure nothrow {
		return LenØ;
	};

	@property auto ptr() inout @trusted pure nothrow {
		return cast(inout(Tº)*) PtrØ;
	};

	auto popFront() @safe pure nothrow {
		this = typeof(this)((this[])[1 .. $]);
	};

	auto popBack() @safe pure nothrow {
		this = typeof(this)((this[])[0 .. $ - 1]);
	};

	@property auto save() inout @safe pure nothrow {
		return this;
	};

	unittest {
		alias Aº = typeof(this);
		alias Bº = typeof(this[]);
		static assert(is(ElementType_!Aº : ElementType_!Bº));
		static assert(isInputRange_!Aº == isInputRange_!Bº);
		static assert(isForwardRange_!Aº == isForwardRange_!Bº);
		static assert(isBidirectionalRange_!Aº == isBidirectionalRange_!Bº);
		static assert(isRandomAccessRange_!Aº == isRandomAccessRange_!Bº);
		static assert(hasMobileElements_!Aº == hasMobileElements_!Bº);
		//static assert(hasSwappableElements_!Aº == hasSwappableElements_!Bº);
		//static assert(hasSlicing_!Aº == hasSlicing_!Bº);
	};
};

unittest {
	Ptr1stº!int A = [0, 3, 5];
	static assert(A.sizeof == [].sizeof);
	assert(A.length == 3);
	assert(A == [0, 3, 5]);

	const Ptr1stº!int B = [0, 3, 5];
	const Ptr1stº!int C = [0, 3, 5].assumeUnique_;
	static assert(is(typeof(C[]) == const(int)[]));

	immutable Ptr1stº!int D = [0, 3, 5].assumeUnique_;
	static assert(is(typeof(D[]) == immutable(int)[]));

	/+auto E = Ptr1stº([0, 3, 5]);
	auto F = immutable(Ptr1stº!int)([0, 3, 5]);
	auto G = Ptr1stº!(immutable int)([0, 3, 5]);+/

	auto H = Ptr1stº!(immutable int)([]);
	assert(H.length == 0);
	assert(H == []);

	Ptr1stº!(immutable int) I;
	assert(I.length == 0);
	assert(I == []);

	Ptr1stº!(immutable int) J = [];
	assert(J.length == 0);
	assert(J == []);

	auto K = A.dup;
	assert(K == A);
	static assert(is(typeof(K[]) == int[]));

	auto L = A.idup;
	assert(K == A);
	static assert(is(typeof(L[]) == immutable(int)[]));
};

unittest {
	immutable struct Lº {
		Lº* Next;
		Ptr1stº!int Payload;
	};

	auto A = Ptr1stº!Lº([]);
	// ...
	// ...
};

/* -------------------------------------------------------------------------- */

/+

struct Int64º {
	/* 1's complement arithmetic */
	union {
		struct {
			Funcº Func = dispatch_methods!(typeof(this));
			byte Sign = 1;
			ulong Mag;
		};
		Valº Val;
	};
	alias Val this;
	static assert(this.sizeof == Val.sizeof);

	invariant {
		assert(ordered_(-1, Sign, 1));
		assert(Sign != 0 || Mag == 0);
	};

	this(Tº)(Tº X) pure @safe nothrow @nogc if (isIntegral_!Tº) {
		Sign = cast(typeof(Sign)) sgn_(X);
		Mag = X < 0 ? -X : X;
	};

	private this(byte S, ulong M) pure @safe nothrow @nogc {
		Sign = M > 0 ? S : 0;
		Mag = M;
	};

	unittest {
		assert(sgn_(-1) == -1);
		assert(sgn_(0) == 0);
		assert(sgn_(ulong.max) == 1);
	};

	string toString() const {
		return (Sign < 0 ? '-' : '+')~Mag.to_!string;
	};

	auto opUnary(string Op : `-`)() const {
		return Int64º(-Sign, Mag);
	};

	unittest {
		assert((-Int64º(0)).Sign == 0);
		assert((-Int64º(0)).Mag == 0);
		assert((-Int64º(1)).Sign == -1);
		assert((-Int64º(1)).Mag == 1);
		assert((-Int64º(ulong.max)).Sign == -1);
		assert((-Int64º(ulong.max)).Mag == ulong.max);
	};

	size_t toHash() const {
		return hash_of_(Mag, Sign);
	};

	bool opEquals()(auto ref const typeof(this) A) const {
		return this is A;
	};

	unittest {
		foreach (X; [
			Int64º(0), Int64º(1), Int64º(2), -Int64º(1), -Int64º(2),
			Int64º(ulong.max), -Int64º(ulong.max), -Int64º(ulong.max - 1),
		]) {
			assert(X == X);
			assert(X.toHash == X.toHash);
			if (X.Sign != 0) {
				assert(X != -X);
				assert(X.toHash != (-X).toHash);
			};
		};
	};

	Int64º opBinary(string Op : `-`)(in typeof(this) A) const {
		return this + (-A);
	};

	Int64º opBinary(string Op : `+`)(in typeof(this) A) const {
		/* (0,0) + (s,y) = (s,y) */
		if (Sign == 0) {return A;};

		/* (s,x) + (0,0) = (s,x) */
		if (A.Sign == 0) {return this;};

		/* (1,x) + (1,y) = (?,x+y) */
		if (Sign == 1 && A.Sign == 1) {
			ulong R = Mag + A.Mag;
			if (R < Mag || R < A.Mag) {
				return Int64º(-1, ~R);
			};
			return Int64º(1, R);
		};

		/* (1,x) + (-1,y) = (?,x-y) */
		if (Sign == 1 && A.Sign == -1) {
			ulong R = Mag - A.Mag;
			if (Mag < A.Mag) {
				return Int64º(-1, ~R + 1);
			};
			return Int64º(1, R);
		};

		/* (-1,x) + (1,y) = (?,y-x) */
		if (Sign == -1 && A.Sign == 1) {
			return A + this;
		};

		/* (-1,x) + (-1,y) = (?,x+y) */
		if (Sign == -1 && A.Sign == -1) {
			return -((-this) + (-A));
		};

		assert(0);
	};

	unittest {
		assert(Int64º(ulong.max) + Int64º(1) == -Int64º(ulong.max));
		assert(Int64º(ulong.max) + Int64º(2) == -Int64º(ulong.max-1));
		assert(Int64º(ulong.max) + Int64º(ulong.max) == -Int64º(1));

		assert(Int64º(5) - Int64º(1) == Int64º(4));
		assert(Int64º(5) - Int64º(10) == -Int64º(5));
		assert(Int64º(5) + (-Int64º(10)) == -Int64º(5));
		assert(Int64º(5) + (-Int64º(ulong.max)) == -Int64º(ulong.max-5));
		assert(Int64º(ulong.max) + (-Int64º(ulong.max)) == Int64º(0));

		assert((-Int64º(ulong.max)) + (-Int64º(1)) == Int64º(ulong.max));
		assert((-Int64º(ulong.max)) + (-Int64º(ulong.max)) == Int64º(1));
	};
};









































+/

/* -------------------------------------------------------------------------- */