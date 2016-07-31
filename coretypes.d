/* -------------------------------------------------------------------------- */

import Std_;
import Hash_ = core.internal.hash;

import Rt_ = runtime;
import Lang_ = language;

/* -------------------------------------------------------------------------- */

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
	size_t[3] Data;

	enum PtrCount = 0;

	bool opCast(Tº)() if (is(Tº == bool)) {return this !is this.init;};

	extern(C) Valº voke(Tsº...)(Tsº Vals) if (allSatisfy_!(IsVal, Tsº)) {
		/* run through apply() to ensure stack alignment */
		static if (Vals.length > 0) {
			return apply((cast(Valº*) &Vals[0])[0 .. Vals.length]);
		} else {
			return apply([]);
		};
	};

	Valº apply(Valº[] Vals) {
		/* return Func(1 + Vals.length, this, Vals...) */
		version (X86) {} else {static assert(0);};

		void* ValsStart = Vals.ptr;
		void* ValsEnd = Vals.ptr + Vals.length;
		size_t ArgC = 1 + Vals.length;

		/* aligned memory for return value */
		Valº[2] RetMem;
		size_t RetPtr = (cast(size_t) &RetMem[1]) & 0xfffffff0;
		assert((RetPtr & 0xf) == 0);

		asm {
			mov EBX, ESP;
			and ESP, 0xfffffff0; /* align stack for SSE */

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

	struct Dº {
		union {Valº V; size_t[4] X;};
		alias V this;
	};
	static assert(IsVal!Dº);
	
};

/* --- closure --- */

union Closureº {
	Valº Val;
	struct {
		Funcº Func;
		Valº* Upvals;
		Rt_.RuntimeStateº* Runtime;
	};
	enum PtrCount = 1;
	alias Val this;
	static assert(this.sizeof == Val.sizeof);
};

/* -- ns -- */

struct Namespaceº {
	union {
		Valº Val;
		private struct {
			Funcº Func;
			Implº O;
		};
	};
	enum PtrCount = 0;
	alias Val this;
	static assert(this.sizeof == Val.sizeof);

	private static class Implº {
		Symbolº Sym; /* the NS's own name */
		Nullable_!Namespaceº Parent;
		Entryº[Atomº] NameTbl;
		struct Entryº {
			Valº Val;
			Valº[Atomº] AttribTbl;
		};
	};

	invariant {assert(O);};

	@property bool HasParent() const {return !O.Parent.isNull;};

	@property auto SelfSym() inout {return O.Sym;};

	void define(Atomº Name, Valº[Atomº] AttribTbl, Valº Val) {
		enforce_(Name.Str != ``, `define empty symbol`);
		enforce_(Name.Str != O.Sym.Name, `attempt to redefine symbol`);
		enforce_(Name !in O.NameTbl, `attempt to redefine symbol`);
		O.NameTbl[Name] = O.Entryº(Val, AttribTbl.dup);
	};

	auto query(Symbolº Sym) {
		struct Rº {
			Namespaceº Ns;
			Symbolº Sym;
			Valº[Atomº] AttribTbl;
			Valº Val;
		};

		if (auto X = atom(Sym.Name) in O.NameTbl) {
			if (!Sym.Parent || *Sym.Parent == O.Sym) {
				Rº R = {
					Ns : this,
					Sym : symbol(Sym.Name, O.Sym),
					AttribTbl : X.AttribTbl,
					Val : X.Val
				};
				return Nullable_!Rº(R);
			};
		};

		if (
			(Sym.Name == O.Sym.Name) &&
			(!Sym.Parent || (HasParent && *Sym.Parent == O.Parent.O.Sym))
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

		return Nullable_!Rº();
	};
};

Namespaceº namespace(string Name, Namespaceº Parent) {
	return namespace(Name, Nullable_!Namespaceº(Parent));
};
Namespaceº namespace(
	string Name,
	Nullable_!Namespaceº Parent = Nullable_!Namespaceº.init
) {
	Namespaceº V = {
		Func : cast(Funcº) &voke_namespace!(),
		O : new Namespaceº.Implº
	};
	V.O.Parent = Parent;
	V.O.Sym = V.HasParent ?
		symbol(Name, Parent.O.Sym)
	:
		symbol(Name)
	;

	return V;
};

bool is_namespace(Valº V) {return V.Func is cast(Funcº) &voke_namespace!();};

extern(C) Valº voke_namespace()(size_t ArgC, Namespaceº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(is_atom(Key));
} body {
	return [
		atom(`get`) : delegate {
			Self.Func = cast(Funcº) &ns_get!();
			return cast(Valº) Self;
		},
		atom(`def`) : delegate {
			Self.Func = cast(Funcº) &ns_define!();
			return cast(Valº) Self;
		},
		atom(`root`) : {
			while (Self.HasParent) {Self = Self.O.Parent;};
			return cast(Valº) Self;
		},
	].get(Key, delegate() => Valº.init)();
};

extern(C) Valº ns_get()(
	size_t ArgC,
	Namespaceº Self,
	Symbolº Sym,
	Valº Else
) in {
	assert(2 <= ArgC && ArgC <= 3);
	assert(is_symbol(Sym));
} body {
	auto Q = Self.query(Sym);
	if (Q.isNull) {
		if (ArgC == 3) {return Else;};
		throw new Exception(`reference to undefined symbol`);
	};
	return Q.Val;
};

extern(C) Valº ns_define()(
	size_t ArgC,
	Namespaceº Self,
	Atomº Name,
	Dictº AttribDict,
	Valº Val
) in {
	assert(ArgC == 4);
	assert(is_atom(Name));
	assert(is_dict(AttribDict));
} body {
	Self.define(Name, AttribDict.O, Val);
	return Valº.init;
};

/* -- symbol type -- */

struct Symbolº {
	/*
		symbols represent qualified and unqualified names.
		unqualified:
			`bar` -> symbol(`bar`)
		qualified:
			`foo:bar` -> symbol(`bar`, symbol(`foo`))
	*/
	union {
		Valº Val;
		struct {
			Funcº Func;
			Symbolº* Parent;
			Ptr1stº!(immutable char) Name;
		};
	};
	enum PtrCount = 2;
	alias Val this;
	static assert(this.sizeof == Val.sizeof);

	invariant {assert(Name != ``);};

	bool opEquals()(auto ref in typeof(this) A) const {
		if (A.Name != Name) {return false;};
		if ((A.Parent is null) != (Parent is null)) {return false;};
		if (Parent) {return *A.Parent == *Parent;};
		return true;
	};
};

Symbolº symbol(string Name, Symbolº Parent = Symbolº.init) {
	return symbol(Name, Parent, cast(Funcº) &voke_symbol!());
};
auto symbol(string Name, Symbolº Parent, Funcº F) {
	enforce_(Name != ``, `symbol cannot be empty`);
	Symbolº A = {Func : F, Name : Name, Parent : (
		Parent is Symbolº.init ? null : new Symbolº(cast(Valº) Parent)
	)};
	return A;
};

bool is_symbol(Valº V) {
	return V.Func is cast(Funcº) &voke_symbol!();
};

extern(C) Valº voke_symbol()(size_t ArgC, Symbolº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(&Key);
} body {
	return [
		atom(`to-source`) : () => cast(Valº) utf8(Self.Name),
	].get(Key, delegate() => Valº.init)();
};

/* -- invocation type -- */

struct Invocationº {
	union {
		Valº Val;
		struct {
			Funcº Func;
			Valº* Invokee;
			Ptr1stº!Valº Params;
		};
	};
	enum PtrCount = 2;
	alias Val this;
	static assert(this.sizeof == Val.sizeof);
	invariant {assert(Invokee);};
};

Invocationº invocation(Valº Invokee, Valº[] Params) {
	return invocation(Invokee, Params, cast(Funcº) &voke_invocation!());
};
auto invocation(Valº Invokee, Valº[] Params, Funcº F) {
	auto Vals = Invokee~Params;
	Invocationº A = {Func : F, Invokee : Vals.ptr, Params : Vals[1 .. $]};
	return A;
};

bool is_invocation(Valº V) {
	return V.Func is cast(Funcº) &voke_invocation!();
};

extern(C) Valº voke_invocation()(size_t ArgC, Invocationº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(&Key);
} body {
	return [
		atom(`invokee`) : () => cast(Valº) *Self.Invokee,
		atom(`to-source`) : {
			char[] Src; reserve(Src, Self.Params.length + 3);
			Src ~= Utf8º(Self.Invokee.voke(atom(`to-source`))).S;
			Src ~= '(';
			foreach (Idx, V; Self.Params) {
				Src ~= Utf8º(V.voke(atom(`to-source`))).S;
				if (Idx != Self.Params.length - 1) {Src ~= ' ';};
			};
			Src ~= ')';
			return cast(Valº) utf8(assumeUnique_(Src));
		},
	].get(Key, {
		return voke_array(2, Arrayº(cast(Valº) Self), Key);
	})();
};

/* -- basic array type -- */

union Arrayº {
	Valº Val;
	struct {
		Funcº Func;
		union {
			Ptr1stº!Valº Elems;
			struct {
				Valº* Ptr;
				size_t Len;
			};
		};
	};
	enum PtrCount = 1;
	alias Val this;
	static assert(this.sizeof == Val.sizeof);
};

Arrayº array(Valº[] Elems) {return array(Elems, cast(Funcº) &voke_array!());};
auto array(Valº[] Elems, Funcº F) {
	Arrayº A = {Func : F, Elems : Elems};
	return A;
};

bool is_array(Valº V) {
	return V.Func is cast(Funcº) &voke_array!();
};

extern(C) Valº voke_array()(size_t ArgC, Arrayº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(is_atom(Key));
} body {
	return [
		atom(`front`) : () => cast(Valº) Self.Elems[0],
		atom(`empty`) : () =>
			Self.Elems.length ? Valº.init : (cast(Valº) atom(`t`))
		,
		atom(`next`) : () => cast(Valº) array(Self.Elems[1 .. $]),
		atom(`get`) : () => cast(Valº)
			array(Self.Elems, cast(Funcº) &read_array!())
		,
		atom(`len`) : () => cast(Valº) number(Self.Elems.length),
		atom(`dup`) : () => cast(Valº) array(Self.Elems.dup),
		atom(`slic`) : () => cast(Valº)
			array(Self.Elems, cast(Funcº) &slice_array!())
		,
		atom(`to-source`) : {
			char[] Src; reserve(Src, Self.Elems.length + 2);
			Src ~= '(';
			foreach (Idx, V; Self.Elems) {
				Src ~= Utf8º(V.voke(atom(`to-source`))).S;
				if (Idx != Self.Elems.length - 1) {Src ~= ' ';};
			};
			Src ~= ')';
			return cast(Valº) utf8(assumeUnique_(Src));
		},
	].get(Key, delegate() => Valº.init)();
};

extern(C) Valº read_array()(size_t ArgC, Arrayº Self, Valº IdxV) in {
	assert(ArgC == 2);
} body {
	ptrdiff_t Idx = val_to_ptrdiff_t(IdxV);
	if (Idx < 0) {Idx += Self.Elems.length;};
	version (D_NoBoundsChecks) {} else {
		enforce_(0 <= Idx && Idx <= Self.Elems.length, `range violation`);
	};
	return Self.Elems[Idx];
};

extern(C) Valº slice_array()(size_t ArgC, Arrayº Self, Valº V1, Valº V2) in {
	assert(ArgC == 3);
} body {
	size_t Len = Self.Elems.length;
	ptrdiff_t Idx1 = val_to_ptrdiff_t(V1);
	ptrdiff_t Idx2 = val_to_ptrdiff_t(V2);
	if (Idx1 < 0) {Idx1 += Len;};
	if (Idx2 < 0) {Idx2 += Len;};
	version (D_NoBoundsChecks) {} else {
		enforce_(0 <= Idx1 && Idx1 <= Idx2 && Idx2 <= Len, `range violation`);
	};
	return array(Self.Elems[Idx1 .. Idx2]);
};

/* -- basic dict type -- */

union Dictº {
	Valº Val;
	private struct {
		Funcº Func;
		Valº[Atomº] O;
	};
	enum PtrCount = 1;
	alias Val this;
	static assert(this.sizeof == Val.sizeof);
};

auto dict(Valº[Atomº] X) {
	Dictº V = {Func : cast(Funcº) &voke_dict!(), O : X};
	return V;
};

bool is_dict(Valº V) {
	return V.Func is cast(Funcº) &voke_dict!();
};

extern(C) Valº voke_dict()(size_t ArgC, Dictº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(&Key);
} body {
	return [
		atom(`dup`) : () => cast(Valº) (Self.O = Self.O.dup, Self),
		atom(`len`) : () => cast(Valº) number(Self.O.length),
		atom(`get`) : () => cast(Valº)
			(Self.Func = cast(Funcº) &read_dict!(), Self)
		,
	].get(Key, delegate() => Valº.init)();
};

extern(C) Valº read_dict()(size_t ArgC, Dictº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(is_atom(Key));
} body {
	if (auto X = Key in Self.O) {return *X;};
	throw new Exception(`range violation`);
};

/* -- utf8 string type -- */

union Utf8º {
	Valº Val;
	struct {
		Funcº Func;
		Ptr1stº!(immutable char) S;
		size_t Len; /* number of codepoints */
	};
	enum PtrCount = 1;
	alias Val this;
	static assert(this.sizeof == Val.sizeof);
};

Utf8º utf8(string S) {return utf8(S, cast(Funcº) &voke_utf8!());};
auto utf8(string S, Funcº F) {
	Utf8º A = {Func : F, S : S, Len : S.count_};
	return A;
};

bool is_utf8(Valº V) {
	return V.Func is cast(Funcº) &voke_utf8!();
};

extern(C) Valº voke_utf8()(size_t ArgC, Utf8º Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(&Key);
} body {
	return [
		atom(`len`) : () => cast(Valº) number(Self.S.length),
		atom(`get`) : () => cast(Valº)
			utf8(Self.S, cast(Funcº) &read_utf8!())
		,
		atom(`slic`) : () => cast(Valº)
			utf8(Self.S, cast(Funcº) &slice_utf8!())
		,
		atom(`to-source`) : {
			char[] Src; reserve(Src, Self.S.length + 2);
			Src ~= '`';
			foreach (dchar C; Self.S) {
				if (C == '`') {Src ~= C;}; /* ` -> `` */
				Src ~= encode_!char(C);
			};
			Src ~= '`';
			return cast(Valº) utf8(Src.assumeUnique_);
		},
	].get(Key, delegate() => Valº.init)();
};

extern(C) Valº read_utf8()(size_t ArgC, Utf8º Self, Valº IdxV) in {
	assert(ArgC == 2);
} body {
	ptrdiff_t Idx = val_to_ptrdiff_t(IdxV);
	if (Idx < 0) {Idx += Self.Len;};
	version (D_NoBoundsChecks) {} else {
		enforce_(0 <= Idx && Idx <= Self.Len, `range violation`);
	};
	size_t ReadIdx = toUTFindex_(Self.S, Idx);
	{
		auto SubStr = Self.S[ReadIdx .. $];
		return number(decode_(SubStr));
	};
};

extern(C) Valº slice_utf8()(
	size_t ArgC, Utf8º Self, Valº V1, Valº V2
) in {
	assert(ArgC == 3);
} body {
	ptrdiff_t Idx1 = val_to_ptrdiff_t(V1);
	ptrdiff_t Idx2 = val_to_ptrdiff_t(V2);
	if (Idx1 < 0) {Idx1 += Self.Len;};
	if (Idx2 < 0) {Idx2 += Self.Len;};
	version (D_NoBoundsChecks) {} else {
		enforce_(
			0 <= Idx1 && Idx1 <= Idx2 && Idx2 <= Self.Len, `range violation`
		);
	};
	size_t Start = toUTFindex_(Self.S, Idx1);
	size_t End = Start + toUTFindex_(Self.S[Start .. $], Idx2 - Idx1);
	return utf8(Self.S[Start .. End]);
};

/* -- numeric types (only basic functionality at the moment) -- */

Valº number(
	int Sign, const(dchar)[] IntChrs, const(dchar)[] FracChrs, uint Radix
) {
	double N = 0;
	foreach (Idx, Chr; IntChrs) {
		dchar[] Src = [Chr];
		auto Digit = parse_!uint(Src, Radix);
		enforce_(Src == []);
		uint Exp = IntChrs.length - (Idx + 1);
		N += Digit * Radix^^Exp;
	};
	foreach (Idx, Chr; FracChrs) {
		dchar[] Src = [Chr];
		auto Digit = parse_!uint(Src, Radix);
		enforce_(Src == []);
		int Exp = -(Idx + 1);
		N += Digit * (1.0 * Radix)^^Exp;
	};
	enforce_(N >= 0, `failed to convert numeric literal`);
	return floht(Sign * N);
};

Valº number(double N) {return floht(N);};

alias is_number = is_float;

struct Floatº {
	union {
		Valº Val;
		struct {
			Funcº Func;
			double N;
		};
	};
	alias Val this;
	static assert(this.sizeof == Val.sizeof);
};

Floatº floht(double N) {return floht(N, cast(Funcº) &voke_float!());};
auto floht(double N, Funcº F) {
	Floatº V = {Func : F, N : N};
	return V;
};

bool is_float(Valº V) {
	return V.Func is cast(Funcº) &voke_float!();
};

extern(C) Valº voke_float()(size_t ArgC, Floatº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(&Key);
} body {
	auto binary(string Op)() {
		return () => cast(Valº) floht(Self.N, cast(Funcº) &operate_floats!Op);
	};
	return [
		atom(`+`) : binary!`+`,
		atom(`-`) : binary!`-`,
		atom(`*`) : binary!`*`,
		atom(`/`) : binary!`/`,
		atom(`^`) : binary!`^^`,
		atom(`mod`) : binary!`%`,
		atom(`to-source`) : {
			return cast(Valº) utf8(to_!string(Self.N)); // temporary; incorrect
		},
	].get(Key, delegate() {return Valº.init;})();
};

extern(C) Valº operate_floats(string Op)(size_t ArgC, Floatº A, Floatº B) in {
	assert(ArgC == 2);
} body {
	return floht(mixin(`A.N`~Op~`B.N`));
};

auto val_to_ptrdiff_t(Valº V) {
	assert(is_float(V));
	return to_!ptrdiff_t(Floatº(V).N);
};

auto val_to_size_t(Valº V) {
	assert(is_float(V));
	return to_!size_t(Floatº(V).N);
};

/* -- atom type -- */

struct Atomº {
	union {
		Valº Val;
		struct {
			Funcº Func;
			union {
				char[size_t.sizeof * 2] ShortStr;
				struct {
					immutable(char)* LongStr;
					size_t LongStrHash;
				};
				size_t[2] Payload;
			};
			size_t Len;
		};
	};
	alias PtrCount = X => (X.IsShort ? 0 : 1);
	alias Val this;
	static assert(this.sizeof == Val.sizeof);

	invariant {
		if (Len > ShortStr.length) {
			assert(LongStrHash == Hash_.hashOf(LongStr[0 .. Len]));
		};
	};

	size_t toHash() const @safe pure nothrow {
		return IsShort ? (Payload[0]^Payload[1]) : LongStrHash;
	};

	@property bool IsShort() const @safe pure nothrow {
		/* note: this returns false when Len==0, but it doesn't matter */
		return !((Len - 1) & ~0b111);
		//return !(((Len - 8) >> 3) ^ 0x1FFFFFFF);
	};
	unittest {
		immutable char[1000] Src;
		foreach (size_t X; 0 .. Src.length) {
			Atomº A = atom(Src[0 .. X]);
			if (A.Len == 0) {continue;};
			assert(A.IsShort == (A.Len <= ShortStr.length));
		};
	};

	bool opEquals()(auto ref in typeof(this) A) const {
		if (/* these fields must be identical */
			Func !is A.Func ||
			Payload[1] != A.Payload[1] ||
			Len != A.Len
		) {return false;};

		if (Payload[0] == A.Payload[0]) {return true;};
		if (IsShort) {return false;};
		return LongStr[0 .. Len] == A.LongStr[0 .. Len];
	};

	@property char[] Str() const {return InternalStr.dup;};
	private @property const(char)[] InternalStr() const {
		if (IsShort) {
			return ShortStr[0 .. Len];
		} else {
			return LongStr[0 .. Len];
		};
	};
};

Atomº atom(string Src) out (A) {
	assert(A.InternalStr == Src);
	if (!A.IsShort) {
		assert(Hash_.hashOf(Src) == A.toHash);
	};
} body {
	Atomº A = {
		Func : cast(Funcº) &voke_atom!(),
		Len : Src.length,
		Payload : [0, 0]
	};
	if (Src.length <= A.ShortStr.length) {
		A.ShortStr[0 .. Src.length] = Src;
	} else {
		A.LongStr = Src.ptr;
		A.LongStrHash = Hash_.hashOf(Src);
	};
	return A;
};

bool is_atom(Valº V) {
	return V.Func is cast(Funcº) &voke_atom!();
};

extern(C) Valº voke_atom()(size_t ArgC, Atomº Self, Atomº Key) in {
	assert(ArgC == 2);
	assert(is_atom(Key));
} body {
	return [
		atom(`to-source`) : () => cast(Valº)
			utf8(`:`~Self.Str.assumeUnique_)
		,
		atom(`to-hash`) : () => cast(Valº)
			number(Self.toHash)
		,
	].get(Key, delegate() {return Valº.init;})();
};

unittest {
	assert(atom(``) == atom(``));
	assert(atom(``).toHash == atom(``).toHash);
	assert(atom(`x`) == atom(`x`));
	assert(atom(`x`).toHash == atom(`x`).toHash);
	assert(atom(`x`) != atom(`y`));
	assert(atom(`x`).toHash != atom(`y`).toHash);
	assert(atom(`asdfghja`).IsShort);
	assert(!atom(`asdfghjaw`).IsShort);
	assert(atom(`asdfghjawww`).toHash);
	auto S = randomUUID_().toString;
	assert(atom(S) == atom(S));
	assert(atom(S).toHash == atom(S).toHash);
	assert(atom(S) != atom(randomUUID_().toString));
	assert(atom(S).toHash != atom(randomUUID_().toString).toHash);
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

	/+this(Elemsº...)(Elemsº Elems) inout @safe pure nothrow if (
		is(CommonType_!Elemsº : inout(Tº))
	) {
		inout Tº[] A = [Elems];
		this(A);
	};+/

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

	/+@property size_t length(size_t) @safe pure nothrow {
		//
	};+/

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
		//pragma(msg, Aº);
		//pragma(msg, Bº);
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











































+/

/* -------------------------------------------------------------------------- */