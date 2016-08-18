/* -------------------------------------------------------------------------- */

import Std_;

import Misc_ = miscellaneous;
import Parser_ = parser;
import C_ = coretypes : Valº_ = Valº;
import Ir_ = intermediate;
import Lang_ = language;
import X86_ = x86generator;

/* -------------------------------------------------------------------------- */

// PROBLEM: druntime GC doesn't scan SSE registers
// TODO: optimise the no-splicing case in quote

/* --- --- */

struct RuntimeStateº {
	auto ValignedMalloc = &valigned_malloc!(C_.Valº);
	auto DecFromBytes = &dec_from_bytes;
	auto VokeAtom = C_.Atomº.init.Func;
	auto VokeDec = C_.Decimalº.init.Func;
	auto VokeUtf8 = C_.Utf8º.init.Func;
	auto VokeArray = C_.Csliceº.init.Func;
	/* ... */

	/* allocator for executable memory */
	auto CodeAllocator = AllocatorList_!(
		Sz => Region_!(MmapCodeAllocator, X86_.Valignment)(max_(Sz, 0x10000)),
		GCAllocator_
	).init;

	this(int) {
		//
	};
	~this() {
		//
	};
};

C_.Namespaceº root_namespace(RuntimeStateº* Rt) out (Ns) {
	assert(&Ns);
	assert(Ns.SelfSym == C_.Symbolº(Lang_.CoreNameTbl.EnvNs));
	assert(!Ns.HasParent);
} body {
	auto Ns = C_.Namespaceº(Lang_.CoreNameTbl.EnvNs);

	alias Ctbl = Lang_.CoreNameTbl;

	Ns.define(Ctbl.Apply, Valº_(cast(C_.Funcº) &apply!()));
	Ns.define(Ctbl.EmptyArray, C_.Csliceº.init);
	Ns.define(Ctbl.EmptyDict, C_.Htableº.init);
	Ns.define(Ctbl.AtomToSym, Valº_(cast(C_.Funcº) &atom_to_sym!()));
	Ns.define(Ctbl.StrToAtom, Valº_(cast(C_.Funcº) &str_to_atom!()));

	Ns.define(Ctbl.ParseSrc, Valº_(cast(C_.Funcº) &utf8_to_forms!()));
	Ns.define(Ctbl.CompileForm, C_.Closureº(
		cast(C_.Funcº) &form_to_chunk!(), null, Rt
	));

	Ns.define(Ctbl.ArrayOf, Valº_(cast(C_.Funcº) &array_of!()));
	Ns.define(
		Ctbl.SplicingInvocation,
		Valº_(cast(C_.Funcº) &splicing_invocation!())
	);
	Ns.define(
		Ctbl.Quote,
		[C_.Atomº(`macro`) : C_.Atomº(`t`)],
		Valº_(cast(C_.Funcº) &quote_form!())
	);

	return Ns;
};

/* --- --- */

struct SeqRangeº {
	Valº_ Seq;
	@property bool empty() {
		return Seq.voke(C_.Atomº(`front?`)) is Valº_.init;
	};
	@property Valº_ front() {
		return Seq.voke(C_.Atomº(`front`));
	};
	void popFront() {
		Seq = Seq.voke(C_.Atomº(`next`));
	};
};

extern(C) auto dec_from_bytes(ubyte[] Bytes) {
	return C_.Decimalº.from_bytes(Bytes);
};

/* Len is number of Tº-sized elements, not total byte size */
extern(C) Tº* valigned_malloc(Tº)(RuntimeStateº*, size_t Len) out (Ptr) {
	assert(X86_.is_valigned(cast(size_t) Ptr));
} body {
	static assert(Tº.sizeof == Valº_.sizeof);
	if (Len == 0) {return cast(Tº*) null;};

	void* Ptr = GC_.malloc(Len * Valº_.sizeof);
	if (!X86_.is_valigned(cast(size_t) Ptr)) {
		GC_.free(Ptr);
		Ptr = GC_.malloc(Len * Valº_.sizeof + X86_.Valignment);
		if (!X86_.is_valigned(cast(size_t) Ptr)) {
			Ptr = cast(void*) X86_.valign_up(cast(size_t) Ptr);
		};
	};

	return cast(Tº*) Ptr;
};

/* Len is number of Tº-sized elements, not total byte size */
extern(C) Tº* aligned_malloc(Tº, size_t Alignment)(
	RuntimeStateº*, size_t Len
) out (Ptr) {
	assert((cast(size_t) Ptr) % Alignment == 0);
} body {
	if (Len == 0) {return cast(Tº*) null;};

	void* Ptr = GC_.malloc(Len * Tº.sizeof);
	if (!Misc_.is_aligned!Alignment(Ptr)) {
		GC_.free(Ptr);
		Ptr = GC_.malloc(Len * Tº.sizeof + Alignment);
		if (!Misc_.is_aligned!Alignment(Ptr)) {
			Ptr = Misc_.align_up!Alignment(Ptr);
		};
	};

	return cast(Tº*) Ptr;
};

extern(C) Valº_ apply()(size_t ArgC, Valº_, Valº_ Invokee, C_.Csliceº Params) in {
	assert(ArgC == 3);
} body {
	if (!C_.is_cslice(Params)) {
		Params = C_.Csliceº.from(SeqRangeº(Params).array_);
	};
	return Invokee.apply(Params.Elems);
};

extern(C) Valº_ atom_to_sym()(size_t ArgC, Valº_, C_.Atomº A, C_.Symbolº P) in {
	assert(ordered_(2, ArgC, 3));
	assert(C_.is_atom(A));
} body {
	alias Xº = Nullable_!(C_.Symbolº);
	return C_.Symbolº(A.Txt.assumeUnique_, ArgC == 3 ? Xº(P) : Xº.init);
};

extern(C) Valº_ utf8_to_forms()(size_t ArgC, Valº_, C_.Utf8º S) in {
	assert(ArgC == 2);
	assert(C_.is_utf8(S));
} body {
	return C_.Csliceº.from(Parser_.source_to_forms(S.Txt));
};

extern(C) Valº_ form_to_chunk()(
	size_t ArgC, C_.Closureº Self, C_.Namespaceº Ns, Valº_ Form
) in {
	assert(ArgC == 3);
} body {
	auto Ir = Ir_.form_to_ir(Ns, Form);
	return X86_.gen_chunk(Self.Runtime, Ns, Ir);
};

extern(C) Valº_ str_to_atom()(size_t ArgC, Valº_, C_.Utf8º S) in {
	assert(ArgC == 2);
	assert(C_.is_utf8(S));
} body {
	return C_.Atomº(S.Txt);
};

extern(C) Valº_ array_of()(size_t ArgC, Valº_, Valº_ Elems /* ... */) in {
	assert(ArgC >= 1);
} body {
	return C_.Csliceº.from((&Elems)[0 .. ArgC - 1]);
};

extern(C) Valº_ splicing_invocation()(
	size_t ArgC, Valº_, Valº_ Invokee, Valº_ Seqs
) in {
	assert(ArgC == 3);
	assert(C_.is_cslice(Seqs));
} body {
	/* extracts parameters from Seqs to create an invocation form. */
	/* Seqs is an array of sequences of parameters,
	e.g. ((a b) (c) () (d e f)) */

	return C_.Invocationº(
		Invokee,
		(cast(C_.Csliceº) Seqs).Elems
			.map_!(X => SeqRangeº(X))
			.joiner_
			.array_
	);
};

extern(C) Valº_ quote_form()(size_t ArgC, Valº_, Valº_ Form) in {
	assert(ArgC == 2);
} body {
	alias is_unquote = X =>
		C_.is_symbol(X) &&
		(cast(C_.Symbolº) X).Name == Lang_.KeywordTbl.Unquote
	;
	alias is_splice = X =>
		C_.is_symbol(X) &&
		(cast(C_.Symbolº) X).Name == Lang_.KeywordTbl.SpliceUnquote
	;

	if (C_.is_symbol(Form)) {
		auto Sym = cast(C_.Symbolº) Form;
		/* `foo:bar` becomes `.atom->sym(:foo .q\bar)` */
		return C_.Invocationº(
			C_.Symbolº(Lang_.CoreNameTbl.AtomToSym),
			(!Sym.HasParent ?
				[cast(Valº_) C_.Atomº(Sym.Name)]
			:
				[
					cast(Valº_) C_.Atomº(Sym.Name),
					cast(Valº_) C_.Invocationº(
						C_.Symbolº(Lang_.CoreNameTbl.Quote), [Sym.Parent]
					)
				]
			)
		);

	} else if (C_.is_cslice(Form)) {
		auto Arr = cast(C_.Csliceº) Form;
		/* `(x y z)` becomes `.arr-of_(.q\x .q\y .q\z)` */
		return C_.Invocationº(
			C_.Symbolº(Lang_.CoreNameTbl.ArrayOf),
			Arr.Elems.map_!(X => C_.Invocationº(
				C_.Symbolº(Lang_.CoreNameTbl.Quote), only_(X)
			))
		);

	} else if (C_.is_invocation(Form)) {
		auto V = cast(C_.Invocationº) Form;

		if (is_unquote(V.Invokee)) {
			/* `.uq\foo` becomes `foo` */
			assert(V.Params.length == 1, `unquote expected 1 parameter`);
			return V.Params[0];
		};

		enforce_(!is_splice(V.Invokee), `splice must be in parameter list`);

		if (!V.Params.canFind_!(X =>
			C_.is_invocation(X) && is_splice((cast(C_.Invocationº) X).Invokee)
		)) {
			/* no splicing; optimise */
			//return ?
		};

		static Valº_ quote_param(Valº_ Form) {
			if (C_.is_invocation(Form)) {
				auto V = cast(C_.Invocationº) Form;

				if (is_unquote(V.Invokee)) {
					/* `.uq\foo` becomes `.list(foo)`, more or less */
					assert(V.Params.length == 1,
						`unquote expected 1 parameter`
					);
					return C_.Invocationº(
						C_.Symbolº(Lang_.CoreNameTbl.ArrayOf),
						only_(V.Params[0])
					);

				} else if (is_splice(V.Invokee)) {
					/* `.uq*\foo` becomes `foo` */
					assert(V.Params.length == 1,
						`unquote-splice expects 1 parameter`
					);
					return V.Params[0];
				};
			};

			/* `foo` becomes `.list(.q\foo)`, more or less */
			return C_.Invocationº(
				C_.Symbolº(Lang_.CoreNameTbl.ArrayOf),
				only_(C_.Invocationº(
					C_.Symbolº(Lang_.CoreNameTbl.Quote),
					only_(Form)
				))
			);
		};

		/* `foo(bar)` becomes ? */
		return C_.Invocationº(
			C_.Symbolº(Lang_.CoreNameTbl.SplicingInvocation),
			only_(
				C_.Invocationº(
					C_.Symbolº(Lang_.CoreNameTbl.Quote),
					only_(V.Invokee)
				),
				C_.Invocationº(
					C_.Symbolº(Lang_.CoreNameTbl.ArrayOf),
					V.Params.map_!quote_param
				)
			)
		);

	} else {
		return Form;
	};
};

/* --- --- */

struct MmapCodeAllocator {
	/* allocates writable|executable pages */

	static shared typeof(this) instance;
	alias parent = MmapAllocator_.instance;
	alias parent this;

	void[] allocate(size_t Sz) shared {
		void[] Mem = MmapAllocator_.instance.allocate(Sz);
		if (!Mem) {return [];};

		Misc_.set_page_access(Mem, Misc_.PageAllAccess);
		return Mem;
	};

	unittest {
		alias X = MmapCodeAllocator.instance;

		auto Mem = cast(ubyte[]) X.allocate(1);
		Mem[0] = X86_.Op1.Ret;
		auto Ptr = Mem.ptr;
		asm {call [Ptr];};

		X.deallocate(Mem);
	};
};

/* -------------------------------------------------------------------------- */

/+
















































+/

/* -------------------------------------------------------------------------- */