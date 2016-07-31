/* -------------------------------------------------------------------------- */

import Std_;

import Parser_ = parser;
import C_ = coretypes : Valº_ = Valº;
import Lang_ = language;
import X86_ = x86generator;

/* -------------------------------------------------------------------------- */

/* --- --- */

struct RuntimeStateº {
	auto ValignedMalloc = &valigned_malloc!void;
	auto VokeAtom = &C_.voke_atom!();
	auto VokeUtf8 = &C_.voke_utf8!();
	auto VokeFloat = &C_.voke_float!();
	auto VokeArray = &C_.voke_array!();
	/* ... */
};

C_.Namespaceº root_namespace() {
	auto Ns = C_.namespace(Lang_.CoreNameTbl.EnvNs);

	Ns.define(
		C_.atom(Lang_.CoreNameTbl.Quote),
		[C_.atom(`macro`) : C_.atom(`t`)],
		Valº_(cast(C_.Funcº) &quote_form!())
	);
	Ns.define(
		C_.atom(Lang_.CoreNameTbl.AtomToSym),
		null,
		Valº_(cast(C_.Funcº) &atom_to_sym!())
	);
	Ns.define(
		C_.atom(Lang_.CoreNameTbl.Array1),
		null,
		Valº_(cast(C_.Funcº) &array1!())
	);
	Ns.define(
		C_.atom(Lang_.CoreNameTbl.SplicingInvocation),
		null,
		Valº_(cast(C_.Funcº) &splicing_invocation!())
	);

	return Ns;
};

/* --- --- */

Valº_[] source_to_forms(Tº)(Tº Src) if (
	isInputRange_!Tº && is(ElementType_!Tº : dchar)
) {
	/* ? */

	struct FormGenerator {
		/* used by the parser to produce forms from source */

		alias num = C_.number;

		Valº_ text(const(dchar)[] S) {
			return C_.utf8(to_!string(S));
		};

		Valº_ name(const(dchar)[] S, C_.Symbolº Parent = C_.Symbolº.init) in {
			assert(S != []);
		} body {
			bool IsAtom;
			/* if name starts with `:`, it's definitely an atom */
			if (S[0] == Lang_.SyntaxTbl.AtomDel) {
				IsAtom = true;
				S = S[1 .. $];
			};

			auto R = S.findSplit_([Lang_.SyntaxTbl.AtomDel]);
			if (R[1] != []) {/* contains another `:` */

				/* atom like `:foo:bar` */
				if (IsAtom) {goto RetAtom;};

				/* qualified symbol `parent:name` */
				return name(R[2].array_, C_.Symbolº(name(R[0].array_)));
			};

			/* atom like `:foo` */
			if (IsAtom) {goto RetAtom;};

			/* unqualified symbol `name` */
			return C_.symbol(to_!string(S), Parent);

			RetAtom:;
			enforce_(S.length <= C_.Atomº.Len.max,
				`atom name too long (over `~
				to_!string(C_.Atomº.Len.max)~` characters)`
			);
			return C_.atom(to_!string(S));
		};

		Valº_ list(Valº_[] Elems) {
			return C_.array(Elems);
		};

		Valº_ call(Valº_ Callee, Valº_ ParamExpr) {
			enforce_(C_.is_array(ParamExpr), `malformed expression`);
			return C_.invocation(Callee, C_.Arrayº(ParamExpr).Elems);
		};

		Valº_ subscript(Valº_ ObjExpr, Valº_ FieldExpr) {
			if (C_.is_symbol(FieldExpr)) {
				FieldExpr = C_.atom(C_.Symbolº(FieldExpr).Name);
			};
			return call(ObjExpr, list([FieldExpr]));
		};

		Valº_ methcall(Valº_ ObjExpr, Valº_ FieldExpr, Valº_ ParamExpr) {
			return call(subscript(ObjExpr, FieldExpr), ParamExpr);
		};
	};

	struct SourceRangeº(Rº) {
		Rº Src;
		size_t Line = 1;
		bool empty() {return Src.empty;};
		auto front() {return Src.front;};
		void popFront() {
			if (Parser_.is_linebreak(front)) {Line += 1;};
			Src.popFront();
		};
	};

	auto Srng = SourceRangeº!(typeof(Src.stride_(1)))(Src.stride_(1));

	return Parser_.parse(&Srng, FormGenerator()).ifThrown_!Exception((X) {
		throw new Exception(
			`syntax error at line `~Srng.Line.to_!string~`: `~X.msg
		);
		return [Valº_.init];
	});
};

extern(C) Tº* valigned_malloc(Tº)(RuntimeStateº*, size_t Len) out (Ptr) {
	assert(X86_.is_valigned(cast(size_t) Ptr));
} body {
	if (Len == 0) {return cast(Tº*) null;};
	auto Ptr = cast(size_t) GC_.malloc(Len * Valº_.sizeof + X86_.Valignment);
	if (!X86_.is_valigned(Ptr)) {
		Ptr = X86_.valign_up(Ptr);
	};
	return cast(Tº*) Ptr;
};

extern(C) Valº_ atom_to_sym()(size_t ArgC, Valº_, C_.Atomº A, C_.Symbolº P) in {
	assert(2 <= ArgC && ArgC <= 3);
} body {
	return C_.symbol(A.Str.assumeUnique_, ArgC == 3 ? P : C_.Symbolº.init);
};

extern(C) Valº_ array1()(size_t ArgC, Valº_, Valº_ Elem) in {
	assert(ArgC == 2);
} body {
	return C_.array([Elem]);
};

extern(C) Valº_ splicing_invocation()(
	size_t ArgC, Valº_, Valº_ Invokee, Valº_ Seqs
) in {
	assert(ArgC >= 2);
	assert(C_.is_array(Seqs));
} body {
	/* extracts parameters from Seqs to create an invocation form. */
	/* Seqs is an array of sequences of parameters,
	e.g. ((a b) (c) () (d e f)) */

	struct SeqRangeº {
		Valº_ Seq;
		@property Valº_ front() {return Seq.voke(C_.atom(`front`));};
		void popFront() {Seq = Seq.voke(C_.atom(`next`));};
		@property bool empty() {
			return Seq.voke(C_.atom(`empty`)) != Valº_.init;
		};
	};

	return C_.invocation(
		Invokee,
		C_.Arrayº(Seqs).Elems
			.map_!(X => SeqRangeº(X))
			.join_
	);
};

extern(C) Valº_ quote_form()(size_t ArgC, Valº_, Valº_ Form) in {
	assert(ArgC == 2);
} body {
	alias is_unquote = X =>
		C_.is_symbol(X) &&
		C_.Symbolº(X).Name == Lang_.KeywordTbl.Unquote
	;
	alias is_splice = X =>
		C_.is_symbol(X) &&
		C_.Symbolº(X).Name == Lang_.KeywordTbl.SpliceUnquote
	;

	if (C_.is_symbol(Form)) {
		auto Sym = C_.Symbolº(Form);
		/* `foo:bar` becomes `.atom->sym(:foo .q\bar)` */
		return C_.invocation(
			C_.symbol(Lang_.CoreNameTbl.AtomToSym),
			(Sym.Parent is null ?
				[cast(Valº_) C_.atom(Sym.Name)]
			:
				[
					cast(Valº_) C_.atom(Sym.Name),
					cast(Valº_) C_.invocation(
						C_.symbol(Lang_.CoreNameTbl.Quote), [*Sym.Parent]
					)
				]
			)
		);

	} else if (C_.is_invocation(Form)) {
		auto V = C_.Invocationº(Form);

		if (is_unquote(*V.Invokee)) {
			/* `.uq\foo` becomes `foo` */
			assert(V.Params.length == 1, `unquote expected 1 parameter`);
			return V.Params[0];
		};

		enforce_(!is_splice(*V.Invokee), `splice must be in parameter list`);

		if (!V.Params.canFind_!(X =>
			C_.is_invocation(X) && is_splice(*C_.Invocationº(X).Invokee)
		)) {
			/* no splicing; optimise */
			//return ?
		};

		static Valº_ quote_param(Valº_ Form) {
			if (C_.is_invocation(Form)) {
				auto V = C_.Invocationº(Form);

				if (is_unquote(*V.Invokee)) {
					/* `.uq\foo` becomes `.list(foo)`, more or less */
					assert(V.Params.length == 1,
						`unquote expected 1 parameter`
					);
					return C_.invocation(
						C_.symbol(Lang_.CoreNameTbl.Array1),
						[V.Params[0]]
					);

				} else if (is_splice(*V.Invokee)) {
					/* `.uq*\foo` becomes `foo` */
					assert(V.Params.length == 1,
						`unquote-splice expects 1 parameter`
					);
					return V.Params[0];
				};
			};

			/* `foo` becomes `.list(.q\foo)`, more or less */
			return C_.invocation(
				C_.symbol(Lang_.CoreNameTbl.Array1),
				[C_.invocation(C_.symbol(Lang_.CoreNameTbl.Quote), [Form])]
			);
		};

		/* `foo(bar)` becomes ? */
		return C_.invocation(
			C_.symbol(Lang_.CoreNameTbl.SplicingInvocation),
			[
				cast(Valº_) C_.invocation(
					C_.symbol(Lang_.CoreNameTbl.Quote),
					[*V.Invokee]
				),
				cast(Valº_) C_.array(V.Params.map_!(quote_param).array_)
			]
		);

	} else {
		return Form;
	};
};

/* -------------------------------------------------------------------------- */

/+
















































+/

/* -------------------------------------------------------------------------- */