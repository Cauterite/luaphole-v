/* -------------------------------------------------------------------------- */

import Std_;
import Hash_ = core.internal.hash;

import C_ = coretypes : Valº_ = Valº;
import Lang_ = language;

/* -------------------------------------------------------------------------- */

// TODO: all the to_source() implementations are crappy temporary code

/* --- intermediate representations of expressions --- */

abstract class Irº {
	/* ? */

	alias Symsº = InputRange_!(immutable Symbolº);

	/* range of all referenced symbols (in deterministic order) */
	@property Symsº AllSyms() immutable {
		return inputRangeObject_(new immutable(Symbolº)[0]);
	};

	/* range of upvalues (in deterministic order) */
	@property Symsº UpvalSyms() immutable {
		return inputRangeObject_(new immutable(Symbolº)[0]);
	};

	/* number of stack spaces needed to store locals */
	@property size_t LocalSymC() immutable {return 0;};

	InputRange_!dchar to_source(/+Formatterº X+/) immutable;

	mixin ToStringOverride;

	/* auto-generate toString() methods */
	mixin template ToStringOverride() {
		override string toString() const {
			return obj_to_string(cast() this);
		};
	};
};

class Nilº : Irº {
	static immutable X = new immutable Nilº;
	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(`.n`);
	};
	mixin ToStringOverride;
};

class Atomº : Irº {
	string Txt;
	this(string X) immutable {Txt = X;};
	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(`:`~Txt);
	};
	mixin ToStringOverride;
};

class Utf8º : Irº {
	string Txt;
	this(string X) immutable {Txt = X;};
	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_("`"~Txt~"`");
	};
	mixin ToStringOverride;
};

class Numberº : Irº {
	immutable(C_.DynDecº)* Num;
	this(immutable(C_.DynDecº)* X) immutable {
		Num = X;
	};
	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(to_!string(Num));
	};
	mixin ToStringOverride;
};

class Symbolº : Irº {
	string Name;
	Nullable_!(immutable Symbolº, null) Parent;

	this(string N, immutable Symbolº P = null) immutable in {
		assert(N != ``);
	} body {
		Name = N;
		Parent = Unqual_!(typeof(Parent))(P);
	};

	override @property Irº.Symsº AllSyms() immutable {
		return inputRangeObject_([this]);
	};

	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(
			(Parent.isNull ? `` : Parent.to_source.to_!string~`:`)~Name
		);
	};

	override size_t toHash() const @safe nothrow {
		return Hash_.hashOf(Name, Parent.isNull ? 0 : Parent.toHash());
	};

	override bool opEquals(Object Obj) {
		return (cast(const) this).opEquals(Obj);
	};
	bool opEquals(in Object Obj) const {
		if (auto S = cast(typeof(this)) Obj) {
			if (S.Name != Name) {return false;};
			if (S.Parent.isNull != Parent.isNull) {return false;};
			if (!Parent.isNull) {return S.Parent == Parent;};
			return true;
		};
		return false;
	};

	mixin ToStringOverride;
};
unittest {
	alias s = (X, Y) => new immutable Symbolº(X, Y);

	assert(s(`foo`, null) == s(`foo`, null));
	assert(s(`foo`, null) != s(` foo`, null));
	assert(s(`foo`, null).toHash == s(`foo`, null).toHash);
	assert(s(`foo`, s(`bar`, null)) == s(`foo`, s(`bar`, null)));
	assert(
		s(`foo`, s(`bar`, null)).toHash ==
		s(`foo`, s(`bar`, null)).toHash
	);

	/* cross your fingers */
	assert(
		s(`foo`, s(`bar `, null)).toHash !=
		s(`foo`, s(`bar`, null)).toHash
	);
	assert(
		s(`f oo`, s(`bar`, null)).toHash !=
		s(`foo`, s(`bar`, null)).toHash
	);
	assert(
		s(`foo`, s(`bar`, s(`arb`, null))) !=
		s(`foo`, s(`bar`, null))
	);
	assert(
		s(`foo`, s(`bar`, s(`arb`, null))).toHash !=
		s(`foo`, s(`bar`, null)).toHash
	);
	assert(
		s(`.`, s(`.`, null)).toHash !=
		s(`.`, s(`.`, s(`.`, null))).toHash
	);
};

class Invocationº : Irº {
	Irº Invokee;
	Irº[] Params;
	bool ForceTailJump = false; /* ? */

	this(Tº)(immutable Irº I, Tº P) immutable if (
		isInputRange_!Tº && is(ElementType_!Tº : immutable(Irº))
	) {
		Invokee = I;
		Params = array_(P);
	};

	override @property Irº.Symsº AllSyms() immutable {
		return inputRangeObject_(
			[Invokee].chain_(Params)
				.map_!(X => X.AllSyms)
				.joiner_
				.drop_duplicates
		);
	};

	override @property Irº.Symsº UpvalSyms() immutable {
		return inputRangeObject_(
			[Invokee].chain_(Params)
				.map_!(X => X.UpvalSyms)
				.joiner_
				.drop_duplicates
		);
	};

	override @property size_t LocalSymC() immutable {
		return [Invokee].chain_(Params)
			.map_!(X => X.LocalSymC)
			.maxCount_[0]
		;
	};

	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(Invokee.to_source.to_!string~`(`~
		Params.map_!(X => X.to_source.to_!string).join_(` `)~`)`);
	};

	mixin ToStringOverride;
};

class Ifº : Irº {
	Irº Pred;
	Irº Then;
	Irº Else;

	this(immutable Irº P, immutable Irº T, immutable Irº E) immutable {
		Pred = P;
		Then = T;
		Else = E;
	};

	override @property Irº.Symsº AllSyms() immutable {
		return inputRangeObject_(
			only_(Pred, Then, Else)
				.map_!(X => X.AllSyms)
				.joiner_
				.drop_duplicates
		);
	};

	override @property Irº.Symsº UpvalSyms() immutable {
		return inputRangeObject_(
			only_(Pred, Then, Else)
				.map_!(X => X.UpvalSyms)
				.joiner_
				.drop_duplicates
		);
	};

	override @property size_t LocalSymC() immutable {
		return [Pred, Then, Else]
			.map_!(X => X.LocalSymC)
			.maxCount_[0]
		;
	};

	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(
			`.if_(`~only_(Pred, Then, Else)
			.map_!(X => X.to_source).join_(` `)~`)`
		);
	};

	mixin ToStringOverride;
};

class Funcº : Irº {
	string Name; /* 'internal' name (for self-recursion) */
	string[] PosNames; /* positional formals */
	Nullable_!(string, ``) VaName; /* variadic params array */
	Irº[] Bodies;
	bool StrictArity; /* allow excess parameters? */

	invariant {
		assert(!StrictArity || VaName.isNull);
		assert(Bodies != []);
	};

	this(T1º, T2º)(
		string Nameª, T1º Namesª, string VaNameª, T2º Bodiesª
	) immutable if (
		isInputRange_!T1º && is(ElementType_!T1º : string) &&
		isInputRange_!T2º && is(ElementType_!T2º : immutable(Irº))
	) {
		Name = Nameª;
		PosNames = array_(Namesª).assumeUnique_;
		VaName = Unqual_!(typeof(VaName))(VaNameª);
		Bodies = array_(Bodiesª).assumeUnique_;
		StrictArity = !IsVariadic;
	};

	@property bool IsVariadic() const {return !VaName.isNull;};

	@property auto SelfSym() const {
		return new immutable Symbolº(Name);
	};

	override @property Irº.Symsº AllSyms() immutable {
		return UpvalSyms;
	};

	@property Irº.Symsº ParamSyms() immutable {
		/* order: (self, ...positionals..., varargs) */
		return inputRangeObject_(
			[SelfSym].chain_(
				PosNames.chain_(IsVariadic ? [VaName.get] : [])
					.map_!(X => new immutable Symbolº(X, SelfSym))
			)
		);
	};

	@property size_t BodyLocalSymC() immutable {
		/* LocalSymC for the function body */
		return Bodies
			.map_!(X => X.LocalSymC)
			.maxCount_[0]
		;
	};

	override @property Irº.Symsº UpvalSyms() immutable {
		return inputRangeObject_(
			Bodies
				.map_!(X => X.AllSyms)
				.joiner_
				/* exclude subsymbols */
				.filter_!(X => X != SelfSym)
				.filter_!(X =>
					X.Parent.isNull || X.Parent != SelfSym
				)
				.drop_duplicates
		);
	};

	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(
			`.fn_(`~Name~` (`~PosNames.join_(` `)~` `~
			(IsVariadic ? VaName : ``)~`) `~
			Bodies.map_!(X => X.to_source.to_!string).join_(` `)~`)`
		);
	};

	mixin ToStringOverride;
};

class Letº : Irº {
	Symbolº SelfSym;
	string[] Names;
	Irº[] Vals;
	Irº[] Bodies;

	invariant {
		assert(Names.length == Vals.length);
		assert(Bodies != []);
	};

	this(T1º, T2º, T3º)(
		immutable Symbolº SelfSymª, T1º Namesª, T2º Valsª, T3º Bodiesª
	) immutable if (
		isInputRange_!T1º && is(ElementType_!T1º : string) &&
		isInputRange_!T2º && is(ElementType_!T2º : immutable(Irº)) &&
		isInputRange_!T3º && is(ElementType_!T3º : immutable(Irº))
	) {
		SelfSym = SelfSymª;
		Names = array_(Namesª).assumeUnique_;
		Vals = array_(Valsª).assumeUnique_;
		Bodies = array_(Bodiesª).assumeUnique_;
	};

	override @property Irº.Symsº AllSyms() immutable {
		return UpvalSyms;
	};

	override @property Irº.Symsº UpvalSyms() immutable {
		return inputRangeObject_(
			chain_(Vals, Bodies)
				.map_!(X => X.AllSyms)
				.joiner_
				/* exclude subsymbols */
				.filter_!(X => X.Parent.isNull || X.Parent != SelfSym)
				.drop_duplicates
		);
	};

	override @property size_t LocalSymC() immutable {
		return Names.length + (
			chain_(Vals, Bodies)
				.map_!(X => X.LocalSymC)
				.maxCount_[0]
		);
	};

	@property Irº.Symsº ParamSyms() immutable {
		return inputRangeObject_(
			Names.map_!(X => new immutable Symbolº(X, SelfSym))
		);
	};

	override InputRange_!dchar to_source() immutable {
		return inputRangeObject_(`.let_(####)`);
	};

	mixin ToStringOverride;
};

/* --- semantic analyser --- */

immutable(Irº) form_to_ir(C_.Namespaceº Ns, Valº_ Form) {
	/* ? */

	static auto get_env(C_.Namespaceº Ns) {
		auto Q = Ns.query(C_.Symbolº(Lang_.CoreNameTbl.EnvNs));
		assert(!Q.isNull && C_.is_namespace(Q.Val));
		return cast(C_.Namespaceº) Q.Val;
	};

	static auto query_env_with_attrib(
		C_.Namespaceº Ns, C_.Symbolº Sym, C_.Atomº AttrName
	) {
		/* aliases and macros can only be read from .env and above
		because deeper namespaces don't exist at runtime */
		auto Q = get_env(Ns).query(Sym);
		if (!Q.isNull && AttrName in Q.AttribTbl) {return Q;};
		return Q.init;
	};

	if (C_.is_atom(Form)) {
		return new immutable Atomº((cast(C_.Atomº) Form).Txt.assumeUnique_);

	} else if (C_.is_decimal(Form)) {
		return new immutable Numberº((cast(C_.Decimalº) Form).Num);

	} else if (C_.is_utf8(Form)) {
		return new immutable Utf8º((cast(C_.Utf8º) Form).Txt);

	} else if (C_.is_symbol(Form)) {
		auto Sym = cast(C_.Symbolº) Form;

		/* keywords */
		if (Sym.Name == Lang_.KeywordTbl.Nil) {
			return Nilº.X;
		};
		foreach (Kw; __traits(allMembers, Lang_.KeywordTbl)) {
			enforce_(Sym.Name != Kw, `invalid name "`~Sym.Name~`"`);
		};

		auto ResolvedSym = resolve_symbol(Ns, Sym);

		/* search for matching aliases/macros */
		{auto Q = query_env_with_attrib(Ns, ResolvedSym, C_.Atomº(`alias`));
			if (!Q.isNull) {
				return form_to_ir(Ns, Q.Val);
			};
		};
		{auto Q = query_env_with_attrib(Ns, ResolvedSym, C_.Atomº(`macro`));
			enforce_(Q.isNull, `can't take value of macro "`~Sym.Name~`"`);
		};

		/* lookup the name at runtime - .env.at(:foo) */
		if (
			ResolvedSym.HasParent &&
			ResolvedSym.Parent == get_env(Ns).SelfSym
		) {
			return new immutable Invocationº(
				new immutable Invocationº(
					sym_form_to_ir(get_env(Ns).SelfSym),
					[new immutable Atomº(`at`)]
				),
				[new immutable Atomº(ResolvedSym.Name)]
			);
		};

		return sym_form_to_ir(ResolvedSym);

	} else if (C_.is_invocation(Form)) {
		auto V = cast(C_.Invocationº) Form;

		if (!C_.is_symbol(V.Invokee)) {
			return new immutable Invocationº(
				form_to_ir(Ns, V.Invokee),
				V.Params.map_!(X => form_to_ir(Ns, X))
			);
		};

		/* keywords */
		switch ((cast(C_.Symbolº) V.Invokee).Name) {
			case Lang_.KeywordTbl.Func : {
				return func_form_to_ir(Ns, V.Params);
			};
			case Lang_.KeywordTbl.Let : {
				return let_form_to_ir(Ns, V.Params);
			};
			case Lang_.KeywordTbl.If : {
				enforce_(V.Params.length == 3,
					`expected 3 params for `~Lang_.KeywordTbl.If~`, found `~
					to_!string(V.Params.length)
				);
				return new immutable Ifº(
					form_to_ir(Ns, V.Params[0]),
					form_to_ir(Ns, V.Params[1]),
					form_to_ir(Ns, V.Params[2])
				);
			};
			default : break;
		};

		auto Invokee = resolve_symbol(Ns, cast(C_.Symbolº) V.Invokee);

		/* search for matching aliases/macros */
		{auto Q = query_env_with_attrib(Ns, Invokee, C_.Atomº(`alias`));
			/* alias expansion must occur here to allow aliases for keywords */
			if (!Q.isNull) {
				return form_to_ir(Ns, C_.Invocationº(Q.Val, V.Params));
			};
		};
		{auto Q = query_env_with_attrib(Ns, Invokee, C_.Atomº(`macro`));
			if (!Q.isNull) {
				/* macro expansion */
				Valº_[] Params = V.Params.map_!(
					X => resolve_form_for_macro(Ns, X)
				).array_;

				debug writeln_(`expanding macro invocation: `~C_.dump_val(V));
				Valº_ R;
				try {
					R = Q.Val.apply(Params);
				} catch (Exception X) {
					throw new Exception(`macro expansion failed: `~X.toString);
				};
				debug writeln_(`macro expansion result: `~C_.dump_val(R));
				return form_to_ir(Ns, R);
			};
		};

		return new immutable Invocationº(
			form_to_ir(Ns, V.Invokee),
			V.Params.map_!(X => form_to_ir(Ns, X))
		);
	};

	/* can't compile this form */
	throw new Exception(`invalid form: `~C_.dump_val(Form));
};

immutable(Symbolº) sym_form_to_ir(C_.Symbolº Sym) {
	return new immutable Symbolº(
		Sym.Name,
		Sym.HasParent ? sym_form_to_ir(Sym.Parent) : null
	);
};

immutable(Funcº) func_form_to_ir(C_.Namespaceº Ns, Valº_[] Params) {
	/* .fn_(ownname (param1 param2 . varargs) body…) */
	enforce_(Params.length >= 3);

	enforce_(C_.is_symbol(Params[0]));
	auto SelfSym = cast(C_.Symbolº) Params[0];
	assert(!SelfSym.HasParent);
	auto NewNs = C_.Namespaceº(
		SelfSym.Name, C_.maybe(Ns), Yes_.IsolateSubSyms
	);

	/* split the formals into [param1 param2] and [varargs] */
	enforce_(C_.is_cslice(Params[1]));
	auto Split = (cast(C_.Csliceº) Params[1]).Elems[]
		.map_!(X => (enforce_(C_.is_symbol(X)), cast(C_.Symbolº) X))
		.findSplit_!(q{a.Name == b.Name})(
			[C_.Symbolº(Lang_.KeywordTbl.Varargs)]
		)
	;

	auto PositionalNames = Split[0].map_!(X => X.Name[]);
	foreach (Name; PositionalNames) {
		NewNs.define(C_.Atomº(Name), null, Valº_.init);
	};

	string VaName;
	if (Split) {
		enforce_(Split[2].walkLength_ == 1);
		VaName = Split[2].front.Name;
		NewNs.define(C_.Atomº(VaName), null, Valº_.init);
	};

	/* compile the body forms */
	auto Bodies = Params[2 .. $]
		.map_!(X => bind_form(NewNs, X, chain_([SelfSym], Split[0], Split[2])))
		.map_!(X => form_to_ir(NewNs, X))
	;

	return new immutable Funcº(
		SelfSym.Name,
		PositionalNames,
		VaName,
		Bodies
	);
};

immutable(Letº) let_form_to_ir(C_.Namespaceº Ns, Valº_[] Params) {
	/* .let_((name1 val1 name2 val2 …) body…)
	equivalent to letrec* from Scheme.
	for performance, not implemented in terms of .fn_ */
	enforce_(Params.length >= 2);

	enforce_(C_.is_cslice(Params[0]));
	auto Bindings = (cast(C_.Csliceº) Params[0]).Elems;
	enforce_(Bindings.length % 2 == 0);

	auto NewNs = C_.Namespaceº(`let;`~randomUUID_().toString, C_.maybe(Ns));
	C_.Symbolº[] RawNames;
	/* traverse the binding form and add the names to the new NS */
	foreach (B; Bindings.chunks_(2)) {
		enforce_(C_.is_symbol(B[0]));
		auto Sym = cast(C_.Symbolº) B[0];
		RawNames ~= Sym;
		NewNs.define(C_.Atomº(Sym.Name), null, Valº_.init);
	};

	/* compile the values */
	auto Vals = Bindings.chunks_(2)
		.map_!(X => bind_form(NewNs, X[1], RawNames))
		.map_!(X => form_to_ir(NewNs, X))
	;

	/* compile the body forms */
	auto Bodies = Params[1 .. $]
		.map_!(X => bind_form(NewNs, X, RawNames))
		.map_!(X => form_to_ir(NewNs, X))
	;

	return new immutable Letº(
		sym_form_to_ir(NewNs.SelfSym),
		RawNames.map_!(X => X.Name[]),
		Vals,
		Bodies
	);
};

private C_.Symbolº resolve_symbol(C_.Namespaceº Ns, C_.Symbolº Sym) out (X) {
	/* the root namespace is the only symbol without a parent */
	version (none) assert(X.HasParent);
} body {
	/* if it's a keyword, just return the name */
	foreach (Kw; __traits(allMembers, Lang_.KeywordTbl)) {
		if (Kw == Sym.Name) {return C_.Symbolº(Sym.Name);};
	};

	if (Sym.HasParent) {return Sym; /* already qualified */};

	/* use Ns to resolve the unqualified name */
	auto Q = Ns.query(Sym);
	enforce_(!Q.isNull, `unable to resolve name `~Sym.Name~` in this context`);
	assert(&Q); /* validate invariants */
	return Q.Sym;
};

private Valº_ bind_form(Tº)(C_.Namespaceº Ns, Valº_ Form, Tº OldSyms) if (
	isInputRange_!Tº && is(ElementType_!Tº == C_.Symbolº)
) {
	/* returns a new form where every symbol appearing in the original form
	that appears in the list OldSyms is re-resolved */

	if (C_.is_symbol(Form)) {
		auto Sym = cast(C_.Symbolº) Form;
		foreach (O; OldSyms) {
			if (O != Sym) {continue;};
			return resolve_symbol(Ns, C_.Symbolº(Sym.Name));
		};
		return Form;

	} else if (C_.is_invocation(Form)) {
		auto V = cast(C_.Invocationº) Form;
		return C_.Invocationº(
			bind_form(Ns, V.Invokee, OldSyms),
			V.Params.map_!(X => bind_form(Ns, X, OldSyms)).array_
		);

	} else {
		return Form;
	};
};

private Valº_ resolve_form_for_macro(C_.Namespaceº Ns, Valº_ Form) {
	/* ? */

	if (C_.is_symbol(Form)) {
		auto Sym = cast(C_.Symbolº) Form;
		return resolve_symbol(Ns, Sym).ifThrown_(
			C_.Symbolº(Sym.Name, Ns.SelfSym)
		);

	} else if (C_.is_invocation(Form)) {
		auto V = cast(C_.Invocationº) Form;
		return C_.Invocationº(
			resolve_form_for_macro(Ns, V.Invokee),
			V.Params.map_!(X => resolve_form_for_macro(Ns, X)).array_
		);

	} else {
		return Form;
	};
};

/* --- miscellaneous --- */

private auto drop_duplicates(Tº)(Tº Src) if (
	isInputRange_!Tº &&
	is(ElementType_!Tº Eº) &&
	__traits(compiles, {bool[Eº] X = [Eº.init : true];})
) {
	alias Eº = ElementType_!Tº;
	return new class {
		bool[Eº] Seen;
		@property bool empty() {return Src.empty;};
		@property Eº front() {return Src.front;};
		void popFront() {
			Seen[Src.front] = true;
			Src.popFront();
			while (!Src.empty && Seen.get(Src.front, false)) {
				Src.popFront();
			};
		};
	};
};

private string obj_to_string(Tº)(Tº Obj) if (is(Tº == class)) {
	if (Obj is null) {
		static assert(Obj.init is null);
		return Tº.stringof~`.init`;
	};

	Appender_!string S = (Unqual_!Tº).stringof~`(`;
	foreach (Idx, Field; FieldNameTuple_!Tº) {
		auto X = __traits(getMember, Obj, Field);
		static if (
			is(Unqual_!(typeof(X)) == Nullable_!(Xº), Xº) ||
			is(Unqual_!(typeof(X)) == Nullable_!(Xº,Y), Xº, alias Y)
		) {
			S ~= (X.isNull ? `null` : to_!string(cast() X.get));
		} else {
			S ~= to_!string(X);
		};
		if (Idx < FieldNameTuple_!Tº.length - 1) {
			S ~= `, `;
		};
	};
	S ~= `)`;
	return S.data.assumeUnique_;
};

/* -------------------------------------------------------------------------- */

/+











































+/

/* -------------------------------------------------------------------------- */