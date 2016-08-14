/* -------------------------------------------------------------------------- */

import std_;

import Lang_ = language : S_ = SyntaxTbl;
import C_ = coretypes : Valº_ = Valº;

/* -------------------------------------------------------------------------- */

/* --- parse source range into AST forms --- */

Valº_[] source_to_forms(Tº)(Tº Src) if (
	isInputRange_!Tº && is(ElementType_!Tº : dchar)
) {
	/* ? */

	struct FormGenerator {
		/* used by the parser to produce forms from source */

		Valº_ num(byte Sign, in dchar[] I, in dchar[] F, uint Radix) {
			return C_.Decimalº.from_lit(
				Sign, I, F, Radix
			);
		};

		Valº_ text(const(dchar)[] S) {
			return C_.Utf8º(S.to_!string);
		};

		Valº_ name(const(dchar)[] S) {
			return name(S, Nullable_!(C_.Symbolº).init);
		};
		Valº_ name(const(dchar)[] S, C_.Symbolº P) {
			return name(S, Nullable_!(C_.Symbolº)(P));
		};
		Valº_ name(const(dchar)[] S, Nullable_!(C_.Symbolº) Parent) in {
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
				return name(R[2].array_, cast(C_.Symbolº) name(R[0].array_));
			};

			/* atom like `:foo` */
			if (IsAtom) {goto RetAtom;};

			/* unqualified symbol `name` */
			return C_.Symbolº(to_!string(S), Parent);

			RetAtom:;
			enforce_(S.length <= C_.Atomº.Len.max,
				`atom name too long (over `~
				to_!string(C_.Atomº.Len.max)~` characters)`
			);
			return C_.Atomº(to_!string(S));
		};

		Valº_ list(Valº_[] Elems) {
			return C_.Csliceº.from(Elems);
		};

		Valº_ call(Valº_ Callee, Valº_ ParamExpr) {
			enforce_(C_.is_cslice(ParamExpr), `malformed expression`);
			return C_.Invocationº(Callee, (cast(C_.Csliceº) ParamExpr).Elems);
		};

		Valº_ subscript(Valº_ ObjExpr, Valº_ FieldExpr) {
			if (C_.is_symbol(FieldExpr)) {
				FieldExpr = C_.Atomº((cast(C_.Symbolº) FieldExpr).Name);
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
			if (is_linebreak(front)) {Line += 1;};
			Src.popFront();
		};
	};

	auto Srng = SourceRangeº!(typeof(Src.stride_(1)))(Src.stride_(1));

	return parse(&Srng, FormGenerator()).ifThrown_!Exception((X) {
		throw new Exception(
			`syntax error at line `~Srng.Line.to_!string~`: `~X.msg
		);
		return [Valº_.init];
	});
};

/* --- low-level lexical parser --- */

bool is_linebreak(dchar Chr) {return Lang_.Linebreaks.canFind_(Chr);};
bool is_white(dchar Chr) {return Lang_.Whitespaces.canFind_(Chr);};
bool is_expr_separator(dchar Chr) {
	return is_white(Chr) || Chr == S_.CommDel || Chr == S_.ListClose;
};
bool is_name_chr(dchar Chr) {
	if (is_white(Chr)) {return false;};
	if (Chr.among_!(
		S_.CommDel, S_.TextDel, S_.ListOpen, S_.ListClose, S_.ListMultiWrap,
		S_.Subscript
	)) {return false;};
	return isGraphical_(Chr);
};
bool is_dec_digit(dchar Chr) {
	return '0' <= Chr && Chr <= '9';
};
bool is_digit(dchar Chr) {
	if (is_dec_digit(Chr)) {return true;};
	return ('a' <= Chr && Chr <= 'z') || ('A' <= Chr && Chr <= 'Z');
};

auto parse(Srcº, Genº)(Srcº Src, Genº ValGen) if (
	isInputRange_!Srcº && is(ElementType_!Srcº : dchar)
) {
	alias Valº = typeof(ValGen.list([]));

	Valº delegate() parse_singular;

	Valº parse_expr(Nullable_!Valº Callee = Nullable_!Valº.init) {
		enforce_(!Src.empty, `input ended unexpectedly`);

		Nullable_!Valº V;
		if (Src.front == S_.Subscript && !Callee.isNull) {
			Src.popFront();
			enforce_(!Src.empty, `input ended unexpectedly`);

			Valº ObjXpr = Callee;
			Valº FieldXpr = parse_singular();

			if (!Src.empty && (
				Src.front == S_.ListOpen || Src.front == S_.ListMultiWrap
			)) {
				V = ValGen.methcall(ObjXpr, FieldXpr, parse_singular());
			} else {
				V = ValGen.subscript(ObjXpr, FieldXpr);
			};
		} else {
			V = parse_singular();
			if (!Callee.isNull) {
				V = ValGen.call(Callee, V);
			};
		};

		if (Src.empty || is_expr_separator(Src.front)) {return V;};
		return parse_expr(V);
	};

	void parse_block_comment() in {
		assert(Src.front == S_.CommOpen);
	} body {
		Src.popFront();
		dchar Prev;
		while (true) {
			enforce_(!Src.empty, `input ended unexpectedly`);
			if (Prev == S_.CommDel && Src.front == S_.CommOpen) {/* ;\ */
				parse_block_comment();
				continue;
			};
			if (Prev == S_.CommClose && Src.front == S_.CommDel) {/* \; */
				Src.popFront();
				break;
			};
			Prev = Src.front;
			Src.popFront();
		};
	};

	void parse_comment() in {
		assert(Src.front == S_.CommDel);
	} body {
		Src.popFront();
		if (!Src.empty && Src.front == S_.CommOpen) {/* ;\ */
			return parse_block_comment();
		};
		while (!Src.empty && !is_linebreak(Src.front)) {
			Src.popFront();
		};
	};

	Valº[] parse_list_elements(Valº[] Acc = []) {
		if (Src.empty || Src.front == S_.ListClose) {return Acc;};
		if (Src.front == S_.CommDel) {
			parse_comment();
			return parse_list_elements(Acc);
		};
		if (is_white(Src.front)) {
			Src.popFront();
			return parse_list_elements(Acc);
		};
		Acc ~= parse_expr();
		return parse_list_elements(Acc);
	};

	Valº interp_number(dchar[] Chrs) {
		/* ipart */
		/* ipart, */
		/* ipart,fpart */
		/* radix/ipart */
		/* radix/,fpart */
		/* radix/ipart, */
		/* radix/ipart,fpart */
		/* 0/ipart,fpart -> 16/ipart,fpart */

		dchar[] NotSpaces;
		foreach (Chr; Chrs.idup) {
			if (Chr != S_.NumSpace) {NotSpaces ~= Chr;};
		};
		Chrs = NotSpaces;
		enforce_(Chrs != [], `malformed numeric literal`);

		byte Sign = 1;
		if (Chrs[$ - 1] == S_.NumPlus) {
			Chrs.length -= 1;
		} else if (Chrs[$ - 1] == S_.NumMinus) {
			Sign = -1;
			Chrs.length -= 1;
		};
		enforce_(Chrs != [], `malformed numeric literal`);

		uint Radix = 10;
		{
			dchar[] RadixChrs;
			foreach (Idx, Chr; Chrs) {
				if (Chr == S_.NumRadixDel) {break;};
				RadixChrs ~= Chr;
			};
			if (RadixChrs.length != Chrs.length) {
				Chrs = Chrs[RadixChrs.length + 1 .. $];
				foreach (Chr; RadixChrs) {
					enforce_(is_dec_digit(Chr), `malformed numeric literal`);
				};
				Radix = to_!uint(RadixChrs);
			};
		};
		enforce_(Chrs != [], `malformed numeric literal`);

		dchar[] IntChrs;
		dchar[] FracChrs;
		while (Chrs != [] && Chrs[0] != S_.NumPoint) {
			dchar Chr = Chrs[0];
			Chrs = Chrs[1 .. $];
			enforce_(is_digit(Chr), `malformed numeric literal`);
			IntChrs ~= Chr;
		};
		if (Chrs != [] && Chrs[0] == S_.NumPoint) {
			Chrs = Chrs[1 .. $];
			while (Chrs != []) {
				dchar Chr = Chrs[0];
				Chrs = Chrs[1 .. $];
				enforce_(is_digit(Chr), `malformed numeric literal`);
				FracChrs ~= Chr;
			};
		};

		if (Radix == 0) {Radix = 16;};
		return ValGen.num(Sign, IntChrs, FracChrs, Radix);
	};

	parse_singular = delegate Valº() {
		enforce_(!Src.empty, `input ended unexpectedly`);

		if (Src.front == S_.ListMultiWrap) {/* \… */
			Src.popFront();
			enforce_(!Src.empty, `input ended unexpectedly`);
			return ValGen.list([parse_expr()]);

		} else if (Src.front == S_.TextDel) {/* text */
			Src.popFront();

			dchar[] Text;
			while (true) {
				enforce_(!Src.empty, `input ended unexpectedly`);
				if (Src.front == S_.TextDel) {/* ` */
					Src.popFront();
					if (!Src.empty && Src.front == S_.TextDel) {/* `` */
						Text ~= S_.TextDel;
						Src.popFront();
						continue;
					};
					break;
				};
				Text ~= Src.front;
				Src.popFront();
			};
			return ValGen.text(Text);

		} else if (Src.front == S_.ListOpen) {/* list */
			Src.popFront();

			auto V = ValGen.list(parse_list_elements());
			enforce_(!Src.empty && Src.front == S_.ListClose, (
				`list improperly terminated`
			));
			Src.popFront();
			return V;

		} else if (Src.front == S_.Subscript) {/* .name */
			Src.popFront();
			enforce_(!Src.empty, `input ended unexpectedly`);
			dchar[] Name = [S_.Subscript];
			while (!Src.empty && is_name_chr(Src.front)) {
				Name ~= Src.front;
				Src.popFront();
			};
			return ValGen.name(Name);

		} else if (is_dec_digit(Src.front)) {/* number */
			dchar[] Chrs;
			while (!Src.empty && is_name_chr(Src.front)) {
				Chrs ~= Src.front;
				Src.popFront();
			};
			return interp_number(Chrs);

		} else if (is_name_chr(Src.front)) {/* name */
			dchar[] Name;
			while (!Src.empty && is_name_chr(Src.front)) {
				Name ~= Src.front;
				Src.popFront();
			};
			return ValGen.name(Name);

		} else {
			throw new Exception(`malformed expression`);
		};
	};

	auto Vals = parse_list_elements();
	enforce_(Src.empty, `unexpected character`);
	return Vals;
};

/* -------------------------------------------------------------------------- */

/+














































+/

/* -------------------------------------------------------------------------- */