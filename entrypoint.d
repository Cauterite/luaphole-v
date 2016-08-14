/* -------------------------------------------------------------------------- */

import Std_;

import Parser_ = parser;
import C_ = coretypes : Valº_ = Valº;
import Ir_ = intermediate;
import Lang_ = language;
import Rt_ = runtime;
import X86_ = x86generator;

/* -------------------------------------------------------------------------- */

void main() {
	writeln_(`sse41_enabled: `, sse41_);


	writeln_(`.`);
	writeln_(`success`);
};

unittest {
	/* ? */
	Valº_[] Forms = Parser_.source_to_forms(q"{
		50,50
	}"d);

	auto Rt = Rt_.RuntimeStateº(0);
	auto Ns = Rt_.root_namespace(&Rt);

	auto Ir = Ir_.form_to_ir(Ns, Forms[0]);

	Valº_ Chunk = X86_.gen_chunk(&Rt, Ns, Ir);

	auto Result = Chunk.voke();
	assert(C_.is_decimal(Result));
};

unittest {
	/* basic quote test */
	Valº_[] Forms = Parser_.source_to_forms(q"{
		.q\.env
	}"d);

	auto Rt = Rt_.RuntimeStateº(0);
	auto Ns = Rt_.root_namespace(&Rt);
	auto Ir = Ir_.form_to_ir(Ns, Forms[0]);

	Valº_ Chunk = X86_.gen_chunk(&Rt, Ns, Ir);

	auto Result = Chunk.voke();
	assert(C_.is_symbol(Result));
	assert(cast(C_.Symbolº*) &Result);
	assert((cast(C_.Symbolº) Result) == C_.Symbolº(`.env`));
};

unittest {
	/* environment bindings */
	auto Rt = Rt_.RuntimeStateº(0);
	auto Ns = Rt_.root_namespace(&Rt);

	Valº_[] Forms = Parser_.source_to_forms(q"{
		.env.def(.str->atom(`.aa`) .n
			.fn_(rec (. xs)
				.if_(xs.len.=.0
					.empty-aa_
				;else
					.apply(rec xs.slic(2)).asoc(xs.at.0 xs.at.1)
				)
			)
		)
	}"d);

	auto Ir = Ir_.form_to_ir(Ns, Forms[0]);
	Valº_ Chunk = X86_.gen_chunk(&Rt, Ns, Ir);

	Chunk.voke();

	auto Q = Ns.query(C_.Symbolº(`.aa`));
	assert(Q.Val !is Valº_.init);
	assert(&Q.Val);

	auto Tbl = Q.Val.voke(
		C_.Atomº(`foo`), C_.Decimalº(66),
		C_.Atomº(`bar`), C_.Utf8º(`words`),
	);

	assert(C_.is_htable(Tbl));
	{
		auto X = Tbl.voke_u!`at`.voke_u!`bar`;
		assert(C_.is_utf8(X));
		assert(cast(C_.Utf8º) X == C_.Utf8º(`words`));
	};
};

/* -------------------------------------------------------------------------- */

/+














































+/

/* -------------------------------------------------------------------------- */