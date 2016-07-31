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
	C_.atom(`x`).voke(C_.atom(`y`));
	writeln_(`sse41_enabled: `, sse41_);

	Valº_[] Forms = Rt_.source_to_forms(q"{
		.fn_(c ()
			:longstringlongstringlongstringlongstring
			.fn_(u () c)
			.let_((g c h .env) .if_(g :t .n))
			.if_(:t .env 6,2)
		)()
	}"d);

	auto Ns = Rt_.root_namespace();

	auto Ir = Ir_.form_to_ir(Ns, Forms[0]);
	//writeln_(Ir);

	Rt_.RuntimeStateº Rt;
	Valº_ Chunk = X86_.gen_chunk(&Rt, Ns, Ir);

	C_.Namespaceº(Chunk.voke()).SelfSym.Name.writeln_;

	writeln_(`.`);
	writeln_(`success`);
};

/+	Valº_[] Forms = Parser_.parse(&Srng, FormGenerator()).ifThrown_!Exception(
		X => ({
			writeln_(`syntax error at line `, Src.Line, `: `, X.msg);
			import std.c.stdlib;
			return abort(), [Valº_.init];
		})()
	);+/

/* -------------------------------------------------------------------------- */

/+














































+/

/* -------------------------------------------------------------------------- */