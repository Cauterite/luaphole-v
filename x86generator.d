/* -------------------------------------------------------------------------- */

version (X86):

import Std_;

import C_ = coretypes : Valº_ = Valº;
import Ir_ = intermediate;
import Rt_ = runtime : Rtº_ = RuntimeStateº;

static assert(Valº_.sizeof == 16);

/* -------------------------------------------------------------------------- */

/*
	calling conventions
	¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯
	the call convention for closure functions is a restricted subset of CDECL:

		- all functions have this signature:
		`Valº function(size_t argc, Valº self, ...)`

		- `argc` is the number of parameters passed on the stack (excluding
		the `argc` parameter itself)

		- `self` is the closure object being invoked

		- all parameters except argc (and the implicit return pointer) must be
		aligned on the stack at 16-byte boundaries


	position-independent code
	¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯
	generated code should not contain any references to absolute memory
	addresses. all memory access is either relative to the current function's
	start address or via the runtime state pointer. both these pointers are
	available in the `self` parameter of every closure function.
*/

// TODO: unittest merge_append
// TODO: funcinfoº
// TODO: allocator for function code

/* --- code generators --- */

C_.Closureº gen_chunk(
	Rtº_* Rt,
	C_.Namespaceº Ns,
	immutable Ir_.Irº Body
) out (X) {
	assert(X.Func);
	assert(X.Runtime is Rt);
} body {
	/* generate a closure that evaluates and returns 'Body', with 'Ns' as its
	only upvalue */

	auto ChunkIr = new immutable Ir_.Funcº(
		`chunk;`~randomUUID_.to_!string,
		new string[0], /* formals */
		``, /* formal va */
		[Body]
	);
	size_t UpvalC = ChunkIr.UpvalSyms.walkLength_;
	enforce_(UpvalC <= 1, `chunk body contains multiple upvalue references`);

	/* generate the function code */
	immutable FuncCodeº Code = gen_func_body(ChunkIr).assume_unique();

	/* allocate aligned memory for the code */
	ubyte[] Payload = Rt_.valigned_malloc!ubyte(
		Rt, Code.ValignedSize/Valignment
	)[0 .. Code.ValignedSize];

	/* write the code into memory */
	copy_(Code.Read, Payload);

	/* function start address */
	auto EntryPtr = cast(C_.Funcº) (Payload.ptr + Code.ValignedTrailSize);

	/* allocate closure if necessary */
	Valº_* Upvals = Rt_.valigned_malloc!Valº_(Rt, UpvalC);
	if (UpvalC == 1) {
		Upvals[0] = Ns;
	};

	C_.Closureº Chunk = {
		Func : EntryPtr,
		Upvals : Upvals,
		Runtime : Rt,
	};
	return Chunk;
};

struct Ctxº {
	FuncCodeº Code;
	/* symbol table maps symbols to code generators */
	BufChainº delegate(R16º)[immutable Ir_.Symbolº] SymTbl;
	/* is the code being generated in the tail position of a function? */
	bool IsTailPosition;
	/* there are at least this many parameters in scope */
	size_t MinimumArgC;
	/* how many locals on the stack? */
	size_t LocalC;

	void put(Tº)(Tº Xs) {Code.put(Xs);};
};

private struct gen_expr {
	alias Generators = AliasSeq_!(
		gen_nil, gen_utf8, gen_atom, gen_num, gen_sym,
		gen_invocation, gen_if, gen_func, gen_let
	);

	static void opCall(Ctxº Ctx, R16º R, immutable Ir_.Irº X) {
		debug static int Lvl;
		debug writeln_(
			`   `.repeat_(Lvl).join_(``), typeid(cast(Object) X), ` -<`
		);
		debug ++Lvl;

		/* generate code which evaluates X and writes the result to reg R */
		DispatchTbl[typeid(cast(Object) X)](Ctx, R, cast(Object) X);

		debug --Lvl;
		debug writeln_(`   `.repeat_(Lvl).join_(``), `>-`);
	};

	/* dynamic dispatch table */
	private static immutable Generº[TypeInfo] DispatchTbl;
	private alias Generº = void function(Ctxº, R16º, Object);
	shared static this() {
		foreach (X; Generators) {
			alias KeyTº = Unqual_!(Parameters_!X[2]);
			DispatchTbl[typeid(KeyTº)] = cast(Generº) &X;
		};
		DispatchTbl.rehash;
	};

	unittest {
		// http://forum.dlang.org/post/wyxxgkcauzmdjdvshrom@forum.dlang.org
		class Tº {};
		assert(typeid(new immutable(Tº)) == typeid(Tº));
	};
};

private void gen_nil(Ctxº C, R16º R, immutable Ir_.Nilº) {
	/* ? */
	gen_opaque_lit(C.Code, R, cast(uint[4]) bytes(Valº_.init));
};

private void gen_atom(Ctxº C, R16º R, immutable Ir_.Atomº Obj) {
	/* ? */
	auto V = C_.atom(Obj.Txt);

	/* R.Func <- &runtime.voke_atom */
	C.put_(gen_load_self_m4!q{Runtime}(R4º.Ax));
	C.put_(op_mov_r4m4(R4º.Ax, R4º.Ax, Rtº_.VokeAtom.offsetof));
	C.put_(op_insr_r16r4(R, R4º.Ax, V.Func.offsetof/4));

	/* R.Len <- V.Len */
	C.put_(op_mov_r4i4(R4º.Ax, V.Len));
	C.put_(op_insr_r16r4(R, R4º.Ax, V.Len.offsetof/4));

	/* R.Payload[1] <- V.Payload[1] */
	C.put_(op_mov_r4i4(R4º.Ax, V.Payload[1]));
	C.put_(op_insr_r16r4(R, R4º.Ax, 1 + V.Payload.offsetof/4));

	if (V.IsShort) {
		/* R.Payload[0] <- V.Payload[0] */
		C.put_(op_mov_r4i4(R4º.Ax, V.Payload[0]));
		C.put_(op_insr_r16r4(R, R4º.Ax, V.Payload.offsetof/4));

	} else {
		auto Txt = new BufChainº;
		Txt.put_(cast(ubyte[]) (V.LongStr[0 .. V.Len]));
		ptrdiff_t Offset = C.Code.prepend(Txt.assume_unique());

		/* R.LongStr <- Txt */
		C.put_(gen_load_self_m4!q{Func}(R4º.Ax)); /* EAX <- Self.Func */
		C.put_(op_sub_r4i4(R4º.Ax, Offset)); /* EAX -= Offset */
		C.put_(op_insr_r16r4(R, R4º.Ax, V.LongStr.offsetof/4));
	};
};

private void gen_utf8(Ctxº C, R16º R, immutable Ir_.Utf8º Obj) {
	/* ? */
	auto V = C_.utf8(Obj.Txt);

	/* R.Func <- &runtime.voke_utf8 */
	C.put_(gen_load_self_m4!q{Runtime}(R4º.Ax));
	C.put_(op_mov_r4m4(R4º.Ax, R4º.Ax, Rtº_.VokeUtf8.offsetof));
	C.put_(op_insr_r16r4(R, R4º.Ax, V.Func.offsetof/4));

	auto Txt = new BufChainº;
	Txt.put_(cast(ubyte[]) (V.S[]));
	ptrdiff_t Offset = C.Code.prepend(Txt.assume_unique());

	/* R.Ptr <- Txt */
	C.put_(gen_load_self_m4!q{Func}(R4º.Ax)); /* EAX <- Self.Func */
	C.put_(op_sub_r4i4(R4º.Ax, Offset)); /* EAX -= Offset */
	C.put_(op_insr_r16r4(R, R4º.Ax, V.S.offsetof/4));

	/* R.Size <- V.Size */
	C.put_(op_mov_r4i4(R4º.Ax, V.S.length));
	C.put_(op_insr_r16r4(R, R4º.Ax, V.S.offsetof/4 + 1));

	/* R.Len <- V.Len */
	C.put_(op_mov_r4i4(R4º.Ax, V.Len));
	C.put_(op_insr_r16r4(R, R4º.Ax, V.Len.offsetof/4));
};

private void gen_num(Ctxº C, R16º R, immutable Ir_.Numberº Obj) {
	auto V = C_.floht(Obj.N);

	/* ECX <- &runtime.voke_float */
	C.put_(gen_load_self_m4!q{Runtime}(R4º.Cx));
	C.put_(op_mov_r4m4(R4º.Cx, R4º.Cx, Rtº_.VokeFloat.offsetof));

	C.put_(op_xor_r16r16(R, R)); /* R <- 0 */

	/* R.payload = V.payload */
	foreach (ubyte Idx; 1 .. 4) {
		if (V.Val.Data[Idx-1] != 0) {
			C.put_(op_mov_r4i4(R4º.Ax, V.Val.Data[Idx-1]));
			C.put_(op_insr_r16r4(R, R4º.Ax, Idx));
		};
	};

	/* R.Func <- &runtime.voke_float */
	C.put_(op_insr_r16r4(R, R4º.Cx, V.Func.offsetof/4));
};

private void gen_sym(Ctxº C, R16º R, immutable Ir_.Symbolº Sym) {
	/* ? */

	/* get generator */
	auto f = C.SymTbl.get(Sym, null);
	enforce_(f !is null, `reference to undefined symbol `~to_!string(Sym));
	/* generate */
	C.Code.merge_append(f(R));
};

private void gen_if(Ctxº C, R16º R, immutable Ir_.Ifº If) {
	/* ? */

	{/* evaluate predicate */
		Ctxº InnerCtx = C;
		InnerCtx.IsTailPosition = false;
		gen_expr(InnerCtx, R, If.Pred);
		C.put_(op_test_r16r16(R, R)); /* if (Pred is nil) {… */
	};

	size_t BranchOffset = C.Code.NextOffset;
	C.put_(bytes(Op2.JeI4)~bytes(0xffffffff)); /* if (Pred is nil) goto Else */

	/* evaluate 'Then' */
	gen_expr(C, R, If.Then);

	/* jump over Else */
	size_t JumpOffset = C.Code.NextOffset;
	C.put_(Op1.JmpI4~bytes(0xffffffff));

	/* evaluate 'Else' */
	size_t ElseOffset = C.Code.NextOffset;
	gen_expr(C, R, If.Else);
	size_t EndOffset = C.Code.NextOffset;

	/* fix the branch destination */
	C.Code.Payload.overwrite_at(
		BranchOffset,
		bytes(Op2.JeI4)~bytes(ElseOffset - BranchOffset - 6),
	);
	/* fix the jump destination */
	C.Code.Payload.overwrite_at(
		JumpOffset,
		Op1.JmpI4~bytes(EndOffset - JumpOffset - 5),
	);
};

private void gen_invocation(Ctxº C, R16º R, immutable Ir_.Invocationº V) {
	/* ? */
	size_t ArgC = 1 + V.Params.length; /* #(self~params) */
	bool DoTailJump;
	{
		/* does the current scope have enough param space for this tail-jump? */
		bool CanTailJump = ArgC <= C.MinimumArgC;
		if (V.ForceTailJump) {
			enforce_(CanTailJump, `too many parameters to force a tail-jump`);
			DoTailJump = true;
		} else {
			DoTailJump = CanTailJump && C.IsTailPosition;
		};
	};
	C.IsTailPosition = false;

	/* set the stack up for a call */
	version (assert) {
		/* verify stack alignment */
		C.put_(op_mov_r4r4(R4º.Ax, R4º.Sp)); /* EAX <- ESP */
		gen_assert_ax_aligned(C);
		/* verify return value alignment */
		C.put_(op_mov_r4m4(R4º.Ax, R4º.Bp, 0x8)); /* EAX <- return value ptr */
		gen_assert_ax_aligned(C);
	};
	C.put_(op_sub_r4i4(R4º.Sp, 16*ArgC)); /* ESP -= 16*argc */

	/* stack layout:
		ESP+00: [¯¯¯¯¯¯]
		ESP+04: [??????]
		ESP+08: [??????]
		ESP+0c: [______]
		ESP+10: [¯¯¯¯¯¯]
		ESP+14: [??????]
		ESP+18: [??????]
		ESP+1c: [______]
		ESP+20: [¯¯¯¯¯¯]
		ESP+……: [???……
	*/

	gen_expr(C, R, V.Invokee); /* R <- invokee */
	C.put_(op_mova_m16r16(R4º.Sp, 0, R)); /* [ESP] <- R */

	/* stack layout:
		ESP+00: [¯¯¯¯¯¯]
		ESP+04: [ arg0 ]
		ESP+08: [(self)]
		ESP+0c: [______]
		ESP+10: [¯¯¯¯¯¯]
		ESP+14: [??????]
		ESP+18: [??????]
		ESP+1c: [______]
		ESP+20: [¯¯¯¯¯¯]
		ESP+……: [???……
	*/

	foreach (Idx, Param; V.Params) {
		gen_expr(C, R, Param); /* R <- param */
		C.put_(op_mova_m16r16(R4º.Sp, 16*Idx, R)); /* [ESP + 16*Idx] <- R */
	};

	/* stack layout:
		ESP+00: [¯¯¯¯¯¯]
		ESP+04: [ arg0 ]
		ESP+08: [(self)]
		ESP+0c: [______]
		ESP+10: [¯¯¯¯¯¯]
		ESP+14: [ arg1 ]
		ESP+18: [      ]
		ESP+1c: [______]
		ESP+20: [¯¯¯¯¯¯]
		ESP+……: [ arg2…
	*/

	if (DoTailJump) {/* do a tail-jump */

		/* move parameters off the stack top, down into parameter positions */
		foreach (Offset; iota_(0, 16*ArgC, 16)) {
			/* R <- [ESP + Offset] */
			C.put_(op_mova_r16m16(R, R4º.Sp, Offset));
			/* [EBP + 16 + Offset] <- R */
			C.put_(op_mova_m16r16(R4º.Bp, 16 + Offset, R));
		};

		C.put_(op_mov_r4i4(R4º.Ax, ArgC)); /* EAX <- argc */
		C.put_(op_mov_m4r4(R4º.Bp, 0xc, R4º.Ax)); /* [EBP + 0xc] <- EAX */
		C.put_(op_mov_r4r4(R4º.Sp, R4º.Bp)); /* ESP <- EBP */
		C.put_(ubyte(Op1.PopR4 + R4º.Bp)); /* POP EBP */

		/* stack layout:
			ESP+00: [ return address ]
			ESP+04: [ return value pointer ]
			ESP+08: [ argc ]
			ESP+0c: [¯¯¯¯¯¯]
			ESP+10: [ arg0 ]
			ESP+14: [(self)]
			ESP+18: [______]
			ESP+1c: [¯¯¯¯¯¯]
			ESP+20: [ arg1 ]
			ESP+24: [      ]
			ESP+28: [______]
			ESP+2c: [¯¯¯¯¯¯]
			ESP+……: [ arg2…
		*/

		/* JMP invokee.func */
		C.put_(op_mov_r4m4(R4º.Ax, R4º.Sp, 0xc + Valº_.Func.offsetof));
		C.put_(op_jmp_r4(R4º.Ax));

		/* <unreachable> */

	} else {/* do a call */

		C.put_(op_mov_r4m4(R4º.Ax, R4º.Sp, 0)); /* EAX <- invokee.func */

		C.put_(Op1.PushI4~bytes(ArgC)); /* PUSH ArgC */
		C.put_(op_mov_r4m4(R4º.Cx, R4º.Bp, 0x8)); /* ECX <- return value ptr */
		C.put_(ubyte(Op1.PushR4 + R4º.Cx)); /* PUSH ECX */

		C.put_(op_call_r4(R4º.Ax)); /* CALL EAX */

		C.put_(ubyte(Op1.PopR4 + R4º.Ax)); /* EAX <- return value ptr */
		C.put_(op_mova_r16m16(R, R4º.Ax, 0)); /* R <- [EAX] */
		C.put_(op_add_r4i4(R4º.Sp, 4 + 16*ArgC)); /* ESP += 4 + 16*argc */

		/* return value is in R */
	};
};

private void gen_let(Ctxº C, R16º R, immutable Ir_.Letº Let) {
	/* ? */
	bool IsTailPos = C.IsTailPosition;
	C.IsTailPosition = false;

	/* inner symbol table */
	C.SymTbl = C.SymTbl.dup;

	/* bind new locals */
	foreach (Idx, Sym; Let.ParamSyms) {
		C.put_(op_xor_r16r16(R, R)); /* R <- 0 (break depend.) */
		gen_expr(C, R, Let.Vals[Idx]);

		C.LocalC += 1;
		ptrdiff_t Offset = -16*(C.LocalC);
		C.put_(op_mova_m16r16(R4º.Bp, Offset, R)); /* [EBP + Offset] <- R */

		C.SymTbl[Sym] = (R16º R) {
			auto C = new BufChainº;
			C.put_(op_mova_r16m16(R, R4º.Bp, Offset)); /* R <- [EBP + Offset] */
			return C;
		};
	};

	/* evaluate body expressions */
	foreach (Idx, Body; Let.Bodies) {
		if (Idx == Let.Bodies.length - 1) {
			C.IsTailPosition = IsTailPos;
		};
		C.put_(op_xor_r16r16(R, R)); /* R <- 0 (break depend.) */
		gen_expr(C, R, Body);
	};
};

private void gen_func(Ctxº C, R16º R, immutable Ir_.Funcº Func) {
	/* ? */

	ptrdiff_t Offset;
	{/* generate function body */
		auto Payload = gen_func_body(Func).assume_unique();
		Offset = C.Code.prepend(Payload);
		Offset += Payload.ValignedTrailSize;
	};

	/* R <- new function value */
	C.put_(op_xor_r16r16(R, R));
	{
		C.put_(gen_load_self_m4!q{Func}(R4º.Ax)); /* EAX <- Self.Func */
		/* R.Func <- Self.Func + Offset */
		C.put_(op_add_r4i4(R4º.Ax, Offset));
		C.put_(op_insr_r16r4(R, R4º.Ax, C_.Closureº.Func.offsetof/4));
	};

	/* EAX <- &runtime */
	C.put_(gen_load_self_m4!q{Runtime}(R4º.Ax));

	/* R.runtime <- &runtime */
	C.put_(op_insr_r16r4(R, R4º.Ax, C_.Closureº.Runtime.offsetof/4));

	auto UpSyms = Func.UpvalSyms.array_;
	if (UpSyms != []) {

		/* ECX <- &runtime.valigned_malloc */
		C.put_(op_mov_r4m4(R4º.Cx, R4º.Ax, Rtº_.ValignedMalloc.offsetof));

		/* allocate upvalues array */
		C.put_(Op1.PushI4~bytes(UpSyms.length)); /* PUSH # of upvals */
		C.put_(ubyte(Op1.PushR4 + R4º.Ax)); /* PUSH &runtime */
		C.put_(op_call_r4(R4º.Cx)); /* EAX <- valigned_malloc(…) */
		C.put_(op_insr_r16r4(R, R4º.Ax, C_.Closureº.Upvals.offsetof/4));
		C.put_(ubyte(Op1.PopR4 + R4º.Ax)); /* POP EAX */
		C.put_(ubyte(Op1.PopR4 + R4º.Ax)); /* POP EAX */

		// TODO: find an available scratch register

		{/* PUSH R */
			C.put_(op_sub_r4i4(R4º.Sp, 16));
			C.put_(op_mova_m16r16(R4º.Sp, 0, R));
		};
		/* evaluate upsyms, fill upvalues array */
		foreach (Idx, Sym; UpSyms) {
			R16º Scratch = R;
			gen_expr(C, Scratch, Sym); /* Scratch <- upvalue */
			/* R.Upvals[Idx] <- Scratch */
			C.put_(op_mov_r4m4(R4º.Ax, R4º.Sp, C_.Closureº.Upvals.offsetof));
			C.put_(op_mova_m16r16(R4º.Ax, Idx*16, Scratch));
		};
		{/* POP R */
			C.put_(op_mova_r16m16(R, R4º.Sp, 0));
			C.put_(op_add_r4i4(R4º.Sp, 16));
		};
	};
};

struct FuncInfoº {
	string Name;
};

private FuncCodeº gen_func_body(immutable Ir_.Funcº Func) {
	Ctxº C = {
		Code : new FuncCodeº,
		MinimumArgC : 1 + Func.PosNames.length,
	};

	{/* prepend funcinfo */
		FuncInfoº Info = {
			Name : Func.SelfSym.to_source.to_!string
		};
		auto Buf = new BufChainº;
		Buf.put_(bytes(Info));
		C.Code.prepend(Buf.assume_unique());
	};

	{/* fill the symbol table */
		foreach (Idx, Sym; Func.ParamSyms) {
			bool IsVa = Func.IsVariadic && Sym.Name == Func.VaName;
			ptrdiff_t Offset = IsVa ? -16 : 16 + Idx*16;
			C.SymTbl[Sym] = (R16º R) {
				auto C = new BufChainº;
				/* R <- [EBP + Offset] */
				C.put_(op_mova_r16m16(R, R4º.Bp, Offset));
				return C;
			};
		};

		foreach (Idx, Sym; Func.UpvalSyms) {
			C.SymTbl[Sym] = (R16º R) {
				auto C = new BufChainº;
				/* EAX <- self.upvals */
				C.put_(gen_load_self_m4!q{Upvals}(R4º.Ax));
				/* R <- upvals[idx] */
				C.put_(op_mova_r16m16(R, R4º.Ax, Idx*16));
				return C;
			};
		};
	};

	/* prologue */
	C.put_(ubyte(Op1.PushR4 + R4º.Bp)); /* PUSH EBP */
	C.put_(op_mov_r4r4(R4º.Bp, R4º.Sp)); /* EBP <- ESP */

	/* stack layout:
		EBP+00: [ saved EBP ]
		EBP+04: [ return address ]
		EBP+08: [ return value pointer ]
		EBP+0c: [ argc ]
		EBP+10: [¯¯¯¯¯¯]
		EBP+14: [ arg0 ]
		EBP+18: [(self)]
		EBP+1c: [______]
		EBP+20: [¯¯¯¯¯¯]
		EBP+24: [ arg1 ]
		EBP+28: [      ]
		EBP+2c: [______]
		EBP+30: [¯¯¯¯¯¯]
		EBP+……: [ arg2…

	params must be 16-byte aligned */

	version (assert) {
		/* verify stack alignment */
		C.put_(op_mov_r4r4(R4º.Ax, R4º.Sp)); /* EAX <- ESP */
		gen_assert_ax_aligned(C);
		/* verify return value alignment */
		C.put_(op_mov_r4m4(R4º.Ax, R4º.Bp, 0x8)); /* EAX <- return value ptr */
		gen_assert_ax_aligned(C);
	};

	{/* verify argc */
		C.put_(op_mov_r4m4(R4º.Ax, R4º.Bp, 0xc)); /* EAX <- argc */
		C.put_(Op1.CmpAxI4~bytes(C.MinimumArgC)); /* CMP argc, arity */

		if (!Func.IsVariadic && Func.StrictArity) {/* fixed arity */
			C.put_(Op1.JneI1.bytes~ubyte(2)); /* if argc != arity */
		} else {/* variadic */
			C.put_(Op1.JlI1.bytes~ubyte(2)); /* if argc < arity */
		};
		C.put_(Op1.JmpI1.bytes~ubyte(1));
		C.put_(Op1.Break); /* invalid argc */
	};

	/* … EAX still holding argc … */

	if (Func.IsVariadic) {
		/* construct a C_.Arrayº pointing to varargs on stack */

		C.put_(op_xor_r16r16(R16º.X0, R16º.X0)); /* XMM0 <- 0 */
		C.put_(gen_load_self_m4!q{Runtime}(R4º.Cx)); /* ECX <- &runtime */

		/* EDX <- runtime.VokeArray */
		C.put_(op_mov_r4m4(R4º.Dx, R4º.Cx, Rtº_.VokeArray.offsetof));
		/* XMM0.Func <- runtime.VokeArray */
		C.put_(op_insr_r16r4(R16º.X0, R4º.Dx, C_.Arrayº.Func.offsetof/4));

		/* XMM0.Len <- ArgC - PosNames.len - 1 */
		C.put_(op_sub_r4i4(R4º.Ax, Func.PosNames.length + 1));
		C.put_(op_insr_r16r4(R16º.X0, R4º.Ax, C_.Arrayº.Len.offsetof/4));

		/* XMM0.Ptr <- EBP + 0x20 + 16*PosNames.len */
		C.put_(op_mov_r4r4(R4º.Ax, R4º.Bp));
		C.put_(op_add_r4i4(R4º.Ax, 0x20 + 16*Func.PosNames.length));
		C.put_(op_insr_r16r4(R16º.X0, R4º.Ax, C_.Arrayº.Ptr.offsetof/4));

		/* PUSH XMM0 */
		C.put_(op_sub_r4i4(R4º.Sp, 16));
		C.put_(op_mova_m16r16(R4º.Sp, 0, R16º.X0));

		C.LocalC += 1;

		/* stack layout:
			EBP-10: [¯¯¯¯¯¯¯]
			EBP-0c: [varargs]
			EBP-08: [(array)]
			EBP-04: [_______]
			EBP+00: [ saved EBP ]
			EBP+04: [ return address ]
			EBP+08: [ return value pointer ]
			EBP+0c: [ argc ]
			EBP+10: [¯¯¯¯¯¯]
			EBP+……: [ arg0…
		*/
	};

	/* allocate stack space for body locals */
	C.put_(op_sub_r4i4(R4º.Sp, 16 * Func.BodyLocalSymC));

	/* generate body expressions */
	foreach (Idx, Body; Func.Bodies) {
		C.IsTailPosition = Idx == Func.Bodies.length - 1;
		C.put_(op_xor_r16r16(R16º.X0, R16º.X0)); /* XMM0 <- 0 (break depend.) */
		gen_expr(C, R16º.X0, Body);
	};
	/* if the last expression was a tail call, following code is unreachable.
	otherwise the return value is in XMM0 */

	/* return the last expression */
	C.put_(op_mov_r4m4(R4º.Ax, R4º.Bp, 0x8)); /* EAX <- return value ptr */
	C.put_(op_mova_m16r16(R4º.Ax, 0, R16º.X0)); /* [EAX] <- XMM0 */

	/* epilogue */
	C.put_(op_mov_r4r4(R4º.Sp, R4º.Bp)); /* ESP <- EBP */
	C.put_(ubyte(Op1.PopR4 + R4º.Bp)); /* POP EBP */
	C.put_(Op1.Ret); /* RET */

	return C.Code;
};

/* --- generator utilities --- */

private void gen_assert_ax_aligned(Ctxº C) {
	/* if (EAX & 0x0000000f) {int3} */
	C.put_(Op1.TestAxI4~bytes(0xf));
	C.put_(Op1.JneI1.bytes~ubyte(2));
	C.put_(Op1.JmpI1.bytes~ubyte(1));
	C.put_(Op1.Break); /* stack misaligned */
};

private auto gen_load_param(R16º R, size_t Idx) {
	/* loads a val from the current function's parameters */
	return op_mova_r16m16(R, R4º.Bp, 0x10 + Idx*16);
};

private auto gen_load_self_m4(string FieldName)(R4º R) if (
	staticIndexOf_!(FieldName, FieldNameTuple_!(C_.Closureº))
) {
	/* R <- self.FieldName */
	enum Offset = mixin(`C_.Closureº.`~FieldName~`.offsetof`);
	return op_mov_r4m4(R, R4º.Bp, 0x10 + Offset);
};

private void gen_opaque_lit(Tº)(Tº C, R16º R, uint[4] V) if (
	isOutputRange_!(Tº, ubyte)
) {
	/* write literal value V into XMM register R:
		pxor R, R;
		mov EAX, V[0];
		pinsrd R, EAX, 0;
		mov EAX, V[1];
		pinsrd R, EAX, 1;
		mov EAX, V[2];
		pinsrd R, EAX, 2;
		mov EAX, V[3];
		pinsrd R, EAX, 3;
	*/
	C.put_(op_xor_r16r16(R, R)); /* R <- 0 */
	foreach (ubyte Idx; 0 .. 4) {
		if (V[Idx] != 0) {
			C.put_(op_mov_r4i4(R4º.Ax, V[Idx]));
			C.put_(op_insr_r16r4(R, R4º.Ax, Idx));
		};
	};
};
unittest {
	auto C = new BufChainº;
	gen_opaque_lit(C, R16º.X1, [
		0xff445566, 0x00000000, 0x06000300, 0xffffffff
	]);

	static void expect() {asm {
		naked;
		pxor XMM1, XMM1;
		mov EAX, 0xff445566;
		pinsrd XMM1, EAX, 0;
		mov EAX, 0x06000300;
		pinsrd XMM1, EAX, 2;
		mov EAX, 0xffffffff;
		pinsrd XMM1, EAX, 3;
	};};
	enum ExpectSz = 0x25;

	assert(C.assume_unique().Read
		.take_(ExpectSz)
		.equal_((cast(ubyte*) &expect)[0 .. ExpectSz])
	);
};

/* --- code buffers --- */

interface Codeº {
	enum ubyte Pad = Op1.Break;
	@property InputRange_!ubyte Read() immutable;
	@property size_t ValignedSize() const;//out (Sz) {assert(is_valigned(Sz));};
};

class FuncCodeº : Codeº {
	/* ? */
	private SList_!(Rebindable_!(immutable Codeº)) Trail;
	Unique_!BufChainº Payload;

	/* note: don't let any references to the trail escape! */

	invariant {assert(!Payload.isEmpty);};

	this() {Payload = new BufChainº;};

	void put(Tº)(Tº Xs) {Payload.put(Xs);};

	@property override InputRange_!ubyte Read() immutable {
		/* traverse the entire code sequence, with aligned payloads.
		return range object because recursive type inference. */
		return inputRangeObject_(
			(cast() Trail)[]
				.map_!(X => X.Read)
				.joiner_
				.chain_(Payload.Read)
		);
	};

	@property size_t NextOffset() const {
		/* returns code offset of where the next byte appended will be placed,
		relative to the start of the payload. */
		return Payload.RawSize;
	};

	@property override size_t ValignedSize() const {
		return ValignedTrailSize + Payload.ValignedSize;
	};

	@property size_t ValignedTrailSize() const {
		return (cast() Trail)[].fold_!((Acc, X) => Acc + X.ValignedSize)(0);
	};

	void merge_append(BufChainº X) out {assert(X.Buffers.empty);} body {
		version (assert) size_t XSz = X.RawSize;
		version (assert) size_t OldSz = Payload.RawSize;

		/* moves all buffers from X to the end of Payload */
		Payload.Buffers.insertBack(X.Buffers[]);
		X.Buffers.clear();

		assert(Payload.RawSize == OldSz + XSz);
	};

	ptrdiff_t prepend(immutable Codeº X) {
		/* prepends code to the trail.
		returns code offset from the start of the payload. */
		Trail.insertFront(rebindable_(X));
		return -ValignedTrailSize;
	};
};

class BufChainº : Codeº {
	/* ? */
	private DList_!(Appender_!(ubyte[])) Buffers;

	/* note: don't let any references to the buffers escape! */

	void put()(ubyte X) {put_impl(only_(X));};
	void put(size_t Len)(ubyte[Len] X) {put_impl(X[]);};
	void put(Tº)(Tº Xs) if (isInputRange_!Tº && is(ElementType_!Tº == ubyte)) {
		put_impl(Xs);
	};

	private void put_impl(Tº)(Tº Xs) {
		/* append to the last buffer */
		if (Buffers.empty) {
			Buffers.insert(typeof(Buffers.front)());
		};
		Buffers.back.put(Xs);
	};

	@property override InputRange_!ubyte Read() immutable {
		/* iterates over all the bytes in all the buffers, in forward order. */
		/* resulting range is padded to alignment. */
		return inputRangeObject_(
			(cast() Buffers)[].map_!(X => X.data)
				.joiner_
				.chain_(Pad.repeat_)
				.takeExactly_(ValignedSize)
		);
	};

	@property size_t RawSize() const {
		return (cast() Buffers)[]
			.fold_!((Acc, X) => Acc + X.data.length)(0)
		;
	};

	@property override size_t ValignedSize() const {
		return valign_up(RawSize);
	};

	void overwrite_at(Tº)(size_t Offset, Tº Xs) if (
		isInputRange_!Tº && is(ElementType_!Tº == ubyte) && hasLength_!Tº
	) {
		/* must not straddle buffers */
		ubyte[] S = slice(Offset, Offset + Xs.length);
		foreach (Idx, X; Xs) {S[Idx] = X;};
	};

	private ubyte[] slice(size_t Start, size_t End) {
		size_t PastSz;
		foreach (Buf; Buffers[]) {
			if (Start < PastSz + Buf.data.length) {
				enforce_(End-PastSz <= Buf.data.length, `range violation`);
				return Buf.data[Start-PastSz .. End-PastSz];
			};
			PastSz += Buf.data.length;
		};
		throw new Exception(`range violation`);
	};
};

auto assume_unique(Tº)(Tº Obj) if (is(Tº == class)) {
	return Obj.assume_unique();
};
auto assume_unique(Tº)(ref Tº Obj) if (is(Tº == class)) {
	auto Imm = cast(immutable) Obj;
	Obj = null;
	return Imm;
};

unittest {
	auto C = new FuncCodeº;
	put_(C, ubyte(77).repeat_(Valignment));
	auto U = C.assume_unique();
	assert(U !is C);
	assert(is(typeof(U) == immutable));
	assert(U.Read.equal_(ubyte(77).repeat_(Valignment)));
};

unittest {
	auto C = new FuncCodeº;

	auto Src1 = ubyte(77).repeat_(Valignment).array_;
	auto Src2 = ubyte(99).repeat_(2*Valignment).array_;

	put_(C, Src1);
	assert(C.ValignedSize == Src1.length);

	ptrdiff_t Offset = C.prepend(({
		auto Buf = new FuncCodeº;
		put_(Buf, Src2);
		assert(Buf.ValignedSize == Src2.length);
		return Buf.assume_unique();
	})());
	assert(Offset == -Src2.length);

	assert(C.assume_unique().Read.equal_(Src2.chain_(Src1)));
};

unittest {
	auto C = new FuncCodeº;

	auto Src1 = ubyte(77).repeat_(Valignment).array_;
	auto Src2 = ubyte(99).repeat_(2*Valignment).array_;
	put_(C, Src1);

	ptrdiff_t Offset = C.prepend(({
		auto Buf = new FuncCodeº;
		put_(Buf, Src2);
		return Buf.assume_unique();
	})());

	C.Payload.overwrite_at(0, bytes(Offset)[]);

	auto Ci = C.assume_unique();
	assert(Ci.Read
		.drop_(Ci.ValignedTrailSize)
		.takeExactly_(Offset.sizeof)
		.equal_(bytes(Offset)[])
	);
};

/* --- --- */

enum Valignment = Valº_.sizeof;
static if (Valignment == 16) {
	alias is_valigned = X => !(X & 0xf);
	alias valign_up = X => (X & 0xfffffff0) + (X & 0xf ? 16 : 0);
	alias valign_down = X => X & 0xfffffff0;
} else {
	alias is_valigned = X => X % Valignment == 0;
	alias valign_up = X => X + (Valignment - (X % Valignment));
	alias valign_down = X => X - X % Valignment;
};
unittest {
	assert(valign_up(0) == 0);
	assert(valign_up(1) == 16);
	assert(valign_up(2) == 16);
	assert(valign_up(15) == 16);
	assert(valign_up(16) == 16);
	assert(valign_up(17) == 32);
	assert(valign_up(31) == 32);
	assert(valign_up(32) == 32);
};

enum R4º : ubyte {Ax, Cx, Dx, Bx, Sp, Bp, Si, Di};
enum R16º : ubyte {X0, X1, X2, X3, X4, X5, X6, X7};

enum Op1 : ubyte {
	Break = 0xcc,
	Nop = 0x90,

	CallI4 = 0xe8, /* 32-bit displacement */
	Ret = 0xc3,

	MovR4I4 = 0xb8,
	MovR4Rm4 = 0x8b,
	MovRm4R4 = 0x89,

	PushR4 = 0x50, /* +R4º */
	PushI4 = 0x68,
	PopR4 = 0x58, /* +R4º */

	CmpAxI4 = 0x3d,
	TestAxI4 = 0xa9,

	AddAxI4 = 0x05,
	SubAxR4 = 0x2d,

	JmpI4 = 0xe9, /* 32-bit displacement */
	JmpRm4 = 0xff,
	JmpI1 = 0xeb, /* 8-bit displacement */
	JeI1 = 0x74, /* 8-bit displacement */
	JneI1 = 0x75, /* 8-bit displacement */
	JlI1 = 0x7c, /* 8-bit displacement */
	JleI1 = 0x7e, /* 8-bit displacement */
	JgI1 = 0x7f, /* 8-bit displacement */
	JgeI1 = 0x7d, /* 8-bit displacement */
};

enum Op2 : ushort {
	CallRm4 = 0x10ff, /* +(R4º<<8) +(mode<<14) */

	SubRm4I4 = 0x2881, /* +(mode<<14) */

	JeI4 = 0x840f, /* 32-bit displacement */
	JneI4 = 0x850f, /* 32-bit displacement */
	JlI4 = 0x8c0f, /* 32-bit displacement */
	JleI4 = 0x8e0f, /* 32-bit displacement */
};

enum Op3 : uint {
	MovaR16Rm16 = 0x6f0f66, /* MOVDQA; aligned */
	MovaRm16R16 = 0x7f0f66, /* MOVDQA; aligned */
	XorR16R16 = 0xef0f66,
};

enum Op4 : uint {
	PinsrD = 0x223a0f66,
	Ptest = 0x17380f66,
};

ubyte[2] op_jmp_r4(R4º Dst) {
	/* JMP Dst */
	return [Op1.JmpRm4, to_!ubyte(Dst + 0b11100000)];
};
unittest {
	assert(op_jmp_r4(R4º.Ax) == x"ff e0");
	assert(op_jmp_r4(R4º.Bx) == x"ff e3");
	assert(op_jmp_r4(R4º.Sp) == x"ff e4");
	assert(op_jmp_r4(R4º.Di) == x"ff e7");
};

auto op_test_r16r16(R16º A, R16º B) {
	/* PTEST A, B */
	ubyte[5] C = bytes(Op4.Ptest)~to_!ubyte(0b11000000 + A*8 + B);
	return C;
};
unittest {
	assert(op_test_r16r16(R16º.X0, R16º.X0) == x"660f3817 c0");
	assert(op_test_r16r16(R16º.X7, R16º.X7) == x"660f3817 ff");
	assert(op_test_r16r16(R16º.X2, R16º.X5) == x"660f3817 d5");
	assert(op_test_r16r16(R16º.X7, R16º.X0) == x"660f3817 f8");
};

auto op_add_r4i4(R4º Dst, int Val) {
	return op_sub_r4i4(Dst, -Val);
};

auto op_sub_r4i4(R4º Dst, int Val) {
	/* SUB Dst, Val */
	ubyte[6] C;
	C[0 .. 2] = bytes(to_!ushort(Op2.SubRm4I4|(Dst<<8)|(0b11<<14)));
	C[2 .. 6] = bytes(Val);
	return C;
};
unittest {
	assert(op_sub_r4i4(R4º.Ax, 0x100) == x"81e800010000");
	assert(op_sub_r4i4(R4º.Bx, 0x100) == x"81eb00010000");
	assert(op_sub_r4i4(R4º.Di, 0x100) == x"81ef00010000");
	assert(op_sub_r4i4(R4º.Sp, 0xaabbccdd) == x"81ecddccbbaa");
};

auto op_mova_r16m16(R16º Dst, R4º SrcPtr, int Displ) {
	/* MOVDQA Dst, [SrcPtr + Displ] */
	ubyte[9] C = Op1.Nop; /* padding */
	C[0 .. 3] = bytes(Op3.MovaR16Rm16)[0 .. 3];
	C[3] = to_!ubyte(0b10000000 + Dst*8 + SrcPtr);
	if (SrcPtr == R4º.Sp) {
		C[4] = to_!ubyte(R4º.Sp*8 + R4º.Sp); /* SIB byte */
		C[5 .. 9] = bytes(Displ);
	} else {
		C[4 .. 8] = bytes(Displ);
	};
	return C;
};
unittest {
	alias f = op_mova_r16m16;
	assert(f(R16º.X0, R4º.Ax, 0) == x"660f6f 80 00000000 90");
	assert(f(R16º.X0, R4º.Ax, 0xdeadbeef) == x"660f6f 80 efbeadde 90");
	assert(f(R16º.X0, R4º.Sp, 0) == x"660f6f 8424 00000000");
	assert(f(R16º.X0, R4º.Sp, 0xdeadbeef) == x"660f6f 8424 efbeadde");
	assert(f(R16º.X7, R4º.Bp, -0x100) == x"660f6fbd00ffffff 90");
};

auto op_mova_m16r16(R4º DstPtr, int Displ, R16º Src) {
	/* MOVDQA [DstPtr + Displ], Src */
	ubyte[9] C = Op1.Nop; /* padding */
	C[0 .. 3] = bytes(Op3.MovaRm16R16)[0 ..3];
	C[3] = to_!ubyte(0b10000000 + Src*8 + DstPtr);
	if (DstPtr == R4º.Sp) {
		C[4] = to_!ubyte(R4º.Sp*8 + R4º.Sp); /* SIB byte */
		C[5 .. 9] = bytes(Displ);
	} else {
		C[4 .. 8] = bytes(Displ);
	};
	return C;
};
unittest {
	alias f = op_mova_m16r16;
	assert(f(R4º.Ax, 0, R16º.X0) == x"660f7f 80 00000000 90");
	assert(f(R4º.Ax, 0xdeadbeef, R16º.X0) == x"660f7f 80 efbeadde 90");
	assert(f(R4º.Ax, 0xdeadbeef, R16º.X1) == x"660f7f 88 efbeadde 90");
	assert(f(R4º.Sp, 0xdeadbeef, R16º.X0) == x"660f7f 8424 efbeadde");
	assert(f(R4º.Sp, 0xdeadbeef, R16º.X7) == x"660f7f bc24 efbeadde");
	assert(f(R4º.Bp, -0x100, R16º.X7) == x"660f7f bd 00ffffff 90");
	assert(f(R4º.Sp, 0, R16º.X0) == x"660f7f 8424 00000000");
};

ubyte[2] op_call_r4(R4º Dst) {
	/* CALL Dst */
	return bytes(to_!ushort(Op2.CallRm4|(Dst<<8)|(0b11<<14)));
};
unittest {
	assert(op_call_r4(R4º.Ax) == x"ffd0");
	assert(op_call_r4(R4º.Si) == x"ffd6");
};

ubyte[4] op_xor_r16r16(R16º Dst, R16º Src) {
	/* PXOR Dst, Src */
	uint Param = 0b11000000 + Dst*8 + Src;
	return bytes(Op3.XorR16R16|(Param<<24));
};
unittest {
	assert(op_xor_r16r16(R16º.X0, R16º.X0) == x"660fef c0");
	assert(op_xor_r16r16(R16º.X7, R16º.X7) == x"660fef ff");
	assert(op_xor_r16r16(R16º.X2, R16º.X5) == x"660fef d5");
	assert(op_xor_r16r16(R16º.X7, R16º.X0) == x"660fef f8");
};

auto op_mov_r4i4(R4º Dst, uint Val) {
	/* MOV Dst, Val */
	ubyte[5] C;
	C[0] = to_!ubyte(Op1.MovR4I4 + Dst);
	C[1 .. 5] = bytes(Val);
	return C;
};
unittest {
	assert(op_mov_r4i4(R4º.Ax, 0) == x"b8 00000000");
	assert(op_mov_r4i4(R4º.Bx, 0) == x"bb 00000000");
	assert(op_mov_r4i4(R4º.Di, 0) == x"bf 00000000");
	assert(op_mov_r4i4(R4º.Sp, 0xaabbccdd) == x"bc ddccbbaa");
};

auto op_mov_r4r4(R4º Dst, R4º Src) {
	/* MOV Dst, Src */
	ubyte[2] C;
	C[0] = Op1.MovR4Rm4;
	C[1] = to_!ubyte(0b11000000 + Dst*8 + Src);
	return C;
};
unittest {
	assert(op_mov_r4r4(R4º.Bp, R4º.Sp) == x"8b ec");
};

auto op_mov_r4m4(R4º Dst, R4º SrcPtr, int Displ) {
	/* MOV Dst, [SrcPtr + Displ] */
	ubyte[7] C = Op1.Nop; /* padding */
	C[0] = Op1.MovR4Rm4;
	C[1] = to_!ubyte(0b10000000 + Dst*8 + SrcPtr);
	if (SrcPtr == R4º.Sp) {
		C[2] = to_!ubyte(R4º.Sp*8 + R4º.Sp); /* SIB byte */
		C[3 .. 7] = bytes(Displ);
	} else {
		C[2 .. 6] = bytes(Displ);
	};
	return C;
};
unittest {
	assert(op_mov_r4m4(R4º.Ax, R4º.Ax, 0) == x"8b80 00000000 90");
	assert(op_mov_r4m4(R4º.Ax, R4º.Sp, 0xdeadbeef) == x"8b8424 efbeadde");
};

auto op_mov_m4r4(R4º DstPtr, int Displ, R4º Src) {
	/* MOV [DstPtr + Displ], Src */
	ubyte[7] C = Op1.Nop; /* padding */
	C[0] = Op1.MovRm4R4;
	C[1] = to_!ubyte(0b10000000 + Src*8 + DstPtr);
	if (DstPtr == R4º.Sp) {
		C[2] = to_!ubyte(R4º.Sp*8 + R4º.Sp); /* SIB byte */
		C[3 .. 7] = bytes(Displ);
	} else {
		C[2 .. 6] = bytes(Displ);
	};
	return C;
};
unittest {
	assert(op_mov_m4r4(R4º.Ax, 0, R4º.Ax) == x"8980 00000000 90");
	assert(op_mov_m4r4(R4º.Sp, 0xdeadbeef, R4º.Ax) == x"898424 efbeadde");
	assert(op_mov_m4r4(R4º.Sp, 0x100001, R4º.Di) == x"89bc24 01001000");
};

auto op_insr_r16r4(R16º Dst, R4º Src, ubyte Idx) in {
	assert(Idx < 4);
} body {
	/* PINSRD XMM*, E*X, Idx */
	ubyte[6] C;
	C[0 .. 4] = bytes(Op4.PinsrD);
	C[4] = to_!ubyte(0b11000000 + Dst*8 + Src);
	C[5] = Idx;
	return C;
};
unittest {
	assert(op_insr_r16r4(R16º.X0, R4º.Ax, 0) == x"660f3a22 c0 00");
	assert(op_insr_r16r4(R16º.X0, R4º.Ax, 3) == x"660f3a22 c0 03");
	assert(op_insr_r16r4(R16º.X1, R4º.Ax, 3) == x"660f3a22 c8 03");
	assert(op_insr_r16r4(R16º.X1, R4º.Cx, 3) == x"660f3a22 c9 03");
	assert(op_insr_r16r4(R16º.X7, R4º.Di, 2) == x"660f3a22 ff 02");
};

/* --- miscellaneous --- */

private auto bytes(Tº)(Tº X) {
	return *(cast(ubyte[Tº.sizeof]*) &X);
};

/* -------------------------------------------------------------------------- */

/+bool sse41_enabled() @safe nothrow pure {
	asm @safe nothrow pure {
		naked;

		mov EAX, 1;
		cpuid;
		shr ECX, 19;
		and ECX, 1;
		mov EAX, ECX;
		ret;
	};
};+/

/+
















































+/

/* -------------------------------------------------------------------------- */