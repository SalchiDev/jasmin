
Require Import
  extension_validation
  compiler_util
  riscv_decl
  riscv_instr_decl
  riscv_extra
  expr.

Section RISCV_EXTENSION_VALIDATION.
Context
  {atoI : arch_toIdent}
  (arch_exts : arch_extensions).

Definition use_B : bool :=
  match arch_exts with
  | AE_RISCV opts => opts.(rv_use_b)
  | AE_NONE => false
  end.

Definition use_C : bool :=
  match arch_exts with
  | AE_RISCV opts => opts.(rv_use_c)
  | AE_NONE => false
  end.

Definition use_M : bool :=
  match arch_exts with
  | AE_RISCV opts => opts.(rv_use_m)
  | AE_NONE => false
  end.

Definition is_B_instruction (op : riscv_op) : bool :=
  match op with
  (* Zba *)
  | SH1ADD | SH2ADD | SH3ADD
  (* Zbb *)
  | ANDN | ORN | XNOR
  | CLZ | CTZ | CPOP
  | MAX | MAXU | MIN | MINU
  | SEXT_B | SEXT_H | ZEXT_H
  | ROL | ROR | RORI
  | ORC_B | REV8
  (* Zbs *)
  | BCLR | BCLRI | BEXT | BEXTI
  | BINV | BINVI | BSET | BSETI => true
  | _ => false
  end.

Definition is_C_instruction (op : riscv_op) : bool :=
  match op with
  | C_ADD
  | C_LW | C_SW | C_LWSP | C_SWSP
  | C_LI | C_LUI | C_ADDI
  | C_ADDI4SPN | C_ADDI16SP
  | C_SLLI | C_SRLI | C_SRAI
  | C_ANDI | C_MV | C_AND
  | C_OR | C_XOR | C_SUB | C_NOP => true
  | _ => false
  end.

Definition is_M_instruction (op : riscv_op) : bool :=
  match op with
  | MUL | MULH | MULHSU | MULHU
  | DIV | DIVU | REM | REMU => true
  | _ => false
  end.

Definition check_riscv_extension (ii : instr_info) (op : asm_op_t) : cexec unit :=
  match op with
  | BaseOp (None, rop) =>
      let desc := riscv_instr_desc rop in
      let name := (desc.(id_pp_asm) [::]).(pp_aop_name) in

      if is_M_instruction rop then
        if use_M then ok tt
        else Error (extension_validation_error ii
          ("RISC-V instruction '" ++ name ++ "' requires extension M"))

      else if is_B_instruction rop then
        if use_B then ok tt
        else Error (extension_validation_error ii
          ("RISC-V instruction '" ++ name ++ "' requires extension B"))

      else if is_C_instruction rop then
        if use_C then ok tt
        else Error (extension_validation_error ii
          ("RISC-V instruction '" ++ name ++ "' requires extension C"))

      else ok tt

  | _ => ok tt
  end.

End RISCV_EXTENSION_VALIDATION.