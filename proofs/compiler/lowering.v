Require Import compiler_util expr.

Section LOWERING.

Definition fresh_vars : Type := string -> atype -> Ident.ident.

Record rv_lowering_options :=
  {
    rv_lo_use_b : bool;
    rv_lo_use_c : bool;
  }.

Variant lowering_options :=
| LO_NONE
| LO_RISCV : rv_lowering_options -> lowering_options.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (lower_i0 :
      (instr_info -> warning_msg -> instr_info)
    -> lowering_options
    -> fresh_vars
    -> instr
    -> cmd)
  (warning : instr_info -> warning_msg -> instr_info)
  (lo_options : lowering_options)
  (fv : fresh_vars)
  {pT : progT}
  (all_fresh_vars : seq Ident.ident)
  (fvars : Sv.t).

Definition disj_fvars (x : Sv.t) : bool := disjoint x fvars.

Definition fvars_correct (fds : fun_decls) : bool :=
  disj_fvars (vars_p fds) && uniq all_fresh_vars.

Definition is_lval_in_memory (x : lval) : bool :=
  match x with
  | Lnone _ _ => false
  | Lvar v => is_var_in_memory v
  | Laset _ _ _ v _ => is_var_in_memory v
  | Lasub _ _ _ v _ => is_var_in_memory v
  | Lmem _ _ _ _ => true
  end.

Notation lower_i :=
  (lower_i0 warning lo_options fv).

Definition lower_cmd  (c : cmd) : cmd :=
  List.flat_map lower_i c.

Definition lower_fd (fd : fundef) : fundef :=
  with_body fd (lower_cmd (f_body fd)).

Definition lower_prog (p : prog) :=
  map_prog lower_fd p.

End LOWERING.
