Require Import compiler_util expr arch_decl arch_params.

Definition extension_validation_error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some "extension_validation"%string;
    pel_internal := false;
  |}.
  
Section EXTENSION_VALIDATION.
Context `{asmop : asmOp}.

Variable evp : extension_validation_params.

Fixpoint check_extensions_instruction (arch_exts : arch_extensions) (i : instr) : cexec unit :=
  let '(MkI ii ir) := i in
  match ir with
  | Copn _ _ (Oasm aop) _ =>
      evp_check_extension evp arch_exts ii aop

  | Cif _ c1 c2 =>
      Let _ := allM (check_extensions_instruction arch_exts) c1 in
      allM (check_extensions_instruction arch_exts) c2

  | Cfor _ _ c =>
      allM (check_extensions_instruction arch_exts) c

  | Cwhile _ c0 _ _ c1 =>
      Let _ := allM (check_extensions_instruction arch_exts) c0 in
      allM (check_extensions_instruction arch_exts) c1

  | _ => ok tt
  end.

Definition check_extensions (arch_exts : arch_extensions) (pT : progT) (p : @prog _ _ pT) : cexec unit :=
  allM
    (fun '(_, fd) =>
      allM (check_extensions_instruction arch_exts) (f_body fd))
    (p_funcs p).

End EXTENSION_VALIDATION.