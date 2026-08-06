theory PredicateDefinednessRel
  imports ViperBoogieEndToEnd
begin

text \<open>Analogue of @{thm [source] end_to_end_vpr_method_correct_partial} for a predicate's
  \<open>#definedness\<close> check procedure: a Boogie procedure whose body is just \<^term>\<open>Inhale A\<close> for some
  assertion \<open>A\<close>, with no precondition, no postcondition and no return variables. Concludes that
  the corresponding Viper inhale never fails, given that the Boogie procedure was verified
  correct.\<close>

lemma predicate_definedness_check_correct:
  assumes Boogie_correct: "proc_is_correct (vbpl_absval_ty (TyRep :: 'a ty_repr_bpl)) fun_decls constants unique_consts global_vars axioms (proc_bpl :: ast procedure)
                  (Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty))"
      and WfTyRep: "wf_ty_repr_bpl TyRep"
      and FunInterp: "fun_interp_wf (vbpl_absval_ty TyRep) fun_decls (fun_interp ctxt)"
      and TypeInterpEq: "type_interp ctxt = vbpl_absval_ty TyRep"
      and RtypeInterpEmpty: "rtype_interp ctxt = []"
      and VarCtxtEq: "var_context ctxt = (constants @ global_vars, proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      and ProcPresEmpty: "proc_pres proc_bpl = []"
      and ProcTyArgsEmpty: "proc_ty_args proc_bpl = 0"
      and ProcBodySome: "proc_body proc_bpl = Some (locals_bpl, proc_body_bpl)"
      and StmtRelInst: "stmt_rel R0 R1 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (Inhale A) (convert_ast_to_program_point proc_body_bpl) \<gamma>1"
      and NsEq: "ns = \<lparr> old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty \<rparr>"
      and StateRelInitial: "R0 \<omega> ns"
      and GlobalsWf: "state_typ_wf (vbpl_absval_ty TyRep) [] gs (constants @ global_vars)"
      and LocalsWf: "state_typ_wf (vbpl_absval_ty TyRep) [] ls (proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      and UniqueConstants: "unique_constants_distinct gs unique_consts"
      and AxiomsSat: "axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
      and RedInh: "red_inhale ctxt_vpr StateCons A \<omega> res"
    shows "res \<noteq> RFailure"
proof (rule ccontr)
  assume "\<not> res \<noteq> RFailure"
  hence "res = RFailure" by simp

  let ?abs = "vbpl_absval_ty TyRep"

  have ProcBodyBplCorrect:
      "(Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty)) ?abs [] (constants@global_vars, (proc_args proc_bpl)@(locals_bpl@(proc_rets proc_bpl))) (fun_interp ctxt) []
                                       (proc_all_pres proc_bpl) (proc_checked_posts proc_bpl) proc_body_bpl
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>"
  proof (rule proc_is_correct_elim[OF Boogie_correct ProcBodySome])
    show "\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_vbpl_val TyRep v = t)"
      by (simp add: closed_types_inhabited)
  next
    show "\<forall>v. closed (type_of_vbpl_val TyRep v)"
    proof (rule allI)
      fix v
      show "closed (type_of_vbpl_val TyRep v)"
      proof (cases v)
        case (LitV x1)
        then show ?thesis by simp
      next
        case (AbsV x2)
        then show ?thesis
          using vbpl_absval_ty_closed[OF WfTyRep]
          by fastforce
      qed
    qed
  next
    show "fun_interp_wf (vbpl_absval_ty TyRep) fun_decls (fun_interp ctxt)"
      by (rule FunInterp)
  next
    show "list_all closed [] \<and> length [] = proc_ty_args proc_bpl"
      by (simp add: ProcTyArgsEmpty)
  next
    show "state_typ_wf (vbpl_absval_ty TyRep) [] gs (constants @ global_vars)"
      by (rule GlobalsWf)
  next
    show "state_typ_wf (vbpl_absval_ty TyRep) [] ls (proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      by (rule LocalsWf)
  next
    show "unique_constants_distinct gs unique_consts"
      by (rule UniqueConstants)
  next
    show "axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
      by (rule AxiomsSat)
  qed

  from RedInh \<open>res = RFailure\<close> have "red_stmt_total ctxt_vpr StateCons \<Lambda> (Inhale A) \<omega> RFailure"
    by (auto intro: TotalSemantics.RedInhale)

  with stmt_rel_failure_elim[OF StmtRelInst StateRelInitial]
  obtain c' where
    FailureConfig: "snd c' = Failure" and
    RedBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'"
    by blast

  have "snd c' \<noteq> Failure"
    using red_ast_bpl_proc_body_sat_spec[OF RedBpl, where ?pres="(Ast.proc_all_pres proc_bpl)"]
          ProcPresEmpty ProcBodyBplCorrect
    unfolding expr_all_sat_def
    by (simp add: VarCtxtEq TypeInterpEq RtypeInterpEmpty NsEq)

  thus False
    using FailureConfig
    by simp
qed

end
