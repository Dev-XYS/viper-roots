theory relational_proof_foo
 imports TotalViper.ViperBoogieTranslationInterface TotalViper.ExprWfRelML TotalViper.CPGHelperML TotalViper.StmtRelML TotalViper.ViperBoogieEndToEndML TotalViper.TotalConsistencyInst Boogie_Lang.TypingML "../global_data_vpr" "../boogie_proofs/foo_proofs/foo_before_ast_to_cfg_prog"
begin
definition var_ctxt_viper :: "(nat => ((vtyp) option))" where 
  "var_ctxt_viper  = (nth_option (append [ViperLang.TRef] []))"


definition var_relation_list_1 :: "(((nat\<times>nat)) list)" where 
  "var_relation_list_1  = [(0,7)]"


lemma var_relation_list_1_bound : 

shows "(list_all (\<lambda> x.((7\<le>(snd x))\<and>((snd x)\<le>7))) var_relation_list_1)"
by (simp add: var_relation_list_1_def)


definition tr_vpr_bpl_0 :: "tr_vpr_bpl" where 
  "tr_vpr_bpl_0  = (tr_vpr_bpl.make 5 6 5 6 (map_of global_data_vpr.field_rel_list) f_None (map_of var_relation_list_1) const_repr_basic default_state_rel_options)"


declare tr_vpr_bpl.defs(1)[simp]

declare program.defs(1)[simp]

abbreviation var_ctxt_bpl where 
  "var_ctxt_bpl  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append foo_before_ast_to_cfg_prog.params_vdecls foo_before_ast_to_cfg_prog.locals_vdecls))"


abbreviation state_rel_initial where 
  "state_rel_initial A Pr ctxt w ns \<equiv> (state_rel_def_same Pr consistent_internal_total_full (ty_repr_basic A) tr_vpr_bpl_0 Map.empty ctxt w ns)"


abbreviation type_interp_bpl where 
  "type_interp_bpl A \<equiv> (vbpl_absval_ty (ty_repr_basic A))"


lemmas basic_disjointness_lemmas = not_satisfies_prop_in_set[OF list_all_ran_map_of[OF var_relation_list_1_bound]] not_satisfies_prop_in_set[OF list_all_ran_map_of[OF field_rel_bound]] not_satisfies_prop_in_set[OF const_repr_basic_bound_2]


locale method_proof =
fixes ectxt :: "(('a) econtext_bpl)" and ctxt_vpr :: "(('a) total_context)"assumes VarContextBpl [simp]: "((var_context ectxt)=var_ctxt_bpl)" and 
TyInterpBpl [simp]: "((type_interp ectxt)=(type_interp_bpl (absval_interp_total ctxt_vpr)))" and 
CtxtWf: "(ctxt_wf global_data_vpr.vpr_prog (ty_repr_basic (absval_interp_total ctxt_vpr)) (map_of global_data_vpr.field_rel_list) fun_repr_concrete ectxt)" and 
WfFunBpl: "(fun_interp_wf (type_interp ectxt) global_data.fdecls (fun_interp ectxt))" and 
VprProgramTotal [simp]: "((program_total ctxt_vpr)=global_data_vpr.vpr_prog)" and 
RtypeInterpEmpty[simp]: "((rtype_interp ectxt)=[])" and 
CtxtVprPredWf: "(ctxt_pred_syn_wf ctxt_vpr)" and 
CtxtVprPredSelfFraming: "(ctxt_pred_self_framing_sat ctxt_vpr consistent_internal_total)"
begin
lemma var_ctxt_bpl_wf : 

shows "(\<forall> x t.(((lookup_var_ty (var_context ectxt) x)=(Some t))\<longrightarrow>(wf_ty 0 t)))"
using foo_before_ast_to_cfg_prog.var_context_wf by simp


ML\<open>
val lookup_var_rel_tac =  fn ctxt =>((simp_tac_with_thms @{thms tr_vpr_bpl_0_def var_relation_list_1_def shift_and_add_def} ctxt) THEN_ALL_NEW (fastforce_tac ctxt []))
val simp_with_tr_def_tac = (assm_full_simp_solved_with_thms_tac @{thms tr_vpr_bpl_0_def})
val simp_with_ty_repr_def_tac = (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def})
val type_safety_thm_map = (gen_type_safety_thm_map @{thm WfFunBpl} @{thm global_data.funcs_wf} @{thm var_ctxt_bpl_wf} @{thm state_rel_state_well_typed})
val lookup_var_bpl_thms = @{thms foo_before_ast_to_cfg_prog.lvar5(2) foo_before_ast_to_cfg_prog.lvar6(2) foo_before_ast_to_cfg_prog.lvar7(2) foo_before_ast_to_cfg_prog.lvar8(2) foo_before_ast_to_cfg_prog.lvar4(2) foo_before_ast_to_cfg_prog.lvar0(2) foo_before_ast_to_cfg_prog.lvar1(2) foo_before_ast_to_cfg_prog.lvar2(2) foo_before_ast_to_cfg_prog.lvar3(2)}
val lookup_fun_bpl_thms = @{thms mfunreadHeap mfunreadMask}
fun heap_read_wf_tac ctxt = (((simp_tac_with_thms @{thms tr_vpr_bpl_0_def}) ctxt) THEN' (resolve_tac ctxt @{thms heap_wf_concrete[OF CtxtWf wf_ty_repr_basic]}))
fun heap_read_match_tac ctxt = (assm_full_simp_solved_with_thms_tac @{thms tr_vpr_bpl_0_def ty_repr_basic_def read_heap_concrete_def} ctxt)
fun field_rel_tac ctxt = (assm_full_simp_solved_with_thms_tac @{thms tr_vpr_bpl_0_def field_rel_map_of_lemmas} ctxt)
fun field_lookup_tac ctxt = (assm_full_simp_solved_with_thms_tac @{thms global_data_vpr.vpr_prog_def global_data_vpr.field_list_def} ctxt)
val field_rel_single_tac = (field_rel_single_inst_tac field_rel_tac field_lookup_tac)
val exp_rel_info = {type_safety_thm_map = type_safety_thm_map, lookup_var_rel_tac = lookup_var_rel_tac, vpr_lit_bpl_exp_rel_tac = simp_with_tr_def_tac, lookup_var_thms = lookup_var_bpl_thms, lookup_fun_bpl_thms = lookup_fun_bpl_thms, simplify_rtype_interp_tac = fn ctxt => (TRY_TAC' ((simp_only_tac @{thms RtypeInterpEmpty} ctxt))), field_access_rel_pre_tac = (field_access_rel_pre_tac_aux heap_read_wf_tac heap_read_match_tac field_rel_single_tac)}
fun field_acc_init_tac ctxt = (resolve_tac ctxt @{thms syn_field_access_valid_wf_rel[OF CtxtWf wf_ty_repr_basic]})
val field_access_wf_rel_tac_aux_inst = (field_access_wf_rel_tac_aux field_acc_init_tac simp_with_tr_def_tac field_rel_single_tac simp_with_ty_repr_def_tac exp_rel_info)
val exp_wf_rel_info = {field_access_wf_rel_syn_tac = field_access_wf_rel_tac_aux_inst}
val aux_var_disj_tac = (assm_full_simp_solved_with_thms_tac @{thms tr_vpr_bpl_0_def basic_disjointness_lemmas map_upd_set_dom aux_pred_capture_state_dom ran_shift_and_add})
val basic_stmt_rel_info = {ctxt_wf_thm = @{thm CtxtWf}, consistency_wf_thm = @{thm wf_total_consistency_internal[OF CtxtVprPredWf CtxtVprPredSelfFraming]}, consistency_down_mono_thm = @{thm true_mono_prop_downward_ord}, tr_def_thm = @{thm tr_vpr_bpl_0_def}, method_data_table = method_decl_data, vpr_program_ctxt_eq_thm = @{thm VprProgramTotal}, var_rel_tac = lookup_var_rel_tac, var_context_vpr_tac = assm_full_simp_solved_with_thms_tac @{thms var_ctxt_viper_def shift_and_add_def}, field_rel_single_tac = field_rel_single_tac, aux_var_disj_tac = aux_var_disj_tac, type_interp_econtext = @{thm TyInterpBpl}, vpr_prog_def_thm = @{thm vpr_prog_def}}
val inhale_rel_info = {basic_info = basic_stmt_rel_info, atomic_inhale_rel_tac = atomic_inhale_rel_inst_tac, is_inh_rel_inv_thm = @{thm true_is_inh_rel_invariant}, no_def_checks_tac_opt = NONE}
val inhale_rel_info_opt = {basic_info = basic_stmt_rel_info, atomic_inhale_rel_tac = atomic_inhale_rel_inst_tac, is_inh_rel_inv_thm = @{thm assertion_framing_is_inh_rel_invariant}, no_def_checks_tac_opt = (SOME inh_no_def_checks_tac)}
val exhale_rel_info = {basic_info = basic_stmt_rel_info, atomic_exhale_rel_tac = atomic_exhale_rel_inst_tac, is_exh_rel_inv_thm = @{thm true_is_assertion_red_invariant_exh}, no_def_checks_tac_opt = NONE}
val exhale_rel_info_opt = {basic_info = basic_stmt_rel_info, atomic_exhale_rel_tac = atomic_exhale_rel_inst_tac, is_exh_rel_inv_thm = @{thm framing_exh_is_assertion_red_invariant_exh[OF true_mono_prop_downward]}, no_def_checks_tac_opt = (SOME exh_no_def_checks_tac)}
val stmt_rel_info = {basic_stmt_rel_info = basic_stmt_rel_info, atomic_rel_tac = atomic_rel_inst_tac, inhale_rel_info = inhale_rel_info, exhale_rel_info = exhale_rel_info}
val stmt_rel_info_opt = {basic_stmt_rel_info = basic_stmt_rel_info, atomic_rel_tac = atomic_rel_inst_tac, inhale_rel_info = inhale_rel_info_opt, exhale_rel_info = exhale_rel_info_opt}
val stmt_body_hints = (SeqnHint [(AtomicHint (InhaleHint {inhale_stmt_rel_thm = @{thm inhale_stmt_rel_no_inv}, inhale_rel_hint = (GoodStateAfter (GoodStateAfter (AtomicInhHint (PredicateAccInhHint (exp_wf_rel_info, exp_rel_info, @{thm foo_before_ast_to_cfg_prog.lvar8(2)}, @{thm state_rel_aux_pred_sat_lookup_3[where ?aux_var="8"]})))))})), (AtomicHint (UnfoldHint ((PredAccExhHint (exp_wf_rel_info, exp_rel_info, @{thm foo_before_ast_to_cfg_prog.lvar8(2)}, @{thm state_rel_aux_pred_sat_lookup_3[where ?aux_var="8"]}, @{thm HOL.TrueI})), {inhale_stmt_rel_thm = @{thm inhale_stmt_rel_inst_framing_inv}, inhale_rel_hint = (GoodStateAfter (GoodStateAfter (AtomicInhHint (FieldAccInhHint (exp_wf_rel_info, exp_rel_info, @{thm foo_before_ast_to_cfg_prog.lvar8(2)}, @{thm state_rel_aux_pred_sat_lookup_3[where ?aux_var="8"]})))))})))])
\<close>

lemma method_rel_proof : 

shows "(method_rel (state_rel_empty (state_rel_initial (absval_interp_total ctxt_vpr) global_data_vpr.vpr_prog ectxt)) (state_rel_initial (absval_interp_total ctxt_vpr) global_data_vpr.vpr_prog ectxt) ctxt_vpr consistent_internal_total_full var_ctxt_viper P ectxt method_decls.foo_decl (convert_ast_to_program_point foo_before_ast_to_cfg_prog.proc_body))"
apply ((unfold method_rel_def))
apply ((rule exI))
apply ((intro conjI))
apply ((unfold state_rel_empty_def foo_before_ast_to_cfg_prog.proc_body_def))
apply ((simp only: convert_ast_to_program_point.simps convert_list_to_cont.simps))
apply ((rule stmt_rel_propagate))
apply ((rule red_ast_bpl_rel_transitive))
apply ((rule red_ast_bpl_rel_inst_state_rel_conjunct2))
apply ((rule HOL.refl))
apply ((rule HOL.refl))
apply (tactic \<open> (unfold_bigblock_in_goal @{context} 1) \<close>)
apply ((rule red_ast_bpl_rel_one_simple_cmd))
apply ((rule exI))
apply ((rule conjI))
apply ((rule assign_intro_alt))
apply ((simp add: foo_before_ast_to_cfg_prog.lvar6(2)))
apply ((rule Semantics.RedVar))
apply (tactic \<open> (zero_mask_lookup_tac @{context} @{thm tr_vpr_bpl_0_def} 1) \<close>)
apply ((simp add: ty_repr_basic_def))
apply ((simp only: boogie_const_val.simps))
apply ((rule state_rel_mask_update_3))
apply ((fastforce))
apply ((simp add: tr_vpr_bpl_0_def))
apply ((fastforce intro: zero_mask_rel_2))
apply (simp)
apply ((simp add: tr_vpr_bpl_0_def))
apply (simp)
apply (simp)
apply ((rule red_ast_bpl_rel_inst_state_rel_same))
apply ((rule red_ast_bpl_rel_one_simple_cmd))
apply ((rule exI))
apply ((rule conjI))
apply (tactic \<open> (red_assume_good_state_tac @{context} @{thm CtxtWf} @{thm tr_vpr_bpl_0_def} 1) \<close>)
apply (assumption)
apply ((unfold foo_decl_proj_mpre))
apply ((rule inhale_stmt_rel_no_inv))
apply (simp)
apply (simp)
apply ((rule inhale_rel_true))
apply ((rule post_framing_rel_framing_trivial))
apply ((simp add: foo_decl_proj_mpost))
apply ((rule impI)+)
apply ((rule exI)+)
apply ((intro conjI))
apply ((simp add: foo_decl_proj_mbody))
apply ((rule stmt_rel_propagate_2_same_rel))
apply (tactic \<open> (stmt_rel_tac @{context} stmt_rel_info stmt_body_hints 1) \<close>)
apply (tactic \<open> (progress_red_bpl_rel_tac @{context} 1) \<close>)
apply ((unfold foo_decl_proj_mpost))
apply ((rule exhale_true_stmt_rel))
  sorry


schematic_goal
  "vpr_all_method_spec_correct_total ctxt_vpr consistent_internal_total_full vpr_prog \<Longrightarrow>
   stmt_rel
     (state_rel_well_def_same ectxt vpr_prog consistent_internal_total_full
       (ty_repr_basic (absval_interp_total ctxt_vpr)) tr_vpr_bpl_0 (\<lambda>x. None))
     (state_rel_well_def_same ectxt vpr_prog consistent_internal_total_full
       (ty_repr_basic (absval_interp_total ctxt_vpr)) tr_vpr_bpl_0 (\<lambda>x. None))
     ctxt_vpr consistent_internal_total_full var_ctxt_viper P ectxt
     (Unfold ''P'' [pure_exp.Var 0] (PureExp (ELit WritePerm)))
     (BigBlock None [Assign 8 (expr.Var 3), cmd.Assert (Lit (Lang.lit.LBool True))]
       (Some (ParsedIf (Some (expr.Var 8 \<guillemotleft>Lang.binop.Neq\<guillemotright> expr.Var 2)) [bigblock_1] [bigblock_2])) None,
      KSeq bigblock_3 KStop)
     ?\<gamma>1.233"
  apply (rule unfold_stmt_rel)
               prefer 13
               apply (rule unfold_exhale_pred_rel)
                 apply (simp only: append_Cons append_Nil)
  apply (tactic \<open>exps_wf_rel_tac basic_stmt_rel_info exp_wf_rel_info exp_rel_info @{context} NONE 2 1\<close>)



end

end