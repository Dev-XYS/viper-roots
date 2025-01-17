theory end_to_end_proof_foo
 imports relational_proof_foo "../global_data_end_to_end"
begin
declare Nat.One_nat_def[simp del]

declare econtext_bpl_general.defs(1)[simp]

abbreviation type_interp_bpl where 
  "type_interp_bpl A \<equiv> (vbpl_absval_ty (ty_repr_basic A))"


definition ctxt_bpl where 
  "ctxt_bpl  = (econtext_bpl_general.make (type_interp_bpl (absval_interp_total global_data_end_to_end.ctxt_vpr)) relational_proof_foo.var_ctxt_bpl global_data_end_to_end.has_direct_perm_fun_interp_single_wf [])"


lemma var_context_bpl_eq : 

shows "((var_context ctxt_bpl)=relational_proof_foo.var_ctxt_bpl)"
by (simp add: ctxt_bpl_def)


lemma ctxt_wf : 

shows "(ctxt_wf global_data_vpr.vpr_prog (ty_repr_basic (absval_interp_total global_data_end_to_end.ctxt_vpr)) (map_of global_data_vpr.field_rel_list) fun_repr_concrete ctxt_bpl)"
apply ((unfold ctxt_wf_def))
by (simp add: ctxt_bpl_def global_data_end_to_end.fun_interp_vpr_bpl_inst_wf)


lemmas bound_lemmas = list_all_ran_map_of[OF relational_proof_foo.var_relation_list_1_bound] list_all_ran_map_of[OF field_rel_bound] const_repr_basic_bound_2


lemmas inter_bound_lemmas = inter_disjoint_intervals[OF bound_lemmas(1,2)] inter_disjoint_intervals[OF bound_lemmas(1,3)] inter_disjoint_intervals[OF bound_lemmas(2,3)]


lemma disjoint_property_aux : 

shows "(disj_vars_state_relation relational_proof_foo.tr_vpr_bpl_0 Map.empty)"
apply ((rule disj_vars_state_relation_initialI))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((rule disj_helper_tr_vpr_bpl))
by ((force simp: relational_proof_foo.tr_vpr_bpl_0_def relational_proof_foo.var_relation_list_1_def relational_proof_foo.basic_disjointness_lemmas inter_bound_lemmas))+


lemma method_partial_proof : 
assumes "(proc_is_correct (type_interp_bpl (absval_interp_total global_data_end_to_end.ctxt_vpr)) global_data.fdecls global_data.constants_vdecls global_data.unique_consts global_data.globals_vdecls global_data.axioms foo_before_ast_to_cfg_prog.ast_proc (Ast.proc_body_satisfies_spec::(((('a) vbpl_absval), ast) proc_body_satisfies_spec_ty)))"
shows "(vpr_method_correct_total_partial (global_data_end_to_end.ctxt_vpr::(('a) total_context)) consistent_internal_total_full method_decls.foo_decl)"
apply ((rule end_to_end_vpr_method_correct_partial[where ?ctxt = ctxt_bpl, OF assms consistency_internal_mono_prop_downward_ord wf_ty_repr_basic consistency_internal_wf]))
apply ((simp add: ty_repr_basic_def))
apply ((simp only: global_data_end_to_end.program_total_eq))
apply ((rule method_decls.foo_lookup_lemma[simplified HOL.sym[OF global_data_vpr.methods_vpr_prog]]))
apply ((rule foo_decl_proj_mbody))
apply ((simp add: foo_decl_proj_mpre foo_decl_proj_mpost))
apply ((fastforce simp: foo_decl_proj_mpre foo_decl_proj_margs))
apply ((fastforce simp: shift_down_set_def foo_decl_proj_margs))
apply ((simp add: foo_decl_proj_margs foo_decl_proj_mrets))
apply ((simp add: global_data_end_to_end.fun_interp_wf ctxt_bpl_def))
apply ((simp add: ctxt_bpl_def))
apply ((simp add: ctxt_bpl_def))
apply ((simp add: foo_before_ast_to_cfg_prog.ast_proc_def ctxt_bpl_def))
apply ((simp add: foo_before_ast_to_cfg_prog.ast_proc_def foo_before_ast_to_cfg_prog.pres_def))
apply ((simp add: foo_before_ast_to_cfg_prog.ast_proc_def))
apply ((simp add: foo_before_ast_to_cfg_prog.ast_proc_def))
apply ((simp only: global_data_end_to_end.program_total_eq foo_decl_proj_margs foo_decl_proj_mrets))
apply ((rule relational_proof_foo.method_proof.method_rel_proof[simplified relational_proof_foo.var_ctxt_viper_def[simplified ]]))
apply ((simp only: relational_proof_foo.method_proof_def))
apply ((intro conjI))
apply ((simp add: ctxt_bpl_def))
apply ((simp add: ctxt_bpl_def))
apply ((rule ctxt_wf))
apply ((simp add: global_data_end_to_end.fun_interp_wf ctxt_bpl_def))
apply ((simp add: global_data_end_to_end.program_total_eq))
apply ((simp add: ctxt_bpl_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def default_state_rel_options_def))
apply (((rule exI))+)
apply ((intro conjI))
prefer 2
apply ((rule init_state_in_state_relation[OF wf_ty_repr_basic disjoint_property_aux]))
apply (simp)
apply (simp)
apply ((fastforce intro: is_empty_total_wf_mask))
apply (simp)
apply (rule empty_state_consistent_internal, simp)
apply ((simp add: ctxt_bpl_def))
apply ((simp add: ty_repr_basic_def))
apply (simp)
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((rule strictly_ordered_list_inj))
apply ((simp add: relational_proof_foo.var_relation_list_1_def))
apply ((simp add: ctxt_bpl_def foo_before_ast_to_cfg_prog.consts_wf foo_before_ast_to_cfg_prog.globals_wf closed_wf_ty_fun_eq))
apply ((simp add: ctxt_bpl_def foo_before_ast_to_cfg_prog.params_wf foo_before_ast_to_cfg_prog.locals_wf closed_wf_ty_fun_eq))
apply ((cut_tac foo_before_ast_to_cfg_prog.globals_locals_disj))
apply ((simp add: ctxt_bpl_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((rule strictly_ordered_list_inj))
apply ((simp add: global_data_vpr.field_rel_list_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def inj_const_repr_basic))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def var_context_bpl_eq global_data_end_to_end.field_prop_aux_with_globals))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def ctxt_bpl_def ty_repr_basic_def map_of_lookup_vdecls_ty[OF global_data.mvar5]))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def ctxt_bpl_def ty_repr_basic_def map_of_lookup_vdecls_ty[OF global_data.mvar6]))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def ctxt_bpl_def global_data_end_to_end.lookup_constants_with_globals))
apply ((rule var_rel_prop_aux[where ?var_rel_list="relational_proof_foo.var_relation_list_1"]))
apply (simp)
apply ((simp add: ty_repr_basic_def))
apply ((simp add: relational_proof_foo.var_relation_list_1_def foo_decl_proj_margs foo_decl_proj_mrets))
apply ((simp add: var_rel_prop_def ctxt_bpl_def))
apply ((simp add: ty_repr_basic_def map_of_lookup_vdecls_ty[OF foo_before_ast_to_cfg_prog.mvar7]))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply (blast)
apply ((rule unique_constants_initial_global_state))
apply ((disjoint_globals_aux_tac disj_prop_aux: disjoint_property_aux[simplified disj_vars_state_relation_def]))
apply ((simp add: global_data.unique_consts_def))
apply ((rule unique_consts_field_prop))
apply ((simp add: global_data.unique_consts_def global_data_end_to_end.field_rel_ran relational_proof_foo.tr_vpr_bpl_0_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((rule global_data_end_to_end.fields_dom_eq))
apply ((rule boogie_axioms_state_restriction_aux))
apply ((simp add: ctxt_bpl_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def global_data_end_to_end.lookup_constants))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def var_context_bpl_eq global_data_end_to_end.field_prop_aux_no_globals))
apply ((disjoint_globals_aux_tac disj_prop_aux: disjoint_property_aux[simplified disj_vars_state_relation_def]))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def inj_const_repr_basic))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def global_data_end_to_end.inj_field_rel))
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def global_data.constants_vdecls_def))
apply ((simp only: range_const_repr_basic global_data_end_to_end.field_rel_ran))
apply ((fastforce))
apply ((cut_tac global_data_end_to_end.axiom_sat))
apply ((simp add: ctxt_bpl_def))
apply (simp)
apply ((simp add: relational_proof_foo.tr_vpr_bpl_0_def global_data_end_to_end.program_total_eq))
done


end