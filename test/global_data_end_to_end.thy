theory global_data_end_to_end
 imports global_data_vpr "boogie_proofs/global_data" TotalViper.ViperBoogieEndToEndML
begin
declare Nat.One_nat_def[simp del]

declare total_context.defs(1)[simp]

declare program.defs(1)[simp]

abbreviation type_interp_bpl where 
  "type_interp_bpl A \<equiv> (vbpl_absval_ty (ty_repr_basic A))"


definition ctxt_vpr where 
  "ctxt_vpr  = (total_context.make global_data_vpr.vpr_prog (\<lambda> _.None) (\<lambda> _.undefined))"


lemma program_total_eq : 

shows "((program_total ctxt_vpr)=global_data_vpr.vpr_prog)"
by (simp add: ctxt_vpr_def)


definition has_direct_perm_fun_interp_single_wf where 
  "has_direct_perm_fun_interp_single_wf f = (fun_interp_vpr_bpl_concrete global_data_vpr.vpr_prog (ty_repr_basic (absval_interp_total ctxt_vpr)) (map_of global_data_vpr.field_rel_list) fun_repr_concrete f)"


lemma fun_interp_vpr_bpl_inst_wf : 

shows "(fun_interp_vpr_bpl_wf global_data_vpr.vpr_prog (ty_repr_basic (absval_interp_total ctxt_vpr)) (map_of global_data_vpr.field_rel_list) fun_repr_concrete has_direct_perm_fun_interp_single_wf)"
apply ((unfold has_direct_perm_fun_interp_single_wf_def))
apply ((rule fun_interp_vpr_bpl_concrete_wf))
by (rule fun_repr_concrete_inj)


lemma fun_interp_wf : 

shows "(fun_interp_wf (type_interp_bpl (absval_interp_total ctxt_vpr)) global_data.fdecls has_direct_perm_fun_interp_single_wf)"
apply ((simp only: fun_interp_wf_def))
apply ((rule list_all_map_of))
apply ((simp only: global_data.fdecls_def List.list_all_simps(1)))
apply ((simp del: fun_interp_single_wf.simps fun_interp_single_wf_2.simps))
apply ((simp only: has_direct_perm_fun_interp_single_wf_def))
apply ((intro conjI))
apply (fun_interp_wf_aux_tac FGoodState fun_wf_thm: good_state_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FIdenticalOnKnownLocs fun_wf_thm: identical_on_known_locs_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FReadHeap fun_wf_thm: select_heap_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FUpdateHeap fun_wf_thm: store_heap_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FIsPredicateField fun_wf_thm: is_predicate_field_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FIsWandField fun_wf_thm: is_wand_field_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FReadMask fun_wf_thm: select_mask_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FUpdateMask fun_wf_thm: store_mask_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FGoodMask fun_wf_thm: good_mask_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FHasPerm fun_wf_thm: has_direct_perm_fun_interp_single_wf)
apply (fun_interp_wf_aux_tac FPredicateLoc_P fun_wf_thm: predicate_loc_P_fun_interp_single_wf)
done


lemma lookup_constants : 

shows "((lookup_vdecls_ty global_data.constants_vdecls (const_repr_basic c))=(Some (boogie_const_ty (ty_repr_basic (absval_interp_total ctxt_vpr)) c)))"
apply (cases c)
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mconst2] ty_repr_basic_def))
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mconst3] ty_repr_basic_def))
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mconst0] ty_repr_basic_def))
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mconst1] ty_repr_basic_def))
done


lemma lookup_constants_with_globals : 

shows "((lookup_vdecls_ty (append global_data.constants_vdecls global_data.globals_vdecls) (const_repr_basic c))=(Some (boogie_const_ty (ty_repr_basic (absval_interp_total ctxt_vpr)) c)))"
apply (cases c)
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mvar2] ty_repr_basic_def))
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mvar3] ty_repr_basic_def))
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mvar0] ty_repr_basic_def))
apply ((simp add: map_of_lookup_vdecls_ty[OF global_data.mvar1] ty_repr_basic_def))
done


lemma field_rel_ran : 

shows "((ran (map_of global_data_vpr.field_rel_list))={4})"
by (simp add: global_data_vpr.field_rel_list_def)


lemma inj_field_rel : 

shows "(inj_on (map_of global_data_vpr.field_rel_list) (dom (map_of global_data_vpr.field_rel_list)))"
apply ((rule strictly_ordered_list_inj))
by (simp add: global_data_vpr.field_rel_list_def)


lemma field_prop_aux_no_globalslist_all2 : 

shows "(list_all2 (field_tr_prop (ty_repr_basic (absval_interp_total ctxt_vpr)) global_data.constants_vdecls) global_data_vpr.field_list global_data_vpr.field_rel_list)"
apply ((simp only: global_data_vpr.field_list_def global_data_vpr.field_rel_list_def))
by (simp add: field_tr_prop_def ty_repr_basic_def map_of_lookup_vdecls_ty[OF global_data.mconst4])


lemma field_prop_aux_no_globals : 

shows "(field_tr_prop_full (program_total ctxt_vpr) global_data.constants_vdecls (ty_repr_basic (absval_interp_total ctxt_vpr)) (map_of global_data_vpr.field_rel_list))"
apply ((simp only: field_tr_prop_full_def))
apply ((rule allI | rule impI)+)
apply ((simp add: global_data_vpr.vpr_prog_def program_total_eq))
by (erule list_all2_map_of[OF field_prop_aux_no_globalslist_all2 field_tr_prop_fst])


lemma field_prop_aux_with_globalslist_all2 : 

shows "(list_all2 (field_tr_prop (ty_repr_basic (absval_interp_total ctxt_vpr)) (append global_data.constants_vdecls global_data.globals_vdecls)) global_data_vpr.field_list global_data_vpr.field_rel_list)"
apply ((simp only: global_data_vpr.field_list_def global_data_vpr.field_rel_list_def))
by (simp add: field_tr_prop_def ty_repr_basic_def map_of_lookup_vdecls_ty[OF global_data.mvar4])


lemma field_prop_aux_with_globals : 

shows "(field_tr_prop_full (program_total ctxt_vpr) (append global_data.constants_vdecls global_data.globals_vdecls) (ty_repr_basic (absval_interp_total ctxt_vpr)) (map_of global_data_vpr.field_rel_list))"
apply ((simp only: field_tr_prop_full_def))
apply ((rule allI | rule impI)+)
apply ((simp add: global_data_vpr.vpr_prog_def program_total_eq))
by (erule list_all2_map_of[OF field_prop_aux_with_globalslist_all2 field_tr_prop_fst])


lemma fields_dom_eq : 

shows "((dom (program.declared_fields (program_total ctxt_vpr)))=(dom (map_of global_data_vpr.field_rel_list)))"
apply ((simp add: program_total_eq global_data_vpr.vpr_prog_def))
by (simp add: dom_map_of_2 global_data_vpr.field_list_def global_data_vpr.field_rel_list_def)


lemma axiom_sat : 
assumes "(boogie_const_rel const_repr_basic (global_data.constants_vdecls,[]) ns)" and 
"(field_rel global_data_vpr.vpr_prog (global_data.constants_vdecls,[]) (map_of global_data_vpr.field_rel_list) ns)"
shows "(axioms_sat (type_interp_bpl (absval_interp_total ctxt_vpr)) (global_data.constants_vdecls,[]) has_direct_perm_fun_interp_single_wf ns global_data.axioms)"
apply ((simp only: global_data.axioms_def axioms_sat_def))
apply (simp)
apply ((intro conjI))
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply ((simp add: select_heap_aux_def))
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply ((simp add: select_heap_aux_def))
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply ((simp add: select_heap_aux_def))
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply ((force simp: mask_rel_def))
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply ((simp add: non_pred_is_bounded_field_bpl))
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply ((simp add: mask_rel_def))
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
apply (axiom_proof_init)
apply ((rule expr_sat_rewrite))
apply (tactic \<open> (axiom_tac @{context} @{thm has_direct_perm_fun_interp_single_wf_def} @{thms lookup_boogie_const_concrete_lemmas[OF assms(1)]} @{thms field_rel_lookup_lemmas[OF assms(2)]} @{thms axioms_sat_proof_del} 1) \<close>)
apply (simp)
done


end