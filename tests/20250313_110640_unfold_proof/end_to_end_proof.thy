theory end_to_end_proof
 imports "method_proof_foo/end_to_end_proof_foo"
begin
lemma all_methods_correct_list_all_aux : 
assumes "(proc_is_correct (type_interp_bpl (absval_interp_total global_data_end_to_end.ctxt_vpr)) global_data.fdecls global_data.constants_vdecls global_data.unique_consts global_data.globals_vdecls global_data.axioms foo_before_ast_to_cfg_prog.ast_proc (Ast.proc_body_satisfies_spec::(((('a) vbpl_absval), ast) proc_body_satisfies_spec_ty)))"
shows "(list_all (comp (vpr_method_correct_total_partial (global_data_end_to_end.ctxt_vpr::(('a) total_context)) consistent_internal_total_full) snd) [(''foo'',method_decls.foo_decl)])"
apply (simp)
apply (((intro conjI))?)
apply ((rule end_to_end_proof_foo.method_partial_proof[OF assms(1)]))
done


lemma all_methods_correct_aux : 
assumes "(((program.methods global_data_vpr.vpr_prog) m)=(Some mdecl))" and 
"(proc_is_correct (type_interp_bpl (absval_interp_total global_data_end_to_end.ctxt_vpr)) global_data.fdecls global_data.constants_vdecls global_data.unique_consts global_data.globals_vdecls global_data.axioms foo_before_ast_to_cfg_prog.ast_proc (Ast.proc_body_satisfies_spec::(((('a) vbpl_absval), ast) proc_body_satisfies_spec_ty)))"
shows "(vpr_method_correct_total_partial (global_data_end_to_end.ctxt_vpr::(('a) total_context)) consistent_internal_total_full mdecl)"
by (rule map_of_list_all[OF assms(1)[simplified global_data_vpr.methods_vpr_prog methodLookupFun_def] all_methods_correct_list_all_aux,OF assms(2-)])


lemma all_methods_correct : 
assumes "(((program.methods (program_total (global_data_end_to_end.ctxt_vpr::(('a) total_context)))) m)=(Some mdecl))" and 
"(proc_is_correct (type_interp_bpl (absval_interp_total global_data_end_to_end.ctxt_vpr)) global_data.fdecls global_data.constants_vdecls global_data.unique_consts global_data.globals_vdecls global_data.axioms foo_before_ast_to_cfg_prog.ast_proc (Ast.proc_body_satisfies_spec::(((('a) vbpl_absval), ast) proc_body_satisfies_spec_ty)))"
shows "(vpr_method_correct_total (global_data_end_to_end.ctxt_vpr::(('a) total_context)) consistent_internal_total_full mdecl)"
apply ((rule vpr_method_correct_total_from_partial[OF assms(1)]))
apply ((rule all_methods_correct_aux[OF _ assms(2-)]))
apply ((simp only: global_data_end_to_end.program_total_eq))
done


end