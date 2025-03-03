theory global_data_vpr
 imports ViperCommon.ViperLang TotalViper.TotalViperUtil TotalViper.TotalViperHelperML TotalViper.ViperBoogieTranslationInterface method_decls
begin
definition field_list where 
  "field_list  = [(''f'',ViperLang.TInt)]"


definition field_rel_list :: "(((string\<times>nat)) list)" where 
  "field_rel_list  = [(''f'',4)]"


lemma field_rel_bound : 

shows "(list_all (\<lambda> x.((4\<le>(snd x))\<and>((snd x)\<le>4))) field_rel_list)"
by (simp add: field_rel_list_def)


definition vpr_prog :: "program" where 
  "vpr_prog  = (program.make methodLookupFun (map_of [(''P'',(predicate_decl.make [ViperLang.TRef] (Some (Atomic (Acc (ViperLang.Var 0) ''f'' (PureExp (ELit WritePerm)))))))]) f_None (map_of field_list) 0)"


lemma mfield_f : 

shows "(((map_of field_rel_list) ''f'')=(Some 4))"
by (simp add: field_rel_list_def)


lemma lfield_f : 
assumes FieldRel: "(field_rel vpr_prog VarC (map_of field_rel_list) ns)"
shows "((lookup_var VarC ns 4)=(Some (AbsV (AField (NormalField 4 ViperLang.TInt)))))"
apply ((rule lookup_field_rel[OF FieldRel mfield_f]))
by (simp add: vpr_prog_def field_list_def program.defs(1))


lemmas field_rel_map_of_lemmas = mfield_f


lemmas field_rel_lookup_lemmas = lfield_f


lemma methods_vpr_prog : 

shows "((program.methods vpr_prog)=methodLookupFun)"
by (simp add: vpr_prog_def ViperLang.program.defs(1))


ML\<open>
val foo_data = {method_arg_thm = @{thm foo_decl_proj_margs}, method_rets_thm = @{thm foo_decl_proj_mrets}, method_pre_thm = @{thm foo_decl_proj_mpre}, method_post_thm = @{thm foo_decl_proj_mpost}, method_lookup_thm = @{thm method_decls.foo_lookup_lemma[simplified HOL.sym[OF methods_vpr_prog]]}}
val method_decl_data : method_data Symtab.table = 
(Symtab.empty|>(Symtab.update ("foo", foo_data)))
\<close>

end