theory method_decls
 imports ViperCommon.ViperLang
begin
definition foo_body :: "((stmt) option)" where 
  "foo_body  = (Some (Seq (Inhale (Atomic (AccPredicate ''P'' [(ViperLang.Var 0)] (PureExp (ELit WritePerm))))) (Unfold ''P'' [(ViperLang.Var 0)] (PureExp (ELit WritePerm)))))"


abbreviation foo_args :: "(((nat\<times>vtyp)) list)" where 
  "foo_args  \<equiv> [(0,ViperLang.TRef)]"


abbreviation foo_returns :: "(((nat\<times>vtyp)) list)" where 
  "foo_returns  \<equiv> []"


definition foo_pre where 
  "foo_pre  = (Atomic (Pure (ELit (LBool True))))"


definition foo_post where 
  "foo_post  = (Atomic (Pure (ELit (LBool True))))"


definition foo_decl where 
  "foo_decl  = (method_decl.make [ViperLang.TRef] [] foo_pre foo_post foo_body)"


lemma foo_decl_proj_margs : 

shows "((method_decl.args foo_decl)=[ViperLang.TRef])"
by (simp add: foo_decl_def method_decl.defs(1))


lemma foo_decl_proj_mrets : 

shows "((method_decl.rets foo_decl)=[])"
by (simp add: foo_decl_def method_decl.defs(1))


lemma foo_decl_proj_mpre : 

shows "((method_decl.pre foo_decl)=(Atomic (Pure (ELit (LBool True)))))"
by (simp add: foo_decl_def method_decl.defs(1) foo_pre_def)


lemma foo_decl_proj_mpost : 

shows "((method_decl.post foo_decl)=(Atomic (Pure (ELit (LBool True)))))"
by (simp add: foo_decl_def method_decl.defs(1) foo_post_def)


lemma foo_decl_proj_mbody : 

shows "((method_decl.body foo_decl)=(Some (Seq (Inhale (Atomic (AccPredicate ''P'' [(ViperLang.Var 0)] (PureExp (ELit WritePerm))))) (Unfold ''P'' [(ViperLang.Var 0)] (PureExp (ELit WritePerm))))))"
by (simp add: foo_decl_def method_decl.defs(1) foo_body_def)


definition methodLookupFun where 
  "methodLookupFun  = (map_of [(''foo'',method_decls.foo_decl)])"


lemma foo_lookup_lemma : 

shows "((methodLookupFun ''foo'')=(Some method_decls.foo_decl))"
by (simp add: methodLookupFun_def)


end