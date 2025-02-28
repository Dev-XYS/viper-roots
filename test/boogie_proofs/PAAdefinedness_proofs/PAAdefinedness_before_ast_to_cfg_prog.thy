theory PAAdefinedness_before_ast_to_cfg_prog
imports Boogie_Lang.Ast Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util "../global_data"
begin
definition bigblock_0
  where
    "bigblock_0  = (BigBlock (None ) [(Assign 6 (Var 1)),(Assume (FunExp ''state'' [] [(Var 5),(Var 6)])),(Assign 8 (Var 3)),(Assert (Lit (LBool True))),(Assume (BinOp (Lit (LBool True)) Imp (BinOp (Var 7) Neq (Var 0)))),(Assign 6 (FunExp ''updMask'' [((TCon ''NormalField'') []),(TPrim TInt)] [(Var 6),(Var 7),(Var 4),(BinOp (FunExp ''readMask'' [((TCon ''NormalField'') []),(TPrim TInt)] [(Var 6),(Var 7),(Var 4)]) Add (Var 8))])),(Assume (FunExp ''state'' [] [(Var 5),(Var 6)])),(Assume (FunExp ''state'' [] [(Var 5),(Var 6)]))] (None ) (None ))"
definition cont_0
  where
    "cont_0  = KStop"
definition proc_body
  where
    "proc_body  = [bigblock_0]"
definition pres
  where
    "pres  = []"
definition post
  where
    "post  = []"
definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = [(7,((TCon ''Ref'') []),(None ))]"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(8,(TPrim TReal),(None ))]"
lemma locals_min_aux:
shows "(((map fst (append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)))) \<ge> 7))"
unfolding PAAdefinedness_before_ast_to_cfg_prog.params_vdecls_def PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 7)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)))) = {})"
using max_min_disjoint_2[OF global_data.globals_max PAAdefinedness_before_ast_to_cfg_prog.locals_min]
by linarith

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) global_data.constants_vdecls) )"
unfolding global_data.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) global_data.globals_vdecls) )"
unfolding global_data.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) PAAdefinedness_before_ast_to_cfg_prog.params_vdecls) )"
unfolding PAAdefinedness_before_ast_to_cfg_prog.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls) )"
unfolding PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma mvar7:
shows "((map_of (append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls) 7) = (Some (((TCon ''Ref'') []),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma mvar8:
shows "((map_of (append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls) 8) = (Some ((TPrim TReal),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma lvar7:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 7) = (Some (((TCon ''Ref'') []),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 7) = (Some ((TCon ''Ref'') [])))"
using globals_locals_disj mvar7
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar8:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 8) = (Some ((TPrim TReal),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 8) = (Some (TPrim TReal)))"
using globals_locals_disj mvar8
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar5:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 5) = (Some (((TCon ''HeapType'') []),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 5) = (Some ((TCon ''HeapType'') [])))"
using globals_locals_disj global_data.mvar5
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar6:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 6) = (Some (((TCon ''MaskType'') []),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 6) = (Some ((TCon ''MaskType'') [])))"
using globals_locals_disj global_data.mvar6
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar0:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 0) = (Some (((TCon ''Ref'') []),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 0) = (Some ((TCon ''Ref'') [])))"
using globals_locals_disj global_data.mvar0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar1:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 1) = (Some (((TCon ''MaskType'') []),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 1) = (Some ((TCon ''MaskType'') [])))"
using globals_locals_disj global_data.mvar1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar2:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 2) = (Some ((TPrim TReal),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 2) = (Some (TPrim TReal)))"
using globals_locals_disj global_data.mvar2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar3:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 3) = (Some ((TPrim TReal),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 3) = (Some (TPrim TReal)))"
using globals_locals_disj global_data.mvar3
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma lvar4:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 4) = (Some (((TCon ''Field'') [((TCon ''NormalField'') []),(TPrim TInt)]),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append PAAdefinedness_before_ast_to_cfg_prog.params_vdecls PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls)) 4) = (Some ((TCon ''Field'') [((TCon ''NormalField'') []),(TPrim TInt)])))"
using globals_locals_disj global_data.mvar4
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition ast_proc :: "(ast procedure)"
  where
    "ast_proc  = (|proc_ty_args = 0,proc_args = PAAdefinedness_before_ast_to_cfg_prog.params_vdecls,proc_rets = [],proc_modifs = [5,6],proc_pres = PAAdefinedness_before_ast_to_cfg_prog.pres,proc_posts = PAAdefinedness_before_ast_to_cfg_prog.post,proc_body = (Some (PAAdefinedness_before_ast_to_cfg_prog.locals_vdecls,PAAdefinedness_before_ast_to_cfg_prog.proc_body))|)"

end
