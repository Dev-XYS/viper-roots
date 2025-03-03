theory global_data
imports Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util
begin
definition axioms
  where
    "axioms  = [(ForallT (ForallT (Forall ((TCon ''HeapType'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (Forall (TVar 0) (BinOp (FunExp ''readHeap'' [(TVar 1),(TVar 0)] [(FunExp ''updHeap'' [(TVar 1),(TVar 0)] [(BVar 3),(BVar 2),(BVar 1),(BVar 0)]),(BVar 2),(BVar 1)]) Eq (BVar 0)))))))),(ForallT (ForallT (ForallT (ForallT (Forall ((TCon ''HeapType'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 3),(TVar 2)]) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (Forall (TVar 2) (BinOp (BinOp (BinOp (BVar 4) Neq (BVar 3)) Or (BinOp (BVar 2) Neq (BVar 1))) Imp (BinOp (FunExp ''readHeap'' [(TVar 1),(TVar 0)] [(FunExp ''updHeap'' [(TVar 3),(TVar 2)] [(BVar 5),(BVar 4),(BVar 2),(BVar 0)]),(BVar 3),(BVar 1)]) Eq (FunExp ''readHeap'' [(TVar 1),(TVar 0)] [(BVar 5),(BVar 3),(BVar 1)]))))))))))))),(ForallT (ForallT (Forall ((TCon ''HeapType'') []) (Forall ((TCon ''HeapType'') []) (Forall ((TCon ''MaskType'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (BinOp (FunExp ''IdenticalOnKnownLocations'' [] [(BVar 4),(BVar 3),(BVar 2)]) Imp (BinOp (FunExp ''HasDirectPerm'' [(TVar 1),(TVar 0)] [(BVar 2),(BVar 1),(BVar 0)]) Imp (BinOp (FunExp ''readHeap'' [(TVar 1),(TVar 0)] [(BVar 4),(BVar 1),(BVar 0)]) Eq (FunExp ''readHeap'' [(TVar 1),(TVar 0)] [(BVar 3),(BVar 1),(BVar 0)]))))))))))),(ForallT (ForallT (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (BinOp (FunExp ''readMask'' [(TVar 1),(TVar 0)] [(Var 1),(BVar 1),(BVar 0)]) Eq (Var 2)))))),(BinOp (Var 2) Eq (Lit (LReal 0.0))),(BinOp (Var 3) Eq (Lit (LReal 1.0))),(ForallT (ForallT (Forall ((TCon ''MaskType'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (Forall (TPrim TReal) (BinOp (FunExp ''readMask'' [(TVar 1),(TVar 0)] [(FunExp ''updMask'' [(TVar 1),(TVar 0)] [(BVar 3),(BVar 2),(BVar 1),(BVar 0)]),(BVar 2),(BVar 1)]) Eq (BVar 0)))))))),(ForallT (ForallT (ForallT (ForallT (Forall ((TCon ''MaskType'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 3),(TVar 2)]) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (Forall (TPrim TReal) (BinOp (BinOp (BinOp (BVar 4) Neq (BVar 3)) Or (BinOp (BVar 2) Neq (BVar 1))) Imp (BinOp (FunExp ''readMask'' [(TVar 1),(TVar 0)] [(FunExp ''updMask'' [(TVar 3),(TVar 2)] [(BVar 5),(BVar 4),(BVar 2),(BVar 0)]),(BVar 3),(BVar 1)]) Eq (FunExp ''readMask'' [(TVar 1),(TVar 0)] [(BVar 5),(BVar 3),(BVar 1)]))))))))))))),(Forall ((TCon ''HeapType'') []) (Forall ((TCon ''MaskType'') []) (BinOp (FunExp ''state'' [] [(BVar 1),(BVar 0)]) Imp (FunExp ''GoodMask'' [] [(BVar 0)])))),(ForallT (ForallT (Forall ((TCon ''MaskType'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (BinOp (FunExp ''GoodMask'' [] [(BVar 2)]) Imp (BinOp (BinOp (FunExp ''readMask'' [(TVar 1),(TVar 0)] [(BVar 2),(BVar 1),(BVar 0)]) Ge (Var 2)) And (BinOp (BinOp (BinOp (FunExp ''GoodMask'' [] [(BVar 2)]) And (UnOp Not (FunExp ''IsPredicateField'' [(TVar 1),(TVar 0)] [(BVar 0)]))) And (UnOp Not (FunExp ''IsWandField'' [(TVar 1),(TVar 0)] [(BVar 0)]))) Imp (BinOp (FunExp ''readMask'' [(TVar 1),(TVar 0)] [(BVar 2),(BVar 1),(BVar 0)]) Le (Var 3)))))))))),(ForallT (ForallT (Forall ((TCon ''MaskType'') []) (Forall ((TCon ''Ref'') []) (Forall ((TCon ''Field'') [(TVar 1),(TVar 0)]) (BinOp (FunExp ''HasDirectPerm'' [(TVar 1),(TVar 0)] [(BVar 2),(BVar 1),(BVar 0)]) Iff (BinOp (FunExp ''readMask'' [(TVar 1),(TVar 0)] [(BVar 2),(BVar 1),(BVar 0)]) Gt (Var 2)))))))),(UnOp Not (FunExp ''IsPredicateField'' [((TCon ''NormalField'') []),(TPrim TInt)] [(Var 4)])),(UnOp Not (FunExp ''IsWandField'' [((TCon ''NormalField'') []),(TPrim TInt)] [(Var 4)])),(Forall ((TCon ''Ref'') []) (FunExp ''IsPredicateField'' [((TCon ''PredicateType_P'') []),(TPrim TBool)] [(FunExp ''P'' [] [(BVar 0)])])),(Forall ((TCon ''Ref'') []) (Forall ((TCon ''Ref'') []) (BinOp (BinOp (FunExp ''P'' [] [(BVar 1)]) Eq (FunExp ''P'' [] [(BVar 0)])) Imp (BinOp (BVar 1) Eq (BVar 0)))))]"
definition fdecls
  where
    "fdecls  = [(''state'',0,[((TCon ''HeapType'') []),((TCon ''MaskType'') [])],(TPrim TBool)),(''IdenticalOnKnownLocations'',0,[((TCon ''HeapType'') []),((TCon ''HeapType'') []),((TCon ''MaskType'') [])],(TPrim TBool)),(''readHeap'',2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TVar 1)),(''updHeap'',2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TVar 1)],((TCon ''HeapType'') [])),(''IsPredicateField'',2,[((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool)),(''IsWandField'',2,[((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool)),(''readMask'',2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TReal)),(''updMask'',2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TPrim TReal)],((TCon ''MaskType'') [])),(''GoodMask'',0,[((TCon ''MaskType'') [])],(TPrim TBool)),(''HasDirectPerm'',2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool)),(''P'',0,[((TCon ''Ref'') [])],((TCon ''Field'') [((TCon ''PredicateType_P'') []),(TPrim TBool)]))]"
definition globals_vdecls :: "(vdecls)"
  where
    "globals_vdecls  = [(5,((TCon ''HeapType'') []),(None )),(6,((TCon ''MaskType'') []),(None ))]"
definition constants_vdecls :: "(vdecls)"
  where
    "constants_vdecls  = [(0,((TCon ''Ref'') []),(None )),(1,((TCon ''MaskType'') []),(None )),(2,(TPrim TReal),(None )),(3,(TPrim TReal),(None )),(4,((TCon ''Field'') [((TCon ''NormalField'') []),(TPrim TInt)]),(None ))]"
definition unique_consts :: "((vname)list)"
  where
    "unique_consts  = [4]"
lemma globals_max_aux:
shows "(((map fst (append global_data.constants_vdecls global_data.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls)))) \<le> 6))"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls)))) \<longrightarrow> (x \<le> 6)))"
using globals_max_aux helper_max
by blast

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp

lemma mconst0:
shows "((map_of global_data.constants_vdecls 0) = (Some (((TCon ''Ref'') []),(None ))))"
by (simp add:global_data.constants_vdecls_def)

lemma mconst1:
shows "((map_of global_data.constants_vdecls 1) = (Some (((TCon ''MaskType'') []),(None ))))"
by (simp add:global_data.constants_vdecls_def)

lemma mconst2:
shows "((map_of global_data.constants_vdecls 2) = (Some ((TPrim TReal),(None ))))"
by (simp add:global_data.constants_vdecls_def)

lemma mconst3:
shows "((map_of global_data.constants_vdecls 3) = (Some ((TPrim TReal),(None ))))"
by (simp add:global_data.constants_vdecls_def)

lemma mconst4:
shows "((map_of global_data.constants_vdecls 4) = (Some (((TCon ''Field'') [((TCon ''NormalField'') []),(TPrim TInt)]),(None ))))"
by (simp add:global_data.constants_vdecls_def)

lemma mfunstate:
shows "((map_of fdecls ''state'') = (Some (0,[((TCon ''HeapType'') []),((TCon ''MaskType'') [])],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfunIdenticalOnKnownLocations:
shows "((map_of fdecls ''IdenticalOnKnownLocations'') = (Some (0,[((TCon ''HeapType'') []),((TCon ''HeapType'') []),((TCon ''MaskType'') [])],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfunreadHeap:
shows "((map_of fdecls ''readHeap'') = (Some (2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TVar 1))))"
by (simp add:fdecls_def)

lemma mfunupdHeap:
shows "((map_of fdecls ''updHeap'') = (Some (2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TVar 1)],((TCon ''HeapType'') []))))"
by (simp add:fdecls_def)

lemma mfunIsPredicateField:
shows "((map_of fdecls ''IsPredicateField'') = (Some (2,[((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfunIsWandField:
shows "((map_of fdecls ''IsWandField'') = (Some (2,[((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfunreadMask:
shows "((map_of fdecls ''readMask'') = (Some (2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TReal))))"
by (simp add:fdecls_def)

lemma mfunupdMask:
shows "((map_of fdecls ''updMask'') = (Some (2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TPrim TReal)],((TCon ''MaskType'') []))))"
by (simp add:fdecls_def)

lemma mfunGoodMask:
shows "((map_of fdecls ''GoodMask'') = (Some (0,[((TCon ''MaskType'') [])],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfunHasDirectPerm:
shows "((map_of fdecls ''HasDirectPerm'') = (Some (2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfunP:
shows "((map_of fdecls ''P'') = (Some (0,[((TCon ''Ref'') [])],((TCon ''Field'') [((TCon ''PredicateType_P'') []),(TPrim TBool)]))))"
by (simp add:fdecls_def)

lemma mvar5:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 5) = (Some (((TCon ''HeapType'') []),(None ))))"
by (simp add:global_data.constants_vdecls_def global_data.globals_vdecls_def)

lemma mvar6:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 6) = (Some (((TCon ''MaskType'') []),(None ))))"
by (simp add:global_data.constants_vdecls_def global_data.globals_vdecls_def)

lemma mvar0:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 0) = (Some (((TCon ''Ref'') []),(None ))))"
by (simp add: mconst0 del: Nat.One_nat_def)

lemma mvar1:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 1) = (Some (((TCon ''MaskType'') []),(None ))))"
by (simp add: mconst1 del: Nat.One_nat_def)

lemma mvar2:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 2) = (Some ((TPrim TReal),(None ))))"
by (simp add: mconst2 del: Nat.One_nat_def)

lemma mvar3:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 3) = (Some ((TPrim TReal),(None ))))"
by (simp add: mconst3 del: Nat.One_nat_def)

lemma mvar4:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 4) = (Some (((TCon ''Field'') [((TCon ''NormalField'') []),(TPrim TInt)]),(None ))))"
by (simp add: mconst4 del: Nat.One_nat_def)


end
