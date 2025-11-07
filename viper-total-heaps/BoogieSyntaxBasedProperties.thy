theory BoogieSyntaxBasedProperties
  imports BoogieInterface
begin


subsection \<open>Syntactic Check on Program Points\<close>


(*
function (sequential) contains_no_heap_assignment_until :: "vname \<Rightarrow> (bigblock \<times> cont) \<Rightarrow> (bigblock \<times> cont) \<Rightarrow> bool" where
  "contains_no_heap_assignment_until _ \<gamma> \<gamma> = True"
| "contains_no_heap_assignment_until hvar ((BigBlock name (c#cs) str tr), cont) \<gamma> = ((\<exists>v e. c = Assign v e \<longrightarrow> v \<noteq> hvar) \<and> contains_no_heap_assignment_until hvar ((BigBlock name cs str tr), cont) \<gamma>)"
| "contains_no_heap_assignment_until hvar ((BigBlock name [] (Some (ParsedIf _ [then_bb] [])) None), cont) \<gamma> = contains_no_heap_assignment_until hvar (then_bb, cont) \<gamma>"
| "contains_no_heap_assignment_until _ _ _ = False"
*)


inductive contains_no_heap_assignment_until :: "vname \<Rightarrow> (bigblock \<times> cont) \<Rightarrow> (bigblock \<times> cont) \<Rightarrow> bool"
  for hvar :: vname and \<gamma>\<^sub>b :: "bigblock \<times> cont" where
  NoAssignReach:
  "contains_no_heap_assignment_until hvar \<gamma>\<^sub>b \<gamma>\<^sub>b"
| NoAssignSimpleCmd:
  "\<lbrakk> (\<forall>v e. c = Assign v e \<longrightarrow> v \<noteq> hvar) \<and> (\<forall>v. c \<noteq> Havoc v);
     contains_no_heap_assignment_until hvar \<gamma>\<^sub>b (BigBlock name cs str tr, cont)
   \<rbrakk> \<Longrightarrow>
   contains_no_heap_assignment_until hvar \<gamma>\<^sub>b (BigBlock name (c#cs) str tr, cont)"
| NoAssignIf:
  "\<lbrakk> contains_no_heap_assignment_until hvar \<gamma>\<^sub>b (then_bb, cont);
     contains_no_heap_assignment_until hvar \<gamma>\<^sub>b (else_bb, cont)
   \<rbrakk> \<Longrightarrow>
   contains_no_heap_assignment_until hvar \<gamma>\<^sub>b (BigBlock name [] (Some (ParsedIf _ [then_bb] [else_bb])) None, cont)"
| NoAssignCont:
  "contains_no_heap_assignment_until hvar \<gamma>\<^sub>b (b, cont)
   \<Longrightarrow>
   contains_no_heap_assignment_until hvar \<gamma>\<^sub>b (BigBlock name [] None None, KSeq b cont)"

\<comment> \<open>Test for the definition above\<close>
definition bigblock_3
  where
    "bigblock_3  = (BigBlock (None ) [(Assign 7 (FunExp ''updMask'' [((TCon ''PredicateType_P'') []),((TCon ''FrameType'') [])] [(Var 7),(Var 0),(FunExp ''P'' [] [(Var 8)]),(BinOp (FunExp ''readMask'' [((TCon ''PredicateType_P'') []),((TCon ''FrameType'') [])] [(Var 7),(Var 0),(FunExp ''P'' [] [(Var 8)])]) Sub (Var 9))])),(Assign 9 (BinOp (Var 4) Mul (BinOp (Lit (LInt 1)) RealDiv (Lit (LInt 1))))),(Assert (BinOp (Var 9) Ge (Var 3))),(Assume (BinOp (BinOp (Var 9) Gt (Var 3)) Imp (BinOp (Var 8) Neq (Var 0)))),(Assign 7 (FunExp ''updMask'' [((TCon ''NormalField'') []),(TPrim TInt)] [(Var 7),(Var 8),(Var 5),(BinOp (FunExp ''readMask'' [((TCon ''NormalField'') []),(TPrim TInt)] [(Var 7),(Var 8),(Var 5)]) Add (Var 9))])),(Assume (FunExp ''state'' [] [(Var 6),(Var 7)])),(Assume (FunExp ''state'' [] [(Var 6),(Var 7)])),(Assign 6 (FunExp ''updHeap'' [((TCon ''PredicateType_P'') []),((TCon ''PMaskType'') [])] [(Var 6),(Var 0),(FunExp ''P#sm'' [] [(Var 8)]),(Var 2)])),(Assume (FunExp ''state'' [] [(Var 6),(Var 7)]))] (None ) (None ))"
definition bigblock_3\<^sub>b
  where
    "bigblock_3\<^sub>b  = (BigBlock (None ) [(Assign 6 (FunExp ''updHeap'' [((TCon ''PredicateType_P'') []),((TCon ''PMaskType'') [])] [(Var 6),(Var 0),(FunExp ''P#sm'' [] [(Var 8)]),(Var 2)])),(Assume (FunExp ''state'' [] [(Var 6),(Var 7)]))] (None ) (None ))"
definition bigblock_2
  where
    "bigblock_2  = (BigBlock (None ) [] (None ) (None ))"
definition bigblock_1
  where
    "bigblock_1  = (BigBlock (None ) [(Assert (BinOp (Var 9) Le (FunExp ''readMask'' [((TCon ''PredicateType_P'') []),((TCon ''FrameType'') [])] [(Var 7),(Var 0),(FunExp ''P'' [] [(Var 8)])])))] (None ) (None ))"
definition bigblock_0
  where
    "bigblock_0  = (BigBlock (None ) [(Assert (Lit (LBool True))),(Assign 9 (Var 4)),(Assert (Lit (LBool True)))] (Some (ParsedIf (Some (BinOp (Var 9) Neq (Var 3))) [bigblock_1] [bigblock_2])) (None ))"
lemma
  "contains_no_heap_assignment_until 6 (bigblock_3\<^sub>b, KStop) (bigblock_0, KSeq bigblock_3 KStop)"
  apply (subst bigblock_0_def)
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignIf)
   apply (subst bigblock_1_def)
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (rule NoAssignCont)
   apply (subst bigblock_3_def)
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (rule NoAssignSimpleCmd)
    apply fastforce
   apply (subst bigblock_3\<^sub>b_def)
   apply (rule NoAssignReach)
  apply (subst bigblock_2_def)
  apply (rule NoAssignCont)
  apply (subst bigblock_3_def)
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (rule NoAssignSimpleCmd)
   apply fastforce
  apply (subst bigblock_3\<^sub>b_def)
  apply (rule NoAssignReach)
  done


lemma bpl_red_final_normal_implies_initial_normal:
  assumes "red_bigblock_small_multi P ctxt_bpl (\<gamma>, s) (\<gamma>', Normal ns')"
  shows "\<exists>ns. s = Normal ns"
  sorry



subsection \<open>Decreasing Measure\<close>


fun sum :: "nat list \<Rightarrow> nat" where
  "sum xs = foldl (+) 0 xs"


fun flatten_cont :: "cont \<Rightarrow> bigblock list" where
  "flatten_cont KStop = []"
| "flatten_cont (KEndBlock cont) = flatten_cont cont"
| "flatten_cont (KSeq bb cont) = bb # flatten_cont cont"


(*
fun max_cmd_count_bigblock :: "bigblock \<Rightarrow> nat" where
  "max_cmd_count_bigblock (BigBlock name cs None None) = length cs"
| "max_cmd_count_bigblock (BigBlock name cs (Some (ParsedIf bb_guard then_bbs else_bbs)) None) =
     length cs + max (sum (map max_cmd_count_bigblock then_bbs)) (sum (map max_cmd_count_bigblock else_bbs))"
| "max_cmd_count_bigblock _ = 0"


fun max_cmd_count :: "bigblock \<times> cont \<Rightarrow> nat" where
  "max_cmd_count (bb, cont) = max_cmd_count_bigblock bb + sum (map max_cmd_count_bigblock (flatten_cont cont))"
*)


fun bigblock_count :: "bigblock \<Rightarrow> nat" where
  "bigblock_count (BigBlock name cs None None) = 1"
| "bigblock_count (BigBlock name cs (Some (ParsedIf bb_guard then_bbs else_bbs)) None) =
     1 + max (sum (map bigblock_count then_bbs)) (sum (map bigblock_count else_bbs))"
| "bigblock_count _ = 1"


fun program_point_measure :: "bigblock \<times> cont \<Rightarrow> nat \<times> nat" where
  "program_point_measure (BigBlock name cs str tr, cont) = (sum (map bigblock_count (flatten_cont cont)), length cs)"


fun pair_smaller :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "pair_smaller (a,b) (c,d) = (a < c \<or> (a = c \<and> b < d))"


lemma pair_smaller_transitive:
  assumes "pair_smaller p1 p2" and "pair_smaller p2 p3"
  shows "pair_smaller p1 p3"
  apply (cases p1, cases p2, cases p3)
  using assms
  by auto


lemma red_bigblock_decreases_measure:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(bb, cont, s)\<rangle> \<longrightarrow> (bb', cont', s')"
  shows "pair_smaller (program_point_measure (bb', cont')) (program_point_measure (bb, cont))"
  sorry


lemma red_bigblock_small_decreases_measure:
  assumes "red_bigblock_small P ctxt (\<gamma>, s) (\<gamma>', s')"
  shows "pair_smaller (program_point_measure \<gamma>') (program_point_measure \<gamma>)"
  apply (cases rule: red_bigblock_small.cases[OF assms])
   apply simp
  by (metis Pair_inject red_bigblock_decreases_measure)


lemma tranclp_red_bigblock_small_decreases_measure:
  assumes "tranclp (red_bigblock_small P ctxt) s1 s2"
  shows "pair_smaller (program_point_measure (fst s2)) (program_point_measure (fst s1))"
  using assms
proof (induction arbitrary: rule: converse_tranclp_induct)
  case (base s1)
  then show ?case
    by (metis prod.exhaust_sel red_bigblock_small_decreases_measure)
next
  case (step s1 s1')
  show ?case
    apply (rule pair_smaller_transitive)
     apply fact
    by (metis prod.collapse red_bigblock_small_decreases_measure step.hyps(1))
qed


subsection \<open>Relation between Program Points\<close>


lemma bpl_no_heap_assignment:
  assumes
    NoHeapAssign: "contains_no_heap_assignment_until hvar \<gamma>' \<gamma>" and
    BplRed: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
  shows "lookup_var (var_context ctxt_bpl) ns hvar = lookup_var (var_context ctxt_bpl) ns' hvar"
  using assms
proof (induction arbitrary: ns)
  case NoAssignReach
  have "ns = ns'"
    by (metis fstI less_imp_neq NoAssignReach pair_smaller.elims(2) red_ast_bpl_def rtranclpD snd_eqD state.inject tranclp_red_bigblock_small_decreases_measure)
  then show ?case
    by auto
next
  case (NoAssignSimpleCmd c name cs str tr cont)
  note NoAssignSimpleCmd.prems[unfolded red_ast_bpl_def]
  then show ?case
  proof (cases rule: converse_rtranclpE)
    case base
    then show ?thesis
      by blast
  next
    case (step config)
    then obtain s' where "(type_interp ctxt_bpl), ([] :: ast proc_context), (var_context ctxt_bpl), (fun_interp ctxt_bpl), (rtype_interp ctxt_bpl) \<turnstile> \<langle>c, Normal ns\<rangle> \<rightarrow> s'" and "config = ((BigBlock name cs str tr, cont), s')"
      by (auto elim: red_bigblock_small.cases)
    then show ?thesis
    proof (cases)
      case (RedAssertOk e)
      then show ?thesis
        by (metis NoAssignSimpleCmd.IH \<open>config = _\<close> step(2) red_ast_bpl_def)
    next
      case (RedAssumeOk e)
      then show ?thesis
        by (metis NoAssignSimpleCmd.IH \<open>config = _\<close> step(2) red_ast_bpl_def)
    next
      case (RedAssign x ty v e)
      moreover have "x \<noteq> hvar"
        using NoAssignSimpleCmd.hyps(1) RedAssign(1)
        by blast
      ultimately show ?thesis
        by (metis NoAssignSimpleCmd.IH \<open>config = _\<close> step(2) red_ast_bpl_def update_var_other)
    next
      case (RedHavocNormal x ty w v)
      then show ?thesis
        by (simp add: NoAssignSimpleCmd.hyps(1))
    qed (insert bpl_red_final_normal_implies_initial_normal[OF step(2)[unfolded \<open>config = _\<close>]], simp_all)
  qed
next
  case (NoAssignIf then_bb cont else_bb name guard)
  note NoAssignIf.prems[unfolded red_ast_bpl_def]
  then show ?case
  proof (cases rule: converse_rtranclpE)
    case base
    then show ?thesis
      by simp
  next
    case (step config)
    then obtain b' cont' s' where "red_bigblock (type_interp ctxt_bpl) ([] :: ast proc_context) (var_context ctxt_bpl) (fun_interp ctxt_bpl) (rtype_interp ctxt_bpl) P (if_bigblock name guard [then_bb] [else_bb], cont, Normal ns) (b', cont', s')" and "config = ((b', cont'), s')"
      by (auto elim: red_bigblock_small.cases)
    then show ?thesis
    proof (cases)
      case RedParsedIfTrue
      thus ?thesis
        by (metis NoAssignIf.IH(1) \<open>config = _\<close> convert_list_to_cont.simps(1) step(2) red_ast_bpl_def)
    next
      case RedParsedIfFalse
      thus ?thesis
        by (metis NoAssignIf.IH(2) \<open>config = _\<close> convert_list_to_cont.simps(1) step(2) red_ast_bpl_def)
    qed auto
  qed
next
  case (NoAssignCont b cont name)
  note NoAssignCont.prems[unfolded red_ast_bpl_def]
  then show ?case
  proof (cases rule: converse_rtranclpE)
    case base
    then show ?thesis
      by simp
  next
    case (step config)
    then obtain b' cont' s' where "red_bigblock (type_interp ctxt_bpl) ([] :: ast proc_context) (var_context ctxt_bpl) (fun_interp ctxt_bpl) (rtype_interp ctxt_bpl) P (BigBlock name [] None None, KSeq b cont, Normal ns) (b', cont', s')" and "config = ((b', cont'), s')"
      by (auto elim: red_bigblock_small.cases)
    moreover hence "b' = b" and "cont' = cont" and "s' = Normal ns"
      by (auto elim: red_bigblock.cases)
    ultimately show ?thesis 
      using step(2)[folded red_ast_bpl_def] NoAssignCont
      by (simp add: red_ast_bpl_def)
  qed
qed

end
