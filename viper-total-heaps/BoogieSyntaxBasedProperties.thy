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



subsection \<open>Auxiliary Definitions Lemmas\<close>


abbreviation natlist_sum :: "nat list \<Rightarrow> nat" where
  "natlist_sum xs \<equiv> foldr (+) xs 0"


fun flatten_cont :: "cont \<Rightarrow> bigblock list" where
  "flatten_cont KStop = []"
| "flatten_cont (KEndBlock cont) = empty_bigblock None # flatten_cont cont"
| "flatten_cont (KSeq bb cont) = bb # flatten_cont cont"


fun pair_smaller :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "pair_smaller (a,b) (c,d) = (a < c \<or> (a = c \<and> b < d))"


lemma pair_smaller_transitive:
  assumes "pair_smaller p1 p2" and "pair_smaller p2 p3"
  shows "pair_smaller p1 p3"
  apply (cases p1, cases p2, cases p3)
  using assms
  by auto


lemma convert_list_to_cont_flatten:
  shows "flatten_cont (convert_list_to_cont bbs cont) = bbs @ flatten_cont cont"
  by (induction bbs, auto)


lemma natlist_sum_append:
  shows "natlist_sum (xs @ ys) = natlist_sum xs + natlist_sum ys"
  by (induction xs, auto)


lemma red_bigblock_final_normal_implies_initial_not_fail_or_magic:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(bb, cont, s)\<rangle> \<longrightarrow> (bb', cont', Normal ns')"
  shows "s \<noteq> Failure \<and> s \<noteq> Magic"
  using assms
  by (cases, auto)


lemma red_bigblock_small_final_normal_implies_initial_not_fail_or_magic:
  assumes "red_bigblock_small P ctxt_bpl ps ps'"
      and "ps = (\<gamma>, s)"
      and "ps' = (\<gamma>', Normal ns')"
    shows "s \<noteq> Failure \<and> s \<noteq> Magic"
  using assms
proof cases
  case (RedBigBlockSmallSimpleCmd c s s' name cs str tr cont)
  then show ?thesis
    using assms(2,3) failure_stays_cmd magic_stays_cmd by blast
next
  case (RedBigBlockSmallNoSimpleCmdOneStep name str tr cont s b' cont' s')
  then show ?thesis
    by (metis Pair_inject assms(2,3) red_bigblock_final_normal_implies_initial_not_fail_or_magic)
qed


lemma bpl_red_final_normal_implies_initial_not_fail_or_magic:
  assumes "red_bigblock_small_multi P ctxt_bpl ps ps'"
      and "ps = (\<gamma>, s)"
      and "ps' = (\<gamma>', Normal ns')"
    shows "s \<noteq> Failure \<and> s \<noteq> Magic"
  using assms
proof (induction arbitrary: \<gamma> s rule: converse_rtranclp_induct)
  case base
  then show ?case
    by auto
next
  case (step ps ps'')
  obtain \<gamma>'' s'' where "ps'' = (\<gamma>'', s'')"
    by fastforce
  have "s'' \<noteq> Failure \<and> s'' \<noteq> Magic"
    apply (rule step.IH)
    by fact+
  thus ?case
    using red_bigblock_small_final_normal_implies_initial_not_fail_or_magic
    by (metis \<open>ps'' = _\<close> state.exhaust step.hyps(1) step.prems(1))
qed


lemma bpl_red_final_normal_implies_initial_normal:
  assumes "red_bigblock_small_multi P ctxt_bpl (\<gamma>, s) (\<gamma>', Normal ns')"
  shows "\<exists>ns. s = Normal ns"
  by (metis assms bpl_red_final_normal_implies_initial_not_fail_or_magic state.exhaust)



subsection \<open>Restriction on Program Points\<close>


fun bigblock_restriction where
  "bigblock_restriction (BigBlock name cs None None) = True"
| "bigblock_restriction (BigBlock name cs (Some (ParsedIf bb_guard then_bbs else_bbs)) None) = (list_all id (map bigblock_restriction then_bbs) \<and> list_all id (map bigblock_restriction else_bbs))"
| "bigblock_restriction _ = False"


fun program_point_restriction where
  "program_point_restriction (bb, cont) = (bigblock_restriction bb \<and> list_all id (map bigblock_restriction (flatten_cont cont)))"


lemma red_bigblock_preserves_restriction:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(bb, cont, Normal ns)\<rangle> \<longrightarrow> (bb', cont', Normal ns')"
      and "program_point_restriction (bb, cont)"
    shows "program_point_restriction (bb', cont')"
  using assms(1)
proof (cases)
  case (RedSimpleCmds cs bb_name str_cmd tr_cmd)
  then show ?thesis
    using assms(2) bigblock_restriction.elims(2)
    by fastforce
next
  case (RedParsedIfTrue bb_guard bb_name then_bbs elsebigblocks)
  then show ?thesis
    using assms(2)
    unfolding program_point_restriction.simps
    by (simp add: convert_list_to_cont_flatten)
next
  case (RedParsedIfFalse bb_guard bb_name thenbigblocks else_bbs)
  then show ?thesis
    using assms(2)
    unfolding program_point_restriction.simps
    by (simp add: convert_list_to_cont_flatten)
qed (insert assms, auto)


lemma red_bigblock_small_preserves_restriction:
  assumes "program_point_restriction \<gamma>"
      and "red_bigblock_small P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
    shows "program_point_restriction \<gamma>'"
proof (cases rule: red_bigblock_small.cases[OF assms(2)])
  case (1 c s s' name cs str tr cont)
  then show ?thesis
    using assms(1)
    by (fastforce elim: program_point_restriction.elims bigblock_restriction.elims)
next
  case (2 name str tr cont s b' cont' s')
  then show ?thesis
    by (metis Pair_inject assms(1) red_bigblock_preserves_restriction)
qed



subsection \<open>Decreasing Measure\<close>


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
     1 + max (natlist_sum (map bigblock_count then_bbs)) (natlist_sum (map bigblock_count else_bbs))"
| "bigblock_count _ = 1"


fun program_point_measure :: "bigblock \<times> cont \<Rightarrow> nat \<times> nat" where
  "program_point_measure (BigBlock name cs str tr, cont) = (bigblock_count (BigBlock name cs str tr) + natlist_sum (map bigblock_count (flatten_cont cont)), length cs)"


lemma red_bigblock_decreases_measure:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(bb, cont, Normal ns)\<rangle> \<longrightarrow> (bb', cont', Normal ns')"
      and "bb = BigBlock bb_name cs str None"
      and "str \<noteq> None \<Longrightarrow> \<exists>guard then_bbs else_bbs. str = Some (ParsedIf guard then_bbs else_bbs)"
    shows "pair_smaller (program_point_measure (bb', cont')) (program_point_measure (bb, cont))"
  using assms(1)
proof (cases)
  case (RedSimpleCmds cs bb_name str_cmd tr_cmd)
  then show ?thesis
    using assms(2,3)
    by force
next
  case (RedSkip bb_name)
  show ?thesis
    unfolding RedSkip
    apply (cases bb')
    by simp
next
  case (RedSkipEndBlock bb_name)
  show ?thesis
    unfolding RedSkipEndBlock
    by simp
next
  case (RedParsedIfTrue bb_guard bb_name then_bbs elsebigblocks)
  show ?thesis
    unfolding RedParsedIfTrue
    apply simp
    apply (cases bb')
    apply (rename_tac guard cs str tr)
    apply (case_tac str; simp)
     apply (unfold convert_list_to_cont_flatten map_append natlist_sum_append)
    by linarith+
next
  case (RedParsedIfFalse bb_guard bb_name thenbigblocks else_bbs)
  show ?thesis
    unfolding RedParsedIfFalse
    apply simp
    apply (cases bb')
    apply (rename_tac guard cs str tr)
    apply (case_tac str; simp)
     apply (unfold convert_list_to_cont_flatten map_append natlist_sum_append)
    by linarith+
qed (insert assms, auto)


lemma red_bigblock_small_decreases_measure:
  assumes "red_bigblock_small P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
      and "\<gamma> = (BigBlock bb_name cs str None, cont)"
      and "str \<noteq> None \<Longrightarrow> \<exists>guard then_bbs else_bbs. str = Some (ParsedIf guard then_bbs else_bbs)"
    shows "pair_smaller (program_point_measure \<gamma>') (program_point_measure \<gamma>)"
proof (cases rule: red_bigblock_small.cases[OF assms(1)])
  case (1 c s s' name cs str tr cont)
  then show ?thesis
    apply simp
    apply (rule disjI2)
    apply (case_tac str; case_tac tr; simp)
    apply (rename_tac str')
    by (case_tac str'; simp)
next
  case (2 name str tr cont s b' cont' s')
  then show ?thesis
    by (metis Pair_inject assms(2,3) red_bigblock_decreases_measure)
qed


lemma tranclp_red_bigblock_small_decreases_measure:
  assumes "tranclp (red_bigblock_small P ctxt) s s'"
      and "s = (\<gamma>, Normal ns)"
      and "s' = (\<gamma>', Normal ns')"
      and "program_point_restriction \<gamma>"
    shows "pair_smaller (program_point_measure \<gamma>') (program_point_measure \<gamma>)"
  using assms
proof (induction arbitrary: \<gamma> ns rule: converse_tranclp_induct)
  case (base s)
  show ?case
    using base.hyps[unfolded base.prems, THEN red_bigblock_small_decreases_measure]
    by (metis base.prems(3) bigblock_restriction.elims(2) program_point_restriction.elims(2))
next
  case (step s s'')
  obtain \<gamma>'' ns'' where "s'' = (\<gamma>'', Normal ns'')"
    by (metis bpl_red_final_normal_implies_initial_normal old.prod.exhaust r_into_rtranclp step.hyps(2) step.prems(2) tranclp_rtranclp_absorb)
  show ?case
    apply (rule pair_smaller_transitive)
     apply (rule step.IH[OF \<open>s'' = _\<close> \<open>s' = _\<close>])
    using \<open>s'' = _\<close> red_bigblock_small_preserves_restriction step.hyps(1) step.prems(1,3)
     apply blast
    by (metis \<open>s'' = _\<close> bigblock_restriction.elims(2) program_point_restriction.elims(2) red_bigblock_small_decreases_measure step.hyps(1) step.prems(1,3))
qed


subsection \<open>Relation between Program Points\<close>


lemma bpl_no_heap_assignment:
  assumes
    NoHeapAssign: "contains_no_heap_assignment_until hvar \<gamma>' \<gamma>" and
    ProgramPointRestriction: "program_point_restriction \<gamma>" and
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
  note NoAssignSimpleCmd.prems(2)[unfolded red_ast_bpl_def]
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
        by (metis NoAssignSimpleCmd.IH NoAssignSimpleCmd.prems(1) \<open>config = _\<close> step(1,2) red_ast_bpl_def red_bigblock_small_preserves_restriction)
    next
      case (RedAssumeOk e)
      then show ?thesis
        by (metis NoAssignSimpleCmd.IH NoAssignSimpleCmd.prems(1) \<open>config = _\<close> step(1,2) red_ast_bpl_def red_bigblock_small_preserves_restriction)
    next
      case (RedAssign x ty v e)
      moreover have "x \<noteq> hvar"
        using NoAssignSimpleCmd.hyps(1) RedAssign(1)
        by blast
      ultimately show ?thesis
        by (metis NoAssignSimpleCmd.IH NoAssignSimpleCmd.prems(1) \<open>config = _\<close> step(1,2) red_ast_bpl_def red_bigblock_small_preserves_restriction update_var_other)
    next
      case (RedHavocNormal x ty w v)
      then show ?thesis
        by (simp add: NoAssignSimpleCmd.hyps(1))
    qed (insert bpl_red_final_normal_implies_initial_normal[OF step(2)[unfolded \<open>config = _\<close>]], simp_all)
  qed
next
  case (NoAssignIf then_bb cont else_bb name guard)
  note NoAssignIf.prems(2)[unfolded red_ast_bpl_def]
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
        by (metis NoAssignIf.IH(1) NoAssignIf.prems(1) \<open>config = _\<close> convert_list_to_cont.simps(1) step(1,2) red_ast_bpl_def red_bigblock_small_preserves_restriction)
    next
      case RedParsedIfFalse
      thus ?thesis
        by (metis NoAssignIf.IH(2) NoAssignIf.prems(1) \<open>config = _\<close> convert_list_to_cont.simps(1) step(1,2) red_ast_bpl_def red_bigblock_small_preserves_restriction)
    qed auto
  qed
next
  case (NoAssignCont b cont name)
  note NoAssignCont.prems(2)[unfolded red_ast_bpl_def]
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
