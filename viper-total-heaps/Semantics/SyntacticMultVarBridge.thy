theory SyntacticMultVarBridge
  imports TotalSemProperties
begin

text \<open>Carbon's Boogie encoding scales a predicate body by inserting a reference to a fresh
  Boogie/Viper local variable on the Silver side, which produces \<open>Binop (Var n) Mult e\<close>
  subterms, rather than a literal, as \<^const>\<open>syntactic_mult\<close> does. \<open>var_mult\<close> (defined below)
  mirrors \<^const>\<open>syntactic_mult\<close>'s definition but scales by \<open>Var n\<close> instead of a literal;
  \<open>red_inhale_var_mult_eq_syntactic_mult\<close> shows the two agree on \<^const>\<open>red_inhale\<close>, provided the
  store maps \<open>n\<close> to the same value \<open>p\<close> that \<^const>\<open>syntactic_mult\<close> is instantiated with.\<close>

fun var_mult_permexpr :: "nat \<Rightarrow> pure_exp exp_or_wildcard \<Rightarrow> pure_exp exp_or_wildcard"
  where
    "var_mult_permexpr n Wildcard = Wildcard"
  | "var_mult_permexpr n (PureExp e) = PureExp (Binop (Var n) Mult e)"

fun var_mult :: "nat \<Rightarrow> assertion \<Rightarrow> assertion"
  where
    "var_mult n (Atomic (Pure e)) = (Atomic (Pure e))"
  | "var_mult n (Atomic (Acc e_r f e_p)) = (Atomic (Acc e_r f (var_mult_permexpr n e_p)))"
  | "var_mult n (Atomic (AccPredicate pred_id e_args e_p)) =
       (Atomic (AccPredicate pred_id e_args (var_mult_permexpr n e_p)))"
  | "var_mult n (Imp e A) = (Imp e (var_mult n A))"
  | "var_mult n (Star A B) = Star (var_mult n A) (var_mult n B)"
  | "var_mult n (ForAll ty A) = (ForAll ty (var_mult n A))"
  | "var_mult n (Exists ty A) = (Exists ty (var_mult n A))"
  | "var_mult n (ImpureAnd A B) = ImpureAnd (var_mult n A) (var_mult n B)"
  | "var_mult n (ImpureOr A B) = ImpureOr (var_mult n A) (var_mult n B)"
  | "var_mult n (A --* B) = (var_mult n A) --* (var_mult n B)"
  | "var_mult n (CondAssert e A B) = CondAssert e (var_mult n A) (var_mult n B)"

text \<open>Characterizes the assertion shapes \<^const>\<open>red_inhale\<close> has a reduction rule for.\<close>
fun is_pure_atomic_assertion :: "assertion \<Rightarrow> bool" where
  "is_pure_atomic_assertion (Atomic _) = True"
| "is_pure_atomic_assertion (Imp _ _) = True"
| "is_pure_atomic_assertion (CondAssert _ _ _) = True"
| "is_pure_atomic_assertion (Star _ _) = True"
| "is_pure_atomic_assertion _ = False"

lemma direct_sub_expressions_assertion_empty_no_reduce:
  assumes "direct_sub_expressions_assertion A = []"
      and "\<not> is_pure_atomic_assertion A"
    shows "\<not> red_inhale ctxt R A \<omega> res"
proof (cases A)
  case (ForAll ty A')
  with assms show ?thesis
    by (auto elim: red_inhale.cases)
next
  case (Exists ty A')
  with assms show ?thesis
    by (auto elim: red_inhale.cases)
next
  case (ImpureAnd A1 A2)
  with assms show ?thesis
    by (auto elim: red_inhale.cases)
next
  case (ImpureOr A1 A2)
  with assms show ?thesis
    by (auto elim: red_inhale.cases)
next
  case (Wand A1 A2)
  with assms show ?thesis
    by (auto elim: red_inhale.cases)
qed (insert assms, auto)

text \<open>Inhaling never changes the store (only heap/mask); needed since \<^const>\<open>var_mult\<close>'s
  scaling variable \<open>n\<close> must keep referring to the same value throughout a \<open>Star\<close> inhale.\<close>
lemma red_inhale_store_same:
  assumes "red_inhale ctxt R A \<omega> res"
  shows "\<And>\<omega>'. res = RNormal \<omega>' \<Longrightarrow> get_store_total \<omega>' = get_store_total \<omega>"
  using assms
proof (induction rule: red_inhale.induct)
  case InhAcc
  then show ?case
    unfolding inhale_perm_single_def
    by (auto split: if_splits elim: th_result_rel.cases)
next
  case InhAccWildcard
  then show ?case
    unfolding inhale_perm_single_def
    by (auto split: if_splits elim: th_result_rel.cases)
next
  case InhAccPred
  then show ?case
    unfolding inhale_perm_single_pred_def
    by (auto split: if_splits elim: th_result_rel.cases)
next
  case InhAccPredWildcard
  then show ?case
    unfolding inhale_perm_single_pred_def
    by (auto split: if_splits elim: th_result_rel.cases)
next
  case (InhPure \<omega> e b)
  then show ?case by (cases b) auto
next
  case (InhStarNormal Ap om1 om2 Bp res1)
  from InhStarNormal(4)[OF InhStarNormal(5)] have eq1: "get_store_total \<omega>' = get_store_total om2" .
  from InhStarNormal(3)[OF refl] have eq2: "get_store_total om2 = get_store_total om1" .
  show ?case using eq1 eq2 by simp
next
  case InhStarFailureMagic
  then show ?case by auto
next
  case InhImpTrue
  then show ?case by auto
next
  case InhImpFalse
  then show ?case by auto
next
  case InhCondAssertTrue
  then show ?case by auto
next
  case InhCondAssertFalse
  then show ?case by auto
next
  case InhSubExpFailure
  then show ?case by simp
qed

inductive_cases RedBinopFailure_case: "ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
inductive_cases RedVarFailure_case: "ctxt, \<omega>_def \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
inductive_cases RedLitFailure_case: "ctxt, \<omega>_def \<turnstile> \<langle>ELit l; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

lemma binop_var_lit_eq:
  assumes "get_store_total \<omega> n = Some (VPerm p)"
  shows "(ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) =
         (ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"
proof
  assume "ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  then show "ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  proof (rule RedBinop_case)
    fix v1 v2
    assume "ctxt, Some \<omega> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2"
       and "eval_binop_lazy v1 Mult = None"
       and "eval_binop v1 Mult v2 = BinopNormal v"
    hence "v1 = VPerm p"
      using assms by (auto elim: RedVar_case)
    then show ?thesis
      using \<open>ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2\<close> \<open>eval_binop_lazy v1 Mult = None\<close> \<open>eval_binop v1 Mult v2 = BinopNormal v\<close>
      by (auto intro: RedBinop RedLit)
  next
    fix v1
    assume "ctxt, Some \<omega> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "eval_binop_lazy v1 Mult = Some v"
    hence "v1 = VPerm p"
      using assms by (auto elim: RedVar_case)
    then show ?thesis
      using \<open>eval_binop_lazy v1 Mult = Some v\<close>
      by (auto intro: RedBinopLazy RedLit)
  qed
next
  assume "ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  then show "ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  proof (rule RedBinop_case)
    fix v1 v2
    assume "ctxt, Some \<omega> \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2"
       and "eval_binop_lazy v1 Mult = None"
       and "eval_binop v1 Mult v2 = BinopNormal v"
    hence "v1 = VPerm p"
      by (auto elim: RedLit_case)
    then show ?thesis
      using assms \<open>ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2\<close> \<open>eval_binop_lazy v1 Mult = None\<close> \<open>eval_binop v1 Mult v2 = BinopNormal v\<close>
      by (auto intro: RedBinop RedVar)
  next
    fix v1
    assume "ctxt, Some \<omega> \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "eval_binop_lazy v1 Mult = Some v"
    hence "v1 = VPerm p"
      by (auto elim: RedLit_case)
    then show ?thesis
      using assms \<open>eval_binop_lazy v1 Mult = Some v\<close>
      by (auto intro: RedBinopLazy RedVar)
  qed
qed

text \<open>Analogous to \<open>binop_var_lit_eq\<close>, but for the case where evaluation fails
  (\<^term>\<open>VFailure\<close>) rather than succeeding. Since \<^term>\<open>Var n\<close> and \<^term>\<open>real_to_expr p\<close> evaluate
  to the same value \<^term>\<open>VPerm p\<close> and neither can itself fail, this should follow the same way
  \<open>binop_var_lit_eq\<close> does (case split on the two ways a Binop can fail --
  \<open>RedBinopRightFailure\<close> vs \<open>RedBinopOpFailure\<close> -- using determinism of
  \<^term>\<open>Var n\<close>/\<^term>\<open>real_to_expr p\<close>'s evaluation
  to identify \<open>v1\<close> with \<^term>\<open>VPerm p\<close> in each case). Stated but not yet proved: the proof kept
  running into tactic-level friction (an unexplained "Failed to refine any pending goal" after
  what should be a closing \<open>rule\<close> application) that needs interactive debugging to resolve.\<close>
lemma binop_var_lit_eq_fail:
  assumes "get_store_total \<omega> n = Some (VPerm p)"
  shows "(ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure) =
         (ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
proof
  assume "ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  then show "ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  proof (rule RedBinopFailure_case)
    fix v1 v2
    assume "ctxt, Some \<omega> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
       and "eval_binop_lazy v1 Mult = None"
       and "eval_binop v1 Mult v2 \<noteq> BinopTypeFailure"
    hence V1: "v1 = VPerm p"
      using assms by (auto elim: RedVar_case)
    have "ctxt, Some \<omega> \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
      using RedLit[of ctxt "Some \<omega>" "LPerm p" \<omega>] by (simp add: V1 real_to_expr.simps)
    then show ?thesis
      using \<open>ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure\<close> \<open>eval_binop_lazy v1 Mult = None\<close>
            \<open>eval_binop v1 Mult v2 \<noteq> BinopTypeFailure\<close>
      by (auto intro: RedBinopRightFailure)
  next
    fix v1 v2
    assume "ctxt, Some \<omega> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2"
       and "eval_binop v1 Mult v2 = BinopOpFailure"
       and "eval_binop_lazy v1 Mult = None"
    hence "v1 = VPerm p"
      using assms by (auto elim: RedVar_case)
    then show ?thesis
      using \<open>ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2\<close> \<open>eval_binop v1 Mult v2 = BinopOpFailure\<close> \<open>eval_binop_lazy v1 Mult = None\<close>
      by (auto intro: RedBinopOpFailure RedLit)
  next
    assume "sub_pure_exp_total (Binop (Var n) Mult e) \<noteq> []"
       and "red_pure_exps_total ctxt (Some \<omega>) (sub_pure_exp_total (Binop (Var n) Mult e)) \<omega> None"
    hence "red_pure_exps_total ctxt (Some \<omega>) [Var n] \<omega> None"
      by simp
    hence "ctxt, Some \<omega> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      by (auto elim: red_pure_exps_total_singleton)
    thus ?thesis
      by (auto elim: RedVarFailure_case)
  qed
next
  assume "ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  then show "ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  proof (rule RedBinopFailure_case)
    fix v1 v2
    assume "ctxt, Some \<omega> \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
       and "eval_binop_lazy v1 Mult = None"
       and "eval_binop v1 Mult v2 \<noteq> BinopTypeFailure"
    hence V1: "v1 = VPerm p"
      by (auto elim: RedLit_case)
    have "ctxt, Some \<omega> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
      using V1 assms by (simp add: RedVar)
    then show ?thesis
      using \<open>ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure\<close> \<open>eval_binop_lazy v1 Mult = None\<close>
            \<open>eval_binop v1 Mult v2 \<noteq> BinopTypeFailure\<close>
      by (auto intro: RedBinopRightFailure)
  next
    fix v1 v2
    assume "ctxt, Some \<omega> \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
       and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2"
       and "eval_binop v1 Mult v2 = BinopOpFailure"
       and "eval_binop_lazy v1 Mult = None"
    hence "v1 = VPerm p"
      by (auto elim: RedLit_case)
    then show ?thesis
      using assms \<open>ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2\<close> \<open>eval_binop v1 Mult v2 = BinopOpFailure\<close> \<open>eval_binop_lazy v1 Mult = None\<close>
      by (auto intro: RedBinopOpFailure RedVar)
  next
    assume "sub_pure_exp_total (Binop (real_to_expr p) Mult e) \<noteq> []"
       and "red_pure_exps_total ctxt (Some \<omega>) (sub_pure_exp_total (Binop (real_to_expr p) Mult e)) \<omega> None"
    hence "red_pure_exps_total ctxt (Some \<omega>) [real_to_expr p] \<omega> None"
      by simp
    hence "ctxt, Some \<omega> \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      by (auto elim: red_pure_exps_total_singleton)
    thus ?thesis
      using real_to_expr.simps by (auto elim: RedLitFailure_case)
  qed
qed

lemma red_pure_exps_total_append_singleton_failure_iff:
  "red_pure_exps_total ctxt \<omega>_def (es @ [e]) \<omega> None \<longleftrightarrow>
   red_pure_exps_total ctxt \<omega>_def es \<omega> None \<or>
   (\<exists>vs. red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
proof (induction es)
  case Nil
  then show ?case
    by (auto simp: red_exp_list_failure_Nil intro: red_exp_intros elim: red_exp_list_failure_elim)
next
  case (Cons a es)
  show ?case
  proof
    assume H: "red_pure_exps_total ctxt \<omega>_def ((a # es) @ [e]) \<omega> None"
    hence H': "red_pure_exps_total ctxt \<omega>_def (a # (es @ [e])) \<omega> None" by simp
    show "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> None \<or>
          (\<exists>vs. red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
    proof (rule red_exp_list_failure_elim[OF H'])
      fix v e_hd es_tl
      assume Heq: "a # (es @ [e]) = e_hd # es_tl"
         and Hv: "ctxt, \<omega>_def \<turnstile> \<langle>e_hd; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
         and Htl: "red_pure_exps_total ctxt \<omega>_def es_tl \<omega> None"
      from Heq have e_hd_eq: "e_hd = a" and es_tl_eq: "es_tl = es @ [e]" by auto
      from Htl[unfolded es_tl_eq] Cons.IH
      have "red_pure_exps_total ctxt \<omega>_def es \<omega> None \<or>
            (\<exists>vs. red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
        by blast
      then show "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> None \<or>
                 (\<exists>vs. red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
      proof
        assume "red_pure_exps_total ctxt \<omega>_def es \<omega> None"
        thus ?thesis
          using Hv[unfolded e_hd_eq] by (auto intro: red_exp_intros)
      next
        assume "\<exists>vs. red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
        then obtain vs where Hes: "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs)"
                          and Hfail: "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
          by blast
        have "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> (Some (v # vs))"
          using Hv[unfolded e_hd_eq] Hes by (auto intro: red_exp_intros)
        thus ?thesis using Hfail by blast
      qed
    next
      fix e_hd es_tl
      assume Heq: "a # (es @ [e]) = e_hd # es_tl"
         and Hfail: "ctxt, \<omega>_def \<turnstile> \<langle>e_hd; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      from Heq have "e_hd = a" by auto
      with Hfail have "ctxt, \<omega>_def \<turnstile> \<langle>a; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" by simp
      hence "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> None"
        by (auto intro: red_exp_intros)
      thus "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> None \<or>
            (\<exists>vs. red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
        by simp
    qed
  next
    assume "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> None \<or>
            (\<exists>vs. red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
    then show "red_pure_exps_total ctxt \<omega>_def ((a # es) @ [e]) \<omega> None"
    proof (rule disjE)
      assume "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> None"
      thus ?thesis by (rule red_pure_exps_total_append_failure)
    next
      assume "\<exists>vs. red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      then obtain vs where Hs: "red_pure_exps_total ctxt \<omega>_def (a # es) \<omega> (Some vs)"
                        and Hfail: "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
        by blast
      have "red_pure_exps_total ctxt \<omega>_def [e] \<omega> None"
        using Hfail by (auto intro: red_exp_intros)
      with Hs show ?thesis
        using red_pure_exps_total_append_failure_2 by blast
    qed
  qed
qed

lemma red_inhale_star_mult_cong:
  assumes IH1: "\<And>\<omega> res. get_store_total \<omega> n = Some (VPerm p) \<Longrightarrow> 0 < p \<Longrightarrow>
                 red_inhale ctxt R A1' \<omega> res \<longleftrightarrow> red_inhale ctxt R A1'' \<omega> res"
      and IH2: "\<And>\<omega> res. get_store_total \<omega> n = Some (VPerm p) \<Longrightarrow> 0 < p \<Longrightarrow>
                 red_inhale ctxt R A2' \<omega> res \<longleftrightarrow> red_inhale ctxt R A2'' \<omega> res"
      and SV: "get_store_total \<omega> n = Some (VPerm p)"
      and PP: "0 < p"
      and H: "red_inhale ctxt R (Star A1' A2') \<omega> res"
    shows "red_inhale ctxt R (Star A1'' A2'') \<omega> res"
  using H
proof (cases rule: red_inhale.cases)
  case (InhStarNormal \<omega>'')
  have SV'': "get_store_total \<omega>'' n = Some (VPerm p)"
    using red_inhale_store_same[OF InhStarNormal(1), of \<omega>''] SV by simp
  have "red_inhale ctxt R A1'' \<omega> (RNormal \<omega>'')"
    using InhStarNormal(1) IH1[OF SV PP] by blast
  moreover have "red_inhale ctxt R A2'' \<omega>'' res"
    using InhStarNormal(2) IH2[OF SV'' PP] by blast
  ultimately show ?thesis
    by (simp add: red_inhale.InhStarNormal)
next
  case InhStarFailureMagic
  then have "red_inhale ctxt R A1'' \<omega> res"
    using IH1[OF SV PP] by blast
  then show ?thesis
    using InhStarFailureMagic by (simp add: red_inhale.InhStarFailureMagic)
next
  case InhSubExpFailure
  then show ?thesis by simp
qed

lemma red_inhale_var_mult_eq_syntactic_mult:
  assumes StoreVal: "get_store_total \<omega> n = Some (VPerm p)"
      and PermPos: "0 < p"
  shows "red_inhale ctxt R (var_mult n A) \<omega> res \<longleftrightarrow> red_inhale ctxt R (syntactic_mult p A) \<omega> res"
proof -
  have general: "\<And>\<omega> res. get_store_total \<omega> n = Some (VPerm p) \<Longrightarrow> 0 < p \<Longrightarrow>
                  red_inhale ctxt R (var_mult n A) \<omega> res \<longleftrightarrow> red_inhale ctxt R (syntactic_mult p A) \<omega> res"
  proof (induction A arbitrary: \<omega> res)
    case (Atomic x)
    show ?case
    proof (cases x)
      case (Pure e)
      then show ?thesis by simp
    next
      case (Acc e_r f e_p)
      show ?thesis
      proof (cases e_p)
        case Wildcard
        then show ?thesis using Acc Atomic.prems by simp
      next
        case (PureExp e_p')
        have eqp: "\<And>v. (ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) =
                       (ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"
          using binop_var_lit_eq[OF Atomic.prems(1)] .
        have eqfail: "(ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure) =
                      (ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
          using binop_var_lit_eq_fail[OF Atomic.prems(1)] .
        have eqlist: "red_pure_exps_total ctxt (Some \<omega>) ([e_r] @ [Binop (Var n) Mult e_p']) \<omega> None =
                      red_pure_exps_total ctxt (Some \<omega>) ([e_r] @ [Binop (real_to_expr p) Mult e_p']) \<omega> None"
          using red_pure_exps_total_append_singleton_failure_iff[of ctxt "Some \<omega>" "[e_r]"
                  "Binop (Var n) Mult e_p'" \<omega>]
                red_pure_exps_total_append_singleton_failure_iff[of ctxt "Some \<omega>" "[e_r]"
                  "Binop (real_to_expr p) Mult e_p'" \<omega>]
                eqfail
          by blast
        show ?thesis
          using Acc PureExp eqp eqlist
          by (auto elim!: red_inhale.cases intro: red_inhale.intros)
      qed
    next
      case (AccPredicate pred_id e_args e_p)
      show ?thesis
      proof (cases e_p)
        case Wildcard
        then show ?thesis using AccPredicate Atomic.prems by simp
      next
        case (PureExp e_p')
        have eqp: "\<And>v. (ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) =
                       (ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"
          using binop_var_lit_eq[OF Atomic.prems(1)] .
        have eqfail: "(ctxt, Some \<omega> \<turnstile> \<langle>Binop (Var n) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure) =
                      (ctxt, Some \<omega> \<turnstile> \<langle>Binop (real_to_expr p) Mult e_p'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
          using binop_var_lit_eq_fail[OF Atomic.prems(1)] .
        have eqlist: "red_pure_exps_total ctxt (Some \<omega>) (e_args @ [Binop (Var n) Mult e_p']) \<omega> None =
                      red_pure_exps_total ctxt (Some \<omega>) (e_args @ [Binop (real_to_expr p) Mult e_p']) \<omega> None"
          using red_pure_exps_total_append_singleton_failure_iff[of ctxt "Some \<omega>" e_args
                  "Binop (Var n) Mult e_p'" \<omega>]
                red_pure_exps_total_append_singleton_failure_iff[of ctxt "Some \<omega>" e_args
                  "Binop (real_to_expr p) Mult e_p'" \<omega>]
                eqfail
          by blast
        show ?thesis
          using AccPredicate PureExp eqp eqlist
          by (auto elim!: red_inhale.cases intro: red_inhale.intros)
      qed
    qed
  next
    case (Imp e A)
    show ?case
    proof
      assume "red_inhale ctxt R (var_mult n (Imp e A)) \<omega> res"
      hence H: "red_inhale ctxt R (Imp e (var_mult n A)) \<omega> res" by simp
      then show "red_inhale ctxt R (syntactic_mult p (Imp e A)) \<omega> res"
      proof (cases rule: red_inhale.cases)
        case InhImpTrue
        then show ?thesis
          using Imp.IH[OF Imp.prems] by (simp add: red_inhale.InhImpTrue)
      next
        case InhImpFalse
        then show ?thesis by (simp add: red_inhale.InhImpFalse)
      next
        case InhSubExpFailure
        then show ?thesis by (simp add: red_inhale.InhSubExpFailure)
      qed
    next
      assume "red_inhale ctxt R (syntactic_mult p (Imp e A)) \<omega> res"
      hence H: "red_inhale ctxt R (Imp e (syntactic_mult p A)) \<omega> res" by simp
      then show "red_inhale ctxt R (var_mult n (Imp e A)) \<omega> res"
      proof (cases rule: red_inhale.cases)
        case InhImpTrue
        then show ?thesis
          using Imp.IH[OF Imp.prems] by (simp add: red_inhale.InhImpTrue)
      next
        case InhImpFalse
        then show ?thesis by (simp add: red_inhale.InhImpFalse)
      next
        case InhSubExpFailure
        then show ?thesis by (simp add: red_inhale.InhSubExpFailure)
      qed
    qed
  next
    case (Star A1 A2)
    have IH1_sym: "\<And>\<omega> res. get_store_total \<omega> n = Some (VPerm p) \<Longrightarrow> 0 < p \<Longrightarrow>
                    red_inhale ctxt R (syntactic_mult p A1) \<omega> res \<longleftrightarrow> red_inhale ctxt R (var_mult n A1) \<omega> res"
      using Star.IH(1) by blast
    have IH2_sym: "\<And>\<omega> res. get_store_total \<omega> n = Some (VPerm p) \<Longrightarrow> 0 < p \<Longrightarrow>
                    red_inhale ctxt R (syntactic_mult p A2) \<omega> res \<longleftrightarrow> red_inhale ctxt R (var_mult n A2) \<omega> res"
      using Star.IH(2) by blast
    show ?case
    proof
      assume "red_inhale ctxt R (var_mult n (Star A1 A2)) \<omega> res"
      hence H: "red_inhale ctxt R (Star (var_mult n A1) (var_mult n A2)) \<omega> res" by simp
      have "red_inhale ctxt R (Star (syntactic_mult p A1) (syntactic_mult p A2)) \<omega> res"
        using red_inhale_star_mult_cong[OF Star.IH(1) Star.IH(2) Star.prems(1) Star.prems(2) H] .
      thus "red_inhale ctxt R (syntactic_mult p (Star A1 A2)) \<omega> res" by simp
    next
      assume "red_inhale ctxt R (syntactic_mult p (Star A1 A2)) \<omega> res"
      hence H: "red_inhale ctxt R (Star (syntactic_mult p A1) (syntactic_mult p A2)) \<omega> res" by simp
      have "red_inhale ctxt R (Star (var_mult n A1) (var_mult n A2)) \<omega> res"
        using red_inhale_star_mult_cong[OF IH1_sym IH2_sym Star.prems(1) Star.prems(2) H] .
      thus "red_inhale ctxt R (var_mult n (Star A1 A2)) \<omega> res" by simp
    qed
  next
    case (ForAll ty A)
    then show ?case
      using direct_sub_expressions_assertion_empty_no_reduce[of "var_mult n (ForAll ty A)" ctxt R \<omega> res]
            direct_sub_expressions_assertion_empty_no_reduce[of "syntactic_mult p (ForAll ty A)" ctxt R \<omega> res]
      by simp
  next
    case (Exists ty A)
    then show ?case
      using direct_sub_expressions_assertion_empty_no_reduce[of "var_mult n (Exists ty A)" ctxt R \<omega> res]
            direct_sub_expressions_assertion_empty_no_reduce[of "syntactic_mult p (Exists ty A)" ctxt R \<omega> res]
      by simp
  next
    case (ImpureAnd A1 A2)
    then show ?case
      using direct_sub_expressions_assertion_empty_no_reduce[of "var_mult n (ImpureAnd A1 A2)" ctxt R \<omega> res]
            direct_sub_expressions_assertion_empty_no_reduce[of "syntactic_mult p (ImpureAnd A1 A2)" ctxt R \<omega> res]
      by simp
  next
    case (ImpureOr A1 A2)
    then show ?case
      using direct_sub_expressions_assertion_empty_no_reduce[of "var_mult n (ImpureOr A1 A2)" ctxt R \<omega> res]
            direct_sub_expressions_assertion_empty_no_reduce[of "syntactic_mult p (ImpureOr A1 A2)" ctxt R \<omega> res]
      by simp
  next
    case (Wand A1 A2)
    then show ?case
      using direct_sub_expressions_assertion_empty_no_reduce[of "var_mult n (Wand A1 A2)" ctxt R \<omega> res]
            direct_sub_expressions_assertion_empty_no_reduce[of "syntactic_mult p (Wand A1 A2)" ctxt R \<omega> res]
      by simp
  next
    case (CondAssert e A1 A2)
    show ?case
    proof
      assume "red_inhale ctxt R (var_mult n (CondAssert e A1 A2)) \<omega> res"
      hence H: "red_inhale ctxt R (CondAssert e (var_mult n A1) (var_mult n A2)) \<omega> res" by simp
      then show "red_inhale ctxt R (syntactic_mult p (CondAssert e A1 A2)) \<omega> res"
      proof (cases rule: red_inhale.cases)
        case InhCondAssertTrue
        then show ?thesis
          using CondAssert.IH(1)[OF CondAssert.prems] by (simp add: red_inhale.InhCondAssertTrue)
      next
        case InhCondAssertFalse
        then show ?thesis
          using CondAssert.IH(2)[OF CondAssert.prems] by (simp add: red_inhale.InhCondAssertFalse)
      next
        case InhSubExpFailure
        then show ?thesis by (simp add: red_inhale.InhSubExpFailure)
      qed
    next
      assume "red_inhale ctxt R (syntactic_mult p (CondAssert e A1 A2)) \<omega> res"
      hence H: "red_inhale ctxt R (CondAssert e (syntactic_mult p A1) (syntactic_mult p A2)) \<omega> res" by simp
      then show "red_inhale ctxt R (var_mult n (CondAssert e A1 A2)) \<omega> res"
      proof (cases rule: red_inhale.cases)
        case InhCondAssertTrue
        then show ?thesis
          using CondAssert.IH(1)[OF CondAssert.prems] by (simp add: red_inhale.InhCondAssertTrue)
      next
        case InhCondAssertFalse
        then show ?thesis
          using CondAssert.IH(2)[OF CondAssert.prems] by (simp add: red_inhale.InhCondAssertFalse)
      next
        case InhSubExpFailure
        then show ?thesis by (simp add: red_inhale.InhSubExpFailure)
      qed
    qed
  qed
  from general[OF StoreVal PermPos] show ?thesis .
qed

end
