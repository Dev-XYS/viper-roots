theory TotalSemanticsHelper
  imports TotalExpressions TotalInhaleExhale
begin


subsection \<open>Elimination and introduction rules\<close>


subsubsection \<open>Inhale\<close>

lemma inh_imp_failure:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "red_inhale ctxt R (Imp e A) \<omega> RFailure"
  using assms InhSubExpFailure[where ?A="Imp e A"] RedExpListFailure
  by fastforce

lemma inh_cond_assert_failure:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "red_inhale ctxt R (CondAssert e A B) \<omega> RFailure"
  using assms InhSubExpFailure[where ?A="CondAssert e A B"] RedExpListFailure
  by fastforce

lemma inh_pure_normal:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
  shows "red_inhale ctxt R (Atomic (Pure e)) \<omega> (RNormal \<omega>)"
  using assms InhPure
  by force

lemma inh_pure_magic:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  shows "red_inhale ctxt R (Atomic (Pure e)) \<omega> RMagic"
  using assms InhPure
  by force

lemmas red_inhale_intros =
  InhAcc
  InhAccPred
  InhAccWildcard
  InhAccPredWildcard
  inh_pure_normal
  inh_pure_magic
  InhStarNormal
  InhStarFailureMagic
  InhImpTrue
  InhImpFalse
  InhCondAssertTrue
  InhCondAssertFalse
  InhSubExpFailure

inductive_cases InhPure_case: "red_inhale ctxt R (Atomic (Pure e)) \<omega> res"
inductive_cases InhAcc_case: "red_inhale ctxt R (Atomic (Acc e_r f perm)) \<omega> res"
inductive_cases InhAccPerm_case: "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega> res"
inductive_cases InhAccWildcard_case: "red_inhale ctxt R (Atomic (Acc e_r f Wildcard)) \<omega> res"
inductive_cases InhAccPredPerm_case: "red_inhale ctxt R (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> res"
inductive_cases InhAccPredWildcard_case: "red_inhale ctxt R (Atomic (AccPredicate pid e_args Wildcard)) \<omega> res"
inductive_cases InhStar_case: "red_inhale ctxt R (A && B) \<omega> res"
inductive_cases InhImp_case: "red_inhale ctxt R (Imp e A) \<omega> res"
inductive_cases InhCondAssert: "red_inhale ctxt R (CondAssert e A B) \<omega> res"

lemmas red_inhale_elims =
  InhStar_case
  InhImp_case
  InhPure_case


subsubsection \<open>Exhale\<close>

inductive_cases ExhAcc_case: "red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f perm)) \<omega> (RNormal \<omega>')"
inductive_cases ExhAccPred_case: "red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pid e_args perm)) \<omega> (RNormal \<omega>')"
inductive_cases ExhAccPredWildcard_case: "red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pid e_args Wildcard)) \<omega> (RNormal \<omega>')"
inductive_cases ExhImp_case: "red_exhale ctxt R \<omega>0 (Imp e A) \<omega> (RNormal \<omega>')"
inductive_cases ExhStar_case: "red_exhale ctxt R \<omega>0 (A && B) m_pm res"

lemma ExhPure_case:
  assumes "red_exhale ctxt R \<omega>0 (Atomic (Pure e)) \<omega> res"
      and "\<And>b. ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<Longrightarrow> res = (exh_if_total b \<omega>) \<Longrightarrow> P"
      and "ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> res = RFailure \<Longrightarrow> P"
    shows "P"
  using assms
  by (cases) (auto elim: red_pure_exp_total_elims)


subsubsection \<open>Unfold\<close>

(* inductive_cases UnfoldRel_case: "unfold_rel ctxt pred_id vs q \<phi> \<phi>'" *)


end
