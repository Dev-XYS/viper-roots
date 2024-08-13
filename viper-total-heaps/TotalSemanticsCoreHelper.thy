theory TotalSemanticsCoreHelper
  imports TotalSemanticsCore
begin

subsection \<open>Elimination and introduction rules\<close>

(* lemmas red_exp_inhale_unfold_intros = red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.intros *)

lemmas red_exp_intros = red_pure_exp_total_red_pure_exps_total.intros

subsubsection \<open>Expression evaluation and well-definedness\<close>

lemma RedField_no_def_normalI:
  assumes "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
      and "get_hh_total_full \<omega> (a, f) = v"
    shows "ctxt, None \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
proof -
  let ?res = "(if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) (None :: ('a full_total_state) option)) then Val v else VFailure)"

  have "ctxt, None \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t ?res"
    apply (rule RedField)
    using assms
    by auto

  thus ?thesis
    by simp
qed

lemma RedField_def_normalI:
  assumes "ctxt, Some \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
      and "get_hh_total_full \<omega> (a, f) = v"
      and "(a,f) \<in> get_valid_locs \<omega>_def"
    shows "ctxt, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
proof -
  let ?res = "(if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) (Some \<omega>_def)) then Val v else VFailure)"

  have "ctxt, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t ?res"
    apply (rule RedField)
    using assms
    by auto

  thus ?thesis
    using assms
    by simp
qed

lemma RedField_def_failureI:
  assumes "ctxt, Some \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
      and "get_hh_total_full \<omega> (a, f) = v"
      and "(a,f) \<notin> get_valid_locs \<omega>_def"
    shows "ctxt, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
proof -
  let ?res = "(if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) (Some \<omega>_def)) then Val v else VFailure)"

  have "ctxt, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t ?res"
    apply (rule RedField)
    using assms
    by auto

  thus ?thesis
    using assms
    by simp
qed

inductive_cases RedVar_case: "ctxt, \<omega>_def \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

lemma RedLit_case:
  assumes
    "ctxt, \<omega>_def \<turnstile> \<langle>ELit l; \<omega>\<rangle> [\<Down>]\<^sub>t v" and
    "v = Val (val_of_lit l) \<Longrightarrow> P"
  shows P
  using assms
  by (cases) auto

lemma RedFieldNormal_case:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
          "\<And>a. ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<Longrightarrow>
           (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) \<omega>_def) \<Longrightarrow>
           get_hh_total_full \<omega> (a, f) = v \<Longrightarrow>
             P"
        shows P
  using assms
  by cases (metis extended_val.distinct(1) extended_val.inject)

inductive_cases RedUnop_case: "ctxt, \<omega>_def \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"
inductive_cases RedBinop_case: "ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
inductive_cases RedFunApp_case: "ctxt, \<omega>_def \<turnstile> \<langle>FunApp fname es; \<omega>\<rangle> [\<Down>]\<^sub>t res"

inductive_cases RedExpList_case: "red_pure_exps_total ctxt LH es \<omega> (Some vs)"
inductive_cases RedExpListFailure_case: "red_pure_exps_total ctxt LH es \<omega> None"
inductive_cases RedExpListGeneral_case: "red_pure_exps_total ctxt LH es \<omega> res"

lemma red_exp_list_normal_elim:
  assumes
     "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs)" and
     "(\<And>vs_hd vs_tl e_hd es_tl.
        es = e_hd # es_tl \<Longrightarrow>
        vs = vs_hd # vs_tl \<Longrightarrow>
        ctxt, \<omega>_def \<turnstile> \<langle>e_hd;\<omega>\<rangle> [\<Down>]\<^sub>t Val vs_hd \<Longrightarrow> red_pure_exps_total ctxt \<omega>_def es_tl \<omega> (Some vs_tl) \<Longrightarrow> P)" and
     "es = [] \<Longrightarrow> vs = [] \<Longrightarrow> P"
   shows "P"
  using assms
proof cases
  case (RedExpListCons e v es' res)
  from this obtain vs' where "res = Some vs'" and "vs = v#vs'"
    by (metis map_option_eq_Some)
  with RedExpListCons assms(2)[OF \<open>es = e#es'\<close> \<open>vs = _\<close> ]  show ?thesis
    by blast
next
  case RedExpListNil
  then show ?thesis using assms by auto
qed

lemma red_exp_list_failure_Nil:
  assumes "red_pure_exps_total ctxt_vpr \<omega>_def [] \<omega> res"
  shows "res = Some []"
  using assms
  by cases

lemma red_exp_list_failure_elim:
  assumes
     "red_pure_exps_total ctxt \<omega>_def es \<omega> None" and
     "(\<And>v e_hd es_tl.
        es = e_hd # es_tl \<Longrightarrow>
        ctxt, \<omega>_def \<turnstile> \<langle>e_hd;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<Longrightarrow>
        es_tl \<noteq> [] \<Longrightarrow>
        red_pure_exps_total ctxt \<omega>_def es_tl \<omega> None \<Longrightarrow> P)" and
     "(\<And>e_hd es_tl.
        es = e_hd # es_tl \<Longrightarrow>
        ctxt, \<omega>_def \<turnstile> \<langle>e_hd;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P)"
   shows "P"
  using assms
  by (cases) (auto elim: RedExpListFailure_case)

lemma red_exp_list_failure_nth:
  assumes "red_pure_exps_total ctxt \<omega>_def es \<omega> None" and
          "es \<noteq> []"
  shows "\<exists>i. i < length es \<and> ctxt, \<omega>_def \<turnstile> \<langle>es ! i;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  using assms
proof (induction es)
  case Nil
  then show ?case by simp \<comment>\<open>contradiction\<close>
next
  case (Cons a es)
  thus ?case
    by (fastforce elim: red_exp_list_failure_elim dest!: Cons.IH)
qed

inductive_cases RedPerm_case: "ctxt, \<omega>_def \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

lemma red_pure_exps_total_singleton:
  assumes "red_pure_exps_total ctxt \<omega>_def [e] \<omega> res" and
          "\<And>v. res = Some [v] \<and> (ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<Longrightarrow> P" and
          "res = None \<Longrightarrow> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P"
  shows P
  apply (rule RedExpListGeneral_case[OF assms(1)])
  using RedExpListGeneral_case assms(2) apply blast
   apply (simp add: assms(3))
  apply simp
  done

lemmas red_pure_exp_total_elims =
  RedLit_case RedVar_case
  RedUnop_case RedBinop_case RedFunApp_case
  red_exp_list_normal_elim red_exp_list_failure_elim

lemma red_pure_exps_total_append_failure:
  assumes "red_pure_exps_total ctxt \<omega>_def es \<omega> None"
  shows "red_pure_exps_total ctxt \<omega>_def (es@es') \<omega> None"
  using assms
proof (induction es)
  case Nil
  then show ?case
    using red_exp_list_failure_Nil
    by blast
next
  case (Cons e es)
  then show ?case
    by (auto elim: red_exp_list_failure_elim intro: red_exp_intros)
qed

lemma red_pure_exps_total_append_failure_2:
  assumes "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs)"
      and "red_pure_exps_total ctxt \<omega>_def es' \<omega> None"
    shows "red_pure_exps_total ctxt \<omega>_def (es@es') \<omega> None"
  using assms
proof (induction es arbitrary: vs)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  from this obtain v vs_tl where
     "vs = v#vs_tl" and
     RedE: "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
     "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs_tl)"
  by (auto elim: red_pure_exp_total_elims)

  then have "red_pure_exps_total ctxt \<omega>_def (es @ es') \<omega> None"
    using Cons
    by blast

  thus ?case
    using RedE
    by (auto intro: red_exp_intros)
qed

subsubsection \<open>Inhale\<close>

lemma inh_imp_failure:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "red_inhale ctxt (Imp e A) \<omega> RFailure"
  using assms InhSubExpFailure[where ?A="Imp e A"] RedExpListFailure
  by fastforce

lemma inh_cond_assert_failure:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "red_inhale ctxt (CondAssert e A B) \<omega> RFailure"
  using assms InhSubExpFailure[where ?A="CondAssert e A B"] RedExpListFailure
  by fastforce

lemma inh_pure_normal:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
  shows "red_inhale ctxt (Atomic (Pure e)) \<omega> (RNormal \<omega>)"
  using assms InhPure
  by force

lemma inh_pure_magic:
  assumes "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  shows "red_inhale ctxt (Atomic (Pure e)) \<omega> RMagic"
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

inductive_cases InhStar_case: "red_inhale ctxt (A && B) \<omega> res"
inductive_cases InhImp_case: "red_inhale ctxt (Imp e A) \<omega> res"
inductive_cases InhPure_case: "red_inhale ctxt (Atomic (Pure e)) \<omega> res"
thm InhPure_case

lemmas red_inhale_elims =
  InhStar_case
  InhImp_case
  InhPure_case

subsubsection \<open>Unfold\<close>

(* inductive_cases UnfoldRel_case: "unfold_rel ctxt pred_id vs q \<phi> \<phi>'" *)


subsection \<open>Ported from TotalExpressions.thy\<close>

\<comment> \<open>Do we need \<^term>\<open>StateCons\<close> here?\<close>

definition assertion_framing_state :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where
    "assertion_framing_state ctxt StateCons A \<omega> \<equiv>
      \<forall> res. red_inhale ctxt A \<omega> res \<longrightarrow> res \<noteq> RFailure"


end
