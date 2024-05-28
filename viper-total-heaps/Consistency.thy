theory Consistency
  imports TotalExpressions TotalSemantics
begin

section \<open>Definition\<close>

inductive total_heap_consistent_unfold_n_all :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> nat \<Rightarrow> bool"
  for ctxt :: "'a total_context"
  where
  Zero: "\<lbrakk>
    valid_heap_mask (get_mh_total \<phi>)
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_unfold_n_all ctxt \<phi> 0"
| UnfoldStep: "\<lbrakk>
    \<And> pred_id vs q \<phi>'. q = get_mp_total \<phi> (pred_id, vs) \<Longrightarrow> q > 0 \<Longrightarrow>
      unfold_rel ctxt (\<lambda>_. True) pred_id vs q \<phi> \<phi>' \<Longrightarrow>
      \<comment> \<open>Do we need \<^term>\<open>valid_heap_mask\<close> above? It should be equivalent without it?
         Is it easy to prove? Which one is easier to use? Same questions apply to the other definition.\<close>
      total_heap_consistent_unfold_n_all ctxt \<phi>' n
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_unfold_n_all ctxt \<phi> (Suc n)"

definition total_heap_consistent_all :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> bool" where
  "total_heap_consistent_all ctxt \<phi> \<equiv> \<forall> n. total_heap_consistent_unfold_n_all ctxt \<phi> n"

inductive total_heap_consistent_unfold_n :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> nat \<Rightarrow> bool"
  for ctxt :: "'a total_context"
  where
  Zero: "\<lbrakk>
    valid_heap_mask (get_mh_total \<phi>)
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_unfold_n ctxt \<phi> 0"
| UnfoldStep: "\<lbrakk>
    \<And> pred_id vs q \<phi>'. q \<le> get_mp_total \<phi> (pred_id, vs) \<Longrightarrow> q > 0 \<Longrightarrow>
      unfold_rel ctxt (\<lambda>_. True) pred_id vs q \<phi> \<phi>' \<Longrightarrow>
      total_heap_consistent_unfold_n ctxt \<phi>' n
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_unfold_n ctxt \<phi> (Suc n)"

inductive_cases UnfoldStep_cases: "total_heap_consistent_unfold_n ctxt \<phi> (Suc n)"

definition total_heap_consistent :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> bool" where
  "total_heap_consistent ctxt \<phi> \<equiv> \<forall> n. total_heap_consistent_unfold_n ctxt \<phi> n"


section \<open>Auxiliary Lemmas\<close>

lemma forall_implies:
  assumes "\<And> n. P n \<Longrightarrow> Q n"
    shows "(\<forall> n. P n) \<longrightarrow> (\<forall> n. Q n)"
  by (simp add: assms)

lemma iff_intro:
  assumes "P \<longrightarrow> Q" and "Q \<longrightarrow> P"
    shows "P \<longleftrightarrow> Q"
  using assms by blast

lemma field_update_preserves_mask:
  assumes "\<omega>' = update_hh_loc_total_full \<omega> (addr,f) v"
    shows "get_mh_total (get_total_full \<omega>) = get_mh_total (get_total_full \<omega>')"
  using assms update_hh_loc_total_full.simps by fastforce

lemma inhale_perm_single_weaker_consistency:
  assumes "\<And>x. R x \<Longrightarrow> R' x"
    shows "inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_preal p)) \<subseteq> inhale_perm_single R' \<omega> (the_address r, f) (Some (Abs_preal p))"
  by (simp add: Collect_mono_iff assms inhale_perm_single_def)

lemma th_result_rel_weaker_consistency:
  assumes "th_result_rel b\<^sub>1 b\<^sub>2 W (RNormal \<omega>)"
      and "b\<^sub>2 \<Longrightarrow> b\<^sub>2'"
      and "W \<subseteq> W'"
    shows "th_result_rel b\<^sub>1 b\<^sub>2' W' (RNormal \<omega>)"
  by (metis THResultNormal_alt assms subset_iff th_result_rel_normal)

lemma red_pure_exp_weaker_consistency:
  assumes "ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t res"
    shows "ctxt, R', \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t res"
  oops

lemma red_inhale_weaker_consistency:
  assumes "red_inhale ctxt R A \<omega> (RNormal \<omega>')"
      and "\<And>x. R x \<Longrightarrow> R' x"
    shows "red_inhale ctxt R' A \<omega> (RNormal \<omega>')"
  apply (rule red_inhale.cases[of ctxt R A \<omega> "RNormal \<omega>'"])
              apply (simp add: assms)
             apply auto
proof -
  fix e_r r e_p p f
  assume "A = Atomic (Acc e_r f (PureExp e_p))"
     and ref: "ctxt, R, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
     and perm: "ctxt, R, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
     and res_original: "th_result_rel (0 \<le> p)
            ((if r = Null then {\<omega>} else inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_preal p))) \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null))
            (if r = Null then {\<omega>} else inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_preal p)))
            (RNormal \<omega>')"
  define W where W: "W = (if r = Null then {\<omega>} else inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_preal p)))"
  hence res: "th_result_rel (0 \<le> p) (W \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W (RNormal \<omega>')" using res_original by blast
  define W' where W': "W' = (if r = Null then {\<omega>} else inhale_perm_single R' \<omega> (the_address r, f) (Some (Abs_preal p)))"
  hence "W \<subseteq> W'" using inhale_perm_single_weaker_consistency by (metis W assms(2) order_refl)
  hence res': "th_result_rel (0 \<le> p) (W' \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W' (RNormal \<omega>')"
    by (metis (mono_tags, lifting) res subset_empty th_result_rel_weaker_consistency)
  show "red_inhale ctxt R' (Atomic (Acc e_r f (PureExp e_p))) \<omega> (RNormal \<omega>')"
  proof (rule InhAcc)
    show "ctxt, R', Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" sorry
    show "ctxt, R', Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" sorry
    from W' show "W' = (if r = Null then {\<omega>} else inhale_perm_single R' \<omega> (the_address r, f) (Some (Abs_preal p)))" by blast
    from res' show "th_result_rel (0 \<le> p) (W' \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W' (RNormal \<omega>')" by blast
  qed
  oops

lemma fold_unfold_is_identity:
  assumes "fold_rel ctxt R pred_id v_args (Abs_preal v_p) \<omega> (RNormal \<omega>')"
  shows "unfold_rel ctxt R pred_id v_args (Abs_preal v_p) (get_total_full \<omega>') (get_total_full \<omega>)"
  sorry


section \<open>Theorems\<close>

lemma "total_heap_consistent_all ctxt \<phi> \<longleftrightarrow> total_heap_consistent ctxt \<phi>" (is "?LHS \<longleftrightarrow> ?RHS")
proof (rule iff_intro)
  show "?LHS \<longrightarrow> ?RHS"
  proof (simp add: total_heap_consistent_all_def total_heap_consistent_def, rule forall_implies)
    fix n show "total_heap_consistent_unfold_n_all ctxt \<phi> n \<Longrightarrow> total_heap_consistent_unfold_n ctxt \<phi> n"
    proof (induct n arbitrary: \<phi>)
      case 0 then show ?case
        using total_heap_consistent_unfold_n.Zero total_heap_consistent_unfold_n_all.cases by blast
    next
      case IH: (Suc n)
      show ?case sorry
    qed
  qed
next
  show "?RHS \<longrightarrow> ?LHS" sorry
qed


section \<open>Preservation of State Consistency\<close>

lemma assignment_preserves_state_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent ctxt \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (LocalAssign x e) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent ctxt \<phi>'"
proof -
  obtain v where "\<omega>' = update_var_total \<omega> x v" using assms(3) red_stmt_total.simps by blast \<comment> \<open>Quite slow. Why?\<close>
  hence "\<phi> = \<phi>'" using assms(1,4) by force
  thus ?thesis using assms(2) by auto
qed

lemma unfold_preserves_state_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent ctxt \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent ctxt \<phi>'"
proof -
  obtain v_args v_p where
    res: "th_result_rel (0 < v_p \<and> v_p \<le> Rep_preal (get_mp_total (get_total_full \<omega>) (pred_id, v_args))) True
      {\<omega>'. \<exists>\<phi>'. \<omega>' = \<omega>\<lparr>get_total_full := \<phi>'\<rparr> \<and> unfold_rel ctxt R pred_id v_args (Abs_preal v_p) (get_total_full \<omega>) \<phi>' \<and> R \<omega>'}
      (RNormal \<omega>')"
    using assms(3) RedUnfold_case by blast
  define W' where "W' = {\<omega>'. \<exists>\<phi>'. \<omega>' = \<omega>\<lparr>get_total_full := \<phi>'\<rparr> \<and> unfold_rel ctxt R pred_id v_args (Abs_preal v_p) (get_total_full \<omega>) \<phi>' \<and> R \<omega>'}"
  hence "\<omega>' \<in> W'" using res th_result_rel_normal by blast
  hence "unfold_rel ctxt R pred_id v_args (Abs_preal v_p) (get_total_full \<omega>) \<phi>'" using W'_def assms(4) by force
  hence unfold: "unfold_rel ctxt (\<lambda>_. True) pred_id v_args (Abs_preal v_p) (get_total_full \<omega>) \<phi>'"
    apply (rule UnfoldRel_case)
    by (fastforce intro!: UnfoldRelStep dest: red_inhale_weaker_consistency[where ?R'="\<lambda>_. True"])
  show "total_heap_consistent ctxt \<phi>'"
  proof (simp add: total_heap_consistent_def, standard)
    fix n
    from assms(2) have "total_heap_consistent_unfold_n ctxt \<phi> (Suc n)" using total_heap_consistent_def by blast
    moreover from res have "0 < v_p \<and> v_p \<le> Rep_preal (get_mp_total \<phi> (pred_id, v_args))"
      using th_result_rel_normal assms(1) by blast
    moreover note unfold
    ultimately show "total_heap_consistent_unfold_n ctxt \<phi>' n" using UnfoldStep_cases
      sorry
  qed
qed

lemma fold_preserves_state_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent ctxt \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Fold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent ctxt \<phi>'"
proof (simp add: total_heap_consistent_def, standard)
  from assms(3) obtain v_args v_p where
    "red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args)" and
    "ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    "fold_rel ctxt R pred_id v_args (Abs_preal v_p) \<omega> (RNormal \<omega>')"
    using RedFold_case by blast
  hence unfold: "unfold_rel ctxt R pred_id v_args (Abs_preal v_p) (get_total_full \<omega>') (get_total_full \<omega>)"
    using fold_unfold_is_identity assms(1,4) by blast
  fix n
  show "total_heap_consistent_unfold_n ctxt \<phi>' n"
  proof -
    from assms(2) have "total_heap_consistent_unfold_n ctxt \<phi> (Suc n)"
      by (simp add: Consistency.total_heap_consistent_def)
    oops

lemma field_assignment_preserves_state_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent ctxt \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (FieldAssign e_r f e) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent ctxt \<phi>'"
  sorry

end
