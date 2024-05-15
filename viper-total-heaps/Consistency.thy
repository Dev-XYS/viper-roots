theory Consistency
  imports TotalExpressions
begin

section \<open>Definition\<close>

inductive total_heap_consistent_unfold_n :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> nat \<Rightarrow> bool"
  for ctxt :: "'a total_context"
  where
  Zero: "\<lbrakk>
    valid_heap_mask (get_mh_total \<phi>)
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_unfold_n ctxt \<phi> 0"
| UnfoldStep: "\<lbrakk>
    \<And> pred_id vs q \<phi>'. q = get_mp_total \<phi> (pred_id, vs) \<Longrightarrow> q > 0 \<Longrightarrow>
      unfold_rel ctxt (\<lambda>_. True) pred_id vs q \<phi> \<phi>' \<and> valid_heap_mask (get_mh_total \<phi>') \<and>
      \<comment> \<open>Do we need \<^term>\<open>valid_heap_mask\<close> above? It should be equivalent without it?
         Is it easy to prove? Which one is easier to use? Same questions apply to the other definition.\<close>
      total_heap_consistent_unfold_n ctxt \<phi>' n
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_unfold_n ctxt \<phi> (Suc n)"

definition total_heap_consistent :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> bool" where
  "total_heap_consistent ctxt \<phi> \<equiv> \<forall> n. total_heap_consistent_unfold_n ctxt \<phi> n"

inductive total_heap_consistent_amount_unfold_n :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> nat \<Rightarrow> bool"
  for ctxt :: "'a total_context"
  where
  Zero: "\<lbrakk>
    valid_heap_mask (get_mh_total \<phi>)
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_amount_unfold_n ctxt \<phi> 0"
| UnfoldStep: "\<lbrakk>
    \<And> pred_id vs q \<phi>'. q \<le> get_mp_total \<phi> (pred_id, vs) \<Longrightarrow> q > 0 \<Longrightarrow>
      unfold_rel ctxt (\<lambda>_. True) pred_id vs q \<phi> \<phi>' \<and> valid_heap_mask (get_mh_total \<phi>') \<and>
      total_heap_consistent_unfold_n ctxt \<phi>' n
  \<rbrakk> \<Longrightarrow>
    total_heap_consistent_amount_unfold_n ctxt \<phi> (Suc n)"

definition total_heap_consistent_amount :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> bool" where
  "total_heap_consistent_amount ctxt \<phi> \<equiv> \<forall> n. total_heap_consistent_amount_unfold_n ctxt \<phi> n"


section \<open>Auxiliary Lemmas\<close>

lemma forall_implies:
  assumes "\<And> n. P n \<Longrightarrow> Q n"
  shows "(\<forall> n. P n) \<longrightarrow> (\<forall> n. Q n)"
  by (simp add: assms)

lemma iff_intro:
  assumes "P \<longrightarrow> Q" and "Q \<longrightarrow> P"
  shows "P \<longleftrightarrow> Q"
  using assms by blast


section \<open>Theorems\<close>

lemma "total_heap_consistent ctxt \<phi> \<longleftrightarrow> total_heap_consistent_amount ctxt \<phi>" (is "?LHS \<longleftrightarrow> ?RHS")
proof (rule iff_intro)
  show "?LHS \<longrightarrow> ?RHS"
  proof (simp add: total_heap_consistent_def total_heap_consistent_amount_def, rule forall_implies)
    fix n show "total_heap_consistent_unfold_n ctxt \<phi> n \<Longrightarrow> total_heap_consistent_amount_unfold_n ctxt \<phi> n"
    proof (induct n arbitrary: \<phi>)
      case 0 then show ?case
        using total_heap_consistent_amount_unfold_n.Zero total_heap_consistent_unfold_n.cases by blast
    next
      case IH: (Suc n)
      show ?case sorry
      (* proof (simp add: total_heap_consistent_amount_unfold_n.simps, standard,
             (rule allI)+, standard, standard)
        fix pred_id vs q
        assume "q \<le> get_mp_total \<phi> (pred_id, vs)" and "q > 0" *)
    qed
  qed
next
  show "?RHS \<longrightarrow> ?LHS" sorry
qed

end
