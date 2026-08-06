theory FoldStmtRelKF
imports TotalViperSimulation.PredicateRel TotalViperSimulation.BoogieSyntaxBasedProperties
begin

subsection \<open>Preservation of known-folded witnesses across a fold\<close>

text \<open>Elimination-direction counterpart of \<^const>\<open>contains_heap_loc\<close>/\<^const>\<open>pred_folds_perm\<close>'s
      existing introduction lemmas \<open>*_plus_l\<close>/\<open>*_plus_r\<close> (\<open>Simulation/KnownFolded.thy\<close>): a witness
      for a sum \<open>nm1 + nm2\<close> must already live entirely within \<open>nm1\<close> or entirely within \<open>nm2\<close>.\<close>

lemma add_masks_pos_elim:
  fixes \<pi>1 \<pi>2 :: "'b \<Rightarrow> preal"
  assumes "add_masks \<pi>1 \<pi>2 hl > (0::preal)"
  shows "\<pi>1 hl > 0 \<or> \<pi>2 hl > 0"
proof (rule ccontr)
  assume "\<not> (\<pi>1 hl > 0 \<or> \<pi>2 hl > 0)"
  hence "\<pi>1 hl \<le> 0" and "\<pi>2 hl \<le> 0"
    by auto
  hence "\<pi>1 hl = 0" and "\<pi>2 hl = 0"
    using all_pos order_antisym by blast+
  hence "add_masks \<pi>1 \<pi>2 hl = 0"
    unfolding add_masks_def
    by simp
  thus False
    using assms
    by simp
qed

lemma pfun_comb_cases:
  assumes "(f +\<lparr>c\<rparr>+ g) x = Some v"
  obtains
    (OnlyLeft) v1 where "f x = Some v1" and "g x = None" and "v = v1"
  | (OnlyRight) v2 where "f x = None" and "g x = Some v2" and "v = v2"
  | (Both) v1 v2 where "f x = Some v1" and "g x = Some v2" and "v = c v1 v2"
  using assms
  unfolding pfun_comb_def
  by (cases "f x"; cases "g x"; simp add: combine_options_def)

lemma contains_heap_loc_plus_elim:
  assumes "contains_heap_loc l (nm1 + nm2)"
  shows "contains_heap_loc l nm1 \<or> contains_heap_loc l nm2"
  using assms
proof (induction "nm1 + nm2" arbitrary: nm1 nm2 rule: contains_heap_loc.induct)
  case (ContainsLocDirect)
  have step1: "add_masks (get_mh_nm nm1) (get_mh_nm nm2) l > (0::preal)"
    using ContainsLocDirect.hyps
    unfolding plus_nested_mask_def
    by (simp only: get_mh_nm__merge)
  have step2: "get_mh_nm nm1 l > (0::preal) \<or> get_mh_nm nm2 l > 0"
    using add_masks_pos_elim[OF step1]
    by blast
  from step2 show ?case
  proof
    assume "get_mh_nm nm1 l > (0::preal)"
    thus ?thesis using contains_heap_loc.ContainsLocDirect[of nm1] by blast
  next
    assume "get_mh_nm nm2 l > (0::preal)"
    thus ?thesis using contains_heap_loc.ContainsLocDirect[of nm2] by blast
  qed
next
  case (ContainsLocNested lp p\<^sub>x nm')
  from ContainsLocNested.hyps(1)
  have fnm_eq: "get_fnm_nm (nm1 + nm2) lp = Some (p\<^sub>x, nm')" .
  obtain mh\<^sub>1 fnm\<^sub>1 where nm1_eq: "nm1 = NM mh\<^sub>1 fnm\<^sub>1" using nested_mask.exhaust by blast
  obtain mh\<^sub>2 fnm\<^sub>2 where nm2_eq: "nm2 = NM mh\<^sub>2 fnm\<^sub>2" using nested_mask.exhaust by blast
  from fnm_eq[unfolded nm1_eq nm2_eq plus_nested_mask_def nested_mask_merge.simps get_fnm_nm.simps]
  have comb: "(fnm\<^sub>1 +\<lparr>\<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2))\<rparr>+ fnm\<^sub>2) lp = Some (p\<^sub>x, nm')" .
  show ?case
  proof (rule pfun_comb_cases[OF comb])
    fix v1
    assume h1: "fnm\<^sub>1 lp = Some v1" and "fnm\<^sub>2 lp = None" and hv: "(p\<^sub>x, nm') = v1"
    obtain p\<^sub>1 nm\<^sub>1' where v1_eq: "v1 = (p\<^sub>1, nm\<^sub>1')" using prod.exhaust by blast
    have "contains_heap_loc l nm1"
      apply (rule contains_heap_loc.ContainsLocNested[of nm1 lp p\<^sub>1 nm\<^sub>1'])
      using h1 v1_eq nm1_eq
       apply simp
      using ContainsLocNested.hyps(2) hv v1_eq
      by simp
    thus ?thesis by blast
  next
    fix v2
    assume "fnm\<^sub>1 lp = None" and h2: "fnm\<^sub>2 lp = Some v2" and hv: "(p\<^sub>x, nm') = v2"
    obtain p\<^sub>2 nm\<^sub>2' where v2_eq: "v2 = (p\<^sub>2, nm\<^sub>2')" using prod.exhaust by blast
    have "contains_heap_loc l nm2"
      apply (rule contains_heap_loc.ContainsLocNested[of nm2 lp p\<^sub>2 nm\<^sub>2'])
      using h2 v2_eq nm2_eq
       apply simp
      using ContainsLocNested.hyps(2) hv v2_eq
      by simp
    thus ?thesis by blast
  next
    fix v1 v2
    assume h1: "fnm\<^sub>1 lp = Some v1" and h2: "fnm\<^sub>2 lp = Some v2"
       and hv: "(p\<^sub>x, nm') = (fst v1 + fst v2, nested_mask_merge (snd v1) (snd v2))"
    obtain p\<^sub>1 nm\<^sub>1' where v1_eq: "v1 = (p\<^sub>1, nm\<^sub>1')" using prod.exhaust by blast
    obtain p\<^sub>2 nm\<^sub>2' where v2_eq: "v2 = (p\<^sub>2, nm\<^sub>2')" using prod.exhaust by blast
    have nm'_eq: "nm' = nm\<^sub>1' + nm\<^sub>2'"
      using hv v1_eq v2_eq
      unfolding plus_nested_mask_def
      by simp
    have "contains_heap_loc l nm\<^sub>1' \<or> contains_heap_loc l nm\<^sub>2'"
      using ContainsLocNested.hyps(3)[OF nm'_eq]
      by blast
    thus ?thesis
    proof
      assume "contains_heap_loc l nm\<^sub>1'"
      hence "contains_heap_loc l nm1"
        using contains_heap_loc.ContainsLocNested[of nm1 lp p\<^sub>1 nm\<^sub>1' l] h1 v1_eq nm1_eq
        by simp
      thus ?thesis by blast
    next
      assume "contains_heap_loc l nm\<^sub>2'"
      hence "contains_heap_loc l nm2"
        using contains_heap_loc.ContainsLocNested[of nm2 lp p\<^sub>2 nm\<^sub>2' l] h2 v2_eq nm2_eq
        by simp
      thus ?thesis by blast
    qed
  qed
qed

lemma pred_folds_perm_plus_elim:
  assumes "pred_folds_perm lp l (nm1 + nm2)"
  shows "pred_folds_perm lp l nm1 \<or> pred_folds_perm lp l nm2"
  using assms
proof (induction "nm1 + nm2" arbitrary: nm1 nm2 rule: pred_folds_perm.induct)
  case (ContainsPermDirect p\<^sub>x nm')
  from ContainsPermDirect.hyps(1)
  have fnm_eq: "get_fnm_nm (nm1 + nm2) lp = Some (p\<^sub>x, nm')" .
  obtain mh\<^sub>1 fnm\<^sub>1 where nm1_eq: "nm1 = NM mh\<^sub>1 fnm\<^sub>1" using nested_mask.exhaust by blast
  obtain mh\<^sub>2 fnm\<^sub>2 where nm2_eq: "nm2 = NM mh\<^sub>2 fnm\<^sub>2" using nested_mask.exhaust by blast
  from fnm_eq[unfolded nm1_eq nm2_eq plus_nested_mask_def nested_mask_merge.simps get_fnm_nm.simps]
  have comb: "(fnm\<^sub>1 +\<lparr>\<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2))\<rparr>+ fnm\<^sub>2) lp = Some (p\<^sub>x, nm')" .
  show ?case
  proof (rule pfun_comb_cases[OF comb])
    fix v1
    assume h1: "fnm\<^sub>1 lp = Some v1" and "fnm\<^sub>2 lp = None" and hv: "(p\<^sub>x, nm') = v1"
    obtain p\<^sub>1 nm\<^sub>1' where v1_eq: "v1 = (p\<^sub>1, nm\<^sub>1')" using prod.exhaust by blast
    have "pred_folds_perm lp l nm1"
      apply (rule pred_folds_perm.ContainsPermDirect[of nm1 lp p\<^sub>1 nm\<^sub>1'])
      using h1 v1_eq nm1_eq
       apply simp
      using ContainsPermDirect.hyps(2) hv v1_eq
      by simp
    thus ?thesis by blast
  next
    fix v2
    assume "fnm\<^sub>1 lp = None" and h2: "fnm\<^sub>2 lp = Some v2" and hv: "(p\<^sub>x, nm') = v2"
    obtain p\<^sub>2 nm\<^sub>2' where v2_eq: "v2 = (p\<^sub>2, nm\<^sub>2')" using prod.exhaust by blast
    have "pred_folds_perm lp l nm2"
      apply (rule pred_folds_perm.ContainsPermDirect[of nm2 lp p\<^sub>2 nm\<^sub>2'])
      using h2 v2_eq nm2_eq
       apply simp
      using ContainsPermDirect.hyps(2) hv v2_eq
      by simp
    thus ?thesis by blast
  next
    fix v1 v2
    assume h1: "fnm\<^sub>1 lp = Some v1" and h2: "fnm\<^sub>2 lp = Some v2"
       and hv: "(p\<^sub>x, nm') = (fst v1 + fst v2, nested_mask_merge (snd v1) (snd v2))"
    obtain p\<^sub>1 nm\<^sub>1' where v1_eq: "v1 = (p\<^sub>1, nm\<^sub>1')" using prod.exhaust by blast
    obtain p\<^sub>2 nm\<^sub>2' where v2_eq: "v2 = (p\<^sub>2, nm\<^sub>2')" using prod.exhaust by blast
    have nm'_eq: "nm' = nested_mask_merge nm\<^sub>1' nm\<^sub>2'"
      using hv v1_eq v2_eq
      by simp
    from ContainsPermDirect.hyps(2) nm'_eq
    have both_fact: "contains_heap_loc l (nm\<^sub>1' + nm\<^sub>2')"
      unfolding plus_nested_mask_def
      by simp
    hence "contains_heap_loc l nm\<^sub>1' \<or> contains_heap_loc l nm\<^sub>2'"
      using contains_heap_loc_plus_elim[OF both_fact]
      by blast
    thus ?thesis
    proof
      assume "contains_heap_loc l nm\<^sub>1'"
      hence "pred_folds_perm lp l nm1"
        using pred_folds_perm.ContainsPermDirect[of nm1 lp p\<^sub>1 nm\<^sub>1' l] h1 v1_eq nm1_eq
        by simp
      thus ?thesis by blast
    next
      assume "contains_heap_loc l nm\<^sub>2'"
      hence "pred_folds_perm lp l nm2"
        using pred_folds_perm.ContainsPermDirect[of nm2 lp p\<^sub>2 nm\<^sub>2' l] h2 v2_eq nm2_eq
        by simp
      thus ?thesis by blast
    qed
  qed
next
  case (ContainsPermNested lp' p\<^sub>x nm')
  from ContainsPermNested.hyps(1)
  have fnm_eq: "get_fnm_nm (nm1 + nm2) lp' = Some (p\<^sub>x, nm')" .
  obtain mh\<^sub>1 fnm\<^sub>1 where nm1_eq: "nm1 = NM mh\<^sub>1 fnm\<^sub>1" using nested_mask.exhaust by blast
  obtain mh\<^sub>2 fnm\<^sub>2 where nm2_eq: "nm2 = NM mh\<^sub>2 fnm\<^sub>2" using nested_mask.exhaust by blast
  from fnm_eq[unfolded nm1_eq nm2_eq plus_nested_mask_def nested_mask_merge.simps get_fnm_nm.simps]
  have comb: "(fnm\<^sub>1 +\<lparr>\<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2))\<rparr>+ fnm\<^sub>2) lp' = Some (p\<^sub>x, nm')" .
  show ?case
  proof (rule pfun_comb_cases[OF comb])
    fix v1
    assume h1: "fnm\<^sub>1 lp' = Some v1" and "fnm\<^sub>2 lp' = None" and hv: "(p\<^sub>x, nm') = v1"
    obtain p\<^sub>1 nm\<^sub>1' where v1_eq: "v1 = (p\<^sub>1, nm\<^sub>1')" using prod.exhaust by blast
    have "pred_folds_perm lp l nm1"
      apply (rule pred_folds_perm.ContainsPermNested[of nm1 lp' p\<^sub>1 nm\<^sub>1'])
      using h1 v1_eq nm1_eq
       apply simp
      using ContainsPermNested.hyps(2) hv v1_eq
      by simp
    thus ?thesis by blast
  next
    fix v2
    assume "fnm\<^sub>1 lp' = None" and h2: "fnm\<^sub>2 lp' = Some v2" and hv: "(p\<^sub>x, nm') = v2"
    obtain p\<^sub>2 nm\<^sub>2' where v2_eq: "v2 = (p\<^sub>2, nm\<^sub>2')" using prod.exhaust by blast
    have "pred_folds_perm lp l nm2"
      apply (rule pred_folds_perm.ContainsPermNested[of nm2 lp' p\<^sub>2 nm\<^sub>2'])
      using h2 v2_eq nm2_eq
       apply simp
      using ContainsPermNested.hyps(2) hv v2_eq
      by simp
    thus ?thesis by blast
  next
    fix v1 v2
    assume h1: "fnm\<^sub>1 lp' = Some v1" and h2: "fnm\<^sub>2 lp' = Some v2"
       and hv: "(p\<^sub>x, nm') = (fst v1 + fst v2, nested_mask_merge (snd v1) (snd v2))"
    obtain p\<^sub>1 nm\<^sub>1' where v1_eq: "v1 = (p\<^sub>1, nm\<^sub>1')" using prod.exhaust by blast
    obtain p\<^sub>2 nm\<^sub>2' where v2_eq: "v2 = (p\<^sub>2, nm\<^sub>2')" using prod.exhaust by blast
    have nm'_eq: "nm' = nm\<^sub>1' + nm\<^sub>2'"
      using hv v1_eq v2_eq
      unfolding plus_nested_mask_def
      by simp
    have "pred_folds_perm lp l nm\<^sub>1' \<or> pred_folds_perm lp l nm\<^sub>2'"
      using ContainsPermNested.hyps(3)[OF nm'_eq]
      by blast
    thus ?thesis
    proof
      assume "pred_folds_perm lp l nm\<^sub>1'"
      hence "pred_folds_perm lp l nm1"
        using pred_folds_perm.ContainsPermNested[of nm1 lp' p\<^sub>1 nm\<^sub>1' lp l] h1 v1_eq nm1_eq
        by simp
      thus ?thesis by blast
    next
      assume "pred_folds_perm lp l nm\<^sub>2'"
      hence "pred_folds_perm lp l nm2"
        using pred_folds_perm.ContainsPermNested[of nm2 lp' p\<^sub>2 nm\<^sub>2' lp l] h2 v2_eq nm2_eq
        by simp
      thus ?thesis by blast
    qed
  qed
qed

text \<open>The actual "fold preserves known-folded witnesses" lemma: only the single top-level
      \<open>lp0\<close>-slot of \<open>nm\<close> changes under \<^const>\<open>add_to_lpm_nonzero_nm\<close> (growing from whatever was
      already there, possibly nothing, to include \<open>nm_exh\<close>); any existing \<^const>\<open>pred_folds_perm\<close>
      witness either never looked at that slot (unaffected, reused verbatim) or did look at it (in
      which case the witness still applies to the now-larger slot, by the existing monotonicity
      lemmas \<open>pred_folds_perm_stable_larger_nm\<close>/\<open>contains_heap_loc_stable_larger_nm\<close> and
      \<open>nm_sum_is_bigger\<close>). No induction on the derivation's depth is needed: the top-level case
      split (\<open>ContainsPermDirect\<close> vs \<open>ContainsPermNested\<close>, and within each, whether the referenced
      predicate location equals \<open>lp0\<close>) suffices.\<close>

lemma pred_folds_perm_fold_preserved:
  assumes "pred_folds_perm lp l nm"
  shows "pred_folds_perm lp l (add_to_lpm_nonzero_nm nm lp0 p_extra nm_exh)"
  using assms
proof cases
  case (ContainsPermDirect p subm)
  note hyps1 = ContainsPermDirect(1)
  note hyps2 = ContainsPermDirect(2)
  show ?thesis
  proof (cases "lp = lp0")
    assume eq: "lp = lp0"
    have new_fnm: "get_fnm_nm (add_to_lpm_nonzero_nm nm lp0 p_extra nm_exh) lp0 = Some (p + p_extra, subm + nm_exh)"
      using hyps1 eq
      by (cases nm; simp add: plus_nested_mask_def)
    have "subm \<le> subm + nm_exh"
      using nm_sum_is_bigger
      by blast
    hence "contains_heap_loc l (subm + nm_exh)"
      using hyps2 contains_heap_loc_stable_larger_nm
      by blast
    thus ?thesis
      unfolding eq
      using pred_folds_perm.ContainsPermDirect[OF new_fnm]
      by blast
  next
    assume neq: "lp \<noteq> lp0"
    have unch: "get_fnm_nm (add_to_lpm_nonzero_nm nm lp0 p_extra nm_exh) lp = get_fnm_nm nm lp"
      using neq
      by (cases nm; simp)
    show ?thesis
      using pred_folds_perm.ContainsPermDirect[OF unch[unfolded hyps1]] hyps2
      by simp
  qed
next
  case (ContainsPermNested lp' p subm)
  note hyps1 = ContainsPermNested(1)
  note hyps2 = ContainsPermNested(2)
  show ?thesis
  proof (cases "lp' = lp0")
    assume eq: "lp' = lp0"
    have new_fnm: "get_fnm_nm (add_to_lpm_nonzero_nm nm lp0 p_extra nm_exh) lp0 = Some (p + p_extra, subm + nm_exh)"
      using hyps1 eq
      by (cases nm; simp add: plus_nested_mask_def)
    have "subm \<le> subm + nm_exh"
      using nm_sum_is_bigger
      by blast
    hence "pred_folds_perm lp l (subm + nm_exh)"
      using hyps2 pred_folds_perm_stable_larger_nm
      by blast
    thus ?thesis
      unfolding eq
      using pred_folds_perm.ContainsPermNested[OF new_fnm]
      by blast
  next
    assume neq: "lp' \<noteq> lp0"
    have unch: "get_fnm_nm (add_to_lpm_nonzero_nm nm lp0 p_extra nm_exh) lp' = get_fnm_nm nm lp'"
      using neq
      by (cases nm; simp)
    show ?thesis
      using pred_folds_perm.ContainsPermNested[OF unch[unfolded hyps1]] hyps2
      by simp
  qed
qed

text \<open>Sum-aware variant: the witness may live either in the untouched \<open>nm\<close> part (reduces to
      \<open>pred_folds_perm_fold_preserved\<close> directly) or in \<open>nm_exh\<close> (needs one extra
      \<open>ContainsPermNested\<close> hop through the newly-grown \<open>lp0\<close> slot, whose nested submask
      is now \<open>\<ge> nm_exh\<close> by \<open>nm_sum_is_bigger\<close>).\<close>

lemma pred_folds_perm_fold_preserved_sum:
  assumes "pred_folds_perm lp l (nm1 + nm_exh)"
  shows "pred_folds_perm lp l (add_to_lpm_nonzero_nm nm1 lp0 p_extra nm_exh)"
  using pred_folds_perm_plus_elim[OF assms]
proof
  assume "pred_folds_perm lp l nm1"
  thus ?thesis
    using pred_folds_perm_fold_preserved
    by blast
next
  assume h: "pred_folds_perm lp l nm_exh"
  show ?thesis
  proof (cases "get_fnm_nm nm1 lp0")
    case None
    have new_fnm: "get_fnm_nm (add_to_lpm_nonzero_nm nm1 lp0 p_extra nm_exh) lp0 = Some (p_extra, nm_exh)"
      using None
      by (cases nm1; simp)
    show ?thesis
      using pred_folds_perm.ContainsPermNested[OF new_fnm h]
      by simp
  next
    case (Some pnm)
    obtain p0 nm0 where pnm_eq: "pnm = (p0, nm0)" using prod.exhaust by blast
    have new_fnm: "get_fnm_nm (add_to_lpm_nonzero_nm nm1 lp0 p_extra nm_exh) lp0 = Some (p0 + p_extra, nm0 + nm_exh)"
      using Some pnm_eq
      by (cases nm1; simp)
    have "nm_exh \<le> nm0 + nm_exh"
      using nm_sum_is_bigger add.commute
      by metis
    hence "pred_folds_perm lp l (nm0 + nm_exh)"
      using h pred_folds_perm_stable_larger_nm
      by blast
    thus ?thesis
      using pred_folds_perm.ContainsPermNested[OF new_fnm]
      by simp
  qed
qed

text \<open>Known-folded-aware version of \<open>fold_stmt_rel\<close> (\<open>Simulation/PredicateRel.thy\<close>, left completely
      untouched). \<open>fold_stmt_rel\<close> assumes the known-folded invariant holds throughout the exhale of
      the predicate body and the subsequent inhale of the predicate instance (everything stays on
      \<^term>\<open>R\<close>/\<^term>\<open>R''\<close>/\<^term>\<open>R'\<close>, i.e. known-folded is never disabled). But exhaling the body can
      itself involve exhaling nested predicate accesses, whose known-folded-mask update is not
      (yet) automated when known-folded is turned on (see \<open>kfm_upd_rel_tac\<close>'s \<open>AccPredicate\<close> case).

      Mirroring \<open>unfold_stmt_rel\<close> (same file, which faces the structurally identical problem for
      \<open>unfold\<close>): a \<open>fold\<close> can only ever grow the known-folded set (an underestimate of where
      permissions are folded), never shrink it, so the invariant that held right before the fold
      is still true (only possibly stale) throughout the exhale+inhale, and only needs to be
      brought up to date once, at the very end. This version threads a weakened relation
      \<^term>\<open>R\<^sub>w\<close> (known-folded disabled, via \<^const>\<open>disable_knownfolded_rel_opt\<close>) through
      \<open>StepExhale\<close> and \<open>StepInhale\<close>.

      Unlike \<open>unfold_stmt_rel\<close>'s own \<open>StepKFUpdate\<close> (which jumps straight from \<open>R\<^sub>w\<close> to \<open>R'\<close> in one
      step), here \<open>StepKFUpdate\<close> and the \<open>R\<^sub>w \<longrightarrow> R'\<close> transition are kept as two separate premises:
      \<open>StepKFUpdate\<close> stays entirely on \<open>R\<^sub>w\<close> (it only establishes, via a Boogie-level step, that
      \<^const>\<open>pred_kfm_sat_premise\<close> holds at the end), and the new \<open>KFMEnable\<close> premise is a pure
      logical implication (no \<open>red_ast_bpl\<close> involved) that combines \<open>R\<^sub>w\<close> with that fact to
      reconstitute \<open>R'\<close>. This keeps "prove the known-folded mask matches reality" and "combine that
      fact with the weakened relation" as two independent obligations instead of bundling them into
      one step.

      Statement only for now (proof to follow); mirrors \<open>fold_stmt_rel\<close>'s statement verbatim except
      for the \<^term>\<open>R\<^sub>w\<close>/\<^term>\<open>R\<^sub>w''\<close> substitutions and the \<open>StepKFUpdate\<close>/\<open>KFMEnable\<close> split described
      above.\<close>

lemma fold_stmt_rel_kf:
  assumes PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl"
      and PredArgs: "predicate_decl.args pdecl = ty_args"
      and PredBody: "predicate_decl.body pdecl = Some pbody"
      and CtxtPredWf: "ctxt_pred_syn_wf ctxt_vpr"
      and CtxtPredSF: "ctxt_pred_self_framing_inh ctxt_vpr StateCons"
      and WfCons: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and StateRelImpliesIntCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"
      and StateRelImpliesExtCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> consistent_external ctxt_vpr (get_total_full \<omega>)"
      and StateRelImpliesKFRel: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> heap_knownfolded_var_rel (\<lparr> kf_turned_on = True, kf_pos_turned_on = False \<rparr>) (program_total ctxt_vpr) (var_context ctxt_bpl) FieldTr hvar \<omega> ns"
      and StateRelWeakening: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> R\<^sub>w \<omega> ns"
      and ArgsRestriction: "list_all no_unfolding_pure_exp e_args_vpr \<and> list_all no_perm_pure_exp e_args_vpr \<and> list_all no_old_pure_exp e_args_vpr \<and> list_all no_result_pure_exp e_args_vpr"
      and ArgsAreVarOrLit: "list_all is_var_or_lit e_args_vpr"
        \<comment> \<open>Additional restriction (beyond \<open>ArgsRestriction\<close>) needed to close the \<open>framing_exh\<close>
            substitution step below: see the comment there (in \<open>fold_stmt_rel\<close>) for why the general
            case is hard.\<close>
      and BodyNoUnfolding: "no_unfolding_assertion (syntactic_mult p pbody)"  \<comment> \<open>Should be lifted soon.\<close>
      and PermSimp: "e_p_vpr = ELit (LPerm p)" \<comment> \<open>We only support literals as the permission.\<close>
      and PermPos: "p > 0"
      and StepWfSubexp: "exprs_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt_bpl (e_args_vpr @ [e_p_vpr]) \<gamma> \<gamma>\<^sub>2"
      and StepPermPos: "rel_general R R (=) (\<lambda>_. False) P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and StepExhale:
            "\<And>v_args_vpr v_p_vpr.
                exhale_rel (rel_ext_eq R\<^sub>w) (\<lambda>\<omega>def \<omega> ns. R\<^sub>w' \<omega>def \<omega> ns)
                  (framing_exh ctxt_vpr StateCons)
                  ctxt_vpr StateCons P ctxt_bpl
                  (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<gamma>\<^sub>3 \<gamma>\<^sub>4"
      and StateRelStrengthening:
            "\<And>\<omega> ns v_args_vpr.
                R\<^sub>w'' \<omega> ns \<Longrightarrow>
                heap_knownfolded_var_rel (\<lparr> kf_turned_on = True, kf_pos_turned_on = False \<rparr>) (program_total ctxt_vpr) (var_context ctxt_bpl) FieldTr hvar \<omega> ns \<Longrightarrow>
                R' \<omega> ns"
      and StepInhale:
            "\<And>v_args_vpr v_p_vpr.
                rel_general (\<lambda>\<omega>_def_\<omega> ns. R\<^sub>w' (fst \<omega>_def_\<omega>) (snd \<omega>_def_\<omega>) ns \<and> ctxt_vpr, (Some (fst \<omega>_def_\<omega>)) \<turnstile> \<langle>e_p_vpr; snd \<omega>_def_\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_vpr)) (\<lambda>\<omega>_def_\<omega> ns. R\<^sub>w'' (snd \<omega>_def_\<omega>) ns)
                  (\<lambda>\<omega>_def_\<omega> \<omega>_def_\<omega>'. fst \<omega>_def_\<omega> = fst \<omega>_def_\<omega>' \<and> inhale_pred_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr v_p_vpr (fst \<omega>_def_\<omega>) (snd \<omega>_def_\<omega>) (snd \<omega>_def_\<omega>'))
                  (\<lambda>_. False) P ctxt_bpl \<gamma>\<^sub>4 \<gamma>\<^sub>5"
      and StepKFUpdate:
            "\<And>v_args_vpr v_p_vpr.
                rel_general (\<lambda>\<omega> ns. R' \<omega> ns \<and>
                                    pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr
                                      (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega>)
                            R' (=) (\<lambda>_. False) P ctxt_bpl \<gamma>\<^sub>5 \<gamma>'"
      and NoHeapAssignBetween: "contains_no_heap_assignment_until hvar \<gamma>\<^sub>5 \<gamma>"
      and PPSyntacticRestriction: "program_point_restriction \<gamma>"
    shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt_bpl (Fold pid e_args_vpr (PureExp e_p_vpr)) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and
         "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Fold pid e_args_vpr (PureExp e_p_vpr)) \<omega> (RNormal \<omega>')"
  then obtain v_args v_p where
    v_args_eval: "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args_vpr \<omega> (Some v_args)" and
    v_p_eval: "ctxt_vpr, (Some \<omega>) \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    "v_p > 0" and
    fold_rel: "fold_rel ctxt_vpr pid v_args (Abs_preal v_p) \<omega> (RNormal \<omega>')"
    by (fastforce elim: RedFold_case)
  obtain pdecl' pbody' \<omega>0 \<omega>1 \<omega>1' nm_exh where
    "ViperLang.predicates (program_total ctxt_vpr) pid = Some pdecl'" and
    "ViperLang.predicate_decl.body pdecl' = Some pbody'" and
    v_args_ty: "vals_well_typed (absval_interp_total ctxt_vpr) v_args (predicate_decl.args pdecl')" and
    "\<omega>0 = \<omega>\<lparr> get_store_total := nth_option v_args \<rparr>" and
    exh: "red_exhale ctxt_vpr \<omega>0 (syntactic_mult (Rep_preal (Abs_preal v_p)) pbody') \<omega>0 (RNormal \<omega>1')" and
    "\<omega>1 = \<omega>\<lparr> get_total_full := get_total_full \<omega>1' \<rparr>" and
    "get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0" and
    "\<omega>' = add_to_lpm_nonzero_total_full \<omega>1 (pid,v_args) (Abs_posreal (Abs_preal v_p)) nm_exh"
    apply (rule FoldRelNormal_case[OF fold_rel])
    by simp
  hence "pdecl' = pdecl" and "pbody' = pbody"
    using PredBody PredDecl \<open>_ = Some pbody'\<close> \<open>_ = Some pdecl'\<close>
    by auto
  have "v_p = p"
    using PermSimp TotalExpressions.RedLit_case v_p_eval
    by fastforce
  hence "Rep_preal (Abs_preal v_p) = p"
    using Abs_preal_inverse \<open>0 < v_p\<close>
    by auto

  obtain p\<^sub>s nm\<^sub>s where "get_fnm_total_full \<omega>' (pid,v_args) = Some (p\<^sub>s,nm\<^sub>s)"
    unfolding \<open>\<omega>' = _\<close>
    by fastforce
  have "nm_exh \<le> nm\<^sub>s"
    using \<open>_ = Some (p\<^sub>s,nm\<^sub>s)\<close>[unfolded \<open>\<omega>' = _\<close>]
    apply (cases "get_fnm_total_full \<omega>1 (pid,v_args)")
     apply simp_all
    using add.commute nm_sum_is_bigger
    by blast

  have "rel_ext_eq R \<omega> \<omega> ns"
    using \<open>R \<omega> ns\<close>
    by blast

  \<comment> \<open>First step: well-formedness\<close>
  have "red_pure_exps_total ctxt_vpr (Some \<omega>) (e_args_vpr @ [e_p_vpr]) \<omega> (Some (v_args @ [VPerm v_p]))"
    by (simp add: v_args_eval v_p_eval red_pure_exps_append_success)
  from StepWfSubexp[THEN exprs_wf_rel_normal_elim, OF \<open>rel_ext_eq R \<omega> \<omega> ns\<close> this]
  obtain ns\<^sub>2 where
    ns\<^sub>2: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2) \<and> rel_ext_eq R \<omega> \<omega> ns\<^sub>2"
    by blast

  \<comment> \<open>Second step: permission positive\<close>
  with StepPermPos[THEN rel_success_elim]
  obtain ns\<^sub>3 where
    ns\<^sub>3: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>\<^sub>3, Normal ns\<^sub>3) \<and> rel_ext_eq R \<omega> \<omega> ns\<^sub>3"
    by blast

  \<comment> \<open>Third step: exhale\<close>
  have intcons: "StateCons (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>)"
    using StateRelImpliesIntCons WfCons \<open>rel_ext_eq R \<omega> \<omega> ns\<close> total_consistency_store_update_2
    by blast
  have framing_exh: "framing_exh ctxt_vpr StateCons (syntactic_mult p pbody)
          (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>)"
    apply (rule framing_exhI[where ?\<omega>_inh="upd_nm_total_full (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) 0" and ?\<omega>sum="\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>"])
         apply (rule intcons)
    using StateRelImpliesExtCons \<open>R \<omega> ns\<close>
        apply force
       apply (smt (verit, best) WfCons get_mh_total_full.simps intcons wf_total_consistency_def)
      apply (metis CtxtPredSF PermPos PredBody PredDecl \<open>pdecl' = pdecl\<close> assertion_self_framing_def assertion_self_framing_store_def ctxt_pred_self_framing_inh_def full_total_state.cases_scheme full_total_state.select_convs(1) full_total_state.update_convs(1) update_nm_total_full_store_unchanged update_store_total.simps v_args_ty)
    unfolding plus_full_total_state_ext_def
     apply simp
    unfolding plus_total_state_ext_def
     apply simp
     apply (simp add: commutative core_is_smaller core_total_state_ext_def defined_def option.discI)
    using succ_refl
    by blast

  hence "framing_exh ctxt_vpr StateCons (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega> \<omega>"
    \<comment> \<open>Unfold the witness \<open>\<omega>inh\<close> (forced to zero mask by the \<open>\<oplus>\<close>/\<open>\<succeq>\<close> algebra), restore its store to
        \<open>\<omega>\<close>'s original one (sound: \<open>\<oplus>\<close>/\<open>\<succeq>\<close> only care that both sides agree on the store, not what it
        is), and convert via @{thm framing_with_substitution}. This needs \<open>e_args_vpr\<close> to evaluate at
        the (zero-mask) witness, for which we rely on \<open>ArgsAreVarOrLit\<close> (a proof-engineering, not a
        soundness, restriction: field-access args would need a different, currently unproven, fact --
        see the git history of this step for that more general (also more difficult) analysis).\<close>
  proof -
    from framing_exh[unfolded framing_exh_def] obtain \<omega>inh \<omega>sum where
      ValidMaskSubst: "valid_heap_mask (get_mh_total_full (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>))" and
      Plus: "\<omega>inh \<oplus> (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) = Some \<omega>sum" and
      Succ: "(\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) \<succeq> \<omega>sum" and
      Framing: "assertion_framing_state ctxt_vpr StateCons (syntactic_mult p pbody) \<omega>inh"
      by blast

    have StoreInh: "get_store_total \<omega>inh = nth_option v_args"
      using Plus
      unfolding plus_full_total_state_ext_def
      by (auto split: if_split_asm)

    define \<omega>inh' where "\<omega>inh' = \<omega>inh\<lparr> get_store_total := get_store_total \<omega> \<rparr>"
    define \<omega>sum' where "\<omega>sum' = \<omega>sum\<lparr> get_store_total := get_store_total \<omega> \<rparr>"

    have PlusRestored: "\<omega>inh' \<oplus> \<omega> = Some \<omega>sum'"
      using full_total_state_plus_store_update[OF Plus, of "get_store_total \<omega>"]
      unfolding \<omega>inh'_def \<omega>sum'_def
      by simp

    have SuccRestored: "\<omega> \<succeq> \<omega>sum'"
      using full_total_state_succ_store_update[OF Succ, of "get_store_total \<omega>"]
      unfolding \<omega>sum'_def
      by simp

    have FramingRestored: "assertion_framing_state ctxt_vpr StateCons (syntactic_mult p pbody)
                              (\<omega>inh'\<lparr> get_store_total := nth_option v_args \<rparr>)"
      using Framing
      unfolding \<omega>inh'_def StoreInh[symmetric]
      by simp

    have ArgsEvalInh: "red_pure_exps_total ctxt_vpr (Some \<omega>inh') e_args_vpr \<omega>inh' (Some v_args)"
      apply (rule red_pure_exps_var_or_lit_indep[OF v_args_eval])
      using ArgsAreVarOrLit
       apply blast
      unfolding \<omega>inh'_def
      by simp

    have SupportedBody: "supported_pred_body (syntactic_mult p pbody)"
      apply (rule syntactic_mult_supported)
      using CtxtPredWf PredDecl \<open>_ = Some pdecl'\<close> \<open>_ = Some pbody'\<close> \<open>pbody' = pbody\<close>
      unfolding ctxt_pred_syn_wf_def
       apply blast
      using PermPos
      by simp

    have FramingSubst: "assertion_framing_state ctxt_vpr StateCons
                           (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega>inh'"
      apply (rule framing_with_substitution[OF FramingRestored ArgsEvalInh SupportedBody BodyNoUnfolding WfCons])
      using ArgsRestriction
      by simp_all

    show ?thesis
      unfolding framing_exh_def
      apply (intro conjI)
      using StateRelImpliesIntCons \<open>R \<omega> ns\<close>
         apply blast
      using StateRelImpliesExtCons \<open>R \<omega> ns\<close>
        apply blast
       using ValidMaskSubst
       apply simp
      using PlusRestored SuccRestored FramingSubst
      by blast
  qed

  moreover have exh_subst: "red_exhale ctxt_vpr \<omega> (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega> (RNormal \<omega>1)"
    apply (rule exhale_with_substitution)
               apply (rule exh[unfolded \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close>])
              apply (rule \<open>\<omega>0 = _\<close>)+
            apply simp
           apply (rule v_args_eval)
          apply (simp add: \<open>\<omega>1 = _\<close>)
         apply (simp add: \<open>\<omega>1 = _\<close>)
        apply (simp add: \<open>\<omega>1 = _\<close>)
    using PredDecl WfCons CtxtPredWf \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close> \<open>pdecl' = pdecl\<close> \<open>predicate_decl.body pdecl' = Some pbody'\<close> ctxt_pred_syn_wf_def prat_non_negative syntactic_mult_supported
       apply blast
    using BodyNoUnfolding
      apply auto[1]
    by (simp_all add: ArgsRestriction)

  ultimately obtain ns\<^sub>4 where ns\<^sub>4: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>3, Normal ns\<^sub>3) (\<gamma>\<^sub>4, Normal ns\<^sub>4) \<and> R\<^sub>w' \<omega> \<omega>1 ns\<^sub>4"
    using StepExhale[THEN exhale_rel_normal_elim, OF conjI[OF refl StateRelWeakening[OF conjunct2[OF conjunct2[OF ns\<^sub>3]]]]] v_args_eval
    by auto

  \<comment> \<open>Fourth step: inhale\<close>
  let ?\<omega>_def_\<omega> = "(\<omega>, \<omega>1)"
  let ?\<omega>_def_\<omega>' = "(\<omega>, \<omega>')"
  have "fst ?\<omega>_def_\<omega> = fst ?\<omega>_def_\<omega>' \<and> inhale_pred_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args v_p (fst ?\<omega>_def_\<omega>) (snd ?\<omega>_def_\<omega>) (snd ?\<omega>_def_\<omega>')"
    apply (intro conjI)
     apply simp
    unfolding inhale_pred_normal_premise_def
    apply simp
    apply (intro conjI)
        apply (simp add: \<open>_ = Some pdecl'\<close> pred_ty_correct_premise_def v_args_ty)
       apply (metis (mono_tags, lifting) ArgsRestriction Ball_set_list_all exh_subst exhale_only_changes_total_state_aux red_pure_exp_only_differ_on_mask(2) v_args_eval)
      apply (metis PermSimp \<open>v_p = p\<close> red_pure_exp_total_red_pure_exps_total.RedLit val_of_lit.simps(3))
    using \<open>0 < v_p\<close>
     apply auto[1]
    unfolding inhale_perm_single_pred_def
    apply (rule CollectI)
    apply (rule exI[of _ \<omega>'])
    apply (rule exI[of _ "get_total_full \<omega>0\<lparr> get_nm_total := nm_exh \<rparr>"])
    apply (rule exI[of _ "Abs_preal v_p"])
    apply (intro conjI)
         apply simp
        apply simp
       apply (rule exhale_pred_body_part_extcons_wrt_ploc[OF _ _ _ _ _ exh])
             apply fact+
          apply (rule full_total_state.equality; simp)
          apply (simp add: \<open>\<omega>0 = _\<close>)
    using StateRelImpliesExtCons \<open>R \<omega> ns\<close> \<open>\<omega>0 = _\<close>
         apply force
    using \<open>\<omega>1 = _\<close> \<open>get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0\<close>
        apply fastforce
       apply fact
      apply (metis \<open>\<omega>1 = _\<close> exh exhale_only_changes_total_state_aux full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3) get_hh_total_full.elims total_state.select_convs(1) total_state.surjective total_state.update_convs(2))
    using \<open>0 < v_p\<close> \<open>\<omega>' = _\<close> positive_real_preal
     apply force
    using StateRelImpliesIntCons WfCons \<open>R \<omega> ns\<close> \<open>red_stmt_total _ _ _ _ _ _\<close> total_consistency_red_stmt_preserve
    by blast

  with StepInhale[THEN rel_success_elim, OF _ this, simplified, where ?ns=ns\<^sub>4]
  obtain ns\<^sub>5 where ns\<^sub>5: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>4, Normal ns\<^sub>4) (\<gamma>\<^sub>5, Normal ns\<^sub>5) \<and> R\<^sub>w'' \<omega>' ns\<^sub>5"
    using inhale_pred_acc_rel_assms_perm_eval ns\<^sub>4
    by fastforce

  \<comment> \<open>Fifth step: known-folded permission mask update\<close>
  have kf_restore: "heap_knownfolded_var_rel (\<lparr> kf_turned_on = True, kf_pos_turned_on = False \<rparr>) (program_total ctxt_vpr) (var_context ctxt_bpl) FieldTr hvar \<omega>' ns\<^sub>5"
  proof -
    have s2: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2)" using conjunct1[OF ns\<^sub>2] .
    have s3: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>\<^sub>3, Normal ns\<^sub>3)" using conjunct1[OF ns\<^sub>3] .
    have s4: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>3, Normal ns\<^sub>3) (\<gamma>\<^sub>4, Normal ns\<^sub>4)" using conjunct1[OF ns\<^sub>4] .
    have s5: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>4, Normal ns\<^sub>4) (\<gamma>\<^sub>5, Normal ns\<^sub>5)" using conjunct1[OF ns\<^sub>5] .
    have bpl_red_ns_ns5: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>5, Normal ns\<^sub>5)"
      using red_ast_bpl_transitive[OF red_ast_bpl_transitive[OF red_ast_bpl_transitive[OF s2 s3] s4] s5] .
    have hvar_stable: "lookup_var (var_context ctxt_bpl) ns hvar = lookup_var (var_context ctxt_bpl) ns\<^sub>5 hvar"
      using bpl_no_heap_assignment[OF NoHeapAssignBetween PPSyntacticRestriction bpl_red_ns_ns5] .

    obtain hb where
      Lookup: "lookup_var (var_context ctxt_bpl) ns hvar = Some (AbsV (AHeap hb))" and
      KfmExists: "\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))" and
      KfmNormalFields: "knownfolded_masks_normal_fields hb" and
      KfRel: "heap_knownfolded_rel (program_total ctxt_vpr) FieldTr (get_nm_total_full \<omega>) hb"
      using StateRelImpliesKFRel[OF \<open>R \<omega> ns\<close>]
      unfolding heap_knownfolded_var_rel_def
      by auto

    have nm_omega_eq: "get_nm_total_full \<omega> = get_nm_total_full \<omega>1 + nm_exh"
      using \<open>\<omega>0 = _\<close> \<open>get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0\<close>
      by simp
    have nm_omega'_eq: "get_nm_total_full \<omega>' = add_to_lpm_nonzero_nm (get_nm_total_full \<omega>1) (pid,v_args) (Abs_posreal (Abs_preal v_p)) nm_exh"
      using \<open>\<omega>' = _\<close>
      by simp

    have KfRel': "heap_knownfolded_rel (program_total ctxt_vpr) FieldTr (get_nm_total_full \<omega>') hb"
      unfolding heap_knownfolded_rel_def
    proof (intro allI impI)
      fix lp kfm l field_ty_vpr field_bpl
      assume h1: "hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))"
         and h2: "declared_fields (program_total ctxt_vpr) (snd l) = Some field_ty_vpr"
         and h3: "FieldTr (snd l) = Some field_bpl"
         and h4: "kfm (Address (fst l), NormalField field_bpl field_ty_vpr)"
      have "pred_folds_perm lp l (get_nm_total_full \<omega>)"
        using KfRel[unfolded heap_knownfolded_rel_def] h1 h2 h3 h4
        by blast
      hence "pred_folds_perm lp l (get_nm_total_full \<omega>1 + nm_exh)"
        unfolding nm_omega_eq .
      thus "pred_folds_perm lp l (get_nm_total_full \<omega>')"
        unfolding nm_omega'_eq
        using pred_folds_perm_fold_preserved_sum
        by blast
    qed

    have Lookup5: "lookup_var (var_context ctxt_bpl) ns\<^sub>5 hvar = Some (AbsV (AHeap hb))"
      using Lookup hvar_stable
      by simp

    show ?thesis
      unfolding heap_knownfolded_var_rel_def
      apply (rule exI[of _ hb])
      using Lookup5 KfmExists KfmNormalFields KfRel'
      by auto
  qed

  moreover have "\<exists>nm_exh p\<^sub>s nm\<^sub>s.
                    get_fnm_total_full \<omega>' (pid, v_args) = Some (p\<^sub>s,nm\<^sub>s) \<and> nm_exh \<le> nm\<^sub>s \<and>
                    sat ctxt_vpr \<omega>' (get_mh_nm nm_exh) (get_mp_nm nm_exh) (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<and>
                    consistent_external ctxt_vpr (\<lparr> get_hh_total = get_hh_total_full \<omega>', get_nm_total = nm_exh \<rparr>)"
    apply (rule exI[of _ nm_exh])
    apply (rule exI[of _ p\<^sub>s])
    apply (rule exI[of _ nm\<^sub>s])
    apply (rule conjI)
     apply fact
    apply (rule conjI)
     apply fact
    apply (rule exhale_diff_sat_extcons)
    using exh_subst
             apply fast
            apply simp
    subgoal
      apply (rule substitute_assertion_supported_pred)
      using CtxtPredWf PredBody \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pdecl' = pdecl\<close> syntactic_mult_supported
        \<open>program.predicates (program_total ctxt_vpr) pid = Some pdecl'\<close> ctxt_pred_syn_wf_def prat_non_negative
       apply blast
      using ArgsRestriction list_all_length
      by blast
    using StateRelImpliesExtCons \<open>R \<omega> ns\<close>
          apply blast
    using fold_rel fold_rel_normal_only_changes_mask
         apply blast
        apply (metis fold_rel fold_rel_normal_only_changes_mask)
    using \<open>\<omega>0 = _\<close> \<open>get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0\<close>
       apply force
      apply (metis total_state.select_convs(1) fold_rel_normal_only_changes_mask fold_rel)
     apply simp
    apply (rule CtxtPredWf)
    done
  have ns'_exists: "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>5, Normal ns\<^sub>5) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    apply (rule StepKFUpdate[THEN rel_success_elim, where ?\<omega>=\<omega>' and ?\<omega>'=\<omega>' and ?ns=ns\<^sub>5 and ?v_args_vpr1=v_args])
     prefer 2
     apply simp
    unfolding pred_kfm_sat_premise_def
    apply (intro conjI)
    using conjunct2[OF ns\<^sub>5] kf_restore StateRelStrengthening
       apply blast
      apply (metis ArgsRestriction eval_with_None_same_store_same_hh(2) fold_rel fold_rel_normal_only_changes_mask v_args_eval)
    using PredDecl \<open>pdecl' = pdecl\<close> pred_ty_correct_premise_def v_args_ty
     apply blast
    by fact
  then obtain ns' where ns': "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>5, Normal ns\<^sub>5) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    by blast

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    apply (rule exI[of _ ns'])
    apply (intro conjI)
    using ns\<^sub>2 ns\<^sub>3 ns\<^sub>4 ns\<^sub>5 ns' red_ast_bpl_transitive
     apply meson
    using ns'
    by blast

next

  fix \<omega> ns
  assume "R \<omega> ns"
     and "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Fold pid e_args_vpr (PureExp e_p_vpr)) \<omega> RFailure"

  then consider
    (SubExprFail) "red_pure_exps_total ctxt_vpr (Some \<omega>) (sub_expressions (Fold pid e_args_vpr (PureExp e_p_vpr))) \<omega> None" |
     (PermNonPos) "\<exists>v_args v_p. red_pure_exps_total ctxt_vpr (Some \<omega>) e_args_vpr \<omega> (Some v_args) \<and>
                     ctxt_vpr, (Some \<omega>) \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p) \<and> v_p \<le> 0" |
        (ExhFail) "\<exists>v_args v_p. red_pure_exps_total ctxt_vpr (Some \<omega>) e_args_vpr \<omega> (Some v_args) \<and>
                     ctxt_vpr, (Some \<omega>) \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p) \<and> v_p > 0 \<and>
                     fold_rel ctxt_vpr pid v_args (Abs_preal v_p) \<omega> RFailure"
    using RedFoldFailure_case
    by metis

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) c'"
  proof cases
    case SubExprFail
    hence "red_pure_exps_total ctxt_vpr (Some \<omega>) (e_args_vpr @ [e_p_vpr]) \<omega> None"
      by simp
    from StepWfSubexp[THEN exprs_wf_rel_failure_elim, OF _ this]
    show ?thesis
      using \<open>R \<omega> ns\<close>
      by blast
  next
    case PermNonPos
    then show ?thesis
      using PermPos PermSimp TotalExpressions.RedLit_case
      by fastforce
  next
    case ExhFail
    then obtain v_args v_p where
      v_args_eval: "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args_vpr \<omega> (Some v_args)" and
      v_p_eval: "ctxt_vpr, Some \<omega> \<turnstile> \<langle>e_p_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
      "0 < v_p" and
      "fold_rel ctxt_vpr pid v_args (Abs_preal v_p) \<omega> RFailure"
      by blast
    then obtain pdecl' pbody' \<omega>0 where
      "ViperLang.predicates (program_total ctxt_vpr) pid = Some pdecl'" and
      "ViperLang.predicate_decl.body pdecl' = Some pbody'" and
      v_args_ty: "vals_well_typed (absval_interp_total ctxt_vpr) v_args (predicate_decl.args pdecl')" and
      "\<omega>0 = \<omega>\<lparr> get_store_total := nth_option v_args \<rparr>" and
      exh: "red_exhale ctxt_vpr \<omega>0 (syntactic_mult (Rep_preal (Abs_preal v_p)) pbody') \<omega>0 RFailure"
      by (fastforce elim: FoldRelFailure_case)
    hence "pdecl' = pdecl" and "pbody' = pbody"
      using PredBody PredDecl \<open>_ = Some pbody'\<close> \<open>_ = Some pdecl'\<close>
      by auto
    have "v_p = p"
      using PermSimp TotalExpressions.RedLit_case v_p_eval
      by fastforce
    hence "Rep_preal (Abs_preal v_p) = p"
      using Abs_preal_inverse \<open>0 < v_p\<close>
      by auto

    have "rel_ext_eq R \<omega> \<omega> ns"
      using \<open>R \<omega> ns\<close>
      by blast

    \<comment> \<open>First step: well-formedness\<close>
    have "red_pure_exps_total ctxt_vpr (Some \<omega>) (e_args_vpr @ [e_p_vpr]) \<omega> (Some (v_args @ [VPerm v_p]))"
      by (simp add: v_args_eval v_p_eval red_pure_exps_append_success)
    from StepWfSubexp[THEN exprs_wf_rel_normal_elim, OF \<open>rel_ext_eq R \<omega> \<omega> ns\<close> this]
    obtain ns\<^sub>2 where
      ns\<^sub>2: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2) \<and> rel_ext_eq R \<omega> \<omega> ns\<^sub>2"
      by blast

    \<comment> \<open>Second step: permission positive\<close>
    with StepPermPos[THEN rel_success_elim]
    obtain ns\<^sub>3 where
      ns\<^sub>3: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>\<^sub>3, Normal ns\<^sub>3) \<and> rel_ext_eq R \<omega> \<omega> ns\<^sub>3"
      by blast

    \<comment> \<open>Third step: exhale (failure)\<close>
    have intcons: "StateCons (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>)"
      using StateRelImpliesIntCons WfCons \<open>rel_ext_eq R \<omega> \<omega> ns\<close> total_consistency_store_update_2
      by blast
    have framing_exh: "framing_exh ctxt_vpr StateCons (syntactic_mult p pbody)
            (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>)"
      apply (rule framing_exhI[where ?\<omega>_inh="upd_nm_total_full (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) 0" and ?\<omega>sum="\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>"])
           apply (rule intcons)
      using StateRelImpliesExtCons \<open>R \<omega> ns\<close>
          apply force
         apply (smt (verit, best) WfCons get_mh_total_full.simps intcons wf_total_consistency_def)
        apply (metis CtxtPredSF PermPos PredBody PredDecl \<open>pdecl' = pdecl\<close> assertion_self_framing_def assertion_self_framing_store_def ctxt_pred_self_framing_inh_def full_total_state.cases_scheme full_total_state.select_convs(1) full_total_state.update_convs(1) update_nm_total_full_store_unchanged update_store_total.simps v_args_ty)
      unfolding plus_full_total_state_ext_def
       apply simp
      unfolding plus_total_state_ext_def
       apply simp
       apply (simp add: commutative core_is_smaller core_total_state_ext_def defined_def option.discI)
      using succ_refl
      by blast

    (* TODO: duplicated proof *)
    hence "framing_exh ctxt_vpr StateCons (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega> \<omega>"
      \<comment> \<open>Unfold the witness \<open>\<omega>inh\<close> (forced to zero mask by the \<open>\<oplus>\<close>/\<open>\<succeq>\<close> algebra), restore its store to
          \<open>\<omega>\<close>'s original one (sound: \<open>\<oplus>\<close>/\<open>\<succeq>\<close> only care that both sides agree on the store, not what it
          is), and convert via @{thm framing_with_substitution}. This needs \<open>e_args_vpr\<close> to evaluate at
          the (zero-mask) witness, for which we rely on \<open>ArgsAreVarOrLit\<close> (a proof-engineering, not a
          soundness, restriction: field-access args would need a different, currently unproven, fact --
          see the git history of this step for that more general (also more difficult) analysis).\<close>
    proof -
      from framing_exh[unfolded framing_exh_def] obtain \<omega>inh \<omega>sum where
        ValidMaskSubst: "valid_heap_mask (get_mh_total_full (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>))" and
        Plus: "\<omega>inh \<oplus> (\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) = Some \<omega>sum" and
        Succ: "(\<omega>\<lparr> get_store_total := nth_option v_args \<rparr>) \<succeq> \<omega>sum" and
        Framing: "assertion_framing_state ctxt_vpr StateCons (syntactic_mult p pbody) \<omega>inh"
        by blast

      have StoreInh: "get_store_total \<omega>inh = nth_option v_args"
        using Plus
        unfolding plus_full_total_state_ext_def
        by (auto split: if_split_asm)

      define \<omega>inh' where "\<omega>inh' = \<omega>inh\<lparr> get_store_total := get_store_total \<omega> \<rparr>"
      define \<omega>sum' where "\<omega>sum' = \<omega>sum\<lparr> get_store_total := get_store_total \<omega> \<rparr>"

      have PlusRestored: "\<omega>inh' \<oplus> \<omega> = Some \<omega>sum'"
        using full_total_state_plus_store_update[OF Plus, of "get_store_total \<omega>"]
        unfolding \<omega>inh'_def \<omega>sum'_def
        by simp

      have SuccRestored: "\<omega> \<succeq> \<omega>sum'"
        using full_total_state_succ_store_update[OF Succ, of "get_store_total \<omega>"]
        unfolding \<omega>sum'_def
        by simp

      have FramingRestored: "assertion_framing_state ctxt_vpr StateCons (syntactic_mult p pbody)
                                (\<omega>inh'\<lparr> get_store_total := nth_option v_args \<rparr>)"
        using Framing
        unfolding \<omega>inh'_def StoreInh[symmetric]
        by simp

      have ArgsEvalInh: "red_pure_exps_total ctxt_vpr (Some \<omega>inh') e_args_vpr \<omega>inh' (Some v_args)"
        apply (rule red_pure_exps_var_or_lit_indep[OF v_args_eval])
        using ArgsAreVarOrLit
         apply blast
        unfolding \<omega>inh'_def
        by simp

      have SupportedBody: "supported_pred_body (syntactic_mult p pbody)"
        apply (rule syntactic_mult_supported)
        using CtxtPredWf PredDecl \<open>_ = Some pdecl'\<close> \<open>_ = Some pbody'\<close> \<open>pbody' = pbody\<close>
        unfolding ctxt_pred_syn_wf_def
         apply blast
        using PermPos
        by simp

      have FramingSubst: "assertion_framing_state ctxt_vpr StateCons
                             (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega>inh'"
        apply (rule framing_with_substitution[OF FramingRestored ArgsEvalInh SupportedBody BodyNoUnfolding WfCons])
        using ArgsRestriction
        by simp_all

      show ?thesis
        unfolding framing_exh_def
        apply (intro conjI)
        using StateRelImpliesIntCons \<open>R \<omega> ns\<close>
           apply blast
        using StateRelImpliesExtCons \<open>R \<omega> ns\<close>
          apply blast
         using ValidMaskSubst
         apply simp
        using PlusRestored SuccRestored FramingSubst
        by blast
    qed

    moreover have exh_subst: "red_exhale ctxt_vpr \<omega> (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega> RFailure"
      apply (rule exhale_with_substitution_failure)
              apply (rule exh[unfolded \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close>])
             apply (rule \<open>\<omega>0 = _\<close>)+
           apply simp
          apply (rule v_args_eval)
      using PredDecl WfCons CtxtPredWf \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close> \<open>pdecl' = pdecl\<close> \<open>predicate_decl.body pdecl' = Some pbody'\<close> ctxt_pred_syn_wf_def prat_non_negative syntactic_mult_supported
         apply blast
      using BodyNoUnfolding
        apply auto[1]
      by (simp_all add: ArgsRestriction)

    ultimately show ?thesis
      using StepExhale[THEN exhale_rel_failure_elim]
      by (metis StateRelWeakening ns\<^sub>2 ns\<^sub>3 red_ast_bpl_transitive snd_conv)
  qed
qed


lemma turn_on_knownfolded_rel':
  assumes "state_rel_def_same Pr StateCons TyRep (disable_knownfolded_rel_opt Tr) AuxPred ctxt_bpl \<omega> ns"
      and "heap_knownfolded_var_rel (\<lparr> kf_turned_on = True, kf_pos_turned_on = False \<rparr>) Pr (var_context ctxt_bpl) (field_translation Tr) (heap_var Tr) \<omega> ns"
      and "kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
      and "\<not> kf_pos_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
    shows "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns"
  apply (subgoal_tac "enable_knownfolded_rel_opt Tr = Tr")
  using turn_on_knownfolded_rel[OF assms(1), simplified, OF assms(2)] assms(3)
   apply presburger
  using assms(3,4)
  by auto


end
