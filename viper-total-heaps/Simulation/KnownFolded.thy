theory KnownFolded
  imports TotalViperSemantics.TotalSemantics TotalViperSemantics.TotalExtConsProps ViperBoogieAbsValueInst BoogieInterface
begin


record knownfolded_rel_options =
  kf_turned_on :: bool
  \<comment>\<open>Tracks the permission-guarded known-folded relation \<open>heap_knownfolded_rel_pos\<close> (defined below).
     Unlike \<open>kf_turned_on\<close>, this flag can stay on during an exhale: the guarded relation is preserved
     by every exhale step, whereas the unguarded one is invalidated as soon as a predicate loses all
     of its permission.\<close>
  kf_pos_turned_on :: bool


context begin


\<comment> \<open>Todo: This type synonym already appears in \<^file>\<open>ViperBoogieBasicRel.thy\<close>. Merge them.\<close>
private type_synonym 'a bpl_heap_ty = "ref \<times> 'a vb_field \<rightharpoonup> ('a vbpl_absval) bpl_val"


inductive contains_heap_loc :: "heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> bool"
  for l :: "heap_loc" where
  ContainsLocDirect:
  "\<lbrakk> get_mh_nm nm l > 0 \<rbrakk> \<Longrightarrow>
   contains_heap_loc l nm"
| ContainsLocNested:
  "\<lbrakk> get_fnm_nm nm lp = Some (_,nm');
     contains_heap_loc l nm' \<rbrakk> \<Longrightarrow>
   contains_heap_loc l nm"


lemma contains_heap_loc_stable_larger_nm:
  assumes "contains_heap_loc l nm"
      and "nm \<le> nm'"
    shows "contains_heap_loc l nm'"
  using assms
proof (induction arbitrary: nm' rule: contains_heap_loc.inducts)
  case (ContainsLocDirect nm)
  then show ?case
    by (meson KnownFolded.contains_heap_loc.ContainsLocDirect dual_order.strict_trans1 le_funE less_eq_nested_maskD)
next
  case (ContainsLocNested nm lp p nm')
  show ?case
    by (metis ContainsLocNested.IH ContainsLocNested.hyps(1) ContainsLocNested.prems Some_Some_ifD contains_heap_loc.simps nm_larger_sub_larger old.prod.inject option.inject)
qed


lemma contains_heap_loc_scale:
  assumes "contains_heap_loc l nm"
      and "s > 0"
    shows "contains_heap_loc l (s *\<^sub>s nm)"
  using assms(1)
proof (induction rule: contains_heap_loc.inducts)
  case (ContainsLocDirect nm)
  show ?case
    apply (rule contains_heap_loc.ContainsLocDirect)
    using ContainsLocDirect
    apply (cases nm)
    unfolding scale_nested_mask_def
    apply (simp add: mul_mask_def)
    using assms(2) preal_to_real(2,7,9)
    by auto
next
  case (ContainsLocNested nm lp p' nm')
  have "get_fnm_nm (s *\<^sub>s nm) lp = Some ((Abs_posreal s) * p', s *\<^sub>s nm')"
    using ContainsLocNested.hyps(1)
    unfolding scale_nested_mask_def
    apply (cases nm)
    apply simp
    using assms(2) mult.commute
    by blast
  show ?case
    apply (rule contains_heap_loc.ContainsLocNested)
    by fact+
qed


inductive pred_folds_perm :: "'a predicate_loc \<Rightarrow> heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> bool"
  for lp :: "'a predicate_loc" and l :: "heap_loc" where
  ContainsPermDirect:
  "\<lbrakk> get_fnm_nm nm lp = Some (_,nm');
     contains_heap_loc l nm' \<rbrakk> \<Longrightarrow>
   pred_folds_perm lp l nm"
| ContainsPermNested:
  "\<lbrakk> get_fnm_nm nm lp' = Some (_,nm');
     pred_folds_perm lp l nm' \<rbrakk> \<Longrightarrow>
   pred_folds_perm lp l nm"


lemma pred_folds_perm_mh_stable:
  assumes "pred_folds_perm lp l nm"
      and "get_fnm_nm nm = get_fnm_nm nm'"
    shows "pred_folds_perm lp l nm'"
  apply (rule pred_folds_perm.cases)
    apply fact
  using assms(2)
   apply (auto intro: ContainsPermDirect ContainsPermNested)
  done


lemma pred_folds_perm_stable_larger_nm:
  assumes "pred_folds_perm lp l nm"
      and "nm \<le> nm'"
    shows "pred_folds_perm lp l nm'"
  using assms
proof (induction arbitrary: nm' rule: pred_folds_perm.inducts)
  case (ContainsPermDirect nm p nm_sub)
  then obtain p' nm_sub' where "get_fnm_nm nm' lp = Some (p', nm_sub')" and "nm_sub \<le> nm_sub'"
    using nm_larger_sub_larger_not_None
    by blast
  show ?case
    apply (rule pred_folds_perm.ContainsPermDirect)
     apply fact
    by (meson ContainsPermDirect.hyps(2) \<open>nm_sub \<le> nm_sub'\<close> contains_heap_loc_stable_larger_nm)
next
  case (ContainsPermNested nm lp' p nm_sub)
  obtain mh fnm where "nm = NM mh fnm" using nm_get_eq by blast
  obtain mh' fnm' where "nm' = NM mh' fnm'" using nm_get_eq by blast
  obtain p' nm_sub' where "get_fnm_nm nm' lp' = Some (p', nm_sub')" and "nm_sub \<le> nm_sub'"
    using nm_larger_sub_larger_not_None ContainsPermNested.hyps(1) ContainsPermNested.prems
    by blast
  show ?case
    apply (rule pred_folds_perm.ContainsPermNested)
     apply fact
    by (simp add: ContainsPermNested.IH \<open>nm_sub \<le> nm_sub'\<close>)
qed


lemma pred_folds_perm_plus_l:
  assumes "pred_folds_perm lp l nm"
    shows "pred_folds_perm lp l (nm' + nm)"
  apply (rule pred_folds_perm_stable_larger_nm[OF assms(1)])
  by (simp add: add.commute nm_sum_is_bigger)


lemma pred_folds_perm_plus_r:
  assumes "pred_folds_perm lp l nm"
    shows "pred_folds_perm lp l (nm + nm')"
  using assms nested_mask_greater_equiv pred_folds_perm_stable_larger_nm
  by blast


lemma pred_folds_perm_scale:
  assumes "pred_folds_perm lp l nm"
      and "s > 0"
    shows "pred_folds_perm lp l (s *\<^sub>s nm)"
  using assms(1)
proof (induction rule: pred_folds_perm.inducts)
  case (ContainsPermDirect nm p nm')
  show ?case
    apply (rule pred_folds_perm.ContainsPermDirect[of _ _ "Abs_posreal s * p" "s *\<^sub>s nm'"])
     apply (cases nm)
     apply (simp add: scale_nested_mask_def)
    using ContainsPermDirect.hyps(1) assms(2) mult.commute
     apply auto[1]
    by (simp add: ContainsPermDirect.hyps(2) assms(2) contains_heap_loc_scale)
next
  case (ContainsPermNested nm lp' p nm')
  show ?case
    apply (rule pred_folds_perm.ContainsPermNested[of _ lp' "Abs_posreal s * p" "s *\<^sub>s nm'"])
     apply (cases nm)
     apply (simp add: scale_nested_mask_def)
    using ContainsPermNested.hyps(1) assms(2) mult.commute
     apply auto[1]
    by (simp add: ContainsPermNested.IH)
qed


lemma pred_folds_perm_contains_heap_loc:
  assumes "pred_folds_perm lp l nm"
  shows "contains_heap_loc l nm"
  using assms
  by (induction rule: pred_folds_perm.inducts) (auto intro: contains_heap_loc.ContainsLocNested)


lemma has_sumA_zero_nonneg_point:
  fixes pf :: "'b \<Rightarrow> real"
  assumes "pf has_sumA 0"
      and "\<And>x. pf x \<ge> 0"
    shows "pf y = 0"
proof -
  have "(pf has_sum pf y) {y}"
    using has_sum_finite[of "{y}" pf]
    by simp
  hence "pf y \<le> 0"
    using has_sum_mono_neutral[OF _ assms(1)] assms(2)
    by fastforce
  thus ?thesis
    using assms(2)
    by (simp add: order_antisym)
qed


text \<open>A known-folded witness inside a nested mask forces the permission sum of the
      corresponding heap location to be non-zero. Note that no assumption on the permission
      of the enclosing predicate is required, since \<^const>\<open>nm_loc_sum'\<close> recurses into a
      sub-mask without rescaling it.\<close>

lemma contains_heap_loc_not_nm_loc_sum_zero:
  assumes "contains_heap_loc l nm"
  shows "\<not> nm_loc_sum l nm 0"
  using assms
proof (induction rule: contains_heap_loc.inducts)
  case (ContainsLocDirect nm)
  show ?case
  proof
    assume "nm_loc_sum l nm 0"
    hence "get_mh_nm nm l \<le> 0"
      using mh_le_nm_loc_sum
      by blast
    thus False
      using ContainsLocDirect
      by simp
  qed
next
  case (ContainsLocNested nm lp p nm_sub)
  show ?case
  proof
    assume Sum: "nm_loc_sum l nm 0"
    obtain mh fnm where "nm = NM mh fnm"
      using nm_get_eq
      by blast
    from Sum[unfolded \<open>nm = _\<close>] obtain pf where
      MhLe: "Rep_preal (mh l) \<le> Rep_preal (0 :: preal)" and
      PfSum: "pf has_sumA (Rep_preal (0 :: preal) - Rep_preal (mh l))" and
      Pf: "\<And>lp'. option_fold (\<lambda>lpm. nm_loc_sum' l (snd lpm) (pf lp')) (pf lp' = 0) (fnm lp')"
      by auto

    have PfNonneg: "\<And>lp'. pf lp' \<ge> 0"
    proof -
      fix lp'
      show "pf lp' \<ge> 0"
        apply (cases "fnm lp'")
        using Pf[of lp'] apply simp
        using Pf[of lp'] nm_loc_sum'_nonneg by fastforce
    qed

    have "Rep_preal (mh l) = 0"
      by (metis MhLe order_antisym prat_non_negative zero_preal.rep_eq)
    hence "pf has_sumA 0"
      using PfSum
      by (simp add: zero_preal.rep_eq)
    hence "pf lp = 0"
      by (rule has_sumA_zero_nonneg_point[OF _ PfNonneg])

    moreover have "fnm lp = Some (p, nm_sub)"
      using ContainsLocNested.hyps(1) \<open>nm = _\<close>
      by simp

    ultimately have "nm_loc_sum l nm_sub 0"
      using Pf[of lp]
      by (simp add: zero_preal.rep_eq)

    thus False
      using ContainsLocNested.IH
      by blast
  qed
qed


lemma consistent_external_wrt_ploc_same_support:
  assumes "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>1 \<rparr>) lp q\<^sub>1"
      and "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>2 \<rparr>) lp q\<^sub>2"
      and "q\<^sub>1 > 0" and "q\<^sub>2 > 0"
    shows "(\<forall>l. (0 < get_mh_nm nm\<^sub>1 l) = (0 < get_mh_nm nm\<^sub>2 l)) \<and>
           (\<forall>lp. (0 < get_mp_nm nm\<^sub>1 lp) = (0 < get_mp_nm nm\<^sub>2 lp))"
proof -
  obtain pid vs where "lp = (pid, vs)"
    by fastforce
  obtain pdecl\<^sub>1 pbody\<^sub>1 where
    D\<^sub>1: "ViperLang.predicates (program_total ctxt) pid = Some pdecl\<^sub>1"
        "ViperLang.predicate_decl.body pdecl\<^sub>1 = Some pbody\<^sub>1" and
    Sat\<^sub>1: "sat ctxt \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty,
                     get_total_full = \<phi>\<lparr> get_nm_total := 0 \<rparr> \<rparr>
              (get_mh_nm nm\<^sub>1) (get_mp_nm nm\<^sub>1) (syntactic_mult (Rep_preal q\<^sub>1) pbody\<^sub>1)"
    using assms(1)[unfolded \<open>lp = _\<close>] assms(3)
    by (auto elim: SatStep_case)
  obtain pdecl\<^sub>2 pbody\<^sub>2 where
    D\<^sub>2: "ViperLang.predicates (program_total ctxt) pid = Some pdecl\<^sub>2"
        "ViperLang.predicate_decl.body pdecl\<^sub>2 = Some pbody\<^sub>2" and
    Sat\<^sub>2: "sat ctxt \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty,
                     get_total_full = \<phi>\<lparr> get_nm_total := 0 \<rparr> \<rparr>
              (get_mh_nm nm\<^sub>2) (get_mp_nm nm\<^sub>2) (syntactic_mult (Rep_preal q\<^sub>2) pbody\<^sub>2)"
    using assms(2)[unfolded \<open>lp = _\<close>] assms(4)
    by (auto elim: SatStep_case)
  have "pbody\<^sub>1 = pbody\<^sub>2"
    using D\<^sub>1 D\<^sub>2
    by simp
  moreover have "Rep_preal q\<^sub>1 > 0" and "Rep_preal q\<^sub>2 > 0"
    using assms(3,4)
    by (simp_all add: less_preal.rep_eq zero_preal.rep_eq)
  ultimately show ?thesis
    using sat_same_support[OF Sat\<^sub>1] Sat\<^sub>2
    by simp
qed


text \<open>Two copies of the same predicate instance in a state have the same footprint: external
      consistency forces both sub-masks to satisfy the same (scaled) predicate body, evaluated in
      the same state, and by \<^const>\<open>sat\<close> the support of a satisfying mask does not depend on the
      scaling factor. Consequently a location that lies under one copy also lies under the other.\<close>

lemma contains_heap_loc_transfer:
  assumes "contains_heap_loc l nm\<^sub>1"
      and "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>1 \<rparr>) lp q\<^sub>1"
      and "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>2 \<rparr>) lp q\<^sub>2"
      and "q\<^sub>1 > 0" and "q\<^sub>2 > 0"
    shows "contains_heap_loc l nm\<^sub>2"
  using assms
proof (induct arbitrary: nm\<^sub>2 lp q\<^sub>1 q\<^sub>2 rule: contains_heap_loc.inducts)
  case (ContainsLocDirect nm\<^sub>1)
  show ?case
    apply (rule contains_heap_loc.ContainsLocDirect)
    using consistent_external_wrt_ploc_same_support
            [OF ContainsLocDirect.prems(1,2,3,4)] ContainsLocDirect.hyps
    by blast
next
  case (ContainsLocNested nm\<^sub>1 lp' p' nm')
  note Support = consistent_external_wrt_ploc_same_support[OF ContainsLocNested.prems(1,2,3,4)]

  have MpPos\<^sub>1: "0 < get_mp_nm nm\<^sub>1 lp'"
    using ContainsLocNested.hyps(1) Rep_posreal
    by simp
  hence "0 < get_mp_nm nm\<^sub>2 lp'"
    using Support
    by blast
  from this obtain p'' nm'' where Slot\<^sub>2: "get_fnm_nm nm\<^sub>2 lp' = Some (p'', nm'')"
    by (cases "get_fnm_nm nm\<^sub>2 lp'") auto

  obtain pid vs where "lp = (pid, vs)"
    by fastforce
  obtain pid' vs' where "lp' = (pid', vs')"
    by fastforce

  have Cons\<^sub>1: "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>1 \<rparr>)"
    using ContainsLocNested.prems(1)[unfolded \<open>lp = _\<close>]
    by (auto elim: SatStep_case)
  have Cons\<^sub>2: "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>2 \<rparr>)"
    using ContainsLocNested.prems(2)[unfolded \<open>lp = _\<close>]
    by (auto elim: SatStep_case)

  have All\<^sub>1: "\<And>pid\<^sub>0 vs\<^sub>0 q\<^sub>0 nm\<^sub>0. Some (q\<^sub>0, nm\<^sub>0) = get_fnm_nm nm\<^sub>1 (pid\<^sub>0, vs\<^sub>0) \<Longrightarrow>
        consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>0 \<rparr>) (pid\<^sub>0, vs\<^sub>0) (Rep_posreal q\<^sub>0)"
    using Cons\<^sub>1
    by (auto elim: SatAll_case)
  have All\<^sub>2: "\<And>pid\<^sub>0 vs\<^sub>0 q\<^sub>0 nm\<^sub>0. Some (q\<^sub>0, nm\<^sub>0) = get_fnm_nm nm\<^sub>2 (pid\<^sub>0, vs\<^sub>0) \<Longrightarrow>
        consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>0 \<rparr>) (pid\<^sub>0, vs\<^sub>0) (Rep_posreal q\<^sub>0)"
    using Cons\<^sub>2
    by (auto elim: SatAll_case)

  have Sub\<^sub>1: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm' \<rparr>) lp' (Rep_posreal p')"
    using All\<^sub>1 ContainsLocNested.hyps(1) \<open>lp' = _\<close>
    by fastforce
  have Sub\<^sub>2: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm'' \<rparr>) lp' (Rep_posreal p'')"
    using All\<^sub>2 Slot\<^sub>2 \<open>lp' = _\<close>
    by fastforce

  have "contains_heap_loc l nm''"
    apply (rule ContainsLocNested.hyps(3)[OF Sub\<^sub>1 Sub\<^sub>2])
    using Rep_posreal
    by simp_all

  thus ?case
    by (rule contains_heap_loc.ContainsLocNested[OF Slot\<^sub>2])
qed


definition heap_knownfolded_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a nested_mask \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "heap_knownfolded_rel Pr tr_field nm hb \<equiv>
    \<forall>lp kfm l field_ty_vpr field_bpl.
        hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm)) \<longrightarrow>
        declared_fields Pr (snd l) = Some field_ty_vpr \<longrightarrow>
        tr_field (snd l) = Some field_bpl \<longrightarrow>
        kfm (Address (fst l), NormalField field_bpl field_ty_vpr) \<longrightarrow>
        pred_folds_perm lp l nm"


text \<open>Permission-guarded variant of \<^const>\<open>heap_knownfolded_rel\<close>: the known-folded mask stored in
      the Boogie heap must only be backed by real permission for those predicate locations that
      still hold permission. This is the property that the \<open>IdenticalOnKnownLocations\<close> axioms
      require (they are guarded by \<open>Mask[null, pm_f] > 0\<close>), and unlike \<^const>\<open>heap_knownfolded_rel\<close>
      it survives an exhale that removes all permission of a predicate.\<close>

definition heap_knownfolded_rel_pos :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a nested_mask \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "heap_knownfolded_rel_pos Pr tr_field nm hb \<equiv>
    \<forall>lp kfm l field_ty_vpr field_bpl.
        get_mp_nm nm lp > 0 \<longrightarrow>
        hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm)) \<longrightarrow>
        declared_fields Pr (snd l) = Some field_ty_vpr \<longrightarrow>
        tr_field (snd l) = Some field_bpl \<longrightarrow>
        kfm (Address (fst l), NormalField field_bpl field_ty_vpr) \<longrightarrow>
        pred_folds_perm lp l nm"


lemma heap_knownfolded_rel_pos_stable:
  assumes "heap_knownfolded_rel_pos Pr tr_field nm hb"
      and "\<And>lp. hb' (Null, PredKnownFoldedField lp) = hb (Null, PredKnownFoldedField lp)"
    shows "heap_knownfolded_rel_pos Pr tr_field nm hb'"
  using assms
  unfolding heap_knownfolded_rel_pos_def
  by simp


lemma heap_knownfolded_rel_imp_pos:
  assumes "heap_knownfolded_rel Pr tr_field nm hb"
  shows "heap_knownfolded_rel_pos Pr tr_field nm hb"
  using assms
  unfolding heap_knownfolded_rel_def heap_knownfolded_rel_pos_def
  by blast


text \<open>The known-folded masks stored in the Boogie heap only ever flag normal field locations. This
      holds independently of whether the known-folded relation is currently tracked, and is required
      when the exhale havoc resets the known-folded mask of a predicate without permission: without
      it, a known-folded mask could refer to another predicate's known-folded mask location, which
      the framing axioms would then force to be preserved.\<close>

definition knownfolded_masks_normal_fields :: "'a bpl_heap_ty \<Rightarrow> bool"
  where "knownfolded_masks_normal_fields hb \<equiv>
    \<forall>lp kfm r f. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm)) \<longrightarrow>
                 kfm (r, f) \<longrightarrow> is_NormalField f"


text \<open>A witness for a predicate that holds top-level permission can always be found in that
      predicate's own sub-mask.\<close>

lemma pred_folds_perm_direct_witness_aux:
  assumes "pred_folds_perm lp l nm"
      and "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm \<rparr>)"
      and "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm_sub \<rparr>) lp q"
      and "q > 0"
    shows "contains_heap_loc l nm_sub"
  using assms
proof (induct rule: pred_folds_perm.inducts)
  case (ContainsPermDirect nm q' nm')
  have All: "\<And>pid\<^sub>0 vs\<^sub>0 q\<^sub>0 nm\<^sub>0. Some (q\<^sub>0, nm\<^sub>0) = get_fnm_nm nm (pid\<^sub>0, vs\<^sub>0) \<Longrightarrow>
        consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>0 \<rparr>) (pid\<^sub>0, vs\<^sub>0) (Rep_posreal q\<^sub>0)"
    using ContainsPermDirect.prems(1)
    by (auto elim: SatAll_case)
  obtain pid vs where "lp = (pid, vs)"
    by fastforce
  have "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm' \<rparr>) lp (Rep_posreal q')"
    using All ContainsPermDirect.hyps(1) \<open>lp = _\<close>
    by fastforce
  thus ?case
    using contains_heap_loc_transfer[OF ContainsPermDirect.hyps(2) _ ContainsPermDirect.prems(2)]
          ContainsPermDirect.prems(3) Rep_posreal
    by simp
next
  case (ContainsPermNested nm lp'' q'' nm'')
  have All: "\<And>pid\<^sub>0 vs\<^sub>0 q\<^sub>0 nm\<^sub>0. Some (q\<^sub>0, nm\<^sub>0) = get_fnm_nm nm (pid\<^sub>0, vs\<^sub>0) \<Longrightarrow>
        consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>0 \<rparr>) (pid\<^sub>0, vs\<^sub>0) (Rep_posreal q\<^sub>0)"
    using ContainsPermNested.prems(1)
    by (auto elim: SatAll_case)
  obtain pid'' vs'' where "lp'' = (pid'', vs'')"
    by fastforce
  have "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm'' \<rparr>) lp'' (Rep_posreal q'')"
    using All ContainsPermNested.hyps(1) \<open>lp'' = _\<close>
    by fastforce
  hence "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm'' \<rparr>)"
    using \<open>lp'' = _\<close>
    by (auto elim: SatStep_case)
  thus ?case
    using ContainsPermNested.hyps(3) ContainsPermNested.prems(2,3)
    by blast
qed


lemma pred_folds_perm_direct_witness:
  assumes "pred_folds_perm lp l (get_nm_total \<phi>)"
      and "consistent_external ctxt \<phi>"
      and "get_fnm_total \<phi> lp = Some (q, nm_sub)"
    shows "contains_heap_loc l nm_sub"
proof -
  have All: "\<And>pid\<^sub>0 vs\<^sub>0 q\<^sub>0 nm\<^sub>0. Some (q\<^sub>0, nm\<^sub>0) = get_fnm_total \<phi> (pid\<^sub>0, vs\<^sub>0) \<Longrightarrow>
        consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>0 \<rparr>) (pid\<^sub>0, vs\<^sub>0) (Rep_posreal q\<^sub>0)"
    using assms(2)
    by (auto elim: SatAll_case)
  obtain pid vs where "lp = (pid, vs)"
    by fastforce
  have Sub: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm_sub \<rparr>) lp (Rep_posreal q)"
    using All assms(3) \<open>lp = _\<close>
    by fastforce
  have Eq: "\<phi>\<lparr> get_nm_total := get_nm_total \<phi> \<rparr> = \<phi>"
    by simp
  show ?thesis
    apply (rule pred_folds_perm_direct_witness_aux[OF assms(1) _ Sub])
    using assms(2) Eq
     apply simp
    using Rep_posreal
    by simp
qed


text \<open>Preservation of the permission-guarded known-folded relation by the two state updates an
      exhale can perform. Exhaling a field access only changes the top-level field mask, which
      \<^const>\<open>pred_folds_perm\<close> does not depend on. Exhaling a predicate access either scales that
      predicate's sub-mask by a positive factor or removes its slot altogether, in which case the
      permission guard no longer applies to it; for all other predicates the slot is untouched, and
      a witness in the predicate's own slot is available by \<open>pred_folds_perm_direct_witness\<close>.\<close>

lemma heap_knownfolded_rel_pos_fnm_stable:
  assumes "heap_knownfolded_rel_pos Pr tr_field nm hb"
      and "get_fnm_nm nm = get_fnm_nm nm'"
    shows "heap_knownfolded_rel_pos Pr tr_field nm' hb"
  unfolding heap_knownfolded_rel_pos_def
proof (intro allI impI)
  fix lp kfm l field_ty_vpr field_bpl
  assume "0 < get_mp_nm nm' lp"
     and "hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))"
     and "declared_fields Pr (snd l) = Some field_ty_vpr"
     and "tr_field (snd l) = Some field_bpl"
     and "kfm (Address (fst l), NormalField field_bpl field_ty_vpr)"
  moreover have "\<And>lp\<^sub>0. get_mp_nm nm' lp\<^sub>0 = get_mp_nm nm lp\<^sub>0"
    using assms(2)
    by simp
  ultimately have "0 < get_mp_nm nm lp"
    by metis
  hence "pred_folds_perm lp l nm"
    using assms(1) \<open>hb _ = _\<close> \<open>declared_fields _ _ = _\<close> \<open>tr_field _ = _\<close> \<open>kfm _\<close>
    unfolding heap_knownfolded_rel_pos_def
    by blast
  thus "pred_folds_perm lp l nm'"
    using pred_folds_perm_mh_stable assms(2)
    by blast
qed

lemma heap_knownfolded_rel_pos_rm_from_lpm:
  assumes "heap_knownfolded_rel_pos Pr tr_field (get_nm_total \<phi>) hb"
      and "consistent_external ctxt \<phi>"
    shows "heap_knownfolded_rel_pos Pr tr_field (rm_from_lpm_nm (get_nm_total \<phi>) lp\<^sub>0 p) hb"
  unfolding heap_knownfolded_rel_pos_def
proof (intro allI impI)
  fix lp kfm l field_ty_vpr field_bpl
  let ?nm = "get_nm_total \<phi>"
  let ?nm' = "rm_from_lpm_nm ?nm lp\<^sub>0 p"
  assume Guard: "0 < get_mp_nm ?nm' lp"
     and Kfm: "hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))"
     and Decl: "declared_fields Pr (snd l) = Some field_ty_vpr"
     and Tr: "tr_field (snd l) = Some field_bpl"
     and Flag: "kfm (Address (fst l), NormalField field_bpl field_ty_vpr)"

  have Other: "\<And>lp'. lp' \<noteq> lp\<^sub>0 \<Longrightarrow> get_fnm_nm ?nm' lp' = get_fnm_nm ?nm lp'"
    by (cases ?nm) simp

  show "pred_folds_perm lp l ?nm'"
  proof (cases "lp = lp\<^sub>0")
    case False
    hence "get_mp_nm ?nm lp > 0"
      using Guard Other
      by simp
    hence "pred_folds_perm lp l ?nm"
      using assms(1) Kfm Decl Tr Flag
      unfolding heap_knownfolded_rel_pos_def
      by blast
    moreover obtain q nm_sub where Slot: "get_fnm_total \<phi> lp = Some (q, nm_sub)"
      using \<open>get_mp_nm ?nm lp > 0\<close>
      by (cases "get_fnm_nm ?nm lp") auto
    ultimately have "contains_heap_loc l nm_sub"
      using pred_folds_perm_direct_witness[OF _ assms(2) Slot]
      by simp
    thus ?thesis
      apply (rule pred_folds_perm.ContainsPermDirect[rotated])
      using Slot Other False
      by simp
  next
    case True
    obtain q nm_sub where Slot: "get_fnm_nm ?nm lp\<^sub>0 = Some (q, nm_sub)" and
                          NotRemoved: "\<not> (p \<ge> Rep_posreal q)"
      using Guard True
      by (cases "get_fnm_nm ?nm lp\<^sub>0"; cases ?nm) (auto split: if_split_asm)
    have Slot': "get_fnm_nm ?nm' lp\<^sub>0 =
                   Some (Abs_posreal (Rep_posreal q - p), (1 - p / Rep_posreal q) *\<^sub>s nm_sub)"
      using Slot NotRemoved
      by (cases ?nm) simp
    have "get_mp_nm ?nm lp\<^sub>0 > 0"
      using Slot Rep_posreal
      by simp
    hence "pred_folds_perm lp l ?nm"
      using assms(1) Kfm Decl Tr Flag True
      unfolding heap_knownfolded_rel_pos_def
      by blast
    hence Contains: "contains_heap_loc l nm_sub"
      using pred_folds_perm_direct_witness[OF _ assms(2)] Slot True
      by simp
    have Pos: "(1 :: preal) - p / Rep_posreal q > 0"
    proof -
      have "Rep_preal (Rep_posreal q) > 0"
        using Rep_posreal
        by (simp add: less_preal.rep_eq zero_preal.rep_eq)
      moreover have "Rep_preal p < Rep_preal (Rep_posreal q)"
        using NotRemoved
        by (simp add: less_eq_preal.rep_eq linorder_not_le less_preal.rep_eq)
      ultimately show ?thesis
        by (simp add: preal_to_real prat_non_negative)
    qed
    have Scaled: "contains_heap_loc l ((1 - p / Rep_posreal q) *\<^sub>s nm_sub)"
      by (rule contains_heap_loc_scale[OF Contains Pos])
    show ?thesis
      apply (rule pred_folds_perm.ContainsPermDirect[rotated])
       apply (rule Scaled)
      using Slot' True
      by simp
  qed
qed


definition heap_knownfolded_var_rel :: "knownfolded_rel_options \<Rightarrow> ViperLang.program \<Rightarrow> var_context \<Rightarrow> (field_ident \<rightharpoonup> Lang.vname) \<Rightarrow> vname \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns \<equiv> \<exists>hb.
       lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and>
       (\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))) \<and>
       knownfolded_masks_normal_fields hb \<and>
       (kf_turned_on opt \<longrightarrow> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb) \<and>
       (kf_pos_turned_on opt \<longrightarrow> heap_knownfolded_rel_pos Pr FieldTr (get_nm_total_full \<omega>) hb)"


lemma knownfolded_masks_normal_fields_elim:
  assumes "knownfolded_masks_normal_fields hb"
      and "hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))"
      and "kfm (r, f)"
    shows "is_NormalField f"
  using assms
  unfolding knownfolded_masks_normal_fields_def
  by blast


lemma kfm_flag_upd_normal_field:
  assumes "\<And>r f. kfm (r, f) \<Longrightarrow> is_NormalField f"
      and "(kfm((r', NormalField fb ft) := True)) (r, f)"
    shows "is_NormalField f"
  using assms
  by (auto split: if_split_asm)


lemma knownfolded_masks_normal_fields_upd:
  assumes "knownfolded_masks_normal_fields hb"
      and "\<And>r f. kfm (r, f) \<Longrightarrow> is_NormalField f"
    shows "knownfolded_masks_normal_fields (hb((Null, PredKnownFoldedField lp) \<mapsto> AbsV (AKnownFoldedMask kfm)))"
  using assms
  unfolding knownfolded_masks_normal_fields_def
  by auto


lemma heap_knownfolded_var_rel_masks_normal_fields:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns"
      and "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb))"
    shows "knownfolded_masks_normal_fields hb"
  using assms
  unfolding heap_knownfolded_var_rel_def
  by auto


text \<open>Packaged form of the preservation lemmas for the state update performed when exhaling a
      predicate access: the Boogie heap is unchanged, the unguarded relation is not tracked, and the
      guarded one is preserved.\<close>

lemma heap_knownfolded_var_rel_rm_from_lpm:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns"
      and "\<not> kf_turned_on opt"
      and "kf_pos_turned_on opt \<Longrightarrow> consistent_external ctxt (get_total_full \<omega>)"
      and "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
      and "\<omega>' = rm_from_lpm_total_full \<omega> lp p"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns'"
proof -
  obtain hb where hb:
    "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb))"
    "\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))"
    "knownfolded_masks_normal_fields hb"
    "kf_pos_turned_on opt \<longrightarrow> heap_knownfolded_rel_pos Pr FieldTr (get_nm_total_full \<omega>) hb"
    using assms(1)
    unfolding heap_knownfolded_var_rel_def
    by blast

  have Nm: "get_nm_total_full \<omega>' = rm_from_lpm_nm (get_nm_total (get_total_full \<omega>)) lp p"
    using assms(5)
    by simp

  show ?thesis
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ hb])
    apply (intro conjI)
    using hb(1) assms(4)
       apply argo
    using hb(2)
      apply blast
    using hb(3)
     apply blast
    using assms(2)
     apply blast
    apply (intro impI)
    apply (simp only: Nm)
    apply (rule heap_knownfolded_rel_pos_rm_from_lpm[where \<phi> = "get_total_full \<omega>"])
    using hb(4)
     apply simp
    using assms(3)
    by simp
qed


lemma heap_knownfolded_var_rel_stable:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns"
          "get_nm_total_full \<omega> = get_nm_total_full \<omega>'"
          "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns'"
  using assms
  unfolding heap_knownfolded_var_rel_def
  by auto


lemma heap_knownfolded_var_rel_stable_kfm_unchanged:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns"
      and "get_nm_total_full \<omega> = get_nm_total_full \<omega>'"
      and "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb))"
      and "lookup_var \<Lambda> ns' hvar = Some (AbsV (AHeap hb'))"
      and "\<And>r lp. hb (r, PredKnownFoldedField lp) = hb' (r, PredKnownFoldedField lp)"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns'"
  using assms
  unfolding heap_knownfolded_var_rel_def heap_knownfolded_rel_def heap_knownfolded_rel_pos_def
            knownfolded_masks_normal_fields_def
  by auto


lemma heap_knownfolded_var_rel_stable_mh_changed:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns"
      and "get_fnm_total_full \<omega> = get_fnm_total_full \<omega>'"
      and "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns'"
proof -
  obtain hb where hb: "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and>
                       (\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))) \<and>
                       knownfolded_masks_normal_fields hb \<and>
                       (kf_turned_on opt \<longrightarrow> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb) \<and>
                       (kf_pos_turned_on opt \<longrightarrow> heap_knownfolded_rel_pos Pr FieldTr (get_nm_total_full \<omega>) hb)"
    using assms(1) heap_knownfolded_var_rel_def
    by blast

  have GuardSame: "get_mp_nm (get_nm_total_full \<omega>') = get_mp_nm (get_nm_total_full \<omega>)"
    using assms(2)
    by simp

  show ?thesis
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ hb])
    apply (intro conjI)
    using hb assms(3)
        apply argo
    using hb
       apply blast
    using hb
      apply blast
     defer
  proof
    assume "kf_pos_turned_on opt"
    hence *: "heap_knownfolded_rel_pos Pr FieldTr (get_nm_total_full \<omega>) hb"
      using hb
      by force
    show "heap_knownfolded_rel_pos Pr FieldTr (get_nm_total_full \<omega>') hb"
      unfolding heap_knownfolded_rel_pos_def
      apply (intro impI allI)
      using * pred_folds_perm_mh_stable assms(2) GuardSame
      unfolding heap_knownfolded_rel_pos_def
      by fastforce
  next
    show "kf_turned_on opt \<longrightarrow> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>') hb"
    proof
      assume "kf_turned_on opt"
      hence *: "heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb"
        using hb
        by force
      show "heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>') hb"
        unfolding heap_knownfolded_rel_def
        apply (intro impI allI)
        using * pred_folds_perm_mh_stable assms(2,3)
        unfolding heap_knownfolded_rel_def
        by fastforce
    qed
  qed
qed


lemma heap_knownfolded_rel_stable_larger_nm:
  assumes "heap_knownfolded_rel Pr tr_field nm hb"
      and "nm \<le> nm'"
    shows "heap_knownfolded_rel Pr tr_field nm' hb"
  using pred_folds_perm_stable_larger_nm
  by (smt (verit, ccfv_threshold) assms heap_knownfolded_rel_def)


text \<open>Growing the state can turn the permission guard on for further predicates, so the guarded
      relation is not preserved on its own. It is preserved whenever the unguarded relation is
      tracked as well, which is the case everywhere the state grows (the guarded relation is only
      tracked on its own during an exhale, where the state never grows).\<close>

lemma heap_knownfolded_var_rel_stable_larger_\<omega>:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns"
      and "\<omega> \<le> \<omega>'"
      and "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
      and PosImpliesStrict: "kf_pos_turned_on opt \<Longrightarrow> kf_turned_on opt"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns'"
proof -
  obtain hb where hb:
    "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb))"
    "\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))"
    "knownfolded_masks_normal_fields hb"
    "kf_turned_on opt \<longrightarrow> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb"
    using assms(1)
    unfolding heap_knownfolded_var_rel_def
    by blast

  have Strict: "kf_turned_on opt \<longrightarrow> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>') hb"
    using hb(4) assms(2) heap_knownfolded_rel_stable_larger_nm less_eq_full_total_stateD_2
    by blast

  show ?thesis
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ hb])
    apply (intro conjI)
    using hb(1) assms(3)
       apply argo
    using hb(2)
      apply blast
    using hb(3)
      apply blast
     apply (rule Strict)
  proof
    assume "kf_pos_turned_on opt"
    thus "heap_knownfolded_rel_pos Pr FieldTr (get_nm_total_full \<omega>') hb"
      using Strict PosImpliesStrict heap_knownfolded_rel_imp_pos
      by simp
  qed
qed


definition zero_knownfolded_mask where
  "zero_knownfolded_mask \<equiv> AbsV (AKnownFoldedMask (\<lambda>_. False))"


end


end
