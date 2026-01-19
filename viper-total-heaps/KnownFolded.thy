theory KnownFolded
  imports TotalSemantics ViperBoogieAbsValueInst BoogieInterface
begin


record knownfolded_rel_options =
  kf_turned_on :: bool


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


definition heap_knownfolded_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a nested_mask \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "heap_knownfolded_rel Pr tr_field nm hb \<equiv>
    \<forall>lp kfm l field_ty_vpr field_bpl.
        hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm)) \<longrightarrow>
        declared_fields Pr (snd l) = Some field_ty_vpr \<longrightarrow>
        tr_field (snd l) = Some field_bpl \<longrightarrow>
        kfm (Address (fst l), NormalField field_bpl field_ty_vpr) \<longrightarrow>
        pred_folds_perm lp l nm"


definition heap_knownfolded_var_rel :: "knownfolded_rel_options \<Rightarrow> ViperLang.program \<Rightarrow> var_context \<Rightarrow> (field_ident \<rightharpoonup> Lang.vname) \<Rightarrow> vname \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns \<equiv> \<exists>hb.
       lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and>
       (\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))) \<and>
       (kf_turned_on opt \<longrightarrow> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb)"


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
  unfolding heap_knownfolded_var_rel_def heap_knownfolded_rel_def
  by auto


lemma heap_knownfolded_var_rel_stable_mh_changed:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns"
      and "get_fnm_total_full \<omega> = get_fnm_total_full \<omega>'"
      and "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns'"
proof -
  obtain hb where hb: "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and>
                       (\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))) \<and>
                       (kf_turned_on opt \<longrightarrow> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb)"
    using assms(1) heap_knownfolded_var_rel_def
    by blast
  show ?thesis
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ hb])
    apply (intro conjI)
    using hb assms(3)
      apply argo
    using hb
     apply blast
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


lemma heap_knownfolded_rel_stable_larger_nm:
  assumes "heap_knownfolded_rel Pr tr_field nm hb"
      and "nm \<le> nm'"
    shows "heap_knownfolded_rel Pr tr_field nm' hb"
  using pred_folds_perm_stable_larger_nm
  by (smt (verit, ccfv_threshold) assms heap_knownfolded_rel_def)


lemma heap_knownfolded_var_rel_stable_larger_\<omega>:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns"
      and "\<omega> \<le> \<omega>'"
      and "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns'"
  by (smt (verit, best) assms(1,2,3) heap_knownfolded_rel_stable_larger_nm heap_knownfolded_var_rel_def less_eq_full_total_stateD_2)


definition zero_knownfolded_mask where
  "zero_knownfolded_mask \<equiv> AbsV (AKnownFoldedMask (\<lambda>_. False))"


end


end
