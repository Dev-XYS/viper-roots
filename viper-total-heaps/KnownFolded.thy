theory KnownFolded
  imports TotalSemantics ViperBoogieAbsValueInst BoogieInterface
begin


record knownfolded_rel_options =
  kf_turned_on :: bool


context begin


\<comment> \<open>Todo: This type synonym already appears in \<^file>\<open>ViperBoogieBasicRel.thy\<close>. Merge them.\<close>
private type_synonym 'a bpl_heap_ty = "ref \<times> 'a vb_field \<rightharpoonup> ('a vbpl_absval) bpl_val"


inductive pred_folds_perm :: "'a predicate_loc \<Rightarrow> heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> bool"
  for lp :: "'a predicate_loc" and l :: "heap_loc" where
  ContainsPermDirect:
  "\<lbrakk> get_fnm_nm nm lp = Some (_,nm');
     get_mh_nm nm' l > 0 \<rbrakk> \<Longrightarrow>
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
  obtain p' nm_sub' where "get_fnm_nm nm' lp = Some (p', nm_sub')" and "nm_sub \<le> nm_sub'"
    apply (cases nm; cases nm')
    using ContainsPermDirect.prems[unfolded less_eq_nested_mask_def]
    apply simp
    by (smt (verit, del_insts) ContainsPermDirect.hyps(1) get_fnm_nm.simps has_Some_iff less_eq_nested_mask_def option_fold.simps(1) order_le_less prod.exhaust_sel snd_conv)
  show ?case
    apply (rule pred_folds_perm.ContainsPermDirect)
     apply fact
    by (meson ContainsPermDirect.hyps(2) \<open>nm_sub \<le> nm_sub'\<close> dual_order.strict_trans1 le_funE less_eq_nested_maskD)
next
  case (ContainsPermNested nm lp' p nm_sub)
  obtain mh fnm where "nm = NM mh fnm" using nm_get_eq by blast
  obtain mh' fnm' where "nm' = NM mh' fnm'" using nm_get_eq by blast
  obtain p' nm_sub' where "get_fnm_nm nm' lp' = Some (p', nm_sub')" and "nm_sub \<le> nm_sub'"
    using ContainsPermNested.prems[unfolded less_eq_nested_mask_def \<open>nm = _\<close> \<open>nm' = _\<close>, simplified]
    by (smt (verit) ContainsPermNested.hyps(1) \<open>nm = NM mh fnm\<close> \<open>nm' = NM mh' fnm'\<close> get_fnm_nm.simps has_Some_iff less_eq_nested_mask_def option_fold.simps(1) order_le_less prod.exhaust_sel snd_conv)
  show ?case
    apply (rule pred_folds_perm.ContainsPermNested)
     apply fact
    by (simp add: ContainsPermNested.IH \<open>nm_sub \<le> nm_sub'\<close>)
qed


definition heap_knownfolded_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a nested_mask \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "heap_knownfolded_rel Pr tr_field nm hb \<equiv>
    \<forall> lp kfm l field_ty_vpr field_bpl.
        hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm)) \<longrightarrow>
        declared_fields Pr (snd l) = Some field_ty_vpr \<longrightarrow>
        tr_field (snd l) = Some field_bpl \<longrightarrow>
        kfm (Address (fst l), NormalField field_bpl field_ty_vpr) \<longrightarrow>
        pred_folds_perm lp l nm"


definition heap_knownfolded_var_rel :: "knownfolded_rel_options \<Rightarrow> ViperLang.program \<Rightarrow> var_context \<Rightarrow> (field_ident \<rightharpoonup> Lang.vname) \<Rightarrow> vname \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns \<equiv> kf_turned_on opt \<longrightarrow>
       (\<exists>hb. lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and>
             heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb)"


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
proof (cases "kf_turned_on opt")
  case True
  then obtain hb where *: "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb"
    using assms(1)
    unfolding heap_knownfolded_var_rel_def
    by auto
  show ?thesis
    unfolding heap_knownfolded_var_rel_def
    apply (intro impI)
    apply (thin_tac _)
    apply (rule exI[of _ hb])
    using * pred_folds_perm_mh_stable assms(2,3)
    unfolding heap_knownfolded_rel_def
    by fastforce
next
  case False
  then show ?thesis
    unfolding heap_knownfolded_var_rel_def
    by simp
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
  by (metis (full_types) assms heap_knownfolded_rel_stable_larger_nm heap_knownfolded_var_rel_def less_eq_full_total_stateD_2)


end


end
