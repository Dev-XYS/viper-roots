theory KnownFolded
  imports TotalSemantics ViperBoogieAbsValueInst BoogieInterface
begin


record knownfolded_rel_options =
  dummy :: bool


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
    "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns \<equiv>
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
proof -
  obtain hb where *: "lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and> heap_knownfolded_rel Pr FieldTr (get_nm_total_full \<omega>) hb"
    using assms(1)
    unfolding heap_knownfolded_var_rel_def
    by auto
  show ?thesis
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ hb])
    using * pred_folds_perm_mh_stable assms(2,3)
    unfolding heap_knownfolded_rel_def
    by fastforce
qed

lemma heap_knownfolded_var_rel_stable_larger_\<omega>:
  assumes "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega> ns"
      and "\<omega> \<le> \<omega>'"
      and "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
    shows "heap_knownfolded_var_rel opt Pr \<Lambda> FieldTr hvar \<omega>' ns'"
  sorry


end


end
