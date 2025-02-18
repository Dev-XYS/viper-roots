theory TotalExtConsPreservation
  imports TotalExtConsProps TotalIntConsPreservation TotalSemanticsProperties
begin


subsection \<open>Definitions (Todo: put somewhere else)\<close>

definition ctxt_pred_self_framing :: "'a total_context \<Rightarrow> bool" where
  "ctxt_pred_self_framing ctxt \<equiv> \<forall>pid pdecl.
     ViperLang.predicates (program_total ctxt) pid = Some pdecl \<longrightarrow>
     pred_self_framing ctxt pdecl"


subsection \<open>Lemmas (Todo: put somewhere else)\<close>

lemma extcons_preserved_by_mh_change:
  assumes "consistent_external ctxt \<phi>"
  shows "consistent_external ctxt (upd_mh_total \<phi> mh')"
  apply standard
  using assms consistent_external.cases get_fnm_total.simps total_state.surjective total_state.update_convs(2)
  by fastforce

lemma nm_add_mh_sub:
  assumes "nm\<^sub>1 + nm\<^sub>2 = nm"
  shows "get_mh_nm nm - get_mh_nm nm\<^sub>1 = get_mh_nm nm\<^sub>2"
  by (metis add_masks_minus assms get_mh_nm__plus)

lemma nm_add_mp_sub:
  assumes "nm\<^sub>1 + nm\<^sub>2 = nm"
  shows "get_mp_nm nm - get_mp_nm nm\<^sub>1 = get_mp_nm nm\<^sub>2"
  by (metis add_masks_minus assms get_mp_nm_distr_over_plus)

lemma nm_plus_lpm_plus_Some_Some:
  assumes "nm\<^sub>1 + nm\<^sub>2 = nm"
      and "get_fnm_nm nm\<^sub>1 lp = Some (p\<^sub>1, nm'\<^sub>1)"
      and "get_fnm_nm nm\<^sub>2 lp = Some (p\<^sub>2, nm'\<^sub>2)"
      and "get_fnm_nm nm lp = Some (p, nm')"
    shows "nm'\<^sub>1 + nm'\<^sub>2 = nm'"
      and "p\<^sub>1 + p\<^sub>2 = p"
proof -
  obtain mh\<^sub>1 fnm\<^sub>1 where "nm\<^sub>1 = NM mh\<^sub>1 fnm\<^sub>1"
    using nm_get_eq by blast
  obtain mh\<^sub>2 fnm\<^sub>2 where "nm\<^sub>2 = NM mh\<^sub>2 fnm\<^sub>2"
    using nm_get_eq by blast
  show "nm'\<^sub>1 + nm'\<^sub>2 = nm'"
    using assms(1)[simplified \<open>nm\<^sub>1 = _\<close> \<open>nm\<^sub>2 = _\<close> plus_nested_mask_def, simplified]
    by (metis (mono_tags, lifting) \<open>nm\<^sub>1 = NM mh\<^sub>1 fnm\<^sub>1\<close> \<open>nm\<^sub>2 = NM mh\<^sub>2 fnm\<^sub>2\<close> assms(2) assms(3) assms(4) combine_options_simps(3) get_fnm_nm.simps option.sel pfun_comb_def plus_nested_mask_def snd_conv)
  show "p\<^sub>1 + p\<^sub>2 = p"
    using assms(1)[simplified \<open>nm\<^sub>1 = _\<close> \<open>nm\<^sub>2 = _\<close> plus_nested_mask_def, simplified]
    by (metis (mono_tags, lifting) \<open>nm\<^sub>1 = NM mh\<^sub>1 fnm\<^sub>1\<close> \<open>nm\<^sub>2 = NM mh\<^sub>2 fnm\<^sub>2\<close> assms(2) assms(3) assms(4) combine_options_simps(3) get_fnm_nm.simps option.sel pfun_comb_def plus_nested_mask_def fst_conv)
qed

lemma nm_plus_lpm_plus_Some_None:
  assumes "nm\<^sub>1 + nm\<^sub>2 = nm"
      and "get_fnm_nm nm\<^sub>1 lp = Some (p\<^sub>1, nm'\<^sub>1)"
      and "get_fnm_nm nm\<^sub>2 lp = None"
    shows "get_fnm_nm nm lp = Some (p\<^sub>1, nm'\<^sub>1)"
  apply (subst assms(1)[symmetric])
  apply (simp add: plus_nested_mask_def)
  apply (cases nm\<^sub>1, cases nm\<^sub>2)
  using assms(2,3)
  by (simp add: pfun_comb_def)

lemma exhale_pred_body_part_extcons_wrt_ploc:
  assumes "ViperLang.predicates (program_total ctxt) pid = Some pdecl"
      and "ViperLang.predicate_decl.body pdecl = Some pbody"
      and "vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pdecl)"
      and "\<omega> = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = \<phi> \<rparr>"
      and "consistent_external ctxt \<phi>"
      and "red_exhale ctxt StateCons \<omega>0 (syntactic_mult (Rep_preal p) pbody) \<omega> (RNormal \<omega>')"
      and "get_nm_total_full \<omega>' + nm_exh = get_nm_total_full \<omega>"
      and "ctxt_wf_pred ctxt"
    shows "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm_exh \<rparr>) (pid,vs) p"
  apply standard
      apply (rule assms)+
proof -
  have "get_store_total \<omega> = nth_option vs"
    by (simp add: assms(4))
  moreover have "get_mh_total (\<phi>\<lparr> get_nm_total := nm_exh \<rparr>) = get_mh_total_full \<omega> - get_mh_total_full \<omega>'"
    using nm_add_mh_sub[OF assms(7)]
    by force
  moreover have "get_mp_total (\<phi>\<lparr> get_nm_total := nm_exh \<rparr>) = get_mp_total_full \<omega> - get_mp_total_full \<omega>'"
    using nm_add_mp_sub[OF assms(7)]
    by force
  ultimately show "sat ctxt \<lparr> get_store_total = nth_option vs, get_trace_total = \<lambda>x. None,
                              get_total_full = \<phi>\<lparr> get_nm_total := nm_exh, get_nm_total := 0 \<rparr> \<rparr>
                       (get_mh_total (\<phi>\<lparr> get_nm_total := nm_exh \<rparr>))
                       (get_mp_total (\<phi>\<lparr> get_nm_total := nm_exh \<rparr>))
                       (syntactic_mult (Rep_preal p) pbody)"
    using exhale_diff_sat[OF _ assms(6), of \<omega>'] assms ctxt_wf_pred_def syntactic_mult_supported
          prat_non_negative total_state.surjective total_state.update_convs(2)
    by fastforce
next
  show "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm_exh \<rparr>)"
  proof
    fix pid vs q\<^sub>s nm\<^sub>s
    assume lpm\<^sub>s: "Some (q\<^sub>s, nm\<^sub>s) = get_fnm_total (\<phi>\<lparr> get_nm_total := nm_exh \<rparr>) (pid,vs)"
    show "consistent_external_wrt_ploc ctxt
            (\<phi>\<lparr> get_nm_total := nm_exh, get_nm_total := nm\<^sub>s \<rparr>) (pid,vs) (Rep_posreal q\<^sub>s)"
    proof (cases "get_fnm_total_full \<omega>' (pid,vs)")
      case None
      have "Some (q\<^sub>s, nm\<^sub>s) = get_fnm_total_full \<omega> (pid,vs)"
        by (metis None add.commute assms(7) get_fnm_total.simps get_fnm_total_full.simps get_nm_total_full.simps lpm\<^sub>s nm_plus_lpm_plus_Some_None total_state_update_nm_read)
      then show ?thesis
        using assms(4) assms(5) consistent_external.simps
        by fastforce
    next
      case (Some lpm)
      obtain q\<^sub>e nm\<^sub>e where "lpm = (q\<^sub>e, nm\<^sub>e)"
        by fastforce
      obtain q\<^sub>a nm\<^sub>a where
        lpm\<^sub>a: "get_fnm_total_full \<omega> (pid,vs) = Some (q\<^sub>a, nm\<^sub>a)" and
        "q\<^sub>a \<ge> q\<^sub>e" and
        "nm\<^sub>e = (Rep_posreal (q\<^sub>e / q\<^sub>a)) *\<^sub>s nm\<^sub>a"
        using exhale_fraction[OF assms(6) Some[simplified \<open>lpm = _\<close>]]
        by blast
      hence nm\<^sub>a_extcons: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>a \<rparr>) (pid,vs) (Rep_posreal q\<^sub>a)"
        using SatAll_case[OF assms(5)]
        by (metis assms(4) full_total_state.select_convs(3) get_fnm_total.simps get_fnm_total_full.simps)

      have "q\<^sub>e + q\<^sub>s = q\<^sub>a" and "nm\<^sub>e + nm\<^sub>s = nm\<^sub>a"
        using nm_plus_lpm_plus_Some_Some[OF assms(7), of "(pid,vs)"]
        by (metis (mono_tags, lifting) Some lpm\<^sub>s lpm\<^sub>a \<open>lpm = _\<close> get_fnm_total.simps get_fnm_total_full.simps get_nm_total_full.simps total_state_update_nm_read)+
      have "nm\<^sub>e + (Rep_posreal ((q\<^sub>a - q\<^sub>e) / q\<^sub>a)) *\<^sub>s nm\<^sub>a = nm\<^sub>a"
        apply (subst \<open>nm\<^sub>e = _\<close>)
        apply (subgoal_tac "Rep_posreal (q\<^sub>e / q\<^sub>a) + Rep_posreal ((q\<^sub>a - q\<^sub>e) / q\<^sub>a) = 1")
         apply (metis preal_semimodule_class.scale_one scale_add_left)
        apply (subst plus_posreal.rep_eq[symmetric])
        unfolding field_divide_inverse_posreal[of q\<^sub>e q\<^sub>a] field_divide_inverse_posreal[of "q\<^sub>a - q\<^sub>e" q\<^sub>a]
        unfolding comm_semiring_class.distrib[symmetric]
        by (metis PosReal.padd_cancellative Rep_posreal_inverse \<open>q\<^sub>e + q\<^sub>s = q\<^sub>a\<close> \<open>q\<^sub>e \<le> q\<^sub>a\<close> add.commute field_inverse_posreal greater_minus_plus less_eq_posreal.rep_eq minus_posreal_def mult.commute one_posreal.rep_eq plus_posreal.rep_eq)
        
      hence "nm\<^sub>s = (Rep_posreal ((q\<^sub>a - q\<^sub>e) / q\<^sub>a)) *\<^sub>s nm\<^sub>a"
        using \<open>nm\<^sub>e + nm\<^sub>s = nm\<^sub>a\<close>
        by force
      have "q\<^sub>s = q\<^sub>a - q\<^sub>e"
        using Rep_posreal_inverse \<open>q\<^sub>e + q\<^sub>s = q\<^sub>a\<close> minus_posreal_def plus_posreal.rep_eq
        by (metis PosReal.padd_cancellative \<open>q\<^sub>e \<le> q\<^sub>a\<close> add.commute greater_minus_plus less_eq_posreal.rep_eq)
      show ?thesis
        using fraction_consistent_external(1)[OF assms(8) nm\<^sub>a_extcons, of "Rep_posreal (q\<^sub>s / q\<^sub>a)"]
        apply (subgoal_tac "Rep_posreal (q\<^sub>s / q\<^sub>a) * Rep_posreal q\<^sub>a = Rep_posreal q\<^sub>s")
         apply simp
         apply (subst \<open>q\<^sub>s = _\<close>)
         apply (subst \<open>nm\<^sub>s = _\<close>)
        using \<open>q\<^sub>s = q\<^sub>a - q\<^sub>e\<close>
         apply fastforce
        by (metis field_divide_inverse_posreal field_inverse_posreal mult.assoc mult.right_neutral times_posreal.rep_eq)
    qed
  qed
qed


subsection \<open>Preserved by Inhale\<close>

lemma extcons_preserved_by_inhale_perm_single:
  assumes "\<omega>' \<in> inhale_perm_single StateCons \<omega> lh p_opt"
      and "consistent_external ctxt (get_total_full \<omega>)"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof -
  obtain q where "\<omega>' = upd_mh_loc_total_full \<omega> lh (get_mh_total_full \<omega> lh + q)"
    using iffD1[OF mem_Collect_eq assms(1)[simplified inhale_perm_single_def]]
    by blast
  thus ?thesis
    using assms(2) extcons_preserved_by_mh_change
    by auto
qed

lemma extcons_preserved_by_add_to_lpm_nonzero:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm \<rparr> lp p"
      and "p > 0"
    shows "consistent_external ctxt (get_total_full (add_to_lpm_nonzero_total_full \<omega> lp (Abs_posreal p) nm))"
proof
  fix pid vs q nm'
  assume lpm: "Some (q, nm') = get_fnm_total (get_total_full (add_to_lpm_nonzero_total_full \<omega> lp (Abs_posreal p) nm)) (pid,vs)"
  show "consistent_external_wrt_ploc ctxt
          (get_total_full (add_to_lpm_nonzero_total_full \<omega> lp (Abs_posreal p) nm) \<lparr>get_nm_total := nm'\<rparr>)
          (pid,vs) (Rep_posreal q)"
  proof (cases "(pid,vs) = lp")
    case True
    show ?thesis
    proof (cases "get_fnm_total_full \<omega> lp")
      case None
      hence "Rep_posreal q = p \<and> nm' = nm"
        using True lpm
        apply simp
        using assms(3)
        by (simp add: Abs_posreal_inverse)
      then show ?thesis
        apply simp
        by (metis (full_types) True assms(2) get_hh_total_full.simps old.unit.exhaust total_state.surjective total_state.update_convs(2))
    next
      case (Some lpm_orig)
      obtain p_orig nm_orig where
        "lpm_orig = (p_orig, nm_orig)"
        by fastforce
      hence "Rep_posreal q = Rep_posreal p_orig + p \<and> nm' = nm_orig + nm"
        using True lpm Some
        apply simp
        by (simp add: Abs_posreal_inverse assms(3) plus_posreal.rep_eq)
      moreover have "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_orig \<rparr> lp (Rep_posreal p_orig)"
        by (metis Some True \<open>lpm_orig = _\<close> assms(1) consistent_external.cases get_fnm_total_full.simps get_hh_total_full.simps total_state.cases total_state.simps(1) total_state.update_convs(2))
      ultimately show ?thesis
        apply simp
        using assms(2)
        by (metis (full_types) True get_hh_total_full.simps old.unit.exhaust sum_consistent_external(2) total_state.surjective total_state.update_convs(2))
    qed
  next
    case False
    then show ?thesis
      apply simp
      using SatAll_case[OF assms(1)] lpm
      by fastforce
  qed
qed


lemma extcons_preserved_by_inhale_perm_single_pred:
  assumes "\<omega>' \<in> inhale_perm_single_pred ctxt StateCons \<omega> lp p_opt"
      and "consistent_external ctxt (get_total_full \<omega>)"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof -
  obtain \<phi>_inh q where
    inh_extcons: "consistent_external_wrt_ploc ctxt \<phi>_inh lp q" and
    hh_same: "get_hh_total \<phi>_inh = get_hh_total_full \<omega>" and
    \<omega>': "\<omega>' = (if q = 0 then \<omega> else add_to_lpm_nonzero_total_full \<omega> lp (Abs_posreal q) (get_nm_total \<phi>_inh))"
    using iffD1[OF mem_Collect_eq assms(1)[simplified inhale_perm_single_pred_def]]
    by blast
  consider (InhZero) "\<omega>' = \<omega>" | (InhNonZero) "\<omega>' = add_to_lpm_nonzero_total_full \<omega> lp (Abs_posreal q) (get_nm_total \<phi>_inh)"
    using \<omega>'
    by argo
  thus ?thesis
  proof cases
    case InhZero
    then show ?thesis
      using assms(2)
      by blast
  next
    case InhNonZero
    show ?thesis
      by (metis (full_types) \<omega>' assms(2) extcons_preserved_by_add_to_lpm_nonzero hh_same inh_extcons old.unit.exhaust pperm_pnone_pgt total_state.surjective)
  qed
qed

lemma extcons_preserved_by_red_inhale:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_inhale ctxt R A \<omega> (RNormal \<omega>')"
    shows "consistent_external ctxt (get_total_full \<omega>')"
  using assms
proof (induction A arbitrary: \<omega> \<omega>')
  case IH: (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure e)
    then show ?thesis
      by (metis IH.prems(1) IH.prems(2) InhPure_case result_total.distinct(3) result_total.inject result_total.simps(7))
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      obtain W' r p where
        "W' = (if r = Null then {\<omega>} else inhale_perm_single R \<omega> (the_address r,f) (Some (Abs_preal p))) \<and>
         th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W' (RNormal \<omega>')"
        using IH.prems(2)
        by (fastforce simp: Acc PureExp elim: InhAccPerm_case)
      then show ?thesis
        using extcons_preserved_by_inhale_perm_single
        by (metis IH.prems(1) empty_iff insert_iff th_result_rel_normal)
    next
      case Wildcard
      obtain W' r where
        "W' = inhale_perm_single R \<omega> (the_address r,f) None \<and>
         th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' (RNormal \<omega>')"
        using IH.prems(2)
        by (fastforce simp: Acc Wildcard elim: InhAccWildcard_case)
      then show ?thesis
        using extcons_preserved_by_inhale_perm_single IH.prems(1) th_result_rel_normal
        by blast
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      obtain W' v_args p where
        "W' = inhale_perm_single_pred ctxt R \<omega> (pid, v_args) (Some (Abs_preal p)) \<and>
         th_result_rel (p \<ge> 0) (W' \<noteq> {}) W' (RNormal \<omega>')"
        using IH(2)[simplified AccPredicate PureExp]
        by (fastforce elim: InhAccPredPerm_case)
      then show ?thesis
        using IH.prems(1) extcons_preserved_by_inhale_perm_single_pred th_result_rel_normal
        by blast
    next
      case Wildcard
      obtain W' v_args where
        "W' = inhale_perm_single_pred ctxt R \<omega> (pid, v_args) None \<and>
         th_result_rel True (W' \<noteq> {}) W' (RNormal \<omega>')"
        using IH(2)[simplified AccPredicate Wildcard]
        by (blast elim: InhAccPredWildcard_case)
      then show ?thesis
        using IH.prems(1) extcons_preserved_by_inhale_perm_single_pred th_result_rel_normal
        by blast
    qed
  qed
next
  case (Imp x1a A)
  then show ?case
    using InhImp_case
    by blast
next
  case (CondAssert x1a A1 A2)
  then show ?case
    using InhCondAssert
    by blast
qed (blast elim: red_inhale.cases)+


subsection \<open>Preserved by Exhale\<close>

lemma extcons_preserved_by_red_exhale:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_exhale ctxt StateCons \<omega>0 A \<omega> (RNormal \<omega>')"
      and "ctxt_wf_pred ctxt"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof
  fix pid vs p' nm'
  assume "Some (p', nm') = get_fnm_total (get_total_full \<omega>') (pid,vs)"
  then obtain p nm where
    nm'_nm: "get_fnm_total_full \<omega> (pid,vs) = Some (p, nm) \<and> nm' = (Rep_posreal (p' / p)) *\<^sub>s nm"
    using exhale_fraction[OF assms(2)]
    by force
  hence extcons_old: "consistent_external_wrt_ploc ctxt (get_total_full \<omega>\<lparr>get_nm_total := nm\<rparr>) (pid,vs) (Rep_posreal p)"
    using assms(1) consistent_external.cases
    by fastforce
  have 1: "\<And>nm. (get_total_full \<omega>)\<lparr> get_nm_total := nm \<rparr> = (get_total_full \<omega>')\<lparr> get_nm_total := nm \<rparr>"
    apply (rule total_state.equality)
    using assms(2) exhale_only_changes_total_state_aux
    by fastforce+
  have 2: "Rep_posreal p' / Rep_posreal p * Rep_posreal p = Rep_posreal p'"
    by (metis Rep_posreal Rep_preal_inverse divide_eq_eq divide_preal.rep_eq mem_Collect_eq pperm_pgt_pnone times_preal.rep_eq zero_preal_def)
  show "consistent_external_wrt_ploc ctxt (get_total_full \<omega>'\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) (Rep_posreal p')"
    using fraction_consistent_external(1)[OF assms(3) extcons_old, of "Rep_posreal p' / Rep_posreal p",
            simplified, unfolded 1 2, unfolded divide_posreal.rep_eq[symmetric]] nm'_nm
    by fast
qed

definition differ_only_in_0_perm_locs where
  "differ_only_in_0_perm_locs \<phi> \<phi>' \<equiv>
     (\<forall>loc. get_hh_total \<phi> loc \<noteq> get_hh_total \<phi>' loc \<longrightarrow> nm_loc_sum loc (get_nm_total \<phi>) 0) \<and>
     get_nm_total \<phi> = get_nm_total \<phi>'"

lemma extcons_preserved_by_changing_0_locs':
  assumes "ctxt_pred_self_framing ctxt"
    shows "(consistent_external_wrt_ploc ctxt \<phi> lp p \<longrightarrow>
            (\<forall>\<phi>'. differ_only_in_0_perm_locs \<phi> \<phi>' \<longrightarrow>
                  consistent_external_wrt_ploc ctxt \<phi>' lp p)) \<and>
           (consistent_external ctxt \<phi> \<longrightarrow>
            (\<forall>\<phi>'. differ_only_in_0_perm_locs \<phi> \<phi>' \<longrightarrow>
                  consistent_external ctxt \<phi>'))"
  apply (rule consistent_external_wrt_ploc_consistent_external.induct)
   apply (standard, standard, standard)
       apply fast+
    apply (smt (verit) assms ctxt_pred_self_framing_def differ_only_in_0_perm_locs_def full_total_state.select_convs(1) full_total_state.select_convs(3) get_hh_total_full.simps get_mh_total.simps get_mp_total.simps preal_not_0_gt_0 pred_self_framing_subst sum_0_implies_mh_zero total_state.select_convs(1) total_state.surjective total_state.update_convs(2))
   apply blast
proof (standard, intro impI)
  fix \<phi> \<phi>' :: "'a total_state"
  assume IH:
         "\<And>pid vs q nm'. Some (q, nm') = get_fnm_total \<phi> (pid,vs) \<Longrightarrow>
            \<forall>\<phi>''. differ_only_in_0_perm_locs (\<phi>\<lparr> get_nm_total := nm' \<rparr>) \<phi>'' \<longrightarrow>
                  consistent_external_wrt_ploc ctxt \<phi>'' (pid,vs) (Rep_posreal q)"
     and diff_only: "differ_only_in_0_perm_locs \<phi> \<phi>'"
  show "consistent_external ctxt \<phi>'"
  proof
    fix pid vs q nm'
    assume lpm: "Some (q, nm') = get_fnm_total \<phi>' (pid,vs)"
    with IH have "\<forall>\<phi>''. differ_only_in_0_perm_locs (\<phi>\<lparr> get_nm_total := nm' \<rparr>) \<phi>'' \<longrightarrow>
                        consistent_external_wrt_ploc ctxt \<phi>'' (pid,vs) (Rep_posreal q)"
      using diff_only differ_only_in_0_perm_locs_def
      by (metis get_fnm_total.simps)
    moreover have "differ_only_in_0_perm_locs (\<phi>\<lparr> get_nm_total := nm' \<rparr>) (\<phi>'\<lparr> get_nm_total := nm' \<rparr>)"
      apply (subgoal_tac "\<And>loc. nm_loc_sum loc (get_nm_total \<phi>) 0 \<Longrightarrow> nm_loc_sum loc nm' 0")
       apply (simp add: differ_only_in_0_perm_locs_def)
       apply (meson diff_only differ_only_in_0_perm_locs_def nm_loc_sum.elims(2))
      by (metis diff_only differ_only_in_0_perm_locs_def get_fnm_total.simps lpm padd_pos preal_gte_padd sub_mask_smaller)
    ultimately show "consistent_external_wrt_ploc ctxt (\<phi>'\<lparr> get_nm_total := nm' \<rparr>) (pid,vs) (Rep_posreal q)"
      by blast
  qed
qed

lemma extcons_preserved_by_changing_0_locs:
  assumes "\<And>loc. get_hh_total \<phi> loc \<noteq> get_hh_total \<phi>' loc \<Longrightarrow> nm_loc_sum loc (get_nm_total \<phi>) 0"
      and "get_nm_total \<phi> = get_nm_total \<phi>'"
      and "ctxt_pred_self_framing ctxt"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pid,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt \<phi>' (pid,vs) p"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt \<phi>'"
  using assms differ_only_in_0_perm_locs_def extcons_preserved_by_changing_0_locs' 
  by blast+

lemma extcons_preserved_by_red_stmt_exhale:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_stmt_total ctxt StateCons \<Lambda> (Exhale A) \<omega> (RNormal \<omega>')"
      and "ctxt_wf_pred ctxt"
      and "ctxt_pred_self_framing ctxt"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof -
  from assms(2) obtain \<omega>_exh where
    exh: "red_exhale ctxt StateCons \<omega> A \<omega> (RNormal \<omega>_exh)" and
    havoc: "\<omega>' \<in> havoc_locs_state ctxt \<omega>_exh
      { loc. \<exists>p. p > 0 \<and> nm_loc_sum loc (get_nm_total_full \<omega>) p \<and> nm_loc_sum loc (get_nm_total_full \<omega>) 0 }"
    by (blast elim: red_stmt_total.cases)

  hence "consistent_external ctxt (get_total_full \<omega>_exh)"
    using assms(1) assms(3) extcons_preserved_by_red_exhale
    by blast

  thus ?thesis
    using assms(4) extcons_preserved_by_changing_0_locs(2) havoc havoc_locs_state_same_mask
    by (smt (verit) Collect_empty_eq havoc_locs_state_empty less_preal.rep_eq nm_loc_sum.elims(2) nm_loc_sum_unique)
qed


subsection \<open>Preserved by Field Assignment\<close>

lemma extcons_preserved_by_field_assignment_helper:
  assumes "nm_loc_sum loc (get_nm_total \<phi>) 0"
      and "ctxt_pred_self_framing ctxt"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pid,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v) (pid,vs) p"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt (upd_hh_loc_total \<phi> loc v)"
proof -
  have *: "\<And>l. get_hh_total \<phi> l \<noteq> get_hh_total (upd_hh_loc_total \<phi> loc v) l \<Longrightarrow> nm_loc_sum l (get_nm_total \<phi>) 0"
    apply simp
    by (metis assms(1) nm_loc_sum.elims(2))
  show "consistent_external_wrt_ploc ctxt \<phi> (pid,vs) p \<Longrightarrow>
        consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v) (pid,vs) p"
    using extcons_preserved_by_changing_0_locs(1)[OF * _ assms(2), of "upd_hh_loc_total \<phi> loc v"]
    by simp
  show "consistent_external ctxt \<phi> \<Longrightarrow>
        consistent_external ctxt (upd_hh_loc_total \<phi> loc v)"
    using extcons_preserved_by_changing_0_locs(2)[OF * _ assms(2), of "upd_hh_loc_total \<phi> loc v"]
    by simp
qed

lemma extcons_preserved_by_field_assignment:
  assumes "consistent_external ctxt \<phi>"
      and "consistent_internal (get_nm_total \<phi>)"
      and "get_mh_total \<phi> loc = 1"
      and "ctxt_pred_self_framing ctxt"
    shows "consistent_external ctxt (upd_hh_loc_total \<phi> loc v)"
proof -
  have zero_perm: "\<And>lp lpm. get_fnm_total \<phi> lp = Some lpm \<Longrightarrow> nm_loc_sum loc (snd lpm) 0"
    by (metis assms(2) assms(3) get_fnm_total.simps get_mh_total.elims get_fnm_total.simps mh_1_nested_0)
  show ?thesis
  proof
    fix pid vs q nm'
    assume lpm: "Some (q, nm') = get_fnm_total (upd_hh_loc_total \<phi> loc v) (pid,vs)"
    have "nm_loc_sum loc nm' 0"
      using mh_1_nested_0[OF assms(2) assms(3)[simplified] lpm[simplified, symmetric]]
      by simp
    have "get_fnm_total \<phi> (pid,vs) = Some (q, nm')"
      using lpm
      by simp
    hence extcons_nm: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) (Rep_posreal q)"
      using consistent_external.cases[OF assms(1)]
      by metis
    show "consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) (Rep_posreal q)"
      using extcons_preserved_by_field_assignment_helper(1)[of loc "\<phi>\<lparr>get_nm_total := nm'\<rparr>", OF _ assms(4) extcons_nm, of v]
      apply simp
      by (metis \<open>nm_loc_sum loc nm' pos_perm_class.pnone\<close> nm_loc_sum.simps total_state.simps(4) total_state.surjective total_state.update_convs(2))
  qed
qed


subsection \<open>Preserved by Unfold\<close>

lemma extcons_preserved_by_red_stmt_unfold:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pid e_args (PureExp e_q)) \<omega> (RNormal \<omega>')"
      and "ctxt_wf_pred ctxt"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof -
  obtain vs q \<phi>' where
    "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some vs)" and
    "ctxt, (Some \<omega>) \<turnstile> \<langle>e_q; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm q)" and
    "q \<ge> 0" and
    "unfold_rel ctxt pid vs (Abs_preal q) (get_total_full \<omega>) \<phi>'" and
    "\<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr>"
    using assms
    by (auto elim: RedUnfold_case)
  then obtain nm nm' where
    shift: "shift_up pid vs (Abs_preal q) nm nm'" and
    nm: "get_nm_total (get_total_full \<omega>) = nm" and
    \<phi>'_nm: "get_nm_total \<phi>' = nm'" and
    hh_unchanged: "get_hh_total \<phi>' = get_hh_total (get_total_full \<omega>)"
    using assms(2) unfold_rel.simps
    by blast

  show ?thesis
  proof (cases "q = 0")
    case True
    hence "nm = nm'"
      using shift shift_up_case zero_preal.abs_eq
      by force
    have "\<omega> = \<omega>'"
      apply (rule full_total_state.equality)
         apply (simp_all add: \<open>\<omega>' = _\<close>)
      by (simp add: \<open>nm = nm'\<close> \<phi>'_nm hh_unchanged nm)
    then show ?thesis
      using assms(1)
      by blast
  next
    case False
    then obtain mh fnm p\<^sub>p pnm p fnm' nm'_sub where
      "mh = get_mh_nm nm" and
      "fnm = get_fnm_nm nm" and
      "Some (p\<^sub>p, pnm) = fnm (pid,vs)" and
      "p = Rep_posreal p\<^sub>p" and
      "Abs_preal q > 0" and
      "Abs_preal q \<le> p" and
      "fnm' = fnm( (pid,vs) := if p = Abs_preal q then None else Some (Abs_posreal (p - Abs_preal q), ((p - Abs_preal q) / p) *\<^sub>s pnm) )" and
      "nm'_sub = NM mh fnm'" and
      "nm' = nm'_sub + (Abs_preal q / p) *\<^sub>s pnm"
      using shift_up_case
      by (smt (verit) \<open>0 \<le> q\<close> positive_real_preal shift)

    have pnm_extcons_wrt_ploc: "consistent_external_wrt_ploc ctxt (get_total_full \<omega>\<lparr> get_nm_total := pnm \<rparr>) (pid,vs) p"
      using SatAll_case \<open>Some (p\<^sub>p, pnm) = fnm (pid, vs)\<close> \<open>fnm = _\<close> \<open>p = Rep_posreal p\<^sub>p\<close> assms(1) nm
      by fastforce
    hence pnm_extcons: "consistent_external ctxt (get_total_full \<omega>\<lparr> get_nm_total := pnm \<rparr>)"
      using consistent_external_wrt_ploc.cases
      by blast

    have "consistent_external ctxt (get_total_full \<omega>\<lparr> get_nm_total := nm'_sub \<rparr>)"
      apply standard
      apply (simp add: \<open>nm'_sub = _\<close>)
    proof -
      fix pid' vs' q\<^sub>s nm\<^sub>s
      assume lpm: "Some (q\<^sub>s, nm\<^sub>s) = fnm' (pid',vs')"
      show "consistent_external_wrt_ploc ctxt (get_total_full \<omega>\<lparr> get_nm_total := nm\<^sub>s \<rparr>) (pid',vs') (Rep_posreal q\<^sub>s)"
      proof (cases "(pid',vs') = (pid,vs)")
        case True
        have "q\<^sub>s = Abs_posreal (p - Abs_preal q)" and "nm\<^sub>s = ((p - Abs_preal q) / p) *\<^sub>s pnm"
          using lpm[simplified \<open>fnm' = _\<close> True, simplified]
          by (meson not_None_eq old.prod.inject option.inject)+
        show ?thesis
          apply (simp add: True \<open>q\<^sub>s = _\<close> \<open>nm\<^sub>s = _\<close>)
          apply (subgoal_tac "p - Abs_preal q > 0")
           apply (simp add: Abs_posreal_inverse)
           apply (subgoal_tac "(p - Abs_preal q) / p * p = p - Abs_preal q")
          using fraction_consistent_external(1)[OF assms(3) pnm_extcons_wrt_ploc, of "(p - Abs_preal q) / p", simplified]
            apply presburger
           apply (metis PosReal.field_divide_inverse PosReal.field_inverse \<open>Abs_preal q \<le> p\<close> \<open>0 < Abs_preal q\<close> linorder_not_less mult.assoc mult.right_neutral)
          using True \<open>Abs_preal q \<le> p\<close> \<open>fnm' = _\<close> lpm minus_preal_gte preal_not_0_gt_0 greater_minus_plus
          by fastforce
      next
        case False
        then show ?thesis
          by (metis SatAll_case lpm \<open>fnm = _\<close> \<open>fnm' = _\<close> assms(1) fun_upd_other nm)
      qed
    qed
    moreover have "consistent_external ctxt (get_total_full \<omega>\<lparr> get_nm_total := ((Abs_preal q / p) *\<^sub>s pnm) \<rparr>)"
      using fraction_consistent_external(2)[OF assms(3) pnm_extcons, of "Abs_preal q / p", simplified]
      by auto
    ultimately show ?thesis
      by (smt (verit) \<open>\<omega>' = _\<close> \<open>nm' = _\<close> \<phi>'_nm full_total_state.ext_inject full_total_state.surjective full_total_state.update_convs(3) hh_unchanged old.unit.exhaust sum_consistent_external total_state.surjective total_state.update_convs(2))
  qed
qed


subsection \<open>Preserved by Fold\<close>

lemma extcons_preserved_by_red_stmt_fold:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_stmt_total ctxt StateCons \<Lambda> (Fold pid e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "ctxt_wf_pred ctxt"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof -
  obtain vs p where
    "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some vs)" and
    "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
    "p \<ge> 0" and
    fold_rel: "fold_rel ctxt pid vs (Abs_preal p) \<omega> (RNormal \<omega>')"
    using assms(2)
    by (auto elim: RedFold_case)
  obtain pdecl pbody \<omega>0 \<omega>1 \<omega>1' nm_exh where
    pred_decl: "ViperLang.predicates (program_total ctxt) pid = Some pdecl" and
    pred_body: "ViperLang.predicate_decl.body pdecl = Some pbody" and
    ty: "vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pdecl)" and
    "\<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>" and
    red_exh: "red_exhale ctxt (\<lambda>_. True) \<omega>0 (syntactic_mult (Rep_preal (Abs_preal p)) pbody) \<omega>0 (RNormal \<omega>1')" and
    "\<omega>1 = \<omega>\<lparr> get_total_full := get_total_full \<omega>1' \<rparr>" and
    nm_exh: "get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0" and
    "\<omega>' = add_to_lpm_total_full \<omega>1 (pid,vs) (if Abs_preal p = 0 then None else Some (Abs_posreal (Abs_preal p), nm_exh))"
    apply (rule FoldRelNormal_case[OF fold_rel])
    by simp

  have exhaled_extcons: "consistent_external ctxt (get_total_full \<omega>1)"
    by (metis \<open>\<omega>0 = _\<close> \<open>\<omega>1 = _\<close> red_exh assms(1) assms(3) extcons_preserved_by_red_exhale full_total_state.ext_inject full_total_state.surjective full_total_state.update_convs(3))

  have folded_extcons: "consistent_external_wrt_ploc ctxt ((get_total_full \<omega>1)\<lparr> get_nm_total := nm_exh \<rparr>) (pid,vs) (Abs_preal p)"
    using exhale_pred_body_part_extcons_wrt_ploc[OF pred_decl pred_body ty \<open>\<omega>0 = _\<close> assms(1) red_exh _ assms(3), of nm_exh]
    by (smt (verit, ccfv_SIG) \<open>\<omega>0 = _\<close> \<open>\<omega>1 = _\<close> exhale_only_changes_total_state_aux full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3) get_hh_total_full.simps get_nm_total_full.simps nm_exh old.unit.exhaust red_exh total_state.surjective total_state.update_convs(2))

  show ?thesis
  proof (cases "Abs_preal p = 0")
    case True
    hence "\<omega>' = \<omega>1"
      using \<open>\<omega>' = _\<close>
      by simp
    then show ?thesis
      using exhaled_extcons
      by blast
  next
    case False
    hence "\<omega>' = add_to_lpm_nonzero_total_full \<omega>1 (pid,vs) (Abs_posreal (Abs_preal p)) nm_exh"
      using \<open>\<omega>' = _\<close>
      by simp
    thus ?thesis
      using extcons_preserved_by_add_to_lpm_nonzero folded_extcons
      by (metis (full_types) False exhaled_extcons get_hh_total_full.simps old.unit.exhaust preal_not_0_gt_0 total_state.surjective total_state.update_convs(2))
  qed
qed


subsection \<open>Preserved by \<^const>\<open>red_stmt_total\<close>\<close>

lemma extcons_preserved_by_red_stmt:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "consistent_internal_total_full \<omega>"
      and "red_stmt_total ctxt consistent_internal_total_full \<Lambda> stmt \<omega> (RNormal \<omega>')"
      and "ctxt_wf_pred ctxt"
      and "ctxt_pred_self_framing ctxt"
    shows "consistent_external ctxt (get_total_full \<omega>')"
  using assms(1-3)
proof (induction stmt arbitrary: \<Lambda> \<omega> \<omega>')
  case (Inhale A)
  then show ?case
    using extcons_preserved_by_red_inhale RedInhale_case
    by blast
next
  case (Exhale A)
  then show ?case
    using extcons_preserved_by_red_stmt_exhale RedExhale_case assms(4,5)
    by blast
next
  case (Assert A)
  then show ?case
    using RedAssertNormal_case
    by blast
next
  case (Assume A)
  then show ?case
    by (blast elim: red_stmt_total.cases)
next
  case (If e s1 s2)
  then show ?case
    using RedIfNormal_case
    by blast
next
  case IH: (Seq s1 s2)
  then show ?case
    by (meson RedSeqNormal_case intcons_preserved_by_red_stmt)
next
  case IH: (LocalAssign x e)
  then show ?case
    using RedLocalAssign_case[OF IH(3)]
    by fastforce
next
  case IH: (FieldAssign e_r f e)
  obtain addr v where
    "(addr,f) \<in> get_writeable_locs \<omega>" and
    "\<omega>' = upd_hh_loc_total_full \<omega> (addr,f) v"
    using RedFieldAssign_case
    apply simp
    using IH.prems(3)
    by blast
  then show ?case
    using extcons_preserved_by_field_assignment[OF IH(1)] IH.prems(2) assms(5) get_writeable_locs_def
          consistent_internal_total_def consistent_internal_total_full_def
    by fastforce
next
  case (Havoc _)
  then show ?case
    by (fastforce elim: red_stmt_total.cases)
next
  case IH: (MethodCall ys m es)
  obtain v_args mdecl v_rets resPre resPost where
    "red_pure_exps_total ctxt (Some \<omega>) es \<omega> (Some v_args)" and
    "program.methods (program_total ctxt) m = Some mdecl" and
    "vals_well_typed (absval_interp_total ctxt) v_args (method_decl.args mdecl)" and
    "list_all2 (\<lambda> y t. y = Some t) (map \<Lambda> ys) (method_decl.rets mdecl)" and
    "vals_well_typed (absval_interp_total ctxt) v_rets (method_decl.rets mdecl)" and
  red_exh:
    "red_stmt_total ctxt consistent_internal_total_full \<Lambda> (Exhale (method_decl.pre mdecl))
                    \<lparr> get_store_total = (shift_and_add_list_alt Map.empty v_args),
                      get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                      get_total_full = get_total_full \<omega> \<rparr>
                    resPre" and
    "resPre = RFailure \<or> resPre = RMagic \<Longrightarrow> RNormal \<omega>' = resPre" and
  red_inh:
    "\<And> \<omega>Pre. resPre = RNormal \<omega>Pre \<Longrightarrow>
        (red_stmt_total ctxt consistent_internal_total_full \<Lambda> (Inhale (method_decl.post mdecl))
                        \<lparr> get_store_total = (shift_and_add_list_alt Map.empty (v_args @ v_rets)),
                          get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                          get_total_full = get_total_full \<omega>Pre \<rparr>
                        resPost \<and>
        RNormal \<omega>' = map_result_total (reset_state_after_call ys v_rets \<omega>) resPost)"
    using RedMethodCall_case[OF IH(3)]
    by blast
  then obtain \<omega>Pre where "resPre = RNormal \<omega>Pre"
    by (metis result_total.exhaust)
  hence "consistent_external ctxt (get_total_full \<omega>Pre)"
    by (metis IH.prems(1) red_exh assms(4) assms(5) extcons_preserved_by_red_stmt_exhale full_total_state.select_convs(3))
  obtain \<omega>Post where "resPost = RNormal \<omega>Post"
    by (metis \<open>resPre = RNormal \<omega>Pre\<close> map_result_total.elims red_inh)
  hence "consistent_external ctxt (get_total_full \<omega>Post)"
    by (metis RedInhale_case \<open>consistent_external ctxt (get_total_full \<omega>Pre)\<close> \<open>resPre = RNormal \<omega>Pre\<close> extcons_preserved_by_red_inhale full_total_state.select_convs(3) red_inh sub_expressions.simps(7))
  then show ?case
    by (metis \<open>resPost = RNormal \<omega>Post\<close> \<open>resPre = RNormal \<omega>Pre\<close> full_total_state.select_convs(3) map_result_total.simps(1) red_inh reset_state_after_call_def result_total.inject)
next
  case (While _ _ _)
  then show ?case
    by (blast elim: red_stmt_total.cases)
next
  case (Unfold pid es perm)
  then show ?case
    apply (cases perm)
    using assms(4) extcons_preserved_by_red_stmt_unfold
     apply blast
    by (blast elim: red_stmt_total.cases)
next
  case (Fold pid es perm)
  then show ?case
    apply (cases perm)
    using assms(4) extcons_preserved_by_red_stmt_fold
     apply blast
    by (blast elim: red_stmt_total.cases)
next
  case (Package _ _)
  then show ?case
    by (blast elim: red_stmt_total.cases)
next
  case (Apply _ _)
  then show ?case
    by (blast elim: red_stmt_total.cases)
next
  case (Label _)
  then show ?case
    by (fastforce elim: red_stmt_total.cases)
next
  case IH: (Scope \<tau> scopeBody)
  then obtain v res where
    "get_type (absval_interp_total ctxt) v = \<tau>" and
    red: "red_stmt_total ctxt consistent_internal_total_full (shift_and_add \<Lambda> \<tau>) scopeBody (shift_and_add_state_total \<omega> v) res" and
    map: "RNormal \<omega>' = map_result_total (unshift_state_total 1) res"
    using RedScope_case[OF IH(4)]
    by (metis One_nat_def shift_and_add_state_total.elims sub_expressions.simps(17) update_store_total.simps)

  have *: "consistent_external ctxt (get_total_full (shift_and_add_state_total \<omega> v))"
    apply simp
    using IH.prems(1)
    by blast
  obtain \<omega>\<^sub>m where "res = RNormal \<omega>\<^sub>m"
    by (metis map map_result_total.elims)
  have "consistent_external ctxt (get_total_full \<omega>\<^sub>m)"
    using IH(1)[OF * _ red[simplified \<open>res = _\<close>]] IH.prems(2)
    unfolding consistent_internal_total_full_def consistent_internal_total_def
    by simp

  then show ?case
    using \<open>res = RNormal \<omega>\<^sub>m\<close> map
    by auto
next
  case Skip
  then show ?case
    using RedSkip_case
    by blast
qed

end
