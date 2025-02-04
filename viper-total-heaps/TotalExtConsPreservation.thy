theory TotalExtConsPreservation
  imports TotalExtConsProps TotalIntConsPreservation
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
  sorry


subsection \<open>Preserved by \<^const>\<open>red_inhale\<close>\<close>

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
      and "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm \<rparr> lp q"
      and "q > 0"
    shows "consistent_external ctxt (get_total_full (add_to_lpm_nonzero_total_full \<omega> lp (p2pos q) nm))"
  sorry

lemma extcons_preserved_by_inhale_perm_single_pred:
  assumes "\<omega>' \<in> inhale_perm_single_pred ctxt StateCons \<omega> lp p_opt"
      and "consistent_external ctxt (get_total_full \<omega>)"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof -
  obtain \<phi>_inh q where
    inh_extcons: "consistent_external_wrt_ploc ctxt \<phi>_inh lp q" and
    hh_same: "get_hh_total \<phi>_inh = get_hh_total_full \<omega>" and
    \<omega>': "\<omega>' = (if q = 0 then \<omega> else add_to_lpm_nonzero_total_full \<omega> lp (p2pos q) (get_nm_total \<phi>_inh))"
    using iffD1[OF mem_Collect_eq assms(1)[simplified inhale_perm_single_pred_def]]
    by blast
  consider (InhZero) "\<omega>' = \<omega>" | (InhNonZero) "\<omega>' = add_to_lpm_nonzero_total_full \<omega> lp (p2pos q) (get_nm_total \<phi>_inh)"
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


subsection \<open>Preserved by \<^const>\<open>red_exhale\<close>\<close>

lemma extcons_preserved_by_red_exhale:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_exhale ctxt StateCons \<omega>0 A \<omega> (RNormal \<omega>')"
      and "ctxt_wf_pred ctxt"
    shows "consistent_external ctxt (get_total_full \<omega>')"
proof
  fix pid vs p' nm'
  assume "Some (p', nm') = get_fnm_total (get_total_full \<omega>') (pid,vs)"
  then obtain p nm where
    nm'_nm: "get_fnm_total_full \<omega> (pid,vs) = Some (p, nm) \<and> nm' = (pos2p (p' / p)) *\<^sub>s nm"
    using exhale_fraction[OF assms(2)]
    by force
  hence extcons_old: "consistent_external_wrt_ploc ctxt (get_total_full \<omega>\<lparr>get_nm_total := nm\<rparr>) (pid,vs) (pos2p p)"
    using assms(1) consistent_external.cases
    by fastforce
  have 1: "\<And>nm. (get_total_full \<omega>)\<lparr> get_nm_total := nm \<rparr> = (get_total_full \<omega>')\<lparr> get_nm_total := nm \<rparr>"
    apply (rule total_state.equality)
    using assms(2) exhale_only_changes_total_state_aux
    by fastforce+
  have 2: "pos2p p' / pos2p p = pos2p (p' / p)"
    apply (simp add: pos2p_def preal_to_real posreal_to_real)
    by (smt (verit) Rep_posreal Rep_preal_inverse divide_preal.rep_eq mem_Collect_eq preal_to_real(12))
  have 3: "pos2p p' / pos2p p * pos2p p = pos2p p'"
    by (metis (mono_tags, lifting) Rep_preal_inverse divide_preal.rep_eq nonzero_eq_divide_eq pos2p_gt_0 pperm_pgt_pnone times_preal.rep_eq zero_preal.abs_eq)
  show "consistent_external_wrt_ploc ctxt (get_total_full \<omega>'\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) (pos2p p')"
    using fraction_consistent_external(1)[OF assms(3) extcons_old, of "pos2p p' / pos2p p",
            simplified, simplified 1 3, simplified 2]
    using nm'_nm
    by force
qed

lemma extcons_preserved_by_changing_0_locs:
  assumes "\<And>loc. get_hh_total \<phi> loc \<noteq> get_hh_total \<phi>' loc \<Longrightarrow> nm_loc_sum loc (get_nm_total \<phi>) 0"
      and "get_nm_total \<phi> = get_nm_total \<phi>'"
      and "ctxt_pred_self_framing ctxt"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pid,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt \<phi>' (pid,vs) p"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt \<phi>'"
  sorry
(*
  using assms(2)
proof (induct rule: consistent_external_wrt_ploc_consistent_external.inducts)
  case IH: (SatStep pred_id pred_decl pred_body vs \<phi> p)
  show ?case
    apply standard
        defer 3
        apply (simp only: IH)+
  proof -
    have store_equal:
      "get_store_total (\<lparr>get_store_total = nth_option vs, get_trace_total = \<lambda>x. None, get_total_full = \<phi>\<rparr>) =
       get_store_total (\<lparr>get_store_total = nth_option vs, get_trace_total = \<lambda>x. None, get_total_full = upd_hh_loc_total \<phi> loc v\<rparr>)"
      by simp
    have "get_mh_total \<phi> loc = 0"
      using sum_0_implies_mh_zero[OF IH(7)]
      by simp

    hence hh_unchanged:
      "\<forall>l. get_mh_total (upd_hh_loc_total \<phi> loc v) l > 0 \<longrightarrow>
           get_hh_total_full (\<lparr>get_store_total = nth_option vs, get_trace_total = \<lambda>x. None, get_total_full = \<phi>\<rparr>) l =
           get_hh_total_full (\<lparr>get_store_total = nth_option vs, get_trace_total = \<lambda>x. None, get_total_full = upd_hh_loc_total \<phi> loc v\<rparr>) l"
      by simp
    show "sat ctxt
            \<lparr>get_store_total = nth_option vs, get_trace_total = \<lambda>x. None, get_total_full = upd_hh_loc_total \<phi> loc v\<lparr> get_nm_total := 0 \<rparr> \<rparr>
            (get_mh_total (upd_hh_loc_total \<phi> loc v))
            (get_mp_total (upd_hh_loc_total \<phi> loc v))
            (syntactic_mult (Rep_preal p) pred_body)"
      using IH pred_self_framing_subst[OF _ IH(2) store_equal hh_unchanged]
      apply simp
      using assms(3)
      by (smt (verit, best) full_total_state.select_convs(1) full_total_state.select_convs(3) get_hh_total_full.elims pred_self_framing_subst total_state.select_convs(1) total_state.surjective total_state.update_convs(2))
  qed
next
  case IH: (SatAll \<phi>)
  show ?case
  proof
    fix pred_id vs q
    assume "get_mp_total (upd_hh_loc_total \<phi> loc v) (pred_id, vs) = q"
    hence "get_mp_total \<phi> (pred_id, vs) = q"
      by simp
    from IH(1)[OF this]
    show "(q = 0) = (get_nm_loc_total (upd_hh_loc_total \<phi> loc v) (pred_id, vs) = None)"
      by simp
  next
    fix pred_id vs q nm'
    assume "get_mp_total (upd_hh_loc_total \<phi> loc v) (pred_id, vs) = q"
       and "Some nm' = get_nm_loc_total (upd_hh_loc_total \<phi> loc v) (pred_id, vs)"
    hence 1: "get_mp_total \<phi> (pred_id, vs) = q"
      and 2: "Some nm' = get_nm_loc_total \<phi> (pred_id, vs)"
      by simp+
    have "nm_loc_sum loc nm' 0"
      by (metis "2" IH.prems get_fnm_total.simps get_nm_loc_total.simps sum_0_implies_sub_zero)
    have "consistent_external_wrt_ploc ctxt (upd_hh_loc_total (\<phi>\<lparr>get_nm_total := nm'\<rparr>) loc v) (pred_id, vs) q"
      using IH IH(3)[OF 1 2] \<open>nm_loc_sum loc nm' pos_perm_class.pnone\<close>
      by auto
    moreover have "upd_hh_loc_total (\<phi>\<lparr>get_nm_total := nm'\<rparr>) loc v =
                   upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>"
      by simp
    ultimately show "consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>) (pred_id, vs) q"
      by argo
  qed
qed
*)

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
    hence extcons_nm: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) (pos2p q)"
      using consistent_external.cases[OF assms(1)]
      by metis
    show "consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) (pos2p q)"
      using extcons_preserved_by_field_assignment_helper(1)[of loc "\<phi>\<lparr>get_nm_total := nm'\<rparr>", OF _ assms(4) extcons_nm, of v]
      apply simp
      by (metis \<open>nm_loc_sum loc nm' pos_perm_class.pnone\<close> nm_loc_sum.simps total_state.simps(4) total_state.surjective total_state.update_convs(2))
  qed
qed


subsection \<open>Preserved by \<^const>\<open>red_stmt_total\<close>\<close>

lemma extcons_preserved_by_red_stmt:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "consistent_internal (get_nm_total_full \<omega>)"
      and "red_stmt_total ctxt StateCons \<Lambda> stmt \<omega> (RNormal \<omega>')"
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
  case (Seq s1 s2)
  then show ?case
    using RedSeqNormal_case
    by (metis intcons_preserved_by_red_stmt)
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
    by fastforce
next
  case (Havoc _)
  then show ?case
    by (fastforce elim: red_stmt_total.cases)
next
  case (MethodCall x101 x102 x103)
  then show ?case sorry
next
  case (While _ _ _)
  then show ?case
    by (blast elim: red_stmt_total.cases)
next
  case (Unfold x121 x122 x123)
  then show ?case sorry
next
  case (Fold x131 x132 x133)
  then show ?case sorry
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
    red: "red_stmt_total ctxt StateCons (shift_and_add \<Lambda> \<tau>) scopeBody (shift_and_add_state_total \<omega> v) res" and
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
    by fastforce

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
