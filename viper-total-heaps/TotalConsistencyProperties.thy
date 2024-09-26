theory TotalConsistencyProperties
  imports TotalSemantics TotalInternalConsistency TotalSemanticsProperties TotalFraming
begin


\<comment> \<open>Unfold statement preserves external consistency.\<close>

lemma unfold_preserves_external_consistency:
  assumes "consistent_external ctxt \<phi>"
      and "get_total_full \<omega> = \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "consistent_external ctxt \<phi>'"
proof -
  obtain vs v_p where
    "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some vs)" and
    "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    "unfold_rel ctxt pred_id vs (Abs_preal v_p) (get_total_full \<omega>) \<phi>'" and
    "\<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr>"
    using assms
    by (auto elim: RedUnfold_case)
  then obtain nm nm' where
    "shift_up pred_id vs (Abs_preal v_p) nm nm'" and
    nm: "get_nm_total \<phi> = nm" and
    \<phi>'_nm: "get_nm_total \<phi>' = nm'" and
    hh_unchanged: "get_hh_total \<phi>' = get_hh_total \<phi>"
    using assms(2) unfold_rel.simps by blast
  then obtain mh mp fnm pnm p mp' fnm' nm'_sub where
    nm_decomp: "nm = NM mh mp fnm" and
    pnm: "Some pnm = fnm (pred_id,vs)" and
    p: "p = mp (pred_id,vs)" and
    "Abs_preal v_p \<le> p" and
    "Abs_preal v_p \<noteq> 0" and
    mp': "mp' = mp( (pred_id,vs) := p - Abs_preal v_p )" and
    fnm': "fnm' = fnm( (pred_id,vs) := if Abs_preal v_p = p then None else Some (nested_mask_multiply pnm ((p - Abs_preal v_p) / p)) )" and
    nm'_sub: "nm'_sub = NM mh mp' fnm'" and
    nm': "nm' = nested_mask_merge nm'_sub (nested_mask_multiply pnm (Abs_preal v_p / p))"
    by (auto elim: shift_up_case)

  have "Abs_preal v_p \<noteq> p \<Longrightarrow> consistent_external ctxt (\<phi>\<lparr> get_nm_total := nested_mask_multiply pnm ((p - Abs_preal v_p) / p) \<rparr>)"
  proof -
    assume "Abs_preal v_p \<noteq> p"
    hence "Abs_preal v_p > 0"
      using \<open>Abs_preal v_p \<noteq> 0\<close> preal_not_0_gt_0 by blast
    have "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>) (pred_id,vs) p"
      using assms(1) nm nm_decomp pnm p SatAll_case by fastforce
    hence "consistent_external ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>)"
      using SatStep_case by blast
    moreover have "(p - Abs_preal v_p) / p > 0" \<comment> \<open>Simple lemma but hard to prove\<close>
    proof -
      have "p - Abs_preal v_p > 0"
        by (metis \<open>Abs_preal v_p \<le> p\<close> \<open>Abs_preal v_p \<noteq> p\<close> add_0 greater_minus_plus pperm_pnone_pgt)
      thus ?thesis
        using \<open>pos_perm_class.pnone < Abs_preal v_p\<close> divide_preal.rep_eq less_preal.rep_eq minus_preal.rep_eq preal_not_0_gt_0 zero_preal.rep_eq by fastforce
    qed
    moreover have *: "\<phi>\<lparr> get_nm_total := nested_mask_multiply pnm ((p - Abs_preal v_p) / p) \<rparr>
                 = mult_nm_total (\<phi>\<lparr> get_nm_total := pnm \<rparr>) ((p - Abs_preal v_p) / p)"
      by simp
    ultimately show ?thesis
      using fraction_consistent_external(2)[of "(p - Abs_preal v_p) / p" ctxt "\<phi>\<lparr> get_nm_total := pnm \<rparr>"]
      by presburger
  qed

  have nm'_sub_consistent: "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm'_sub \<rparr>)"
    apply (rule SatAll)
     apply simp
  proof -
    have *: "\<And>pred_id vs. (get_mp_nm nm (pred_id, vs) = 0) = (get_fnm_nm nm (pred_id, vs) = None)"
      by (metis SatAll_case assms(1) nm)
    show "\<And>pred_id vs. (get_mp_nm nm'_sub (pred_id, vs) = 0) = (get_fnm_nm nm'_sub (pred_id, vs) = None)"
    proof -
      fix pred_id vs
      have "(mp' (pred_id,vs) = 0) = (fnm' (pred_id,vs) = None)"
        apply (cases "Abs_preal v_p = p")
        using * fnm' minus_preal.abs_eq mp' nm_decomp zero_preal_def apply auto[1]
        using * \<open>Abs_preal v_p \<le> p\<close> fnm' greater_minus_plus mp' nm_decomp by fastforce
      thus "(get_mp_nm nm'_sub (pred_id, vs) = 0) = (get_fnm_nm nm'_sub (pred_id, vs) = None)"
        by (simp add: nm'_sub)
    qed
    show "\<And>pred_id vs q nm'.
             get_mp_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id, vs) = q \<Longrightarrow>
             Some nm' = TotalStateUtil.get_nm_loc_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id, vs) \<Longrightarrow>
             consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'_sub, get_nm_total := nm'\<rparr>) (pred_id, vs) q"
    proof -
      fix pred_id' vs' q nm''
      assume pred_perm: "get_mp_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id', vs') = q" and
             nm'': "Some nm'' = TotalStateUtil.get_nm_loc_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id', vs')"
      show "consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'_sub, get_nm_total := nm''\<rparr>) (pred_id', vs') q"
      proof (cases "(pred_id',vs') = (pred_id,vs)")
        case True
        hence [simp]: "nm'' = nested_mask_multiply pnm ((p - Abs_preal v_p) / p)"
          by (smt (verit) TotalStateUtil.get_nm_loc_total.simps fnm' fun_upd_same get_fnm_nm.simps get_fnm_total.simps nm'' nm'_sub option.distinct(1) option.inject total_state.select_convs(2) total_state.surjective total_state.update_convs(2))
        hence "p > Abs_preal v_p"
          using True \<open>Abs_preal v_p \<le> p\<close> fnm' nm'' nm'_sub order_le_imp_less_or_eq by fastforce
        moreover have "0 < (p - Abs_preal v_p) / p"
        proof -
          have "p - Abs_preal v_p > 0"
            by (metis \<open>Abs_preal v_p \<le> p\<close> add_0 calculation greater_minus_plus order_less_irrefl pperm_pnone_pgt)
          thus ?thesis
            by (metis Rep_preal_inverse \<open>Abs_preal v_p \<le> p\<close> divide_eq_0_iff divide_preal.rep_eq leD pperm_pnone_pgt psub_smaller zero_preal.rep_eq)
        qed
        moreover from True have [simp]: "q = p - Abs_preal v_p"
          using mp' nm'_sub pred_perm by force
        moreover have pnm_consistent: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>) (pred_id, vs) p"
          using SatAll_case assms(1) nm nm_decomp p pnm by fastforce
        moreover have "(p - Abs_preal v_p) / p * p = p - Abs_preal v_p"
          by (metis * Rep_preal_inverse divide_preal.rep_eq get_fnm_nm.simps get_mp_nm.simps nm_decomp nonzero_eq_divide_eq option.distinct(1) p pnm times_preal.rep_eq zero_preal.abs_eq)
        ultimately show ?thesis
          using pnm_consistent
                fraction_consistent_external(1)[of "(p - Abs_preal v_p) / p" ctxt "\<phi>\<lparr>get_nm_total := pnm\<rparr>" pred_id vs p]
          by (simp add: True)
      next
        case False
        then show ?thesis
          using SatAll_case nm'' pred_perm assms(1) fnm' mp' nm nm'_sub nm_decomp total_state.select_convs(2) by fastforce
      qed
    qed
  qed

  \<comment> \<open>The shifted part\<close>
  have shift_consistent: "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nested_mask_multiply pnm (Abs_preal v_p / p) \<rparr>)"
  proof -
    have "consistent_external ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>)"
      by (metis TotalStateUtil.get_nm_loc_total.simps assms(1) consistent_external.cases consistent_external_wrt_ploc.cases get_fnm_nm.simps get_fnm_total.simps nm nm_decomp pnm)
    moreover have "Abs_preal v_p / p > 0"
      by (metis Rep_preal_inverse \<open>Abs_preal v_p \<le> p\<close> \<open>Abs_preal v_p \<noteq> pos_perm_class.pnone\<close> divide_eq_0_iff divide_preal.rep_eq leD preal_not_0_gt_0 zero_preal.rep_eq)
    ultimately show ?thesis
      using fraction_consistent_external(2)[of "Abs_preal v_p / p" ctxt "\<phi>\<lparr> get_nm_total := pnm \<rparr>"]
      by simp
  qed

  \<comment> \<open>Use combinability\<close>
  have "\<phi>' = \<phi>\<lparr> get_nm_total := nested_mask_merge nm'_sub (nested_mask_multiply pnm (Abs_preal v_p / p)) \<rparr>"
    using \<phi>'_nm hh_unchanged nm' by force
  show ?thesis
    using nm'_sub_consistent
    by (metis (full_types) shift_consistent \<phi>'_nm hh_unchanged nm' old.unit.exhaust sum_consistent_external total_state.surjective total_state.update_convs(2))
qed


\<comment> \<open>Field assignment preserves external state consistency.\<close>

lemma field_assignment_no_perm_PEC:
  assumes "consistent_external ctxt \<phi>"
      and "nm_loc_sum loc (get_nm_total \<phi>) 0"
      and "\<And>pred_id pred_decl.
              ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl \<Longrightarrow>
              pred_self_framing ctxt pred_decl"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v) (pred_id,vs) p"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt (upd_hh_loc_total \<phi> loc v)"
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
      using assms(2) sorry
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
    hence "get_mp_total \<phi> (pred_id, vs) = q"
      and "Some nm' = get_nm_loc_total \<phi> (pred_id, vs)"
      by simp+
    with IH have "consistent_external_wrt_ploc ctxt (upd_hh_loc_total (\<phi>\<lparr>get_nm_total := nm'\<rparr>) loc v) (pred_id, vs) q"
      by blast
    moreover have "upd_hh_loc_total (\<phi>\<lparr>get_nm_total := nm'\<rparr>) loc v =
                   upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>"
      by simp
    ultimately show "consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>) (pred_id, vs) q"
      by argo
  qed
qed


lemma field_assignment_preserves_external_consistency':
  assumes "consistent_external ctxt \<phi>"
      and "consistent_internal (get_nm_total \<phi>)"
      and "get_mh_total \<phi> loc = 1"
      and "\<And>pred_id pred_decl.
              ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl \<Longrightarrow>
              pred_self_framing ctxt pred_decl"
    shows "consistent_external ctxt (upd_hh_loc_total \<phi> loc v)"
proof -
  have zero_perm: "\<And>ploc nm. get_nm_loc_total \<phi> ploc = Some nm \<Longrightarrow> nm_loc_sum loc nm 0" sorry
  show ?thesis
    apply standard
    using assms(1) SatAll_case[of ctxt \<phi>]
     apply fastforce
  proof -
    fix pred_id vs q nm'
    assume "get_mp_total (upd_hh_loc_total \<phi> loc v) (pred_id, vs) = q"
       and nm': "Some nm' = get_nm_loc_total (upd_hh_loc_total \<phi> loc v) (pred_id, vs)"
    hence "get_mp_total \<phi> (pred_id, vs) = q"
      and "Some nm' = get_nm_loc_total \<phi> (pred_id, vs)"
      by simp+
    moreover hence "consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'\<rparr>) (pred_id, vs) q"
      by (metis assms(1) consistent_external.cases)
    moreover have "upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr> = upd_hh_loc_total (\<phi>\<lparr>get_nm_total := nm'\<rparr>) loc v"
      by simp
    ultimately show "consistent_external_wrt_ploc ctxt (upd_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>) (pred_id, vs) q"
      by (metis assms(4) consistent_external_wrt_ploc.cases field_assignment_no_perm_PEC(1) total_state_update_nm_read zero_perm)
  qed
qed

\<comment> \<open>Unfold statement preserves external consistency.\<close>

lemma exhale_preserves_external_consistency:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_exhale ctxt R \<omega> A \<omega> (RNormal \<omega>')"
    shows "consistent_external ctxt (get_total_full \<omega>')"
  sorry

lemma exhale_diff_external_consistent:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_exhale ctxt R \<omega> A \<omega> (RNormal \<omega>')"
    shows "consistent_external ctxt (\<lparr> get_hh_total = get_hh_total_full \<omega>', get_nm_total = nested_mask_subtract (get_nm_total_full \<omega>) (get_nm_total_full \<omega>') \<rparr>)"
  sorry

lemma exhale_preserves_hh:
  assumes "red_exhale ctxt R \<omega> A \<omega> (RNormal \<omega>')"
  shows "get_hh_total_full \<omega> = get_hh_total_full \<omega>'"
  sorry

lemma nested_mask_merge_one_sub:
  assumes "nm\<^sub>2 = NM (\<lambda>_. 0)
                    (\<lambda>x. if x = ploc then p else 0)
                    (\<lambda>x. if x = ploc then Some nm_sub else None)"
  shows "nested_mask_merge nm\<^sub>1 nm\<^sub>2 = add_to_nm_loc_nm (add_to_mp_loc_nm nm\<^sub>1 ploc p) ploc nm_sub"
  sorry

lemma supported_mult_supported:
  assumes "supported_pred_body A"
  shows "supported_pred_body (syntactic_mult p A)"
  sorry

lemma fold_preserves_external_consistency:
  assumes "consistent_external ctxt \<phi>"
      and "\<phi> = get_total_full \<omega>"
      and "red_stmt_total ctxt R \<Lambda> (Fold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "\<phi>' = get_total_full \<omega>'"
      and "\<And>pred_id pred_decl pred_body.
              ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl \<Longrightarrow>
              ViperLang.predicate_decl.body pred_decl = Some pred_body \<Longrightarrow>
              supported_pred_body pred_body"
    shows "consistent_external ctxt \<phi>'"
proof -
  obtain v_args v_p where
    "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)" and
    "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    "fold_rel ctxt pred_id v_args (Abs_preal v_p) \<omega> (RNormal \<omega>')"
    using assms(3)
    by (auto elim: RedFold_case)
  then obtain pred_decl pred_body \<omega>0 R \<omega>1 nm_exh where
    pred_decl: "ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl" and
    pred_body: "ViperLang.predicate_decl.body pred_decl = Some pred_body" and
    "Abs_preal v_p \<noteq> 0" and
    \<omega>0: "\<omega>0 = \<lparr> get_store_total = nth_option v_args, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>" and
    exhale: "red_exhale ctxt R \<omega>0 (syntactic_mult (Rep_preal (Abs_preal v_p)) pred_body) \<omega>0 (RNormal \<omega>1)" and
    nm_exh: "nm_exh = nested_mask_subtract (get_nm_total_full \<omega>0) (get_nm_total_full \<omega>1)" and
    \<omega>': "\<omega>' = \<lparr> get_store_total = get_store_total \<omega>,
                get_trace_total = get_trace_total \<omega>,
                get_total_full = add_to_nm_loc_total
                  (add_to_mp_loc_total (get_total_full \<omega>1) (pred_id,v_args) (Abs_preal v_p))
                  (pred_id,v_args) nm_exh
          \<rparr>"
    by (auto elim: FoldRelNormal_case)

  have exhaled_consistent: "consistent_external ctxt (get_total_full \<omega>1)"
    \<comment> \<open>Derived "False" from these facts alone: Unity_def, old.unit.exhaust ???\<close>
    by (metis \<omega>0 exhale assms(1) assms(2) exhale_preserves_external_consistency full_total_state.select_convs(3))
  define \<phi>_exh where
    "\<phi>_exh = \<lparr> get_hh_total = get_hh_total \<phi>,
               get_nm_total = NM (\<lambda>_. 0)
                                 (\<lambda>x. if x = (pred_id,v_args) then (Abs_preal v_p) else 0)
                                 (\<lambda>x. if x = (pred_id,v_args) then Some nm_exh else None) \<rparr>"
  have diff_consistent: "consistent_external ctxt \<phi>_exh"
    apply standard
     apply (simp add: \<open>Abs_preal v_p \<noteq> pos_perm_class.pnone\<close> \<phi>_exh_def)
  proof -
    fix pid vs q nm'
    assume perm: "get_mp_total \<phi>_exh (pid,vs) = q"
       and nm': "Some nm' = TotalStateUtil.get_nm_loc_total \<phi>_exh (pid,vs)"
    show "consistent_external_wrt_ploc ctxt (\<phi>_exh\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) q"
    proof (cases "(pid,vs) = (pred_id,v_args)")
      case True
      show ?thesis
      proof (simp add: True, standard, (simp add: pred_decl pred_body)+)
        have \<omega>0_consistent: "consistent_external ctxt (get_total_full \<omega>0)"
          using \<omega>0 assms(1) assms(2) by force
        moreover have sup_mult: "supported_pred_body (syntactic_mult (Rep_preal (Abs_preal v_p)) pred_body)"
          using assms(5) pred_body pred_decl supported_mult_supported by blast
        moreover have nm'_eq_exh: "nm' = nm_exh"
          using True \<phi>_exh_def nm' by auto
        moreover have "get_mh_nm nm' = field_mask_sub (get_mh_total_full \<omega>0) (get_mh_total_full \<omega>1)"
          by (simp add: nm'_eq_exh nm_exh nm_subtract_mh)
        moreover have "get_mp_nm nm' = predicate_mask_sub (get_mp_total_full \<omega>0) (get_mp_total_full \<omega>1)"
          by (simp add: nm'_eq_exh nm_exh nm_subtract_mp)
        ultimately show
          "sat ctxt
               \<lparr> get_store_total = nth_option v_args,
                 get_trace_total = \<lambda>x. None,
                 get_total_full = \<phi>_exh\<lparr>get_nm_total := 0 \<rparr> \<rparr>
               (get_mh_nm nm') (get_mp_nm nm') (syntactic_mult (Rep_preal q) pred_body)"
          using exhale_diff_sat[of ctxt \<omega>0 R \<omega>0 "(syntactic_mult (Rep_preal (Abs_preal v_p)) pred_body)" _ \<omega>1,
                                OF \<omega>0_consistent exhale _ sup_mult]
          by (smt (verit, ccfv_SIG) True \<omega>0 \<phi>_exh_def assms(2) full_total_state.select_convs(1) full_total_state.select_convs(3) get_mp_nm.simps get_mp_total.elims old.unit.exhaust perm total_state.select_convs(2) total_state.surjective total_state.update_convs(2))
      next
        show "consistent_external ctxt (\<phi>_exh\<lparr>get_nm_total := nm'\<rparr>)"
          by (smt (verit, del_insts) TotalStateUtil.get_nm_loc_total.simps True \<omega>0 \<phi>_exh_def assms(1) assms(2) exhale exhale_diff_external_consistent exhale_preserves_hh full_total_state.select_convs(3) get_fnm_nm.simps get_fnm_total.simps get_hh_total_full.elims nm' nm_exh option.inject total_state.select_convs(2) total_state.update_convs(2))
      next
        show "q > 0"
          using True \<open>Abs_preal v_p \<noteq> pos_perm_class.pnone\<close> \<phi>_exh_def perm pperm_pnone_pgt by auto
      qed
    next
      case False
      then show ?thesis
        using \<phi>_exh_def get_fnm_nm.simps get_fnm_total.simps nm' by auto
    qed
  qed

  have hh_eq: "get_hh_total_full \<omega>0 = get_hh_total_full \<omega>1"
    using exhale exhale_preserves_hh by blast
  have nm_merge: "get_nm_total \<phi>' = nested_mask_merge (get_nm_total_full \<omega>1) (get_nm_total \<phi>_exh)"
  proof -
    from \<phi>_exh_def have
      "get_nm_total \<phi>_exh = NM (\<lambda>_. 0)
                               (\<lambda>x. if x = (pred_id,v_args) then (Abs_preal v_p) else 0)
                               (\<lambda>x. if x = (pred_id,v_args) then Some nm_exh else None)"
      by simp
    moreover have "get_nm_total \<phi>' = add_to_nm_loc_nm (add_to_mp_loc_nm (get_nm_total_full \<omega>1) (pred_id,v_args) (Abs_preal v_p)) (pred_id,v_args) nm_exh"
      by (simp add: assms(4) \<omega>')
    ultimately show ?thesis
      by (simp add: nested_mask_merge_one_sub)
  qed

  show "consistent_external ctxt \<phi>'"
  proof -
    have "get_hh_total_full \<omega>1 = get_hh_total \<phi>"
      using \<omega>0 assms(2) hh_eq by fastforce
    hence cons1: "consistent_external ctxt \<lparr> get_hh_total = get_hh_total \<phi>, get_nm_total = get_nm_total_full \<omega>1 \<rparr>"
      by (metis (full_types) TotalStateUtil.get_nm_total_full.simps exhaled_consistent get_hh_total_full.elims old.unit.exhaust total_state.surjective)
    have "get_hh_total \<phi>_exh = get_hh_total \<phi>"
      by (simp add: \<phi>_exh_def)
    hence cons2: "consistent_external ctxt \<lparr> get_hh_total = get_hh_total \<phi>, get_nm_total = get_nm_total \<phi>_exh \<rparr>"
      using \<phi>_exh_def diff_consistent by force
    have "get_hh_total \<phi>' = get_hh_total \<phi>"
    proof -
      have \<open>get_hh_total (add_to_nm_loc_total
                  (upd_mp_loc_total (get_total_full \<omega>1) (pred_id,v_args) (get_mp_total_full \<omega>1 (pred_id,v_args) + Abs_preal v_p))
                  (pred_id,v_args) nm_exh) = get_hh_total \<phi>'\<close>
        by (simp add: \<omega>' assms(4))
      thus ?thesis
        by (metis \<open>get_hh_total_full \<omega>1 = get_hh_total \<phi>\<close> get_hh_total_full.simps update_mp_loc_total_preserves_hh)
    qed
    thus ?thesis
      using sum_consistent_external[of ctxt "get_hh_total \<phi>" "get_nm_total_full \<omega>1" "get_nm_total \<phi>_exh", OF cons1 cons2]
      by (metis (full_types) nm_merge old.unit.exhaust total_state.surjective)
  qed
qed


end
