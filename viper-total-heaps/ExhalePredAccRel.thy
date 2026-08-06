theory ExhalePredAccRel
  imports TotalViperSimulation.ExhaleRel TotalViperSimulation.PredicateRel
begin


text \<open>This is the completed version of \<^const>\<open>exhale_rel\<close> for a predicate access assertion
      (\<^term>\<open>Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))\<close>) in the general (non-unfold)
      case, i.e. where the well-definedness state may differ from the current state and an
      additional invariant \<^term>\<open>Q\<close> is tracked (as opposed to \<open>unfold_exhale_pred_rel\<close> in
      \<open>PredicateRel.thy\<close>, which only handles the case where the two states coincide and there is no
      \<^term>\<open>Q\<close>). The statement mirrors \<open>exhale_rel_pred_acc\<close> in \<open>Simulation/ExhaleRel.thy\<close> (which is
      left unproved there via \<open>oops\<close>); the proof itself mirrors \<open>exhale_rel_field_acc_general\<close>
      (the analogous rule for a field access assertion), adapted to \<^const>\<open>exhale_pred_acc_rel_assms\<close>
      / \<^const>\<open>exhale_pred_acc_rel_perm_success\<close> / \<^const>\<open>exhale_pred_acc_normal_premise\<close> and the
      \<open>ExhAccPred\<close> case of \<^const>\<open>red_exhale\<close> (as already used inside the proof of
      \<open>unfold_exhale_pred_rel\<close>).\<close>

lemma exhale_rel_pred_acc_general:
  assumes WfSubexp: "exprs_wf_rel
                       (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and>
                         Q (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega>def \<omega>)
                       ctxt_vpr StateCons P ctxt_bpl (e_args_vpr @ [e_p_vpr]) \<gamma> \<gamma>\<^sub>2"
      and CorrectPermRel:
            "\<And>v_args v_p.
               rel_general (\<lambda>\<omega>def_\<omega> ns. (uncurry R \<omega>def_\<omega> ns) \<and>
                              Q (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>))
                 (R' v_args v_p)
                 (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. \<omega>0_\<omega> = \<omega>0_\<omega>' \<and>
                    exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) \<and>
                    exhale_pred_acc_rel_perm_success ctxt_vpr (snd \<omega>0_\<omega>) pred_id v_args v_p)
                 (\<lambda> \<omega>0_\<omega>.
                    exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) \<and>
                    \<not> exhale_pred_acc_rel_perm_success ctxt_vpr (snd \<omega>0_\<omega>) pred_id v_args v_p)
                 P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and UpdExhRel:
            "\<And>v_args v_p.
               rel_general (R' v_args v_p) (uncurry R'') \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                 (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. fst \<omega>0_\<omega> = fst \<omega>0_\<omega>' \<and>
                    exhale_pred_acc_normal_premise ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) (snd \<omega>0_\<omega>'))
                 (\<lambda>_. False)
                 P ctxt_bpl \<gamma>\<^sub>3 \<gamma>'"
    shows "exhale_rel R R'' Q ctxt_vpr StateCons P ctxt_bpl (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<gamma> \<gamma>'"
proof (rule exhale_rel_intro_2)
  fix \<omega>0 \<omega> ns res
  assume R0: "R \<omega>0 \<omega> ns"
     and Q0: "Q (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega>0 \<omega>"
  assume "red_exhale ctxt_vpr \<omega>0 (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> res"

  thus "rel_vpr_aux (R'' \<omega>0) P ctxt_bpl \<gamma> \<gamma>' ns res"
  proof cases
    case (ExhAccPred mp v_args p pdecl pbody)
    hence "red_pure_exps_total ctxt_vpr (Some \<omega>0) (e_args_vpr @ [e_p_vpr]) \<omega> (Some (v_args @ [VPerm p]))"
      by (simp add: red_pure_exps_append_success)
    from this obtain ns2 where "R \<omega>0 \<omega> ns2" and Red2: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns2)"
      using exprs_wf_rel_normal_elim[OF WfSubexp] R0 Q0
      by blast

    hence R2_conv: "uncurry R (\<omega>0, \<omega>) ns2"
      by simp

    have BasicAssms: "exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args p \<omega>0 \<omega>"
      unfolding exhale_pred_acc_rel_assms_def
      using ExhAccPred
      by (auto simp add: pred_ty_correct_premise_def)

    show ?thesis
    proof (rule rel_vpr_aux_intro)
      \<comment>\<open>Normal case\<close>
      fix \<omega>'
      assume "res = RNormal \<omega>'"
      with ExhAccPred have PermCorrect: "0 \<le> p \<and> mp (pred_id, v_args) \<ge> Abs_preal p"
        using exh_if_total_failure by fastforce
      hence PermSuccess: "exhale_pred_acc_rel_perm_success ctxt_vpr \<omega> pred_id v_args p"
        unfolding exhale_pred_acc_rel_perm_success_def
        using \<open>mp = _\<close> Abs_preal_inverse less_eq_preal.rep_eq
        by auto
      from this obtain ns3 where Red3: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>3, Normal ns3)" and R3: "R' v_args p (\<omega>0, \<omega>) ns3"
        using BasicAssms rel_success_elim[OF CorrectPermRel] R2_conv Q0 red_ast_bpl_transitive[OF Red2]
        by (metis fst_eqD snd_eqD)

      from ExhAccPred BasicAssms PermSuccess \<open>res = RNormal \<omega>'\<close> have
        NormalPremise: "exhale_pred_acc_normal_premise ctxt_vpr pred_id e_args_vpr e_p_vpr v_args p \<omega>0 \<omega> \<omega>'"
        unfolding exhale_pred_acc_normal_premise_def
        using exh_if_total_normal_2 \<open>res = exh_if_total _ _\<close> \<open>res = RNormal \<omega>'\<close> exhale_pred_def
        by fastforce

      thus "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R'' \<omega>0 \<omega>' ns'"
        using rel_success_elim[OF UpdExhRel R3] red_ast_bpl_transitive[OF Red3]
        by (metis (no_types, lifting) old.prod.inject prod.collapse uncurry.elims)
    next
      \<comment>\<open>Failure case\<close>
      assume "res = RFailure"
      with ExhAccPred have PermCorrect: "\<not> (0 \<le> p \<and> mp (pred_id, v_args) \<ge> Abs_preal p)"
        using exh_if_total_failure by fastforce
      thus "\<exists>c'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
        using ExhAccPred BasicAssms rel_failure_elim[OF CorrectPermRel] R2_conv Q0 red_ast_bpl_transitive[OF Red2]
              Abs_preal_inverse pgte.rep_eq
        unfolding exhale_pred_acc_rel_perm_success_def
        by (metis fst_conv less_eq_preal.rep_eq mem_Collect_eq snd_conv)
    qed
  next
    case ExhSubExpFailure
    thus ?thesis
      unfolding rel_vpr_aux_def
      using exprs_wf_rel_failure_elim[OF WfSubexp] R0 Q0
      by simp
  qed
qed


text \<open>Two-state (general) version of \<open>exhale_rel_pred_acc_upd_rel\<close> (\<open>Simulation/PredicateRel.thy\<close>),
      which only handles the single-state case (\<open>mask_var_def Tr = mask_var Tr\<close>, used by
      \<open>unfold_exhale_pred_rel\<close>). This mirrors \<open>inhale_rel_pred_acc_upd_rel'\<close> (the already-existing
      two-state version for inhale, \<open>PredicateRel.thy\<close>), with the arithmetic direction reversed
      (decrementing instead of incrementing the permission mask) and reusing the \<open>mh_same\<close>/\<open>mp_rel\<close>/
      \<open>\<omega>'_extcons\<close> derivations already worked out in \<open>exhale_rel_pred_acc_upd_rel\<close>'s own proof, which
      do not depend on the well-definedness state and therefore carry over unchanged to the
      two-state setting.\<close>

lemma exhale_rel_pred_acc_upd_rel_general:
  assumes
    StateRelIn:
      "\<And>\<omega>def \<omega> ns. R (\<omega>def,\<omega>) ns \<Longrightarrow>
          state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega>def \<omega> ns" and
    StateRelOut:
      "\<And>\<omega>def \<omega> ns. state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>def \<omega> ns \<Longrightarrow>
          R' (\<omega>def,\<omega>) ns" and
    AuxDomTemp: "temp_perm \<notin> dom AuxPred" and

    WfCons: "wf_total_consistency ctxt_vpr StateCons StateCons_t" and
    CtxtPredWf: "ctxt_pred_syn_wf ctxt_vpr" and
    WfTyRep: "wf_ty_repr_bpl TyRep" and
    MaskVarDefDiff: "mask_var_def Tr \<noteq> mask_var Tr" and
    TyInterp: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and

    NullConst: "const_repr Tr CNull = nullConst" and
    MaskVar: "m_bpl = mask_var Tr" and

    MaskUpdateWf: "mask_update_wf TyRep ctxt_bpl mask_upd_bpl" and
    MaskReadWf: "mask_read_wf TyRep ctxt_bpl mask_read_bpl" and

    PredType: "pred_snap_field_type TyRep pid = Some pred_ty" and

    NewPermBpl: "new_perm = (mask_read_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl
                                  [pred_ty, TConSingle (TFrameFragmentId TyRep)]) \<guillemotleft>Sub\<guillemotright> (Var temp_perm)" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl new_perm
                                  [pred_ty, TConSingle (TFrameFragmentId TyRep)]" and

    PlocRel: "ploc_rel_vpr_bpl' (curry R) ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and

    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep" and
    ProgEq: "program_total ctxt_vpr = Pr" and

    KFRelOff: "\<not> (kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr)))" and
    ConsOn: "consistent_state_rel_opt (state_rel_opt Tr)"

  shows "rel_general R R'
           (\<lambda>\<omega>def_\<omega> \<omega>def_\<omega>'. fst \<omega>def_\<omega> = fst \<omega>def_\<omega>' \<and>
              exhale_pred_acc_normal_premise ctxt_vpr pid e_args_vpr e_p_vpr v_args_vpr p (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) (snd \<omega>def_\<omega>'))
           (\<lambda>_. False) P ctxt_bpl
           (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
           (BigBlock name cs str tr, cont)"
  apply (rule rel_intro)
   prefer 2
   apply blast
proof -
  fix \<omega>def_\<omega> ns
  fix \<omega>def_\<omega>' :: "'a full_total_state \<times> 'a full_total_state"

  assume "R \<omega>def_\<omega> ns"
     and *: "fst \<omega>def_\<omega> = fst \<omega>def_\<omega>' \<and>
             exhale_pred_acc_normal_premise ctxt_vpr pid e_args_vpr e_p_vpr v_args_vpr p (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) (snd \<omega>def_\<omega>')"

  obtain \<omega>def \<omega> \<omega>def' \<omega>' where "\<omega>def_\<omega> = (\<omega>def, \<omega>)" and "\<omega>def_\<omega>' = (\<omega>def', \<omega>')"
    by fastforce

  hence InitRel: "state_rel Pr StateCons TyRep Tr
                            (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega>def \<omega> ns"
    using StateRelIn \<open>R \<omega>def_\<omega> ns\<close>
    by auto

  hence InitRel': "state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>def \<omega> ns"
    apply (rule state_rel_aux_pred_remove[where ?AuxPred="AuxPred(temp_perm \<mapsto> pred_eq (RealV p))" and ?AuxPred'=AuxPred])
    by (simp add: AuxDomTemp map_le_def)

  have R_pair: "R (\<omega>def,\<omega>) ns"
    using \<open>R \<omega>def_\<omega> ns\<close> \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close>
    by auto

  have \<omega>def'_eq: "\<omega>def' = \<omega>def" and
       NormalPremise: "exhale_pred_acc_normal_premise ctxt_vpr pid e_args_vpr e_p_vpr v_args_vpr p \<omega>def \<omega> \<omega>'"
    using * \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close> \<open>\<omega>def_\<omega>' = (\<omega>def', \<omega>')\<close>
    by auto

  let ?ploc = "(pid,v_args_vpr)"

  have perm_suff: "p \<ge> 0 \<and> p \<le> Rep_preal (get_mp_total_full \<omega> ?ploc)"
    using NormalPremise exhale_pred_acc_normal_premise_def exhale_pred_acc_rel_perm_success_def
    by blast+

  have \<omega>'_def: "\<omega>' = rm_from_lpm_total_full \<omega> ?ploc (Abs_preal p)"
    using NormalPremise exhale_pred_acc_normal_premise_def
    by blast

  hence mh_same: "get_mh_total_full \<omega> = get_mh_total_full \<omega>'" and
        mp_rel: "get_mp_total_full \<omega>' = (get_mp_total_full \<omega>)( ?ploc := get_mp_total_full \<omega> ?ploc - Abs_preal p )"
     apply simp
    apply (subst \<open>\<omega>' = _\<close>)
    apply (rule ext)
    apply (rename_tac lp)
    apply (case_tac "lp = ?ploc"; simp)
    apply (insert perm_suff)
    apply (case_tac "get_fnm_total_full \<omega> ?ploc"; simp)
    using minus_preal.abs_eq zero_preal.rep_eq zero_preal_def apply force
    by (metis Abs_preal_inverse add.commute all_pos comm_monoid_add_class.add_0 greater_minus_plus less_eq_preal.rep_eq mem_Collect_eq minus_preal_gte order_antisym posreal_to_preal(8) pperm_pnone_pgt)

  have store_same: "get_store_total \<omega> = get_store_total \<omega>'"
    by (simp add: \<omega>'_def)

  have trace_same: "get_trace_total \<omega> = get_trace_total \<omega>'"
    by (simp add: \<omega>'_def)

  have hh_same: "get_hh_total_full \<omega> = get_hh_total_full \<omega>'"
    by (simp add: \<omega>'_def)

  have \<omega>'_extcons: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow>
    StateCons \<omega>' \<and> consistent_external (total_context.make Pr (\<lambda>_. None) (domain_type TyRep)) (get_total_full \<omega>')"
    apply (intro conjI)
    using total_consistency_rm_from_lpm_int[OF WfCons]
     apply (metis Abs_preal_inverse InitRel Rep_preal_inverse \<open>\<omega>' = _\<close> less_preal.rep_eq mem_Collect_eq order_le_less perm_suff state_rel_consistent)
    unfolding \<open>\<omega>' = _\<close>
    apply (rule total_consistency_rm_from_lpm_ext[OF WfCons])
    using CtxtPredWf ProgEq
      apply (simp add: total_context.defs ctxt_pred_syn_wf_def)
    using InitRel state_rel_consistent
     apply blast
    using Abs_preal_inverse less_eq_preal.rep_eq perm_suff
    by auto

  obtain mb where
    LookupMask: "lookup_var (var_context ctxt_bpl) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
    LookupMaskTy: "lookup_var_ty (var_context ctxt_bpl) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
    MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) (get_mp_total_full \<omega>) mb"
    using state_rel_obtain_mask[OF StateRelIn[OF R_pair]]
    by blast

  \<comment> \<open>Construct the value of the new permission from the Viper state.\<close>
  let ?np = "Rep_preal (get_mp_total_full \<omega> ?ploc) - p"

  have LookupTempPerm: "lookup_var (var_context ctxt_bpl) ns temp_perm = Some (RealV p)"
    using state_rel_aux_pred_sat_lookup_2[OF StateRelIn[OF R_pair]]
    unfolding pred_eq_def
    by (metis (full_types) fun_upd_same)

  have null_eval: "red_expr_bpl ctxt_bpl (Var nullConst) ns (AbsV (ARef Null))"
    apply (rule red_expr_red_exprs.RedVar)
    by (metis NullConst StateRelIn R_pair boogie_const_rel_lookup boogie_const_val.simps(3) state_rel_boogie_const_rel)

  have new_perm_eval: "red_expr_bpl ctxt_bpl new_perm ns (LitV (LReal ?np))"
    apply (simp add: NewPermBpl)
    apply (rule red_expr_red_exprs.RedBinOp[where ?v1.0="LitV (LReal (Rep_preal (get_mp_total_full \<omega> ?ploc)))" and ?v2.0="LitV (LReal p)"])
      apply (rule mask_read_wf_apply[OF MaskReadWf, where ?m=mb and ?r=Null and ?f="PredSnapshotField ?ploc"])
          apply (metis MaskRel mask_rel_def)
         apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
        apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl'_def] NormalPremise R_pair \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close>
    unfolding exhale_pred_acc_normal_premise_def exhale_pred_acc_rel_assms_def
       apply force
      apply (simp add: PredType)
     apply (fastforce intro: RedVar LookupTempPerm)
    by simp

  \<comment> \<open>Construct the new Boogie heap.\<close>
  let ?mb' = "mb( (Null, PredSnapshotField ?ploc) := ?np )"

  have m_upd_bpl_red: "red_expr_bpl ctxt_bpl m_upd_bpl ns (AbsV (AMask ?mb'))"
    apply (subst \<open>m_upd_bpl = _\<close>)
    apply (rule mask_update_wf_apply[OF MaskUpdateWf])
        apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
       apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl'_def] NormalPremise R_pair \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close>
    unfolding exhale_pred_acc_normal_premise_def exhale_pred_acc_rel_assms_def
      apply simp
    using new_perm_eval
     apply blast
    by (simp add: PredType)

  have "valid_heap_mask (get_mh_total_full \<omega>)"
    using InitRel state_rel_wf_mask_simple
    by blast

  have Disj: "disjoint_list [ {heap_var Tr, heap_var_def Tr},
                              {mask_var Tr, mask_var_def Tr},
                              ran (var_translation Tr),
                              ran (field_translation Tr),
                              range (const_repr Tr), dom AuxPred]"
    using InitRel state_rel_disjoint
    by (smt (verit) dom_fun_upd fun_upd_triv map_le_imp_upd_le option.simps(3) state_rel_aux_pred_remove upd_None_map_le)

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl
                ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns)
                ((BigBlock name cs str tr, cont), Normal ns') \<and> R' \<omega>def_\<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (TMaskId TyRep)" and ?v="AbsV (AMask ?mb')"])
    using MaskVar StateRelIn R_pair state_rel_obtain_mask
       apply blast
      apply (simp add: TyInterp)
    using m_upd_bpl_red
     apply blast
    unfolding \<open>\<omega>def_\<omega>' = _\<close> \<open>\<omega>def' = \<omega>def\<close>
    apply (rule StateRelOut)
    apply (simp only: state_rel_def)
    apply (simp only: state_rel0_def, intro conjI)
    using state_rel_wf_mask_simple[OF InitRel] \<open>\<omega>' = _\<close>
                     apply (simp, simp)
                     apply (metis InitRel' get_mh_total.simps get_mh_total_full.elims state_rel_wf_mask_def_simple)
                    apply (simp add: TyInterp)
    using \<open>valid_heap_mask (get_mh_total_full \<omega>)\<close> mh_same
                    apply simp
                   apply (intro impI conjI)
    using InitRel state_rel_consistent apply blast
    using \<omega>'_extcons apply blast
    using InitRel state_rel_consistent apply blast
    using \<omega>'_extcons apply blast
                  apply (simp add: TyInterp)
                 apply (rule store_rel_stable[where ?\<omega>=\<omega> and ?ns=ns])
    using InitRel state_rel_store_rel
                   apply blast
                  apply (simp add: \<omega>'_def)
                 apply (metis InitRel MaskVar state_rel_disj_mask_store update_var_other)
                apply (simp add: Disj)
    using InitRel state_rel_eval_welldef_eq store_same apply fastforce
    using InitRel state_rel_eval_welldef_eq trace_same apply fastforce
    using InitRel state_rel_eval_welldef_eq hh_same apply fastforce
            defer defer defer defer
            apply (rule heap_knownfolded_var_rel_rm_from_lpm
                          [OF state_rel_heap_knownfolded_var_rel[OF InitRel'] KFRelOff])
    using state_rel_consistent[OF InitRel' ConsOn]
              apply blast
    using InitRel' MaskVar heap_var_disjoint state_rel_state_rel0 update_var_other
             apply metis
            apply (simp add: \<open>\<omega>' = _\<close>)
           apply (metis InitRel MaskVar field_rel_stable mask_var_disjoint state_rel_field_rel state_rel_state_rel0 update_var_other)
          apply (metis InitRel MaskVar boogie_const_rel_stable mask_var_disjoint state_rel_boogie_const_rel state_rel_state_rel0 update_var_other)
         defer
         apply (metis (no_types, lifting) InitRel' MaskVar aux_vars_pred_sat_def domI mask_var_disjoint state_rel_aux_pred_sat_lookup state_rel_state_rel0 update_var_other)
  proof -
    let ?ns' = "update_var (var_context ctxt_bpl) ns m_bpl
                  (AbsV (AMask (mb((Null, PredSnapshotField ?ploc) :=
                                   Rep_preal (get_mp_total_full \<omega> ?ploc) - p))))"

    \<comment> \<open>Prove \<^const>\<open>heap_var_rel\<close>\<close>
    show HeapRel: "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel0_heap_var_rel[OF InitRel[simplified state_rel_def]]])
       apply (simp add: \<omega>'_def)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    \<comment> \<open>Prove \<^const>\<open>mask_var_rel\<close>\<close>
    show MaskRel': "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var Tr) \<omega>' ?ns'"
      apply (unfold mask_var_rel_def)
      apply (rule exI[of _ ?mb'])
      apply (intro conjI)
        apply (simp add: MaskVar)
      using LookupMaskTy
       apply blast
      apply (unfold mask_rel_def)
      apply (intro conjI)
      using MaskRel[simplified mask_rel_def] mh_same
         apply auto[1]
        apply (simp add: MaskRel[simplified mask_rel_def])
      using MaskRel[simplified mask_rel_def] perm_suff Abs_preal_inverse less_eq_preal.rep_eq minus_preal.rep_eq mp_rel perm_suff
      by auto

    show "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var_def Tr) \<omega>def ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF InitRel]])
       apply simp
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    show "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var_def Tr) \<omega>def ?ns'"
      apply (rule mask_var_rel_stable[OF state_rel_mask_var_def_rel[OF InitRel]])
        apply simp
       apply simp
      using MaskVar MaskVarDefDiff
      by force

    show "state_well_typed (type_interp ctxt_bpl) (var_context ctxt_bpl) [] ?ns'"
      apply (rule state_well_typed_upd_2)
      using InitRel state_rel_state_well_typed
       apply blast
      by (simp add: TyInterp LookupMaskTy MaskVar)
  qed
qed

lemma exhale_rel_pred_acc:
  assumes WfSubexp: "exprs_wf_rel
                       (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and>
                         Q (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega>def \<omega>)
                       ctxt_vpr StateCons P ctxt_bpl (e_args_vpr @ [e_p_vpr]) \<gamma> \<gamma>\<^sub>2"
      and CorrectPermRel:
            "\<And>v_args v_p.
               rel_general (uncurry R) (R' v_args v_p)
                 (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. \<omega>0_\<omega> = \<omega>0_\<omega>' \<and>
                    exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) \<and>
                    exhale_pred_acc_rel_perm_success ctxt_vpr (snd \<omega>0_\<omega>) pred_id v_args v_p)
                 (\<lambda> \<omega>0_\<omega>.
                    exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) \<and>
                    \<not> exhale_pred_acc_rel_perm_success ctxt_vpr (snd \<omega>0_\<omega>) pred_id v_args v_p)
                 P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and UpdExhRel:
            "\<And>v_args v_p.
               rel_general (R' v_args v_p) (uncurry R) \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                 (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. fst \<omega>0_\<omega> = fst \<omega>0_\<omega>' \<and>
                    exhale_pred_acc_normal_premise ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) (snd \<omega>0_\<omega>'))
                 (\<lambda>_. False)
                 P ctxt_bpl \<gamma>\<^sub>3 \<gamma>'"
    shows "exhale_rel R R Q ctxt_vpr StateCons P ctxt_bpl (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<gamma> \<gamma>'"
  apply (rule exhale_rel_pred_acc_general)
    apply (rule WfSubexp)
   apply (rule rel_general_conseq_input[OF CorrectPermRel])
   apply simp
  apply (rule UpdExhRel)
  done

end
