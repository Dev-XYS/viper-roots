theory PredicateRel
  imports InhaleRel ExhaleRel StmtRel TotalViperSemantics.TotalExtConsPreservation BoogieSyntaxBasedProperties
begin


subsection \<open>Inhale\<close>


lemma inhale_pred_non_empty_implies_well_typed:
  assumes "inhale_perm_single_pred ctxt StateCons \<omega> (pid,vs) p_opt \<noteq> {}"
  shows "pred_ty_correct_premise ctxt pid vs"
  using assms[unfolded inhale_perm_single_pred_def]
  unfolding pred_ty_correct_premise_def consistent_external_wrt_ploc.simps
  by fastforce


\<comment> \<open>The following definition needs a well-definedness state, because in fold statement, the inhale
    happens after exhale, and the argument and permission evaluation holds only in the initial state.\<close>
definition inhale_pred_normal_premise
  where "inhale_pred_normal_premise ctxt StateCons pid e_args e_p vs p \<omega>_def \<omega> \<omega>' \<equiv>
           pred_ty_correct_premise ctxt pid vs \<and>
           red_pure_exps_total ctxt (Some \<omega>_def) e_args \<omega> (Some vs) \<and>
           ctxt, Some \<omega>_def \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and>
           p \<ge> 0 \<and>
           (let W' = inhale_perm_single_pred ctxt StateCons \<omega> (pid,vs) (Some (Abs_preal p)) in \<omega>' \<in> W')"


lemma inhale_predicate_acc_rel:
  assumes WfSubexp: "exprs_wf_rel (\<lambda>\<omega>def \<omega> ns. R \<omega> ns \<and> \<omega>def = \<omega> \<and> Q (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>)
                       ctxt_vpr StateCons P ctxt (e_args @ [e_p]) \<gamma> \<gamma>2"
      and PosPermRel: "\<And>vs p. rel_general R (R' vs p)
                         (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>' \<and> (ctxt_vpr, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p \<ge> 0) \<and>
                                  red_pure_exps_total ctxt_vpr (Some \<omega>) e_args \<omega> (Some vs) \<and>
                                  pred_ty_correct_premise ctxt_vpr pred_id vs)
                         (\<lambda> \<omega>. (ctxt_vpr, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p < 0))
                         P ctxt \<gamma>2 \<gamma>3"
      and UpdInhRel: "\<And>vs p. rel_general (R' vs p) R \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                         (\<lambda>\<omega> \<omega>'. inhale_pred_normal_premise ctxt_vpr StateCons pred_id e_args e_p vs p \<omega> \<omega> \<omega>')
                         (\<lambda>\<omega>. False) P ctxt \<gamma>3 \<gamma>'"
    shows "inhale_rel R Q ctxt_vpr StateCons P ctxt (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<gamma> \<gamma>'"
proof (rule inhale_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" and "Q (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>"
  hence Rext0: "state_rel_ext R \<omega> \<omega> ns"
    by simp
  assume RedInh: "red_inhale ctxt_vpr StateCons (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> res"
  thus "rel_vpr_aux R P ctxt \<gamma> \<gamma>' ns res"
  proof (cases)
    case (InhAccPred v_args p W')

    hence "red_pure_exps_total ctxt_vpr (Some \<omega>) (e_args @ [e_p]) \<omega> (Some (v_args @ [VPerm p]))"
      by (simp add: red_pure_exps_append_success)
    then obtain ns2 where "R \<omega> ns2" and Red2: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using InhAcc exprs_wf_rel_normal_elim[OF WfSubexp] Rext0 \<open>Q _ \<omega>\<close>
      by blast

    show ?thesis
    proof (rule rel_vpr_aux_intro)
      \<comment>\<open>Normal case\<close>
      fix \<omega>'
      assume "res = RNormal \<omega>'"
      hence "0 \<le> p" and "W' \<noteq> {}" and "\<omega>' \<in> W'"
      using th_result_rel_normal InhAccPred
      by blast+

    with InhAccPred and \<open>res = _\<close>
    have InhNormalPremise: "inhale_pred_normal_premise ctxt_vpr StateCons pred_id e_args e_p v_args p \<omega> \<omega> \<omega>'"
      unfolding inhale_pred_normal_premise_def
      by (simp add: inhale_pred_non_empty_implies_well_typed)

    from InhAccPred \<open>0 \<le> p\<close> obtain ns3 where "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>3, Normal ns3)" and "R' v_args p \<omega> ns3"
      using rel_success_elim[OF PosPermRel \<open>R \<omega> ns2\<close>] Red2 red_ast_bpl_transitive
            \<open>W' \<noteq> {}\<close> inhale_pred_non_empty_implies_well_typed
      by blast

    thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
      using rel_success_elim[OF UpdInhRel _ InhNormalPremise] RedInh \<open>res = _\<close> red_ast_bpl_transitive
      by blast

    next
      \<comment>\<open>Failure case\<close>
      assume "res = RFailure"
      hence "p < 0"
        using th_result_rel_failure_2 InhAccPred
        by fastforce

      with InhAccPred show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
        using rel_failure_elim[OF PosPermRel \<open>R \<omega> ns2\<close>] Red2 red_ast_bpl_transitive
        by blast
    qed
  next
    case InhSubExpFailure
    thus ?thesis
      unfolding rel_vpr_aux_def
      using exprs_wf_rel_failure_elim[OF WfSubexp] \<open>R \<omega> ns\<close> \<open>Q _ \<omega>\<close>
      by simp
  qed
qed


definition ploc_rel_vpr_bpl where
  "ploc_rel_vpr_bpl R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl \<equiv>
     \<forall>\<omega> ns v_args_vpr. R \<omega> ns \<longrightarrow>
         red_pure_exps_total ctxt_vpr (Some \<omega>) e_args_vpr \<omega> (Some v_args_vpr) \<longrightarrow>
         pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<longrightarrow>
         red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredSnapshotField (pid,v_args_vpr))))"


definition ploc_rel_vpr_bpl' where
  "ploc_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl \<equiv>
     \<forall>\<omega>def \<omega> ns v_args_vpr. R \<omega>def \<omega> ns \<longrightarrow>
         red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr) \<longrightarrow>
         pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<longrightarrow>
         red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredSnapshotField (pid,v_args_vpr))))"


lemma inhale_rel_pred_acc_upd_rel:
  assumes
    StateRel: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow>
                         state_rel_def_same Pr StateCons TyRep Tr
                           (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega> ns" and
              "temp_perm \<notin> dom AuxPred" and

    WfTyRep: "wf_ty_repr_bpl TyRep" and
    MaskVarDefSame: "mask_var_def Tr = mask_var Tr" and
    TyInterp: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and

    NullConst: "const_repr Tr CNull = nullConst" and
    MaskVar: "m_bpl = mask_var Tr" and

    MaskUpdateWf: "mask_update_wf TyRep ctxt_bpl mask_upd_bpl" and
    MaskReadWf: "mask_read_wf TyRep ctxt_bpl mask_read_bpl" and

    PredType: "pred_snap_field_type TyRep pid = Some pred_type" and

    NewPermBpl: "new_perm = (mask_read_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl
                                  [pred_type, TConSingle (TFrameFragmentId TyRep)]) \<guillemotleft>Add\<guillemotright> (Var temp_perm)" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl new_perm
                                  [pred_type, TConSingle (TFrameFragmentId TyRep)]" and

    PlocBpl: "e_ploc_bpl = FunExp pid [] e_args_bpl" and
    PlocRel: "ploc_rel_vpr_bpl R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and

    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep" and
    ProgEq: "program_total ctxt_vpr = Pr"
 and

    KFPosOff: "\<not> kf_pos_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
  shows "rel_general R
           (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl)
           (\<lambda>\<omega> \<omega>'. inhale_pred_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr p \<omega> \<omega> \<omega>')
           (\<lambda>\<omega>. False) P ctxt_bpl
           (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
           (BigBlock name cs str tr, cont)"

  apply (rule rel_intro)
   prefer 2
   apply blast
proof -
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and *: "inhale_pred_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr p \<omega> \<omega> \<omega>'"

  hence InitRel: "state_rel_def_same Pr StateCons TyRep Tr
                                     (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega> ns"
    using StateRel
    by blast

  hence InitRel': "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns"
    apply (rule state_rel_aux_pred_remove[where ?AuxPred="AuxPred(temp_perm \<mapsto> pred_eq (RealV p))" and ?AuxPred'=AuxPred])
    by (simp add: assms(2) map_le_def)

  let ?ploc = "(pid,v_args_vpr)"

  obtain \<phi>_inh where \<omega>':
    "consistent_external_wrt_ploc ctxt_vpr \<phi>_inh ?ploc (Abs_preal p)" and
    "get_hh_total \<phi>_inh = get_hh_total_full \<omega>" and
    "\<omega>' = (if Abs_preal p = 0 then \<omega> else add_to_lpm_nonzero_total_full \<omega> ?ploc (Abs_posreal (Abs_preal p)) (get_nm_total \<phi>_inh))" and
    "StateCons \<omega>'"
    by (smt (verit) * inhale_perm_single_pred_def inhale_pred_normal_premise_def mem_Collect_eq option_fold.simps(1))

  hence mh_same: "get_mh_total_full \<omega> = get_mh_total_full \<omega>'" and
        mp_rel: "get_mp_total_full \<omega>' = (get_mp_total_full \<omega>)( ?ploc := get_mp_total_full \<omega> ?ploc + Abs_preal p )"
     apply simp
    apply (cases "p = 0")
    using \<open>\<omega>' = _\<close> zero_preal_def
     apply force
    using \<open>\<omega>' = _\<close>
    apply (simp del: add_to_lpm_nonzero_total_full.simps get_mp_total_full.simps)
    using add_to_lpm_nonzero_total_full__mp
    by (metis all_pos mem_Collect_eq order_less_le posreal_to_preal(8))

  have \<omega>'_extcons: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow>
    consistent_external (total_context.make Pr (\<lambda>_. None) (domain_type TyRep)) (get_total_full \<omega>')"
    apply (cases "p = 0")
     apply (metis InitRel' \<open>\<omega>' = _\<close> state_rel_consistent zero_preal.abs_eq)
  proof -
    assume "consistent_state_rel_opt (state_rel_opt Tr)"
      and "p \<noteq> 0"
    have "consistent_external (total_context.make Pr (\<lambda>_. None) (domain_type TyRep)) (get_total_full \<omega>)"
      using InitRel' \<open>consistent_state_rel_opt (state_rel_opt Tr)\<close> state_rel_consistent
      by blast
    have 3: "\<omega>' = add_to_lpm_nonzero_total_full \<omega> ?ploc (Abs_posreal (Abs_preal p)) (get_nm_total \<phi>_inh)"
      by (meson * \<open>\<omega>' = _\<close> \<open>p \<noteq> 0\<close> inhale_pred_normal_premise_def linorder_neqE_linordered_idom linorder_not_le positive_real_preal)
    have "consistent_external_wrt_ploc ctxt_vpr \<phi>_inh ?ploc (Abs_preal p)"
      using * \<omega>' \<open>p \<noteq> 0\<close> inhale_pred_normal_premise_def
      by force
    hence 2: "consistent_external_wrt_ploc ctxt_vpr
                \<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = get_nm_total \<phi>_inh \<rparr>
                ?ploc (Abs_preal p)"
      by (metis (full_types) \<open>get_hh_total \<phi>_inh = get_hh_total_full \<omega>\<close> old.unit.exhaust total_state.surjective)
    show ?thesis
      unfolding 3
      apply (rule extcons_preserved_by_add_to_lpm_nonzero)
        apply fact
       apply (rule extcons_fun_interp_irrelevant[of ctxt_vpr])
         apply (simp add: total_context.defs)
         apply fact
        apply (simp add: total_context.defs AbsInterpEq)
       apply fact
      by (metis * \<open>p \<noteq> 0\<close> inhale_pred_normal_premise_def order_neq_le_trans positive_real_preal pperm_pnone_pgt)
  qed

  obtain mb where
    LookupMask: "lookup_var (var_context ctxt_bpl) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
    LookupMaskTy: "lookup_var_ty (var_context ctxt_bpl) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
    MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) (get_mp_total_full \<omega>) mb"
    using state_rel_obtain_mask[OF StateRel[OF \<open>R \<omega> ns\<close>]]
    by blast

  \<comment> \<open>Construct the value of the new permission from the Viper state.\<close>
  let ?np = "Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr)) + p"

  have LookupTempPerm: "lookup_var (var_context ctxt_bpl) ns temp_perm = Some (RealV p)"
    using state_rel_aux_pred_sat_lookup_2[OF StateRel[OF \<open>R \<omega> ns\<close>]]
    unfolding pred_eq_def
    by (metis (full_types) fun_upd_same)

  have null_eval: "red_expr_bpl ctxt_bpl (Var nullConst) ns (AbsV (ARef Null))"
    apply (rule red_expr_red_exprs.RedVar)
    by (metis NullConst StateRel \<open>R \<omega> ns\<close> boogie_const_rel_lookup boogie_const_val.simps(3) state_rel_boogie_const_rel)

  have new_perm_eval: "red_expr_bpl ctxt_bpl new_perm ns (LitV (LReal ?np))"
    apply (simp add: NewPermBpl)
    apply (rule red_expr_red_exprs.RedBinOp[where ?v1.0="LitV (LReal (Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr))))" and ?v2.0="LitV (LReal p)"])
      apply (rule mask_read_wf_apply[OF MaskReadWf, where ?m=mb and ?r=Null and ?f="PredSnapshotField (pid,v_args_vpr)"])
          apply (metis MaskRel mask_rel_def)
         apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
        apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl_def] * inhale_pred_normal_premise_def \<open>R \<omega> ns\<close>
       apply blast
    using PredType
      apply simp
     apply (fastforce intro: RedVar LookupTempPerm)
    by simp

  \<comment> \<open>Construct the new Boogie heap.\<close>
  let ?mb' = "mb( (Null, PredSnapshotField (pid,v_args_vpr)) := ?np )"

  have m_upd_bpl_red: "red_expr_bpl ctxt_bpl m_upd_bpl ns (AbsV (AMask ?mb'))"
    apply (subst \<open>m_upd_bpl = _\<close>)
    apply (rule mask_update_wf_apply[OF MaskUpdateWf])
        apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
       apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl_def] * inhale_pred_normal_premise_def \<open>R \<omega> ns\<close>
      apply blast
    using new_perm_eval
     apply blast
    using PredType
    by force

  have "valid_heap_mask (get_mh_total_full \<omega>)"
    using InitRel state_rel_wf_mask_simple by blast

  have Disj: "disjoint_list [ {heap_var Tr, heap_var_def Tr},
                              {mask_var Tr, mask_var_def Tr},
                              ran (var_translation Tr),
                              ran (field_translation Tr),
                              range (const_repr Tr), dom AuxPred]"
    using InitRel' state_rel_disjoint
    by blast

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl
                ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns)
                ((BigBlock name cs str tr, cont), Normal ns') \<and>
              state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (TMaskId TyRep)" and ?v="AbsV (AMask ?mb')"])
    using MaskVar StateRel \<open>R \<omega> ns\<close> state_rel_obtain_mask
       apply blast
      apply (simp add: TyInterp)
    using m_upd_bpl_red
     apply blast
    apply (simp only: state_rel_def)
    apply (simp only: state_rel0_def, intro conjI)
    using state_rel_wf_mask_simple[OF InitRel] \<omega>'
                     apply (simp, simp)
    using mh_same
                     apply auto[1]
    using \<open>valid_heap_mask (get_mh_total_full \<omega>)\<close> mh_same
                    apply force
    using \<omega>'_extcons \<open>StateCons \<omega>'\<close>
                   apply blast
                  apply (simp add: TyInterp)
                 apply (rule store_rel_stable[where ?\<omega>=\<omega> and ?ns=ns])
    using InitRel state_rel_store_rel
                   apply blast
                  apply (metis * inhale_perm_single_pred_store_same inhale_pred_normal_premise_def)
                 apply (metis InitRel MaskVar state_rel_disj_mask_store update_var_other)
                apply (simp add: Disj)
               apply (simp, simp, simp)
            defer defer defer defer defer
            apply (metis InitRel MaskVar field_rel_stable mask_var_disjoint state_rel_field_rel state_rel_state_rel0 update_var_other)
           apply (metis InitRel MaskVar boogie_const_rel_stable mask_var_disjoint state_rel_boogie_const_rel state_rel_state_rel0 update_var_other)
          defer
          apply (metis (no_types, lifting) InitRel' MaskVar aux_vars_pred_sat_def domI mask_var_disjoint state_rel_aux_pred_sat_lookup state_rel_state_rel0 update_var_other)
  proof -
    let ?ns' = "update_var (var_context ctxt_bpl) ns m_bpl
                  (AbsV (AMask (mb((Null, PredSnapshotField (pid,v_args_vpr)) :=
                                   Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr)) + p))))"

    \<comment> \<open>Prove \<^const>\<open>heap_var_rel\<close>\<close>
    show HeapRel: "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel0_heap_var_rel[OF InitRel[simplified state_rel_def]]])
       apply (metis * inhale_perm_single_pred_heap_same inhale_pred_normal_premise_def)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    \<comment> \<open>Prove \<^const>\<open>mask_var_rel\<close>\<close>
    show MaskRel: "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var Tr) \<omega>' ?ns'"
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
      using MaskRel[simplified mask_rel_def]
       apply (smt (verit, best) * MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def is_bounded_field_bpl.simps(1) prod.sel(2))
      apply (subst \<open>get_mp_total_full \<omega>' = _\<close>)
       apply (metis (no_types, lifting) * Abs_preal_inverse MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def mem_Collect_eq plus_preal.rep_eq prod.inject vb_field.simps(2))
      using MaskRel[simplified mask_rel_def]
      by simp

    show "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var_def Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF InitRel]])
       apply (metis * inhale_perm_single_pred_heap_same inhale_pred_normal_premise_def)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    show MaskRel: "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var_def Tr) \<omega>' ?ns'"
      apply (subst MaskVarDefSame)
      using MaskRel
      by blast

    have "\<omega>' \<ge> \<omega>"
      by (meson * inhale_perm_single_pred_mono inhale_pred_normal_premise_def)
    then show "heap_knownfolded_var_rel (knownfolded_state_rel_opt (state_rel_opt Tr)) Pr
            (var_context ctxt_bpl) (field_translation Tr) (heap_var Tr) \<omega>' ?ns'"
      apply (rule heap_knownfolded_var_rel_stable_larger_\<omega>
                    [OF state_rel_heap_knownfolded_var_rel[OF InitRel]])
      using InitRel' MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other
       apply metis
      using KFPosOff
      by blast

    show "state_well_typed (type_interp ctxt_bpl) (var_context ctxt_bpl) [] ?ns'"
      apply (rule state_well_typed_upd_2)
      using InitRel state_rel_state_well_typed
       apply blast
      by (simp add: TyInterp LookupMaskTy MaskVar)
  qed
qed


lemma inhale_pred_acc_rel_assms_perm_eval:
  assumes "inhale_pred_normal_premise ctxt StateCons pred_id e_args e_p v_args v_p \<omega>_def \<omega> \<omega>'"
  shows "ctxt, Some \<omega>_def \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)"
  using assms
  unfolding inhale_pred_normal_premise_def
  by blast



subsection \<open>Exhale\<close>

\<comment> \<open>Todo: Move stuff here.\<close>



subsection \<open>Misc\<close>


lemma bpl_assert_true_is_skip:
  assumes "rel_general R R' Success Fail P ctxt (BigBlock name cs s tr, cont) \<gamma>'"
    shows "rel_general R R' Success Fail P ctxt (BigBlock name (cmd.Assert (Lit (LBool True)) # cs) s tr, cont) \<gamma>'"
  apply (rule rel_propagate_pre_assert_2)
    apply (rule RedLit)
   apply simp
  apply (simp add: assms)
  done


lemma red_bpl_assert_true:
  shows "rel_general R R (=) (\<lambda>_. False) P ctxt (BigBlock name (cmd.Assert (Lit (LBool True)) # cs) s tr, cont) (BigBlock name cs s tr, cont)"
  apply (rule rel_propagate_pre_assert_2)
    apply (rule RedLit)
   apply simp
  apply (rule rel_general_success_refl)
  by simp_all



subsection \<open>Inhale Simulates Unfold\<close>


lemma inhale_simulates_unfold:
  assumes Unfold: "unfold_rel ctxt pid vs q \<phi> \<phi>'"
      and ExtCons: "consistent_external ctxt \<phi>"
      and WfCons: "wf_total_consistency ctxt StateCons StateCons_t"
      and IntCons: "StateCons_t \<phi>"
      and PredDecl: "ViperLang.predicates (program_total ctxt) pid = Some pdecl"
      and PredBody: "ViperLang.predicate_decl.body pdecl = Some pbody"
      and CtxtWfPred: "ctxt_pred_syn_wf ctxt"
      and SelfFraming: "\<And>q. 0 < q \<Longrightarrow> assertion_self_framing_store ctxt StateCons (syntactic_mult q pbody) (nth_option vs)"
      and "\<phi>\<^sub>d = rm_from_lpm_total \<phi> (pid,vs) q"
      and "(\<forall>lbl \<phi>. trace lbl = Some \<phi> \<longrightarrow> StateCons_t \<phi>)"
      and AmountPos: "q > 0"  \<comment> \<open>It is okay because Viper checks if the unfolding amount is positive.\<close>
    shows "red_inhale ctxt StateCons (syntactic_mult (Rep_preal q) pbody)
                      \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>\<^sub>d \<rparr>
             (RNormal \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>' \<rparr>)"
proof -
  from assms(1)
  obtain nm nm' where
    "shift_up pid vs q nm nm'"
    "get_nm_total \<phi> = nm"
    "get_nm_total \<phi>' = nm'"
    "get_hh_total \<phi>' = get_hh_total \<phi>"
    by (blast elim: unfold_rel.cases)

  obtain mh fnm p\<^sub>p pnm p fnm\<^sub>u nm\<^sub>u_sub where
    "mh = get_mh_nm nm" and
    "fnm = get_fnm_nm nm"
    "Some (p\<^sub>p, pnm) = fnm (pid,vs)" and
    "p = Rep_posreal p\<^sub>p" and
    "q > 0" and
    "q \<le> p" and
    "fnm\<^sub>u = fnm( (pid,vs) := if p = q then None else Some (Abs_posreal (p - q), ((p - q) / p) *\<^sub>s pnm) )" and
    "nm\<^sub>u_sub = NM mh fnm\<^sub>u" and
    "nm' = nm\<^sub>u_sub + (q / p) *\<^sub>s pnm"
    apply (rule shift_up_case[OF \<open>shift_up _ _ _ _ _\<close>])
    using AmountPos
    by blast+

  define nm\<^sub>s where "nm\<^sub>s = (q / p) *\<^sub>s pnm"

  \<comment> \<open>The shifted part is external consistent w.r.t. the predicate.\<close>
  have pnm_cons: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>) (pid,vs) p"
    using ExtCons SatAll_case \<open>Some (p\<^sub>p, pnm) = fnm (pid,vs)\<close> \<open>fnm = get_fnm_nm nm\<close> \<open>get_nm_total \<phi> = nm\<close> \<open>p = Rep_posreal p\<^sub>p\<close>
    by fastforce
  have
    ShiftExtCons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = get_hh_total \<phi>, get_nm_total = nm\<^sub>s \<rparr> (pid,vs) q"
    using fraction_consistent_external(1)[OF CtxtWfPred pnm_cons, of "q / p"]
    unfolding nm\<^sub>s_def
    apply simp
    by (metis (mono_tags, lifting) AmountPos Rep_preal_inverse \<open>q \<le> p\<close> divide_preal.rep_eq leD map_fun_apply nonzero_eq_divide_eq old.unit.exhaust times_preal_def total_state.surjective total_state.update_convs(2) zero_preal.abs_eq)

  have 1: "add_to_nm_total_full
          \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>\<^sub>d \<rparr> nm\<^sub>s =
          \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>' \<rparr>"
    apply simp
    apply (rule total_state.equality)
      apply (simp add: \<open>get_hh_total \<phi>' = get_hh_total \<phi>\<close> PredBody)
      apply (simp add: assms(9))
     apply (rule nested_mask_equality)
      apply simp_all
    unfolding \<open>\<phi>\<^sub>d = _\<close>
     apply standard
     apply (simp add: add_masks_def)
     apply (simp add: \<open>get_nm_total \<phi> = nm\<close> \<open>get_nm_total \<phi>' = nm'\<close> \<open>mh = get_mh_nm nm\<close> \<open>nm' = nm\<^sub>u_sub + (q / p) *\<^sub>s pnm\<close> \<open>nm\<^sub>u_sub = NM mh fnm\<^sub>u\<close> add_masks_def nm\<^sub>s_def)
    unfolding \<open>\<phi>\<^sub>d = _\<close> \<open>get_nm_total \<phi> = nm\<close> \<open>get_nm_total \<phi>' = nm'\<close> nm\<^sub>s_def
      \<open>fnm = get_fnm_nm nm\<close>[symmetric] \<open>nm' = _\<close> \<open>nm\<^sub>u_sub = _\<close> \<open>fnm\<^sub>u = _\<close>
    apply (rule arg_cong[where ?f=get_fnm_nm])
    apply (rule arg_cong[where ?f="\<lambda>nm. nm + (q / p) *\<^sub>s pnm"])
    apply (rule nested_mask_equality)
     apply (simp add: \<open>get_nm_total \<phi> = nm\<close> \<open>mh = get_mh_nm nm\<close>)
    apply standard
    apply (rename_tac lp)
    apply (case_tac "lp = (pid,vs)"; simp)
     apply (cases "p = q"; simp)
    unfolding \<open>get_nm_total \<phi> = nm\<close> \<open>fnm = get_fnm_nm nm\<close>[symmetric] \<open>Some (p\<^sub>p, pnm) = fnm (pid,vs)\<close>[symmetric]
      apply (simp add: \<open>p = Rep_posreal p\<^sub>p\<close>)
    unfolding \<open>get_nm_total \<phi> = nm\<close> \<open>fnm = get_fnm_nm nm\<close>[symmetric] \<open>Some (p\<^sub>p, pnm) = fnm (pid,vs)\<close>[symmetric]
     apply simp
    unfolding \<open>p = Rep_posreal p\<^sub>p\<close>[symmetric]
     apply (intro conjI)
      apply (simp add: \<open>q \<le> p\<close> nle_le)
     apply (intro impI)
     apply (intro conjI)
      apply simp
     apply (rule arg_cong[where ?f="\<lambda>nm. nm *\<^sub>s pnm"])
     apply (simp add: preal_to_real)
     apply (smt (verit, del_insts) add_divide_distrib div_self less_divide_eq_1 prat_non_negative)
    by simp

  have Framed: "\<And>q. 0 < q \<Longrightarrow> assertion_framing_state ctxt StateCons (syntactic_mult q pbody)
                      \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>\<^sub>d \<rparr>"
    using assertion_self_framing_store_def SelfFraming
    by (metis full_total_state.update_convs(1) update_store_total.simps)

  have 2: "get_hh_total_full \<lparr>get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>'\<rparr> = get_hh_total \<phi>"
    apply simp
    using \<open>get_hh_total \<phi>' = get_hh_total \<phi>\<close>
    by auto

  have final_intcons: "StateCons_t \<phi>'"
    using WfCons[simplified wf_total_consistency_def] IntCons Unfold
    by blast

  show ?thesis
    apply (rule extcons_state_can_be_inhaled[OF PredDecl PredBody _ Framed ShiftExtCons, simplified 1])
    using CtxtWfPred PredBody PredDecl ctxt_pred_syn_wf_def
           apply blast
          apply simp
         apply (simp add: assms(9))
        apply simp
    using final_intcons WfCons[simplified wf_total_consistency_def]
       apply (simp add: assms(10))
    using CtxtWfPred WfCons[simplified wf_total_consistency_def] AmountPos
      apply simp
    by fact+
qed



subsection \<open>Unfold\<close>


lemma unfold_stmt_rel:
  assumes PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl"
      and PredArgs: "predicate_decl.args pdecl = ty_args"
      and PredBody: "predicate_decl.body pdecl = Some pbody"
      and CtxtPredWf: "ctxt_pred_syn_wf ctxt_vpr"
      and CtxtPredSF: "ctxt_pred_self_framing_inh ctxt_vpr StateCons"
      and WfCons: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and StateRelImpliesIntCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"
      and StateRelImpliesExtCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> consistent_external ctxt_vpr (get_total_full \<omega>)"
      and StateRelImpliesKFRel: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> heap_knownfolded_var_rel opt (program_total ctxt_vpr) (var_context ctxt_bpl) FieldTr hvar \<omega> ns"
      and StateRelWeakening: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> R\<^sub>w \<omega> ns"
      and ArgsRestriction: "list_all no_unfolding_pure_exp e_args \<and> list_all no_perm_pure_exp e_args"
      and BodyNoUnfolding: "no_unfolding_assertion (syntactic_mult p pbody)"  \<comment> \<open>Should be lifted soon.\<close>
      and PermSimp: "e_p = ELit (LPerm p)" \<comment> \<open>We only support literals as the permission.\<close>
      and PermPos: "p > 0"
      and StepExhale:
          "rel_general R\<^sub>w R\<^sub>w
             (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> (RNormal \<omega>'))
             (\<lambda>\<omega>. red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> RFailure)
             P ctxt_bpl \<gamma> \<gamma>\<^sub>2"
      and StepInhale: "inhale_rel R\<^sub>w (assertion_framing_state ctxt_vpr StateCons) ctxt_vpr StateCons P ctxt_bpl (syntactic_mult p (substitute_args_assertion pbody e_args)) \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and StepKFUpdate:
          "\<And>v_p v_args.
           rel_general (uncurry (\<lambda>\<omega>\<^sub>0 \<omega> ns. R\<^sub>w \<omega> ns \<and>
                                           ctxt_vpr, (Some \<omega>\<^sub>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p) \<and>
                                           red_pure_exps_total ctxt_vpr (Some \<omega>\<^sub>0) e_args \<omega> (Some v_args) \<and>
                                           pred_ty_correct_premise ctxt_vpr pid v_args \<and>
                                           unfold_rel ctxt_vpr pid v_args (Abs_preal v_p) (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>) \<and>
                                           heap_knownfolded_var_rel opt (program_total ctxt_vpr) (var_context ctxt_bpl) FieldTr hvar \<omega>\<^sub>0 ns))
                       (uncurry (\<lambda>\<omega>\<^sub>0 \<omega> ns. R' \<omega> ns))
                       (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                       (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                       P ctxt_bpl \<gamma>\<^sub>3 \<gamma>'"
      and NoHeapAssignBetween:
          "contains_no_heap_assignment_until hvar \<gamma>\<^sub>3 \<gamma>"
      and PPSyntacticRestriction: "program_point_restriction \<gamma>"
    shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt_bpl (Unfold pid e_args (PureExp e_p)) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro)
  \<comment> \<open>Specialize predicate body restrictions and self-framing to the predicate in consideration\<close>
  have SupportedPredBody: "supported_pred_body pbody"
    using CtxtPredWf PredBody PredDecl ctxt_pred_syn_wf_def
    by blast
  have SelfFraming: "assertion_self_framing ctxt_vpr StateCons pbody ty_args"
    using CtxtPredSF PredArgs PredBody PredDecl ctxt_pred_self_framing_inh_def
    by blast

  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and red_stmt: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Unfold pid e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
  then obtain v_args v_p \<phi>' where
    e_args_eval: "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args \<omega> (Some v_args)" and
    e_p_eval: "ctxt_vpr, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    "v_p \<ge> 0" and
    UnfoldRel: "unfold_rel ctxt_vpr pid v_args (Abs_preal v_p) (get_total_full \<omega>) \<phi>'" and
    "\<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr>"
    by (blast elim: RedUnfold_case)
  have "v_p > 0"
    using PermSimp PermPos TotalExpressions.RedLit_case e_p_eval
    by fastforce
  have perm_suff: "get_mp_total_full \<omega> (pid,v_args) \<ge> Abs_preal v_p"
    using unfold_rel_perm_sufficient[OF UnfoldRel]
    by simp

  have "R\<^sub>w \<omega> ns"
    by (simp add: StateRelWeakening \<open>R \<omega> ns\<close>)
  have \<omega>\<^sub>0_kfrel: "heap_knownfolded_var_rel opt (program_total ctxt_vpr) (var_context ctxt_bpl) FieldTr hvar \<omega> ns"
    by (simp add: StateRelImpliesKFRel \<open>R \<omega> ns\<close>)

  from \<open>R \<omega> ns\<close> have ExtCons: "consistent_external ctxt_vpr (get_total_full \<omega>)"
    using StateRelImpliesExtCons
    by auto
  have args_well_ty: "vals_well_typed (absval_interp_total ctxt_vpr) v_args ty_args"
    using extcons_pred_well_typed ExtCons PredArgs PredDecl \<open>0 < v_p\<close> order_le_imp_less_or_eq order_less_trans positive_real_preal preal_not_0_gt_0 perm_suff
    by fastforce
  with SelfFraming have FramingArgs: "\<And>p. 0 < p \<Longrightarrow> assertion_self_framing_store ctxt_vpr StateCons (syntactic_mult p pbody) (nth_option v_args)"
    using assertion_self_framing_def
    by blast

  have Cons_t: "StateCons_t (get_total_full \<omega>)"
    using WfCons[simplified wf_total_consistency_def]
    by (meson StateRelImpliesIntCons \<open>R \<omega> ns\<close>)
  have LabelCons: "\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> StateCons_t \<phi>"
    by (smt (verit, best) StateRelImpliesIntCons WfCons \<open>R \<omega> ns\<close> wf_total_consistency_def)

  from inhale_simulates_unfold[OF UnfoldRel ExtCons WfCons Cons_t PredDecl PredBody CtxtPredWf FramingArgs _ LabelCons]
  obtain \<phi>\<^sub>d where
    \<phi>\<^sub>d: "\<phi>\<^sub>d = rm_from_lpm_total (get_total_full \<omega>) (pid,v_args) (Abs_preal v_p)" and
    step_inhale': "red_inhale ctxt_vpr StateCons (syntactic_mult (Rep_preal (Abs_preal v_p)) pbody)
                     \<lparr> get_store_total = nth_option v_args, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>
            (RNormal \<lparr> get_store_total = nth_option v_args, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>' \<rparr>)"
    by (meson \<open>0 < v_p\<close> positive_real_preal pperm_pnone_pgt)

  let ?\<omega>\<^sub>d = "\<omega>\<lparr> get_total_full := \<phi>\<^sub>d \<rparr>"
  have "exh_if_total (v_p \<ge> 0 \<and> get_mp_total_full \<omega> (pid,v_args) \<ge> Abs_preal v_p)
                     (exhale_pred \<omega> (pid,v_args) (Abs_preal v_p))
        = RNormal ?\<omega>\<^sub>d"
    apply (simp only: perm_suff \<open>v_p \<ge> 0\<close>)
    by (simp add: exhale_pred_def \<phi>\<^sub>d)

  hence step_exh: "red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> (RNormal ?\<omega>\<^sub>d)"
    using ExhAccPred
    by (metis PredArgs PredBody PredDecl args_well_ty e_args_eval e_p_eval)

  obtain ns\<^sub>2 where bpl_step_exh: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2) \<and> R\<^sub>w ?\<omega>\<^sub>d ns\<^sub>2"
    using rel_success_elim[OF StepExhale \<open>R\<^sub>w \<omega> ns\<close> step_exh]
    by blast

  \<comment> \<open>Simplification: permission is constant\<close>
  have "v_p = p"
    using TotalExpressions.RedLit_case[OF e_p_eval[simplified PermSimp]]
    by auto
  hence inh_perm_const: "Rep_preal (Abs_preal v_p) = p"
    using one_preal.rep_eq one_preal_def Abs_preal_inverse \<open>0 \<le> v_p\<close>
    by auto

  \<comment> \<open>Step 2: inhale\<close>

  have step_inhale:
    "red_inhale ctxt_vpr StateCons (syntactic_mult (Rep_preal (Abs_preal v_p)) (substitute_args_assertion pbody e_args))
                \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>
       (RNormal \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>' \<rparr>)"
    apply (subst substitute_synmult_commute[symmetric])
     apply (simp add: prat_non_negative)
    apply (rule inhale_with_substitution)
               apply simp_all
           apply fact
          apply (rule eval_with_different_pred_heap(2)[OF _ _ _ _ _ e_args_eval])
    unfolding \<open>\<phi>\<^sub>d = _\<close>
                apply (simp_all add: ArgsRestriction)
    using SupportedPredBody prat_non_negative syntactic_mult_supported
      apply force
    using BodyNoUnfolding inh_perm_const
     apply auto[1]
    by fact

  have FramingSubst:
    "assertion_framing_state ctxt_vpr StateCons
       (syntactic_mult p (substitute_args_assertion pbody e_args))
       \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>"
    apply (subst substitute_synmult_commute[symmetric])
     apply (simp add: PermPos order_less_imp_le)
    apply (rule framing_with_substitution)
    using FramingArgs[of p, OF PermPos, unfolded assertion_self_framing_store_def, simplified]
          apply blast
         apply (rule eval_with_different_pred_heap(2)[OF _ _ _ _ _ e_args_eval])
    unfolding \<open>\<phi>\<^sub>d = _\<close>
               apply (simp_all add: ArgsRestriction)
    using PermPos SupportedPredBody syntactic_mult_supported
      apply auto[1]
    using BodyNoUnfolding inh_perm_const
     apply auto[1]
    by fact

  have \<omega>'_rel: "\<omega>' = \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>' \<rparr>"
    by (simp add: \<open>\<omega>' = _\<close>)
  have \<omega>\<^sub>d_rel: "\<omega>\<lparr> get_total_full := \<phi>\<^sub>d \<rparr> = \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>"
    by simp

  obtain ns\<^sub>3 where bpl_step_inh: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>\<^sub>3, Normal ns\<^sub>3)" and "R\<^sub>w \<omega>' ns\<^sub>3"
    using inhale_rel_normal_elim[OF StepInhale bpl_step_exh[THEN conjunct2], unfolded \<omega>\<^sub>d_rel, OF FramingSubst step_inhale[unfolded inh_perm_const, simplified]]
    unfolding \<omega>'_rel
    by blast

  \<comment> \<open>Step 3: known-folded permission update\<close>

  have \<omega>\<^sub>0_ns\<^sub>3_kfrel: "heap_knownfolded_var_rel opt (program_total ctxt_vpr) (var_context ctxt_bpl) FieldTr hvar \<omega> ns\<^sub>3"
    using \<omega>\<^sub>0_kfrel bpl_no_heap_assignment[OF NoHeapAssignBetween PPSyntacticRestriction]
    unfolding heap_knownfolded_var_rel_def
    by (metis bpl_step_exh bpl_step_inh red_ast_bpl_transitive)

  moreover have "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args \<omega>' (Some v_args)"
    by (metis (no_types, lifting) ArgsRestriction \<omega>'_rel \<omega>\<^sub>d_rel e_args_eval exhale_only_changes_total_state_aux inhale_only_changes_mask list_all_length red_pure_exp_only_differ_on_mask(2) step_exh step_inhale)

  moreover have "pred_ty_correct_premise ctxt_vpr pid v_args"
    using PredArgs PredDecl args_well_ty pred_ty_correct_premise_def
    by blast

  ultimately obtain ns' where bpl_step_kf: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>3, Normal ns\<^sub>3) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    using rel_success_elim[OF StepKFUpdate, where ?\<omega>="(\<omega>,\<omega>')", simplified] \<open>R\<^sub>w \<omega>' ns\<^sub>3\<close> e_args_eval e_p_eval UnfoldRel
    by (metis PermSimp \<omega>'_rel \<open>v_p = p\<close> full_total_state.select_convs(3) red_pure_exp_total_red_pure_exps_total.RedLit snd_eqD val_of_lit.simps(3))

  \<comment> \<open>Combine\<close>
  thus "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    using bpl_step_exh bpl_step_inh red_ast_bpl_transitive
    by blast

next

  fix \<omega> ns
  assume "R \<omega> ns"
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Unfold pid e_args (PureExp e_p)) \<omega> RFailure"

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) c'"
  proof cases
    case RedExhaleFailure
    fix v_args v_p pred_decl
    assume e_args_eval: "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args \<omega> (Some v_args)" and
           e_p_eval: "ctxt_vpr, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
           v_p_fail: "v_p \<le> 0 \<or> Rep_preal (get_mp_total_full \<omega> (pid, v_args)) < v_p" and
           pdecl': "program.predicates (program_total ctxt_vpr) pid = Some pred_decl" and
           args_well_ty: "vals_well_typed (absval_interp_total ctxt_vpr) v_args (predicate_decl.args pred_decl)"
    from v_p_fail have v_p_fail': "\<not> (0 \<le> v_p \<and> Abs_preal v_p \<le> (get_mp_total_full \<omega>) (pid,v_args))"
      apply (simp add: preal_to_real)
      using PermSimp TotalExpressions.RedLit_case e_p_eval PermPos
      by fastforce

    have step_exhale: "red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> RFailure"
      using ExhAccPred[OF _ e_args_eval e_p_eval PredDecl _ PredBody, where ?mp="get_mp_total_full \<omega>"] v_p_fail' PredDecl args_well_ty pdecl'
      by auto
    show ?thesis
      using rel_failure_elim[OF StepExhale _ step_exhale] StateRelWeakening \<open>R \<omega> ns\<close>
      by blast
  next
    case RedSubExpressionFailure
    have step_exhale: "red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> RFailure"
      apply (rule ExhSubExpFailure)
      using RedSubExpressionFailure
      by simp_all
    show ?thesis
      using rel_failure_elim[OF StepExhale _ step_exhale] StateRelWeakening \<open>R \<omega> ns\<close>
      by blast
  qed
qed


lemma unfold_exhale_pred_rel:
  assumes WfSubexp: "exprs_wf_rel
                       (\<lambda>\<omega>def \<omega> ns. R \<omega> ns \<and> \<omega>def = \<omega>)
                       ctxt_vpr StateCons P ctxt_bpl (e_args_vpr @ [e_p_vpr]) \<gamma> \<gamma>\<^sub>2"
      and CorrectPermRel:
            "\<And>v_args v_p.
               rel_general R (R' v_args v_p)
                 (\<lambda>\<omega> \<omega>'. \<omega> = \<omega>' \<and>
                    exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p \<omega> \<omega> \<and>
                    exhale_pred_acc_rel_perm_success ctxt_vpr \<omega> pred_id v_args v_p)
                 (\<lambda>\<omega>.
                    exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p \<omega> \<omega> \<and>
                    \<not> exhale_pred_acc_rel_perm_success ctxt_vpr \<omega> pred_id v_args v_p)
                 P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and UpdExhRel:
            "\<And>v_args v_p.
               rel_general (R' v_args v_p) R  \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                 (\<lambda>\<omega> \<omega>'. exhale_pred_acc_normal_premise ctxt_vpr pred_id e_args_vpr e_p_vpr v_args v_p \<omega> \<omega> \<omega>')
                 (\<lambda>_. False)
                 P ctxt_bpl \<gamma>\<^sub>3 \<gamma>'"
    shows "rel_general R R
             (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> (RNormal \<omega>'))
             (\<lambda>\<omega>. red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> RFailure)
             P ctxt_bpl \<gamma> \<gamma>'"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and exh: "red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> (RNormal \<omega>')"

  then obtain mp v_args p pdecl where
    "mp = get_mp_total_full \<omega>" and
    eval_e_args: "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args_vpr \<omega> (Some v_args)" and
    eval_e_p: "ctxt_vpr, Some \<omega> \<turnstile> \<langle>e_p_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
    pdecl: "program.predicates (program_total ctxt_vpr) pred_id = Some pdecl" and
    args_well_ty: "vals_well_typed (absval_interp_total ctxt_vpr) v_args (ViperLang.predicate_decl.args pdecl)" and
    "RNormal \<omega>' = exh_if_total (p \<ge> 0 \<and> mp (pred_id, v_args) \<ge> Abs_preal p)
                               (exhale_pred \<omega> (pred_id, v_args) (Abs_preal p))"
    by (auto elim: ExhAccPred_case)
  hence "red_pure_exps_total ctxt_vpr (Some \<omega>) (e_args_vpr @ [e_p_vpr]) \<omega> (Some (v_args @ [VPerm p]))"
    by (simp add: red_pure_exps_append_success)

  then obtain ns\<^sub>2 where "R \<omega> ns\<^sub>2" and Red2: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2)"
    using exprs_wf_rel_normal_elim[OF WfSubexp] \<open>R \<omega> ns\<close>
    by blast

  have eval_ok: "exhale_pred_acc_rel_assms ctxt_vpr pred_id e_args_vpr e_p_vpr v_args p \<omega> \<omega>"
    by (simp add: args_well_ty eval_e_args eval_e_p exhale_pred_acc_rel_assms_def pdecl pred_ty_correct_premise_def)
  moreover have perm_ok: "exhale_pred_acc_rel_perm_success ctxt_vpr \<omega> pred_id v_args p"
    unfolding exhale_pred_acc_rel_perm_success_def
    by (metis (full_types) Abs_preal_inverse \<open>RNormal \<omega>' = _\<close> \<open>mp = _\<close> exh_if_total_normal less_eq_preal.rep_eq mem_Collect_eq)
  ultimately obtain ns\<^sub>3 where "R' v_args p \<omega> ns\<^sub>3" and Red3: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>\<^sub>3, Normal ns\<^sub>3)"
    using rel_success_elim[OF CorrectPermRel \<open>R \<omega> ns\<^sub>2\<close>]
    by blast

  have "exhale_pred_acc_normal_premise ctxt_vpr pred_id e_args_vpr e_p_vpr v_args p \<omega> \<omega> \<omega>'"
    unfolding exhale_pred_acc_normal_premise_def
    by (metis \<open>RNormal \<omega>' = _\<close> eval_ok perm_ok exh_if_total_normal_2 exhale_pred_def)
  then obtain ns' where "R \<omega>' ns'" and "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>3, Normal ns\<^sub>3) (\<gamma>', Normal ns')"
    using rel_success_elim[OF UpdExhRel \<open>R' v_args p \<omega> ns\<^sub>3\<close>]
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
    using Red2 Red3 red_ast_bpl_transitive
    by blast

next

  fix \<omega> ns
  assume "R \<omega> ns"
  assume exh: "red_exhale ctxt_vpr \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) c'"
  proof cases
    case (ExhAccPred mp v_args p pdecl pbody)
    then obtain ns\<^sub>2 where "R \<omega> ns\<^sub>2" and Red2: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2)"
      using exprs_wf_rel_normal_elim[OF WfSubexp] \<open>R \<omega> ns\<close>
      by (metis red_pure_exps_append_success)
    from ExhAccPred have "\<not> (0 \<le> p \<and> Abs_preal p \<le> mp (pred_id,v_args))"
      by fastforce
    thus ?thesis
      using rel_failure_elim[OF CorrectPermRel \<open>R \<omega> ns\<^sub>2\<close>]
      unfolding exhale_pred_acc_rel_assms_def exhale_pred_acc_rel_perm_success_def
      by (metis (no_types, lifting) Abs_preal_inverse Red2 less_eq_preal.rep_eq local.ExhAccPred(2-6) mem_Collect_eq pred_ty_correct_premise_def red_ast_bpl_transitive)
  next
    case ExhSubExpFailure
    thus ?thesis
      apply (simp del: split_paired_Ex)
      using WfSubexp \<open>R \<omega> ns\<close> exprs_wf_rel_failure_elim
      by blast
  qed
qed


lemma val_unique_bpl_vpr_single:
  assumes "val_rel_vpr_bpl v_vpr = v_bpl"
    shows "(THE v. val_rel_vpr_bpl v = v_bpl) = v_vpr"
  apply standard
   apply (simp add: assms)
  by (case_tac v; case_tac v_vpr; insert assms; fastforce)

lemma val_unique_bpl_vpr:
  assumes "map val_rel_vpr_bpl vs_vpr = vs_bpl"
    shows "(THE vs. map val_rel_vpr_bpl vs = vs_bpl) = vs_vpr"
  apply standard
   apply (simp add: assms)
  by (smt (verit) assms list.inj_map_strong val_unique_bpl_vpr_single)

(*
lemma val_inject_bpl_vpr_single:
  assumes "(THE v. val_rel_vpr_bpl v = v_bpl1) =
           (THE v. val_rel_vpr_bpl v = v_bpl2)"
      and "val_rel_vpr_bpl v_vpr1 = v_bpl1"
      and "val_rel_vpr_bpl v_vpr2 = v_bpl2"
    shows "v_bpl1 = v_bpl2"
  by (metis assms val_unique_bpl_vpr_single)
*)

lemma val_inject_bpl_vpr:
  assumes "(THE vs. map val_rel_vpr_bpl vs = vs_bpl1) =
           (THE vs. map val_rel_vpr_bpl vs = vs_bpl2)"
      and "map val_rel_vpr_bpl vs_vpr1 = vs_bpl1"
      and "map val_rel_vpr_bpl vs_vpr2 = vs_bpl2"
    shows "vs_bpl1 = vs_bpl2"
  by (metis assms val_unique_bpl_vpr)


lemma val_inject_bpl_vpr':
  assumes "(THE vs. map val_rel_vpr_bpl vs = vs_bpl1) =
           (THE vs. map val_rel_vpr_bpl vs = vs_bpl2)"
      and "list_all (\<lambda>v_bpl. (\<exists>r. v_bpl = AbsV (ARef r)) \<or> (\<exists>i. v_bpl = IntV i) \<or> (\<exists>b. v_bpl = BoolV b) \<or> (\<exists>p. v_bpl = RealV p)) vs_bpl1"
      and "list_all (\<lambda>v_bpl. (\<exists>r. v_bpl = AbsV (ARef r)) \<or> (\<exists>i. v_bpl = IntV i) \<or> (\<exists>b. v_bpl = BoolV b) \<or> (\<exists>p. v_bpl = RealV p)) vs_bpl2"
    shows "vs_bpl1 = vs_bpl2"
proof -
  obtain vs_vpr1 vs_vpr2 where "map val_rel_vpr_bpl vs_vpr1 = vs_bpl1" and "map val_rel_vpr_bpl vs_vpr2 = vs_bpl2"
    using assms(2,3)
    by (smt (verit) Ball_set_list_all ex_map_conv val_rel_vpr_bpl.simps)
  thus ?thesis
    using assms(1)
    by (simp add: val_unique_bpl_vpr)
qed


lemma vpr_well_ty_bpl_well_ty:
  assumes "get_type (domain_type TyRep) v_vpr = ty_vpr"
      and "val_rel_vpr_bpl v_vpr = v_bpl"
      and "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl"
    shows "type_of_vbpl_val TyRep v_bpl = ty_bpl"
  using assms vpr_to_bpl_val_type
  by blast


lemma exp_result_predicate_loc:
  assumes
    CtxtFunWf: "ctxt_wf Pr TyRep F FunMap FunDom ctxt_bpl" and
    StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>_def \<omega> ns" and
    RedArgsVpr: "red_pure_exps_total ctxt_vpr (Some \<omega>_def1) e_args_vpr \<omega> (Some v_args_vpr)" and
    ArgsWellTy: "pred_ty_correct_premise ctxt_vpr pid v_args_vpr" and
    FunName: "FunMap (FPredicateLoc pid tys_bpl) = pred_loc_fun_name \<and> FPredicateLoc pid tys_bpl \<in> FunDom" and
    PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl" and
    VprArgsTy: "predicate_decl.args pdecl = tys_vpr" and
    ArgsTyRel: "map (vpr_to_bpl_ty TyRep) tys_vpr = map Some tys_bpl" and
    ArgsRel: "list_all2 (exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl) ctxt_vpr ctxt_bpl) e_args_vpr e_args_bpl" and
    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep"
  shows "red_expr_bpl ctxt_bpl (FunExp pred_loc_fun_name [] e_args_bpl) ns (AbsV (AField (PredSnapshotField (pid,v_args_vpr))))"
proof -
  have "list_all2 (\<lambda>e v. ctxt_vpr, Some \<omega>_def1 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) e_args_vpr v_args_vpr"
    by (simp add: RedArgsVpr red_pure_exps_total_list_all2)

  then obtain v_args_bpl where v_args_bpl:
    "list_all2 (\<lambda>e v. red_expr_bpl ctxt_bpl e ns v) e_args_bpl v_args_bpl \<and> map val_rel_vpr_bpl v_args_vpr = v_args_bpl"
    using ArgsRel exp_rel_vpr_bpl_def exp_rel_vb_single_def StateRel evals_with_None
    by (smt (verit, best) eval_with_None length_map list_all2_conv_all_nth nth_map)

  have rel_unique: "(THE v_args. map val_rel_vpr_bpl v_args = v_args_bpl) = v_args_vpr"
    using v_args_bpl val_unique_bpl_vpr
    by blast

  have well_ty_vpr: "vals_well_typed (absval_interp_total ctxt_vpr) v_args_vpr tys_vpr"
    using ArgsWellTy PredDecl pred_ty_correct_premise_def VprArgsTy
    by force

  have v_args_ty_bpl: "map (type_of_vbpl_val TyRep) v_args_bpl = tys_bpl"
    apply (rule list_eq_iff_nth_eq[THEN iffD2])
    apply (intro conjI)
     apply (metis ArgsTyRel length_map v_args_bpl vals_well_typed_same_lengthD well_ty_vpr)
    using vpr_well_ty_bpl_well_ty[of TyRep] well_ty_vpr[unfolded vals_well_typed_def AbsInterpEq] v_args_bpl[THEN conjunct2] ArgsTyRel
    by (metis length_map nth_map)

  show ?thesis
    apply (rule RedFunOp[where v_args=v_args_bpl])
      apply (subst FunName[THEN conjunct1, symmetric])
    using CtxtFunWf FunName
    unfolding ctxt_wf_def fun_interp_vpr_bpl_wf_def
      apply blast
     apply (simp add: v_args_bpl bg_expr_list_red_all2)
    apply (simp add: lift_fun_bpl_def)
    by (simp add: map_instantiate_nil rel_unique v_args_ty_bpl)
qed


lemma exp_rel_predicate_loc:
  assumes
    CtxtFunWf: "ctxt_wf Pr TyRep F FunMap FunDom ctxt_bpl" and
    StateRel: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns" and
    FunName: "FunMap (FPredicateLoc pid tys_bpl) = pred_loc_fun_name \<and> FPredicateLoc pid tys_bpl \<in> FunDom" and
    PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl" and
    VprArgsTy: "predicate_decl.args pdecl = tys_vpr" and
    ArgsTyRel: "map (vpr_to_bpl_ty TyRep) tys_vpr = map Some tys_bpl" and
    ArgsRel: "list_all2 (exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl) ctxt_vpr ctxt_bpl) e_args_vpr e_args_bpl" and
    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep" and
    "e_ploc_bpl = FunExp pred_loc_fun_name [] e_args_bpl"
  shows "ploc_rel_vpr_bpl R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl"
  unfolding ploc_rel_vpr_bpl_def \<open>e_ploc_bpl = _\<close>
  apply (rule allI | rule impI)+
  by (insert assms, erule exp_result_predicate_loc, assumption+)


lemma exp_rel_predicate_loc':
  assumes
    CtxtFunWf: "ctxt_wf Pr TyRep F FunMap FunDom ctxt_bpl" and
    StateRel: "\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>def \<omega> ns" and
    FunName: "FunMap (FPredicateLoc pid tys_bpl) = pred_loc_fun_name \<and> FPredicateLoc pid tys_bpl \<in> FunDom" and
    PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl" and
    VprArgsTy: "predicate_decl.args pdecl = tys_vpr" and
    ArgsTyRel: "map (vpr_to_bpl_ty TyRep) tys_vpr = map Some tys_bpl" and
    ArgsRel: "list_all2 (exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl) ctxt_vpr ctxt_bpl) e_args_vpr e_args_bpl" and
    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep" and
    "e_ploc_bpl = FunExp pred_loc_fun_name [] e_args_bpl"
  shows "ploc_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl"
  unfolding ploc_rel_vpr_bpl'_def \<open>e_ploc_bpl = _\<close>
  apply (rule allI | rule impI)+
  by (insert assms, erule exp_result_predicate_loc, assumption+)


lemma exp_rel_perm_pred_access_2:
  assumes
    MaskReadWf: "mask_read_wf TyRep ctxt_bpl mask_read_bpl" and
    StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>def \<omega> ns" and
    "mvar = mask_var Tr" and
    "nullConst = const_repr Tr CNull" and
    "e_bpl = mask_read_bpl (expr.Var mvar) (expr.Var nullConst) e_ploc_bpl [pred_ty, TConSingle (TFrameFragmentId TyRep)]" and
    PredType: "pred_snap_field_type TyRep pid = Some pred_ty" and
    PlocRel: "red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredSnapshotField (pid,v_args_vpr))))"
  shows "red_expr_bpl ctxt_bpl e_bpl ns (RealV (Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr))))"
proof -
  from state_rel_mask_var_rel[OF StateRel] obtain mb
    where LookupMaskVar: "lookup_var (var_context ctxt_bpl) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
          MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) (get_mp_total_full \<omega>) mb"
    unfolding mask_var_rel_def
    by auto

  from state_rel_boogie_const_rel[OF StateRel, unfolded boogie_const_rel_def, THEN spec, of CNull, simplified]
  have LookupNullVar: "lookup_var (var_context ctxt_bpl) ns nullConst = Some (AbsV (ARef Null))"
    unfolding \<open>nullConst = _\<close>
    by auto

  show ?thesis
    unfolding \<open>e_bpl = _\<close> \<open>mvar = _\<close>
    apply (rule mask_read_wf_apply[OF MaskReadWf])
        defer
        apply (rule RedVar)
        apply (rule LookupMaskVar)
       apply (rule RedVar)
       apply (rule LookupNullVar)
      apply (rule PlocRel)
     apply (simp add: PredType)
    by (metis MaskRel mask_rel_def)
qed


lemma exhale_rel_pred_acc_upd_rel:
  assumes
    StateRelIn: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow>
                             state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV p)))
                             ctxt_bpl \<omega> \<omega> ns" and
    TempPermNotInAux: "temp_perm \<notin> dom AuxPred" and
    StateRelOut: "\<And>\<omega> ns. state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> \<omega> ns \<Longrightarrow> R' \<omega> ns" and

    WfCons: "wf_total_consistency ctxt_vpr StateCons StateCons_t" and
    CtxtPredWf: "ctxt_pred_syn_wf ctxt_vpr" and

    WfTyRep: "wf_ty_repr_bpl TyRep" and
    MaskVarDefSame: "mask_var_def Tr = mask_var Tr" and
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

    PlocBpl: "e_ploc_bpl = FunExp pid [] e_args_bpl" and  (* seems unused *)
    PlocRel: "ploc_rel_vpr_bpl R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and

    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep" and
    ProgEq: "program_total ctxt_vpr = Pr" and

    KFRelOff: "\<not> (kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr)))"
 and

    ConsOn: "consistent_state_rel_opt (state_rel_opt Tr)"
  shows "rel_general R R'
           (\<lambda>\<omega> \<omega>'. exhale_pred_acc_normal_premise ctxt_vpr pid e_args_vpr e_p_vpr v_args_vpr p \<omega> \<omega> \<omega>')
           (\<lambda>_. False) P ctxt_bpl
           (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
           (BigBlock name cs str tr, cont)"

  apply (rule rel_intro)
   prefer 2
   apply blast
proof -
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and *: "exhale_pred_acc_normal_premise ctxt_vpr pid e_args_vpr e_p_vpr v_args_vpr p \<omega> \<omega> \<omega>'"

  hence InitRel: "state_rel_def_same Pr StateCons TyRep Tr
                                     (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega> ns"
    using StateRelIn
    by blast

  hence InitRel': "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns"
    apply (rule state_rel_aux_pred_remove[where ?AuxPred="AuxPred(temp_perm \<mapsto> pred_eq (RealV p))" and ?AuxPred'=AuxPred])
    by (simp add: TempPermNotInAux map_le_def)

  let ?ploc = "(pid,v_args_vpr)"

  have perm_suff: "p \<ge> 0 \<and> p \<le> Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr))"
    using * exhale_pred_acc_normal_premise_def exhale_pred_acc_rel_perm_success_def
    by blast+

  have "\<omega>' = rm_from_lpm_total_full \<omega> (pid,v_args_vpr) (Abs_preal p)"
    using * exhale_pred_acc_normal_premise_def
    by blast

  hence mh_same: "get_mh_total_full \<omega> = get_mh_total_full \<omega>'" and
        mp_rel: "get_mp_total_full \<omega>' = (get_mp_total_full \<omega>)( ?ploc := get_mp_total_full \<omega> ?ploc - Abs_preal p )"
     apply simp
    apply (subst \<open>\<omega>' = _\<close>)
    apply (rule ext)
    apply (rename_tac lp)
    apply (case_tac "lp = (pid,v_args_vpr)"; simp)
    apply (insert perm_suff)
    apply (case_tac "get_fnm_total_full \<omega> (pid,v_args_vpr)"; simp)
    using minus_preal.abs_eq zero_preal.rep_eq zero_preal_def apply force
    by (metis Abs_preal_inverse add.commute all_pos comm_monoid_add_class.add_0 greater_minus_plus less_eq_preal.rep_eq mem_Collect_eq minus_preal_gte order_antisym posreal_to_preal(8) pperm_pnone_pgt)

  have \<omega>'_extcons: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow>
    StateCons \<omega>' \<and>
    consistent_external (total_context.make Pr (\<lambda>_. None) (domain_type TyRep)) (get_total_full \<omega>')"
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
    using state_rel_obtain_mask[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    by blast

  \<comment> \<open>Construct the value of the new permission from the Viper state.\<close>
  let ?np = "Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr)) - p"

  have LookupTempPerm: "lookup_var (var_context ctxt_bpl) ns temp_perm = Some (RealV p)"
    using state_rel_aux_pred_sat_lookup_2[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    unfolding pred_eq_def
    by (metis (full_types) fun_upd_same)

  have null_eval: "red_expr_bpl ctxt_bpl (Var nullConst) ns (AbsV (ARef Null))"
    apply (rule red_expr_red_exprs.RedVar)
    by (metis NullConst StateRelIn \<open>R \<omega> ns\<close> boogie_const_rel_lookup boogie_const_val.simps(3) state_rel_boogie_const_rel)

  have new_perm_eval: "red_expr_bpl ctxt_bpl new_perm ns (LitV (LReal ?np))"
    apply (simp add: NewPermBpl)
    apply (rule red_expr_red_exprs.RedBinOp[where ?v1.0="LitV (LReal (Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr))))" and ?v2.0="LitV (LReal p)"])
      apply (rule mask_read_wf_apply[OF MaskReadWf, where ?m=mb and ?r=Null and ?f="PredSnapshotField (pid,v_args_vpr)"])
          apply (metis MaskRel mask_rel_def)
         apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
        apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl_def]
       apply (meson * \<open>R \<omega> ns\<close> exhale_pred_acc_normal_premise_def exhale_pred_acc_rel_assms_def)
      apply (simp add: PredType)
     apply (fastforce intro: RedVar LookupTempPerm)
    by simp

  \<comment> \<open>Construct the new Boogie heap.\<close>
  let ?mb' = "mb( (Null, PredSnapshotField (pid,v_args_vpr)) := ?np )"

  have m_upd_bpl_red: "red_expr_bpl ctxt_bpl m_upd_bpl ns (AbsV (AMask ?mb'))"
    apply (subst \<open>m_upd_bpl = _\<close>)
    apply (rule mask_update_wf_apply[OF MaskUpdateWf])
        apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
       apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl_def]
      apply (meson * \<open>R \<omega> ns\<close> exhale_pred_acc_normal_premise_def exhale_pred_acc_rel_assms_def)
    using new_perm_eval
     apply blast
    by (simp add: PredType)

  have "valid_heap_mask (get_mh_total_full \<omega>)"
    using InitRel state_rel_wf_mask_simple by blast

  have Disj: "disjoint_list [ {heap_var Tr, heap_var_def Tr},
                              {mask_var Tr, mask_var_def Tr},
                              ran (var_translation Tr),
                              ran (field_translation Tr),
                              range (const_repr Tr), dom AuxPred]"
    using InitRel state_rel_disjoint
    by (smt (verit) dom_fun_upd fun_upd_triv map_le_imp_upd_le option.simps(3) state_rel_aux_pred_remove upd_None_map_le)

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl
                ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns)
                ((BigBlock name cs str tr, cont), Normal ns') \<and> R' \<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (TMaskId TyRep)" and ?v="AbsV (AMask ?mb')"])
    using MaskVar StateRelIn \<open>R \<omega> ns\<close> state_rel_obtain_mask
       apply blast
      apply (simp add: TyInterp)
    using m_upd_bpl_red
     apply blast
    apply (rule StateRelOut)
    apply (simp only: state_rel_def)
    apply (simp only: state_rel0_def, intro conjI)
    using state_rel_wf_mask_simple[OF InitRel] \<open>\<omega>' = _\<close>
                     apply (simp, simp)
    using \<omega>'_extcons \<open>\<omega>' = _\<close>
                   apply blast
                  apply (simp add: TyInterp)
                 apply (rule store_rel_stable[where ?\<omega>=\<omega> and ?ns=ns])
    using InitRel state_rel_store_rel
                   apply blast
                  apply (simp add: \<open>\<omega>' = _\<close>)
    using InitRel MaskVar state_rel_disj_mask_store
                 apply fastforce
                apply (simp add: Disj)
               apply (simp, simp, simp)
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
                  (AbsV (AMask (mb((Null, PredSnapshotField (pid,v_args_vpr)) :=
                                   Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr)) - p))))"

    \<comment> \<open>Prove \<^const>\<open>heap_var_rel\<close>\<close>
    show HeapRel: "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel0_heap_var_rel[OF InitRel[simplified state_rel_def]]])
       apply (simp add: \<open>\<omega>' = _\<close>)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    \<comment> \<open>Prove \<^const>\<open>mask_var_rel\<close>\<close>
    show MaskRel: "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var Tr) \<omega>' ?ns'"
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

    show "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var_def Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF InitRel]])
       apply (simp add: \<open>\<omega>' = _\<close>)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    show MaskRel: "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var_def Tr) \<omega>' ?ns'"
      apply (subst MaskVarDefSame)
      using MaskRel
      by blast

    show "state_well_typed (type_interp ctxt_bpl) (var_context ctxt_bpl) [] ?ns'"
      apply (rule state_well_typed_upd_2)
      using InitRel state_rel_state_well_typed
       apply blast
      by (simp add: TyInterp LookupMaskTy MaskVar)
  qed
qed


definition ploc_sm_rel_vpr_bpl' where
  "ploc_sm_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl \<equiv>
     \<forall>\<omega> ns v_args_vpr. R \<omega> ns \<longrightarrow>
         red_pure_exps_total ctxt_vpr None e_args_vpr \<omega> (Some v_args_vpr) \<longrightarrow>
         pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<longrightarrow>
         red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredKnownFoldedField (pid,v_args_vpr))))"


lemma exp_result_predicate_loc_sm':
  assumes
    CtxtFunWf: "ctxt_wf Pr TyRep F FunMap FunDom ctxt_bpl" and
    StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>_def \<omega> ns" and
    RedArgsVpr: "red_pure_exps_total ctxt_vpr None e_args_vpr \<omega> (Some v_args_vpr)" and
    ArgsWellTy: "pred_ty_correct_premise ctxt_vpr pid v_args_vpr" and
    FunName: "FunMap (FPredicateSMLoc pid tys_bpl) = pred_loc_fun_name \<and> FPredicateSMLoc pid tys_bpl \<in> FunDom" and
    PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl" and
    VprArgsTy: "predicate_decl.args pdecl = tys_vpr" and
    ArgsTyRel: "map (vpr_to_bpl_ty TyRep) tys_vpr = map Some tys_bpl" and
    ArgsRel: "list_all2 (exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl) ctxt_vpr ctxt_bpl) e_args_vpr e_args_bpl" and
    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep"
  shows "red_expr_bpl ctxt_bpl (FunExp pred_loc_fun_name [] e_args_bpl) ns (AbsV (AField (PredKnownFoldedField (pid,v_args_vpr))))"
proof -
  have "list_all2 (\<lambda>e v. ctxt_vpr, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) e_args_vpr v_args_vpr"
    by (simp add: RedArgsVpr red_pure_exps_total_list_all2)

  then obtain v_args_bpl where v_args_bpl:
    "list_all2 (\<lambda>e v. red_expr_bpl ctxt_bpl e ns v) e_args_bpl v_args_bpl \<and> map val_rel_vpr_bpl v_args_vpr = v_args_bpl"
    using ArgsRel exp_rel_vpr_bpl_def exp_rel_vb_single_def StateRel
    by (smt (verit, best) length_map list_all2_conv_all_nth nth_map)

  have rel_unique: "(THE v_args. map val_rel_vpr_bpl v_args = v_args_bpl) = v_args_vpr"
    using v_args_bpl val_unique_bpl_vpr
    by blast

  have well_ty_vpr: "vals_well_typed (absval_interp_total ctxt_vpr) v_args_vpr tys_vpr"
    using ArgsWellTy PredDecl pred_ty_correct_premise_def VprArgsTy
    by force

  have v_args_ty_bpl: "map (type_of_vbpl_val TyRep) v_args_bpl = tys_bpl"
    apply (rule list_eq_iff_nth_eq[THEN iffD2])
    apply (intro conjI)
     apply (metis ArgsTyRel length_map v_args_bpl vals_well_typed_same_lengthD well_ty_vpr)
    using vpr_well_ty_bpl_well_ty[of TyRep] well_ty_vpr[unfolded vals_well_typed_def AbsInterpEq] v_args_bpl[THEN conjunct2] ArgsTyRel
    by (metis length_map nth_map)

  show ?thesis
    apply (rule RedFunOp[where v_args=v_args_bpl])
      apply (subst FunName[THEN conjunct1, symmetric])
    using CtxtFunWf FunName
    unfolding ctxt_wf_def fun_interp_vpr_bpl_wf_def
      apply blast
     apply (simp add: v_args_bpl bg_expr_list_red_all2)
    apply (simp add: lift_fun_bpl_def)
    by (simp add: map_instantiate_nil rel_unique v_args_ty_bpl)
qed


lemma exp_rel_predicate_loc_sm':
  assumes
    CtxtFunWf: "ctxt_wf Pr TyRep F FunMap FunDom ctxt_bpl" and
    StateRel: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> \<omega> ns" and
    FunName: "FunMap (FPredicateSMLoc pid tys_bpl) = pred_loc_fun_name \<and> FPredicateSMLoc pid tys_bpl \<in> FunDom" and
    PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl" and
    VprArgsTy: "predicate_decl.args pdecl = tys_vpr" and
    ArgsTyRel: "map (vpr_to_bpl_ty TyRep) tys_vpr = map Some tys_bpl" and
    PlocBpl: "e_ploc_bpl = FunExp pred_loc_fun_name [] e_args_bpl" and
    ArgsRel: "list_all2 (exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl) ctxt_vpr ctxt_bpl) e_args_vpr e_args_bpl" and
    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep"
  shows "ploc_sm_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl"
  unfolding ploc_sm_rel_vpr_bpl'_def \<open>e_ploc_bpl = _\<close>
  apply (rule allI | rule impI)+
  by (insert assms, erule exp_result_predicate_loc_sm', assumption+)


lemma turn_on_knownfolded_rel:
  assumes "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns"
      and "heap_knownfolded_var_rel (\<lparr> kf_turned_on = True, kf_pos_turned_on = False \<rparr>) Pr (var_context ctxt_bpl) (field_translation Tr) (heap_var Tr) \<omega> ns"
    shows "state_rel_def_same Pr StateCons TyRep (enable_knownfolded_rel_opt Tr) AuxPred ctxt_bpl \<omega> ns"
  using assms
  unfolding state_rel_def state_rel0_def
  by force


lemma kfm_update_state_rel:
  assumes "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns"
      and "lookup_var (var_context ctxt_bpl) ns (heap_var Tr) = Some (AbsV (AHeap hb))"
      and "kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr)) \<Longrightarrow> heap_knownfolded_rel Pr (field_translation Tr) (get_nm_total_full \<omega>) (hb((Null, PredKnownFoldedField lp) \<mapsto> AbsV (AKnownFoldedMask kfm)))"
      and "type_interp ctxt_bpl (AHeap hb) = type_interp ctxt_bpl (AHeap (hb((Null, PredKnownFoldedField lp) \<mapsto> AbsV (AKnownFoldedMask kfm))))" (is "_ = type_interp _ (AHeap ?hb')")
      and "heap_var_def Tr = heap_var Tr"
      and KfmNormalFields: "\<And>r f. kfm (r, f) \<Longrightarrow> is_NormalField f"
      and KfPos: "\<not> kf_pos_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
    shows "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>
             (update_var (var_context ctxt_bpl) ns (heap_var Tr)
               (AbsV (AHeap (hb((Null, PredKnownFoldedField lp) \<mapsto> AbsV (AKnownFoldedMask kfm))))))" (is "state_rel_def_same _ _ _ _ _ _ _ ?ns'")
  unfolding state_rel_def state_rel0_def
  apply (intro conjI; (fastforce simp: assms(1)[unfolded state_rel_def state_rel0_def])?)
  using assms(1)[unfolded state_rel_def state_rel0_def]
             apply (simp, simp)
           apply (rule store_rel_stable)
  using assms(1)[unfolded state_rel_def state_rel0_def]
             apply blast
            apply simp
           apply (metis assms(1) heap_var_disjoint state_rel_state_rel0 update_var_other)
          defer
          apply (rule mask_var_rel_stable)
  using assms(1)[unfolded state_rel_def state_rel0_def]
             apply blast
            apply (simp, simp)
          apply (metis assms(1) heap_var_disjoint state_rel_state_rel0 update_var_other)
         defer
         apply (rule mask_var_rel_stable)
  using assms(1)[unfolded state_rel_def state_rel0_def]
            apply blast
           apply (simp, simp)
         apply (metis assms(1) heap_var_disjoint state_rel_state_rel0 update_var_other)
  subgoal
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ "hb((Null, PredKnownFoldedField lp) \<mapsto> AbsV (AKnownFoldedMask kfm))"])
    apply (intro conjI)
       apply force
    using state_rel_heap_knownfolded_var_rel[OF assms(1)]
      apply (simp add: heap_knownfolded_var_rel_def assms(2))
     apply (rule knownfolded_masks_normal_fields_upd
                   [OF heap_knownfolded_var_rel_masks_normal_fields
                         [OF state_rel_heap_knownfolded_var_rel[OF assms(1)] assms(2)] KfmNormalFields])
    using assms(3) KfPos
    by auto
       apply (rule field_rel_stable)
  using assms(1)[unfolded state_rel_def state_rel0_def]
        apply blast
       apply (metis assms(1) heap_var_disjoint state_rel_state_rel0 update_var_other)
      apply (rule boogie_const_rel_stable)
  using assms(1)[unfolded state_rel_def state_rel0_def]
       apply blast
      apply (metis assms(1) heap_var_disjoint state_rel_state_rel0 update_var_other)
  using state_rel_state_well_typed[OF assms(1)] assms(4)
     apply (metis assms(2) option.sel state_well_typed_lookup state_well_typed_upd_2 type_of_val.simps(2))
    apply (rule aux_vars_pred_sat_stable)
  using assms(1)[unfolded state_rel_def state_rel0_def]
     apply blast
    apply (metis assms(1) heap_var_disjoint state_rel_state_rel0 update_var_other)
proof -
  have hb: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
    using assms(1)[unfolded state_rel_def state_rel0_def] heap_var_rel_def
    by (metis Semantics.val.inject(2) assms(2) option.sel vbpl_absval.inject(4))
  show "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var Tr) \<omega> ?ns'"
    unfolding heap_var_rel_def
    apply (intro conjI)
     apply (rule exI[of _ ?hb'])
     apply (intro conjI)
        apply simp
    using assms(1) state_rel_obtain_heap
       apply blast
      apply simp
      apply (metis (mono_tags, lifting) Semantics.val.inject(2) assms(1)[unfolded state_rel_def state_rel0_def] assms(2) heap_bpl_well_typed_elim heap_var_rel_def option.sel)
    using hb
    unfolding heap_rel_def
     apply simp
    using assms(1)[unfolded state_rel_def state_rel0_def] heap_var_rel_def
    by blast

  thus "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var_def Tr) \<omega> ?ns'"
    using assms(5)
    by simp
qed


lemma unfold_set_kfm_to_zero:
  assumes "heap_knownfolded_rel Pr FieldTr (get_nm_total \<phi>\<^sub>0) hb"
      and "unfold_rel ctxt_vpr pid v_args v_p \<phi>\<^sub>0 \<phi>"
    shows "heap_knownfolded_rel Pr FieldTr (get_nm_total \<phi>)
             (hb((Null, PredKnownFoldedField (pid, v_args)) \<mapsto> AbsV (AKnownFoldedMask (\<lambda>_. False))))"
          (is "heap_knownfolded_rel _ _ _ ?hb'")
  unfolding heap_knownfolded_rel_def
proof (intro allI | intro impI)+
  fix lp kfm l field_ty_vpr field_bpl
  assume kfm: "?hb' (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))"
     and fld1: "declared_fields Pr (snd l) = Some field_ty_vpr"
     and fld2: "FieldTr (snd l) = Some field_bpl"
     and kfm_true: "kfm (Address (fst l), NormalField field_bpl field_ty_vpr)"

  with assms(1)
  have folds\<^sub>0: "pred_folds_perm lp l (get_nm_total \<phi>\<^sub>0)"
    unfolding heap_knownfolded_rel_def
    by (metis Semantics.val.inject(2) fun_upd_other fun_upd_same option.inject vbpl_absval.inject(6))

  from assms(2)
  obtain nm nm\<^sub>s where
    sh: "shift_up pid v_args v_p nm nm\<^sub>s" and
    "get_nm_total \<phi>\<^sub>0 = nm" and
    "get_nm_total \<phi> = nm\<^sub>s"
    by (auto elim: unfold_rel.cases)

  show "pred_folds_perm lp l (get_nm_total \<phi>)"
  proof (cases rule: shift_up.cases[OF sh])
    case (1 mh nm\<^sub>c fnm p\<^sub>p' pnm' pid\<^sub>c v_args\<^sub>c p' v_p\<^sub>c fnm_sub nm_sub nm\<^sub>s\<^sub>c)
    then show ?thesis
    proof (cases rule: pred_folds_perm.cases[OF folds\<^sub>0])
      case (1 nm\<^sub>c\<^sub>c p'\<^sub>f nm'\<^sub>f) \<comment> \<open>ContainsPermDirect\<close>
      show ?thesis
      proof (cases "lp = (pid, v_args)")
        case True
        then show ?thesis
          using kfm kfm_true
          by force
      next
        case False
        hence "fnm_sub lp = Some (p'\<^sub>f, nm'\<^sub>f)"
          using \<open>fnm_sub = _\<close> \<open>get_fnm_nm nm\<^sub>c\<^sub>c lp = Some (p'\<^sub>f, nm'\<^sub>f)\<close> \<open>get_nm_total \<phi>\<^sub>0 = nm\<^sub>c\<^sub>c\<close> \<open>fnm = get_fnm_nm nm\<^sub>c\<close> \<open>nm = nm\<^sub>c\<close> \<open>get_nm_total \<phi>\<^sub>0 = nm\<close> \<open>v_args = v_args\<^sub>c\<close> \<open>pid = pid\<^sub>c\<close>
          by fastforce
        show ?thesis
          apply (rule pred_folds_perm_stable_larger_nm[where ?nm="NM mh fnm_sub"])
           apply (rule ContainsPermDirect)
            apply simp
            apply fact
           apply (simp add: 1(3))
          unfolding \<open>get_nm_total \<phi> = nm\<^sub>s\<close> \<open>nm\<^sub>s = nm\<^sub>s\<^sub>c\<close> \<open>nm\<^sub>s\<^sub>c = _\<close> \<open>nm_sub = _\<close>
          by (simp add: nm_sum_is_bigger)
      qed
    next
      case (2 nm\<^sub>c\<^sub>c lp\<^sub>f p'\<^sub>f nm'\<^sub>f) \<comment> \<open>ContainsPermNested\<close>
      show ?thesis
      proof (cases "lp\<^sub>f = (pid, v_args)")
        case True
        hence "pnm' = nm'\<^sub>f"
          using 1(1,2,4,7,8) 2(1,2) \<open>get_nm_total \<phi>\<^sub>0 = nm\<close>
          by auto
        hence "pred_folds_perm lp l pnm'"
          using 2(3)
          by blast
        show ?thesis
          unfolding \<open>get_nm_total \<phi> = nm\<^sub>s\<close> \<open>nm\<^sub>s = _\<close> \<open>nm\<^sub>s\<^sub>c = _\<close>
          apply (rule pred_folds_perm_plus_l)
          apply (rule pred_folds_perm_scale)
           apply fact
          using 1(10,11) preal_to_real(1,10,2,7)
          by auto
      next
        case False
        show ?thesis
          unfolding \<open>get_nm_total \<phi> = nm\<^sub>s\<close> \<open>nm\<^sub>s = _\<close> \<open>nm\<^sub>s\<^sub>c = _\<close> \<open>nm_sub = _\<close> \<open>fnm_sub = _\<close>
          apply (rule pred_folds_perm_plus_r)
          apply (rule ContainsPermNested[of _ lp\<^sub>f p'\<^sub>f nm'\<^sub>f])
          using 1(1,2,4,7) 2(1,2) False \<open>get_nm_total \<phi>\<^sub>0 = nm\<close>
           apply force
          by fact
      qed
    qed
  next
    case (2 pid v_args nm\<^sub>s\<^sub>c)
    then show ?thesis
      using \<open>get_nm_total \<phi> = nm\<^sub>s\<close> \<open>get_nm_total \<phi>\<^sub>0 = nm\<close> folds\<^sub>0
      by argo
  qed
qed


lemma unfold_knownfolded_upd_rel:
  assumes
    StateRelIn: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow>
                          state_rel_def_same Pr StateCons TyRep Tr' AuxPred ctxt_bpl \<omega> ns" and
    StateRelOut: "\<And>\<omega> ns. state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns \<Longrightarrow> R' \<omega> ns" and

    (* KFMOff: "\<not> kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr'))" and *)
    KFMPosOff: "\<not> kf_pos_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))" and
    KFMOn: "kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))" and
    KFMRel: "Tr' = disable_knownfolded_rel_opt Tr" and
    KFMNewOpt: "kf_turned_on kf_opt" and

    HeapVarDefSame: "heap_var_def Tr = heap_var Tr" and
    FieldTranslation: "FieldTr = field_translation Tr" and

    NullConst: "const_repr Tr CNull = nullConst" and
    ZeroPMaskConst: "const_repr Tr CKnownFoldedZeroMask = zeroPMask" and
    HeapVar: "hvar = heap_var Tr" and

    HeapUpdateWf: "heap_update_wf TyRep ctxt_bpl heap_upd_bpl" and
    KnownFoldedUpdBpl: "h_upd_bpl = heap_upd_bpl (Var hvar) (Var nullConst) e_ploc_bpl (Var zeroPMask)
                                      [pred_ty, TConSingle (TKnownFoldedMaskId TyRep)]" and

    PlocRel: "ploc_sm_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and

    TyInterpEq: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and

    PredType: "pred_snap_field_type TyRep pid = Some pred_ty"
  shows "rel_general (uncurry (\<lambda>\<omega>\<^sub>0 \<omega> ns. R \<omega> ns \<and>
                                         ctxt_vpr, (Some \<omega>\<^sub>0) \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_vpr) \<and>
                                         red_pure_exps_total ctxt_vpr (Some \<omega>\<^sub>0) e_args_vpr \<omega> (Some v_args_vpr) \<and>
                                         pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
                                         unfold_rel ctxt_vpr pid v_args_vpr (Abs_preal v_p_vpr) (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>) \<and>
                                         heap_knownfolded_var_rel kf_opt Pr (var_context ctxt_bpl) FieldTr hvar \<omega>\<^sub>0 ns))
                     (uncurry (\<lambda>\<omega>\<^sub>0 \<omega> ns. R' \<omega> ns))
                     (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                     (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                     P ctxt_bpl
                     (BigBlock name ((Assign hvar h_upd_bpl) # cs) str tr, cont)
                     (BigBlock name cs str tr, cont)" (is "rel_general ?R\<^sub>0 _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule rel_intro; blast?)
  fix \<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>' :: "('a full_total_state \<times> 'a full_total_state)"
  fix ns
  obtain \<omega>\<^sub>0 \<omega> where "\<omega>\<^sub>0_\<omega> = (\<omega>\<^sub>0, \<omega>)"
    by fastforce
  assume "?R\<^sub>0 \<omega>\<^sub>0_\<omega> ns" and "\<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>'"

  hence
    "R \<omega> ns" and
    "ctxt_vpr, (Some \<omega>\<^sub>0) \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_vpr)" and
    "red_pure_exps_total ctxt_vpr (Some \<omega>\<^sub>0) e_args_vpr \<omega> (Some v_args_vpr)" and
    "pred_ty_correct_premise ctxt_vpr pid v_args_vpr" and
    "unfold_rel ctxt_vpr pid v_args_vpr (Abs_preal v_p_vpr) (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>)" and
    "heap_knownfolded_var_rel kf_opt Pr (var_context ctxt_bpl) FieldTr (heap_var Tr) \<omega>\<^sub>0 ns"
    by (simp_all add: \<open>\<omega>\<^sub>0_\<omega> = (\<omega>\<^sub>0, \<omega>)\<close> \<open>hvar = _\<close>)

  with PlocRel[unfolded ploc_sm_rel_vpr_bpl'_def] evals_with_None
  have ploc_bpl_eval: "red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredKnownFoldedField (pid, v_args_vpr))))"
    by blast

  obtain hb where
    lookup_heap: "lookup_var (var_context ctxt_bpl) ns (heap_var Tr') = Some (AbsV (AHeap hb))" and
    lookup_heap_ty: "lookup_var_ty (var_context ctxt_bpl) (heap_var Tr') = Some (TConSingle (THeapId TyRep))" and
    heap_ty: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
    using state_rel_obtain_heap[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    by metis

  hence "heap_knownfolded_rel Pr (field_translation Tr') (get_nm_total (get_total_full \<omega>\<^sub>0)) hb"
    by (metis lookup_heap tr_vpr_bpl.update_convs(9) KFMNewOpt tr_vpr_bpl.ext_inject get_nm_total_full.elims
        \<open>heap_knownfolded_var_rel kf_opt Pr (var_context ctxt_bpl) FieldTr (heap_var Tr) \<omega>\<^sub>0 ns\<close> FieldTranslation
        tr_vpr_bpl.surjective heap_knownfolded_var_rel_def option.sel KFMRel vbpl_absval.inject(4) Semantics.val.sel(2))

  let ?hb' = "hb( (Null, PredKnownFoldedField (pid, v_args_vpr)) \<mapsto> zero_knownfolded_mask )"

  have h_upd_eval: "red_expr_bpl ctxt_bpl h_upd_bpl ns (AbsV (AHeap ?hb'))"
    unfolding \<open>h_upd_bpl = _\<close>
    apply (rule heap_update_wf_apply[OF HeapUpdateWf, where ?h=hb and ?r=Null and ?f="PredKnownFoldedField (pid,v_args_vpr)"])
          apply (rule red_expr_red_exprs.RedVar)
    using KFMRel lookup_heap \<open>hvar = _\<close>
          apply fastforce
         apply fact
        apply (rule red_expr_red_exprs.RedVar)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] NullConst KFMRel
        apply force
       apply (simp add: ploc_bpl_eval)
      apply (simp add: PredType)
     apply (rule red_expr_red_exprs.RedVar)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] ZeroPMaskConst
    unfolding zero_knownfolded_mask_def
    using KFMRel
     apply force
    apply simp
    done

  have "Tr = enable_knownfolded_rel_opt Tr'"
    using KFMRel KFMOn KFMPosOff
    by fastforce

  have "heap_var Tr = heap_var Tr'"
    by (simp add: KFMRel)

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl (?\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> uncurry (\<lambda>\<omega>\<^sub>0_\<omega>. R') \<omega>\<^sub>0_\<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (THeapId TyRep)" and ?v="AbsV (AHeap ?hb')"])
    using lookup_heap_ty \<open>hvar = _\<close> KFMRel
       apply simp
      apply (simp add: TyInterpEq zero_knownfolded_mask_def)
      apply (meson heap_bpl_well_typed_elim heap_ty)
     apply (simp add: h_upd_eval)
    unfolding \<open>\<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>'\<close>[symmetric] \<open>\<omega>\<^sub>0_\<omega> = (_, _)\<close>
    apply simp
    apply (rule StateRelOut)
    apply (subst \<open>Tr = _\<close>)
    apply (rule turn_on_knownfolded_rel)
    unfolding zero_knownfolded_mask_def \<open>hvar = _\<close> \<open>heap_var Tr = _\<close>
     apply (rule kfm_update_state_rel)
           apply (rule StateRelIn[OF \<open>R \<omega> ns\<close>])
          apply fact
    using \<open>heap_knownfolded_rel Pr (field_translation Tr') (get_nm_total (get_total_full \<omega>\<^sub>0)) hb\<close>
      \<open>unfold_rel ctxt_vpr pid v_args_vpr (Abs_preal v_p_vpr) (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>)\<close>
      unfold_set_kfm_to_zero apply fastforce
    unfolding TyInterpEq
        apply simp
        apply (meson heap_bpl_well_typed_elim heap_ty)
       apply (simp add: HeapVarDefSame KFMRel)
      apply simp
     apply (simp add: KFMRel)
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ ?hb'])
    apply (intro conjI)
        apply (simp add: zero_knownfolded_mask_def)
    using \<open>heap_knownfolded_var_rel _ _ _ _ _ _ _\<close>
    unfolding heap_knownfolded_var_rel_def zero_knownfolded_mask_def
       apply (simp add: lookup_heap)
       apply (simp add: \<open>heap_var Tr = heap_var Tr'\<close> lookup_heap)
      apply (metis \<open>heap_knownfolded_var_rel kf_opt Pr (var_context ctxt_bpl) FieldTr (heap_var Tr) \<omega>\<^sub>0 ns\<close>
        \<open>heap_var Tr = heap_var Tr'\<close> heap_knownfolded_var_rel_masks_normal_fields knownfolded_masks_normal_fields_upd lookup_heap)
    using \<open>heap_knownfolded_rel Pr (field_translation Tr') (get_nm_total (get_total_full \<omega>\<^sub>0)) hb\<close>
      \<open>unfold_rel ctxt_vpr pid v_args_vpr (Abs_preal v_p_vpr) (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>)\<close> unfold_set_kfm_to_zero
     apply fastforce
    by fastforce
qed



subsection \<open>Fold\<close>

text \<open>The following definition captures a premise that recurs throughout the known-folded permission
      mask update lemmas for \<^const>\<open>Fold\<close>: the predicate arguments evaluate successfully, are
      well-typed, and there is a substate of the mask for the folded predicate that satisfies the
      predicate body (so that the known-folded mask update is justified).\<close>

definition pred_kfm_sat_premise ::
  "'a total_context \<Rightarrow> predicate_ident \<Rightarrow> 'a full_total_state option \<Rightarrow> pure_exp list \<Rightarrow> 'a ValueAndBasicState.val list \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where
    "pred_kfm_sat_premise ctxt_vpr pid \<omega>def e_args_vpr v_args_vpr A \<omega> \<equiv>
       red_pure_exps_total ctxt_vpr \<omega>def e_args_vpr \<omega> (Some v_args_vpr) \<and>
       pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
       (\<exists>nm_exh p\<^sub>s nm\<^sub>s. get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p\<^sub>s,nm\<^sub>s) \<and> nm_exh \<le> nm\<^sub>s \<and>
            sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) A \<and>
            consistent_external ctxt_vpr (\<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_exh \<rparr>))"

lemma pred_kfm_sat_premiseI:
  assumes "red_pure_exps_total ctxt_vpr \<omega>def e_args_vpr \<omega> (Some v_args_vpr)"
      and "pred_ty_correct_premise ctxt_vpr pid v_args_vpr"
      and "get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p\<^sub>s,nm\<^sub>s)"
      and "nm_exh \<le> nm\<^sub>s"
      and "sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) A"
      and "consistent_external ctxt_vpr (\<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_exh \<rparr>)"
    shows "pred_kfm_sat_premise ctxt_vpr pid \<omega>def e_args_vpr v_args_vpr A \<omega>"
  using assms
  unfolding pred_kfm_sat_premise_def
  by blast

lemma pred_kfm_sat_premiseD:
  assumes "pred_kfm_sat_premise ctxt_vpr pid \<omega>def e_args_vpr v_args_vpr A \<omega>"
  shows "red_pure_exps_total ctxt_vpr \<omega>def e_args_vpr \<omega> (Some v_args_vpr) \<and>
         pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
         (\<exists>nm_exh p\<^sub>s nm\<^sub>s. get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p\<^sub>s,nm\<^sub>s) \<and> nm_exh \<le> nm\<^sub>s \<and>
              sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) A \<and>
              consistent_external ctxt_vpr (\<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_exh \<rparr>))"
  using assms
  unfolding pred_kfm_sat_premise_def
  by blast

lemma framing_subst_exprs_wf_rel:
  assumes ConsistencyDownwardsMono: "mono_prop_downward_ord StateCons"
      and "\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow>
              red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr) \<and>
              framing_exh ctxt_vpr StateCons A (\<omega>def\<lparr> get_store_total := nth_option v_args_vpr \<rparr>) (\<omega>\<lparr> get_store_total := nth_option v_args_vpr \<rparr>)"
      and "es = direct_sub_expressions_assertion (substitute_args_assertion A e_args_vpr)"
      and ArgsConstraint: "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) e_args_vpr"
      and AssertionConstraint: "no_perm_assertion A \<and> no_old_assertion A \<and> no_unfolding_assertion A \<and> no_result_assertion A"
    shows "exprs_wf_rel R ctxt_vpr StateCons P ctxt_bpl es \<gamma> \<gamma>"
proof (cases "es = []")
  case True
  then show ?thesis
    using exprs_wf_rel_Nil
    by blast
next
  case False
  show ?thesis
    unfolding exprs_wf_rel_def
    apply (rule wf_rel_intro)
    using red_ast_bpl_refl
     apply blast
  proof (rule ccontr)
    fix \<omega>def \<omega> ns
    assume "R \<omega>def \<omega> ns"
       and direct_expr_eval_assms: "red_pure_exps_total ctxt_vpr (Some \<omega>def) es \<omega> None"
    hence args_eval: "red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr)"
      and "framing_exh ctxt_vpr StateCons A (\<omega>def\<lparr> get_store_total := nth_option v_args_vpr \<rparr>) (\<omega>\<lparr> get_store_total := nth_option v_args_vpr \<rparr>)"
      using assms(2)
      by simp_all

    let ?\<omega>def_subst = "\<omega>def\<lparr> get_store_total := nth_option v_args_vpr \<rparr>"
    let ?\<omega>_subst = "\<omega>\<lparr> get_store_total := nth_option v_args_vpr \<rparr>"
    from \<open>framing_exh _ _ _ _ _\<close>
    obtain \<omega>inh \<omega>sum where
      "\<omega>inh \<oplus> ?\<omega>_subst = Some \<omega>sum" and
      "?\<omega>def_subst \<succeq> \<omega>sum" and
      "assertion_framing_state ctxt_vpr StateCons A \<omega>inh"
      by (metis framing_exh_def)

    have direct_expr_eval_nofail': "\<And>res. red_pure_exps_total ctxt_vpr (Some \<omega>inh) (direct_sub_expressions_assertion A) \<omega>inh res \<Longrightarrow> res \<noteq> None"
      using \<open>assertion_framing_state _ _ _ _\<close>[unfolded assertion_framing_state_def assertion_self_framing_store_def]
      by (metis InhSubExpFailure option.distinct(1) red_exp_list_failure_Nil)

    have "?\<omega>def_subst \<succeq> \<omega>inh" and "?\<omega>def_subst \<succeq> ?\<omega>_subst"
      using \<open>\<omega>inh \<oplus> ?\<omega>_subst = Some \<omega>sum\<close> \<open>?\<omega>def_subst \<succeq> \<omega>sum\<close>
      by (metis commutative greater_equiv succ_trans)+
    hence "?\<omega>def_subst \<ge> \<omega>inh"
      using full_total_state_succ_implies_gte
      by blast
    hence AssertionFramedSubst: "assertion_framing_state ctxt_vpr StateCons A ?\<omega>def_subst"
      using assertion_framing_state_mono[OF ConsistencyDownwardsMono \<open>assertion_framing_state ctxt_vpr StateCons A \<omega>inh\<close>]
            AssertionConstraint
      by blast
    have OnlyMaskDiffers: "get_store_total ?\<omega>_subst = get_store_total ?\<omega>def_subst \<and>
                            get_trace_total ?\<omega>_subst = get_trace_total ?\<omega>def_subst \<and>
                            get_hh_total_full ?\<omega>_subst = get_hh_total_full ?\<omega>def_subst"
      using full_total_state_greater_only_mask_changed[OF \<open>?\<omega>def_subst \<succeq> ?\<omega>_subst\<close>]
      by simp

    have direct_expr_eval_nofail: "\<And>res. red_pure_exps_total ctxt_vpr (Some ?\<omega>def_subst) (direct_sub_expressions_assertion A) ?\<omega>_subst res \<Longrightarrow> res \<noteq> None"
    proof -
      fix res
      assume RedExps: "red_pure_exps_total ctxt_vpr (Some ?\<omega>def_subst) (direct_sub_expressions_assertion A) ?\<omega>_subst res"
      have NoPermUnfolding: "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) (direct_sub_expressions_assertion A)"
        using assert_pred_subexp[of "\<lambda>_. True" "\<lambda>_. True" no_perm_pure_exp_no_rec A]
              assert_pred_subexp[of "\<lambda>_. True" "\<lambda>_. True" no_unfolding_pure_exp_no_rec A]
              AssertionConstraint
        by (auto simp: list_all_length)
      hence "red_pure_exps_total ctxt_vpr (Some ?\<omega>def_subst) (direct_sub_expressions_assertion A) ?\<omega>def_subst res"
        using red_pure_exp_only_differ_on_mask(2)[OF RedExps] OnlyMaskDiffers
        by blast
      thus "res \<noteq> None"
        using AssertionFramedSubst[unfolded assertion_framing_state_def assertion_self_framing_store_def]
        by (metis InhSubExpFailure option.distinct(1) red_exp_list_failure_Nil)
    qed

    have "es = map (\<lambda>e. substitute_args_expr e e_args_vpr) (direct_sub_expressions_assertion A)"
      by (simp add: assms(3) substitute_subexpr_assertion_commute)

    from eval_with_substitution_rev(2)[OF args_eval _ _ _ _ direct_expr_eval_assms this]
    show False
      by (metis ArgsConstraint AssertionConstraint Ball_set_list_all direct_expr_eval_nofail assert_pred_subexp)
  qed
qed


subsubsection \<open>Variables/literals evaluate independently of the definedness state\<close>

text \<open>Unlike @{thm red_pure_exp_only_differ_on_mask} (which fixes the definedness state and only
      lets the \<^emph>\<open>evaluated\<close> state change), the following lemma additionally lets the definedness
      state's \<^emph>\<open>identity\<close> change -- but only for the restricted case where \<open>e\<close> is a variable or a
      literal, for which the definedness state is never inspected at all (no \<^const>\<open>FieldAcc\<close>,
      \<^const>\<open>Perm\<close>, \<^const>\<open>Old\<close>, or \<^const>\<open>Unfolding\<close> is involved, so there is nothing to check).\<close>

fun is_var_or_lit :: "pure_exp \<Rightarrow> bool" where
  "is_var_or_lit (pure_exp.Var _) = True"
| "is_var_or_lit (ELit _) = True"
| "is_var_or_lit _ = False"

lemma red_pure_exp_var_or_lit_indep:
  assumes "ctxt, \<omega>def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
      and "is_var_or_lit e"
      and "get_store_total \<omega> = get_store_total \<omega>'"
    shows "ctxt, \<omega>def' \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t Val v"
proof (cases e)
  case (Var n)
  hence "ctxt, \<omega>def \<turnstile> \<langle>pure_exp.Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
    using assms(1)
    by simp
  hence "get_store_total \<omega> n = Some v"
    by (metis TotalExpressions.RedVar_case)
  with assms(3) Var show ?thesis
    by (auto intro: TotalExpressions.RedVar)
next
  case (ELit l)
  with assms(1) show ?thesis
    by (auto elim: TotalExpressions.RedLit_case intro: TotalExpressions.RedLit)
qed (use assms(2) in auto)

lemma red_pure_exps_var_or_lit_indep:
  assumes "red_pure_exps_total ctxt \<omega>def es \<omega> (Some vs)"
      and "list_all is_var_or_lit es"
      and "get_store_total \<omega> = get_store_total \<omega>'"
    shows "red_pure_exps_total ctxt \<omega>def' es \<omega>' (Some vs)"
  using assms
proof (induction es arbitrary: vs)
  case Nil
  hence "vs = []"
    by (auto elim: TotalExpressions.RedExpListGeneral_case)
  with TotalExpressions.RedExpListNil show ?case
    by simp
next
  case (Cons e es)
  obtain v0 res where
    veq: "Some vs = map_option ((#) v0) res" and
    e_eval0: "ctxt, \<omega>def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v0" and
    es_eval0: "red_pure_exps_total ctxt \<omega>def es \<omega> res"
    using Cons.prems(1)
    by (elim TotalExpressions.RedExpListCons_case)
  obtain vs' where res_eq: "res = Some vs'"
    using veq
    by (cases res) auto
  hence "vs = v0 # vs'"
    using veq
    by simp
  note e_eval = e_eval0
  note es_eval = es_eval0[unfolded res_eq]
  have e_indep: "ctxt, \<omega>def' \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t Val v0"
    apply (rule red_pure_exp_var_or_lit_indep[OF e_eval])
    using Cons.prems(2)
     apply (simp add: list_all_iff)
    using Cons.prems(3)
    apply simp
    done
  have es_indep: "red_pure_exps_total ctxt \<omega>def' es \<omega>' (Some vs')"
    apply (rule Cons.IH[OF es_eval])
    using Cons.prems(2)
     apply (simp add: list_all_iff)
    using Cons.prems(3)
    apply simp
    done
  show ?case
    unfolding \<open>vs = _\<close>
    apply (rule TotalExpressions.RedExpListCons[OF e_indep es_indep])
    by simp
qed

subsubsection \<open>Restoring the store across \<open>\<oplus>\<close>/\<open>\<succeq>\<close>\<close>

text \<open>\<open>\<oplus>\<close> on \<open>full_total_state\<close> (\<open>plus_full_total_state_ext_def\<close>) only requires the store (and
      trace, and \<open>more\<close>) of its two arguments to agree -- it never inspects what the (shared)
      store actually \<^emph>\<open>is\<close>. So replacing that shared store throughout a \<open>\<oplus>\<close>/\<open>\<succeq>\<close> derivation is
      always sound.\<close>

lemma full_total_state_plus_store_update:
  assumes "\<omega>1 \<oplus> \<omega>2 = Some \<omega>3"
  shows "(\<omega>1\<lparr> get_store_total := s \<rparr>) \<oplus> (\<omega>2\<lparr> get_store_total := s \<rparr>) = Some (\<omega>3\<lparr> get_store_total := s \<rparr>)"
  using assms
  unfolding plus_full_total_state_ext_def
  by (auto split: if_split_asm)

lemma full_total_state_succ_store_update:
  assumes "\<omega>1 \<succeq> \<omega>2"
  shows "(\<omega>1\<lparr> get_store_total := s \<rparr>) \<succeq> (\<omega>2\<lparr> get_store_total := s \<rparr>)"
  using assms full_total_state_plus_store_update[where s = s]
  unfolding greater_def
  by metis


subsubsection \<open>Main Lemmas\<close>

lemma fold_stmt_rel:
  assumes PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl"
      and PredArgs: "predicate_decl.args pdecl = ty_args"
      and PredBody: "predicate_decl.body pdecl = Some pbody"
      and CtxtPredWf: "ctxt_pred_syn_wf ctxt_vpr"
      and CtxtPredSF: "ctxt_pred_self_framing_inh ctxt_vpr StateCons"
      and WfCons: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and StateRelImpliesIntCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"
      and StateRelImpliesExtCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> consistent_external ctxt_vpr (get_total_full \<omega>)"
      and ArgsRestriction: "list_all no_unfolding_pure_exp e_args_vpr \<and> list_all no_perm_pure_exp e_args_vpr \<and> list_all no_old_pure_exp e_args_vpr \<and> list_all no_result_pure_exp e_args_vpr"
      and ArgsAreVarOrLit: "list_all is_var_or_lit e_args_vpr"
        \<comment> \<open>Additional restriction (beyond \<open>ArgsRestriction\<close>) needed to close the \<open>framing_exh\<close>
            substitution step below: see the comment there for why the general case is hard.\<close>
      and BodyNoUnfolding: "no_unfolding_assertion (syntactic_mult p pbody)"  \<comment> \<open>Should be lifted soon.\<close>
      and PermSimp: "e_p_vpr = ELit (LPerm p)" \<comment> \<open>We only support literals as the permission.\<close>
      and PermPos: "p > 0"
      and StepWfSubexp: "exprs_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt_bpl (e_args_vpr @ [e_p_vpr]) \<gamma> \<gamma>\<^sub>2"
      and StepPermPos: "rel_general R R (=) (\<lambda>_. False) P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and StepExhale:
            "\<And>v_args_vpr v_p_vpr.
                exhale_rel (rel_ext_eq R) (\<lambda>\<omega>def \<omega> ns. R'' \<omega>def \<omega> ns)
                  (framing_exh ctxt_vpr StateCons)
                  ctxt_vpr StateCons P ctxt_bpl
                  (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<gamma>\<^sub>3 \<gamma>\<^sub>4"
      and StepInhale:
            "\<And>v_args_vpr v_p_vpr.
                rel_general (\<lambda>\<omega>_def_\<omega> ns. R'' (fst \<omega>_def_\<omega>) (snd \<omega>_def_\<omega>) ns \<and> ctxt_vpr, (Some (fst \<omega>_def_\<omega>)) \<turnstile> \<langle>e_p_vpr; snd \<omega>_def_\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_vpr)) (\<lambda>\<omega>_def_\<omega> ns. R' (snd \<omega>_def_\<omega>) ns)
                  (\<lambda>\<omega>_def_\<omega> \<omega>_def_\<omega>'. fst \<omega>_def_\<omega> = fst \<omega>_def_\<omega>' \<and> inhale_pred_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr v_p_vpr (fst \<omega>_def_\<omega>) (snd \<omega>_def_\<omega>) (snd \<omega>_def_\<omega>'))
                  (\<lambda>_. False) P ctxt_bpl \<gamma>\<^sub>4 \<gamma>\<^sub>5"
      and StepKFUpdate:
            "\<And>v_args_vpr v_p_vpr.
                rel_general (\<lambda>\<omega> ns. R' \<omega> ns \<and>
                                    pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr
                                      (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega>)
                            R' (=) (\<lambda>_. False) P ctxt_bpl \<gamma>\<^sub>5 \<gamma>'"
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

  ultimately obtain ns\<^sub>4 where ns\<^sub>4: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>3, Normal ns\<^sub>3) (\<gamma>\<^sub>4, Normal ns\<^sub>4) \<and> R'' \<omega> \<omega>1 ns\<^sub>4"
    using StepExhale[THEN exhale_rel_normal_elim, OF conjunct2[OF ns\<^sub>3]] v_args_eval
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
  obtain ns\<^sub>5 where ns\<^sub>5: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>4, Normal ns\<^sub>4) (\<gamma>\<^sub>5, Normal ns\<^sub>5) \<and> R' \<omega>' ns\<^sub>5"
    by (metis ns\<^sub>4 fst_conv inhale_pred_normal_premise_def snd_conv)

  \<comment> \<open>Fifth step: known-folded permission mask update\<close>
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
    using conjunct2[OF ns\<^sub>5]
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
      by (metis ns\<^sub>2 ns\<^sub>3 red_ast_bpl_transitive snd_conv)
  qed
qed


lemma inhale_rel_pred_acc_upd_rel':
  assumes
    StateRelIn:
      "\<And>\<omega>def \<omega> ns. R (\<omega>def,\<omega>) ns \<Longrightarrow>
          state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega>def \<omega> ns" and
    StateRelOut:
      "\<And>\<omega>def \<omega> ns. state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega>def \<omega> ns \<Longrightarrow>
          R' (\<omega>def,\<omega>) ns" and
    AuxDomTemp: "temp_perm \<notin> dom AuxPred" and
    AuxDomMask: "m_bpl \<notin> dom AuxPred" and

    WfTyRep: "wf_ty_repr_bpl TyRep" and
    MaskVarDefDiff: "mask_var_def Tr \<noteq> mask_var Tr" and
    TyInterp: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and

    NullConst: "const_repr Tr CNull = nullConst" and
    MaskVar: "m_bpl = mask_var Tr" and

    MaskUpdateWf: "mask_update_wf TyRep ctxt_bpl mask_upd_bpl" and
    MaskReadWf: "mask_read_wf TyRep ctxt_bpl mask_read_bpl" and

    PredType: "pred_snap_field_type TyRep pid = Some pred_type" and

    NewPermBpl: "new_perm = (mask_read_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl
                                  [pred_type, TConSingle (TFrameFragmentId TyRep)]) \<guillemotleft>Add\<guillemotright> (Var temp_perm)" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl new_perm
                                  [pred_type, TConSingle (TFrameFragmentId TyRep)]" and

    PlocBpl: "e_ploc_bpl = FunExp pid [] e_args_bpl" and
    PlocRel: "ploc_rel_vpr_bpl' (curry R) ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and

    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep" and
    ProgEq: "program_total ctxt_vpr = Pr" and

    KFPosOff: "\<not> kf_pos_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
  shows "rel_general R R'
           (\<lambda>\<omega>def_\<omega> \<omega>def_\<omega>'. fst \<omega>def_\<omega> = fst \<omega>def_\<omega>' \<and> inhale_pred_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr p (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) (snd \<omega>def_\<omega>'))
           (\<lambda>\<omega>def_\<omega>. False) P ctxt_bpl
           (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
           (BigBlock name cs str tr, cont)"
  apply (rule rel_intro)
   prefer 2
   apply blast
proof -
  fix \<omega>def_\<omega> ns
  fix \<omega>def_\<omega>' :: "'a full_total_state \<times> 'a full_total_state"

  assume "R \<omega>def_\<omega> ns"
     and *: "fst \<omega>def_\<omega> = fst \<omega>def_\<omega>' \<and> inhale_pred_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr p (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) (snd \<omega>def_\<omega>')"

  obtain \<omega>def \<omega> \<omega>def' \<omega>' where "\<omega>def_\<omega> = (\<omega>def, \<omega>)" and "\<omega>def_\<omega>' = (\<omega>def', \<omega>')"
    by fastforce

  hence InitRel: "state_rel Pr StateCons TyRep Tr
                            (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt_bpl \<omega>def \<omega> ns"
    using StateRelIn \<open>R \<omega>def_\<omega> ns\<close>
    by auto

  hence InitRel': "state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>def \<omega> ns"
    apply (rule state_rel_aux_pred_remove[where ?AuxPred="AuxPred(temp_perm \<mapsto> pred_eq (RealV p))" and ?AuxPred'=AuxPred])
    by (simp add: AuxDomTemp map_le_def)

  have "R (\<omega>def,\<omega>) ns"
    using \<open>R \<omega>def_\<omega> ns\<close> \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close>
    by auto

  let ?ploc = "(pid,v_args_vpr)"

  obtain \<phi>_inh q where \<omega>':
    "option_fold ((=) q) (q \<noteq> 0) (Some (Abs_preal p)) \<and>
     consistent_external_wrt_ploc ctxt_vpr \<phi>_inh ?ploc (Abs_preal p) \<and>
     get_hh_total \<phi>_inh = get_hh_total_full \<omega> \<and>
     \<omega>' = (if p = 0 then \<omega> else add_to_lpm_nonzero_total_full \<omega> ?ploc (Abs_posreal (Abs_preal p)) (get_nm_total \<phi>_inh)) \<and>
     StateCons \<omega>'"
    using *[simplified inhale_pred_normal_premise_def inhale_perm_single_pred_def, simplified]
    by (metis (mono_tags, lifting) Abs_preal_inverse \<open>\<omega>def_\<omega> = _\<close> \<open>\<omega>def_\<omega>' = _\<close> get_hh_total_full.simps mem_Collect_eq option_fold.simps(1) split_pairs zero_preal.abs_eq zero_preal.rep_eq)

  hence mh_same: "get_mh_total_full \<omega> = get_mh_total_full \<omega>'" and
        mp_rel: "get_mp_total_full \<omega>' = (get_mp_total_full \<omega>)( ?ploc := get_mp_total_full \<omega> ?ploc + Abs_preal p )"
     apply simp
    apply (cases "p = 0")
    using \<omega>' zero_preal_def
     apply force
    using \<omega>'[THEN conjunct2, THEN conjunct2, THEN conjunct1]
    apply (simp del: add_to_lpm_nonzero_total_full.simps get_mp_total_full.simps)
    using add_to_lpm_nonzero_total_full__mp
    by (metis * Abs_posreal_inverse \<omega>' inhale_pred_normal_premise_def mem_Collect_eq order_less_le positive_real_preal preal_not_0_gt_0)

  have \<omega>'_extcons: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow>
    consistent_external (total_context.make Pr (\<lambda>_. None) (domain_type TyRep)) (get_total_full \<omega>')"
    apply (cases "p = 0")
     apply (metis InitRel' \<omega>' state_rel_consistent)
  proof -
    assume "consistent_state_rel_opt (state_rel_opt Tr)"
      and "p \<noteq> 0"
    have "consistent_external (total_context.make Pr (\<lambda>_. None) (domain_type TyRep)) (get_total_full \<omega>)"
      using InitRel' \<open>consistent_state_rel_opt (state_rel_opt Tr)\<close> state_rel_consistent
      by blast
    have "\<omega>' = add_to_lpm_nonzero_total_full \<omega> ?ploc (Abs_posreal (Abs_preal p)) (get_nm_total \<phi>_inh)"
      by (simp add: \<omega>' \<open>p \<noteq> 0\<close>)
    have "consistent_external_wrt_ploc ctxt_vpr \<phi>_inh ?ploc (Abs_preal p)"
      using * \<omega>' \<open>p \<noteq> 0\<close> inhale_pred_normal_premise_def
      by force
    hence 2: "consistent_external_wrt_ploc ctxt_vpr
                \<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = get_nm_total \<phi>_inh \<rparr>
                ?ploc (Abs_preal p)"
      by (metis (full_types) \<omega>' old.unit.exhaust total_state.surjective)
    show ?thesis
      unfolding \<open>\<omega>' = _\<close>
      apply (rule extcons_preserved_by_add_to_lpm_nonzero)
        apply fact
       apply (rule extcons_fun_interp_irrelevant[of ctxt_vpr])
         apply (simp add: total_context.defs)
         apply fact
        apply (simp add: total_context.defs AbsInterpEq)
       apply fact
      by (metis * \<open>p \<noteq> 0\<close> inhale_pred_normal_premise_def order_neq_le_trans positive_real_preal pperm_pnone_pgt)
  qed

  obtain mb where
    LookupMask: "lookup_var (var_context ctxt_bpl) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
    LookupMaskTy: "lookup_var_ty (var_context ctxt_bpl) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
    MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) (get_mp_total_full \<omega>) mb"
    using state_rel_obtain_mask[OF StateRelIn[OF \<open>R (\<omega>def,\<omega>) ns\<close>]]
    by blast

  \<comment> \<open>Construct the value of the new permission from the Viper state.\<close>
  let ?np = "Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr)) + p"

  have LookupTempPerm: "lookup_var (var_context ctxt_bpl) ns temp_perm = Some (RealV p)"
    using state_rel_aux_pred_sat_lookup_2[OF StateRelIn[OF \<open>R (\<omega>def,\<omega>) ns\<close>]]
    unfolding pred_eq_def
    by (metis (full_types) fun_upd_same)

  have null_eval: "red_expr_bpl ctxt_bpl (Var nullConst) ns (AbsV (ARef Null))"
    apply (rule red_expr_red_exprs.RedVar)
    by (metis NullConst StateRelIn \<open>R (\<omega>def,\<omega>) ns\<close> boogie_const_rel_lookup boogie_const_val.simps(3) state_rel_boogie_const_rel)

  have new_perm_eval: "red_expr_bpl ctxt_bpl new_perm ns (LitV (LReal ?np))"
    apply (simp add: NewPermBpl)
    apply (rule red_expr_red_exprs.RedBinOp[where ?v1.0="LitV (LReal (Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr))))" and ?v2.0="LitV (LReal p)"])
      apply (rule mask_read_wf_apply[OF MaskReadWf, where ?m=mb and ?r=Null and ?f="PredSnapshotField (pid,v_args_vpr)"])
          apply (metis MaskRel mask_rel_def)
         apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
        apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl'_def] * inhale_pred_normal_premise_def \<open>R (\<omega>def,\<omega>) ns\<close> \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close>
       apply fastforce
    using PredType
      apply simp
     apply (fastforce intro: RedVar LookupTempPerm)
    by simp

  \<comment> \<open>Construct the new Boogie heap.\<close>
  let ?mb' = "mb( (Null, PredSnapshotField (pid,v_args_vpr)) := ?np )"

  have m_upd_bpl_red: "red_expr_bpl ctxt_bpl m_upd_bpl ns (AbsV (AMask ?mb'))"
    apply (subst \<open>m_upd_bpl = _\<close>)
    apply (rule mask_update_wf_apply[OF MaskUpdateWf])
        apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
       apply (simp add: null_eval)
    using PlocRel[unfolded ploc_rel_vpr_bpl'_def] * inhale_pred_normal_premise_def \<open>R (\<omega>def,\<omega>) ns\<close> \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close>
      apply fastforce
    using new_perm_eval
     apply blast
    using PredType
    by force

  have "valid_heap_mask (get_mh_total_full \<omega>)"
    using InitRel state_rel_wf_mask_simple by blast

  have Disj: "disjoint_list [ {heap_var Tr, heap_var_def Tr},
                              {mask_var Tr, mask_var_def Tr},
                              ran (var_translation Tr),
                              ran (field_translation Tr),
                              range (const_repr Tr), dom AuxPred]"
    using InitRel' state_rel_disjoint
    by blast

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl
                ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns)
                ((BigBlock name cs str tr, cont), Normal ns') \<and>
              R' \<omega>def_\<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (TMaskId TyRep)" and ?v="AbsV (AMask ?mb')"])
    using MaskVar StateRelIn \<open>R (\<omega>def,\<omega>) ns\<close> state_rel_obtain_mask
       apply blast
      apply (simp add: TyInterp)
    using m_upd_bpl_red
     apply blast
    unfolding \<open>\<omega>def_\<omega>' = _\<close>
    apply (rule StateRelOut)
    apply (simp only: state_rel_def)
    apply (simp only: state_rel0_def, intro conjI)
                     apply (metis * InitRel' \<open>\<omega>def_\<omega> = _\<close> \<open>\<omega>def_\<omega>' = _\<close> fst_eqD state_rel_wf_mask_def_simple)
    using \<open>valid_heap_mask (get_mh_total_full \<omega>)\<close> mh_same
                    apply force
    using \<omega>'_extcons \<omega>'
                   apply (metis * InitRel' \<open>\<omega>def_\<omega> = _\<close> \<open>\<omega>def_\<omega>' = _\<close> fst_conv state_rel_consistent)
                  apply (simp add: TyInterp)
                 apply (rule store_rel_stable[where ?\<omega>=\<omega> and ?ns=ns])
    using InitRel state_rel_store_rel
                   apply blast
                  apply (simp add: \<omega>')
                 apply (metis InitRel MaskVar state_rel_disj_mask_store update_var_other)
                apply (simp add: Disj)
    using InitRel state_rel_disjoint apply fastforce
               apply (metis * InitRel \<open>\<omega>def_\<omega> = _\<close> \<open>\<omega>def_\<omega>' = _\<close> fstI inhale_perm_single_pred_store_same inhale_pred_normal_premise_def snd_conv state_rel_eval_welldef_eq)
              apply (metis * InitRel \<open>\<omega>def_\<omega> = _\<close> \<open>\<omega>def_\<omega>' = _\<close> inhale_perm_single_pred_trace_same inhale_pred_normal_premise_def split_pairs state_rel_eval_welldef_eq)
             apply (metis * InitRel' \<open>\<omega>def_\<omega> = _\<close> \<open>\<omega>def_\<omega>' = _\<close> fst_eqD inhale_perm_single_pred_heap_same inhale_pred_normal_premise_def sndI state_rel_eval_welldef_eq)
            defer defer defer defer
    subgoal
    proof -
      have "\<omega>' \<ge> \<omega>"
        by (metis "*" \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close> \<open>\<omega>def_\<omega>' = (\<omega>def', \<omega>')\<close> inhale_perm_single_pred_mono
            inhale_pred_normal_premise_def prod.sel(2))
      thus ?thesis
        apply (rule heap_knownfolded_var_rel_stable_larger_\<omega>
                      [OF state_rel_heap_knownfolded_var_rel[OF InitRel]])
        using InitRel' MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other
         apply metis
        using KFPosOff
        by blast
    qed
           apply (metis InitRel MaskVar field_rel_stable mask_var_disjoint state_rel_field_rel state_rel_state_rel0 update_var_other)
          apply (metis InitRel MaskVar boogie_const_rel_stable mask_var_disjoint state_rel_boogie_const_rel state_rel_state_rel0 update_var_other)
         defer
    using InitRel'[unfolded state_rel_def state_rel0_def]
         apply (metis InitRel MaskVar aux_vars_pred_sat_stable mask_var_disjoint state_rel_aux_vars_pred_sat state_rel_state_rel0 update_var_other)
  proof -
    let ?ns' = "update_var (var_context ctxt_bpl) ns m_bpl
                  (AbsV (AMask (mb((Null, PredSnapshotField (pid,v_args_vpr)) :=
                                   Rep_preal (get_mp_total_full \<omega> (pid,v_args_vpr)) + p))))"

    \<comment> \<open>Prove \<^const>\<open>heap_var_rel\<close>\<close>
    show HeapRel: "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel0_heap_var_rel[OF InitRel[simplified state_rel_def]]])
       apply (metis * \<open>\<omega>def_\<omega> = _\<close> \<open>\<omega>def_\<omega>' = _\<close> inhale_perm_single_pred_heap_same inhale_pred_normal_premise_def sndI)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    \<comment> \<open>Prove \<^const>\<open>mask_var_rel\<close>\<close>
    show MaskRel: "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var Tr) \<omega>' ?ns'"
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
      using MaskRel[simplified mask_rel_def]
       apply (smt (verit, best) * MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def is_bounded_field_bpl.simps(1) prod.sel(2))
      apply (subst \<open>get_mp_total_full \<omega>' = _\<close>)
       apply (metis (no_types, lifting) * Abs_preal_inverse MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def mem_Collect_eq plus_preal.rep_eq prod.inject vb_field.simps(2))
      using MaskRel[simplified mask_rel_def]
      by simp

    show "heap_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (heap_var_def Tr) \<omega>def' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF InitRel]])
      using * \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close> \<open>\<omega>def_\<omega>' = (\<omega>def', \<omega>')\<close>
       apply fastforce
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    show MaskRel: "mask_var_rel Pr (var_context ctxt_bpl) TyRep (field_translation Tr) (mask_var_def Tr) \<omega>def' ?ns'"
      apply (rule mask_var_rel_stable[OF state_rel_mask_var_def_rel[OF InitRel]])
      using * \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close> \<open>\<omega>def_\<omega>' = (\<omega>def', \<omega>')\<close>
        apply auto[1]
      using * \<open>\<omega>def_\<omega> = (\<omega>def, \<omega>)\<close> \<open>\<omega>def_\<omega>' = (\<omega>def', \<omega>')\<close>
       apply auto[1]
      using MaskVar MaskVarDefDiff
      by force

    show "state_well_typed (type_interp ctxt_bpl) (var_context ctxt_bpl) [] ?ns'"
      apply (rule state_well_typed_upd_2)
      using InitRel state_rel_state_well_typed
       apply blast
      by (simp add: TyInterp LookupMaskTy MaskVar)
  qed
qed


lemma fold_knownfolded_acc_upd_rel:
  assumes
    StateRelIn: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow>
                          state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns" and
    StateRelOut: "\<And>\<omega> ns. state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns \<Longrightarrow> R' \<omega> ns" and

    HeapVarDefSame: "heap_var_def Tr = heap_var Tr" and

    ExpSyntax: "supported_pred_expr e_r_vpr \<and> no_unfolding_pure_exp e_r_vpr" and

    TyInterpEq: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and

    NullConst: "const_repr Tr CNull = nullConst" and
    HeapVar: "hvar = heap_var Tr" and

    PermPosConstExpr: "\<And>\<omega>. ctxt_vpr, None \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> p > 0" and

    HeapUpdateWf: "heap_update_wf TyRep ctxt_bpl heap_upd_bpl" and
    HeapReadWf: "heap_read_wf TyRep ctxt_bpl heap_read_bpl" and
    PMaskUpdateWf: "pmask_update_wf TyRep ctxt_bpl pmask_upd_bpl" and

    KnownFoldedUpdBpl: "h_upd_bpl = heap_upd_bpl (Var (heap_var Tr)) (Var nullConst) e_ploc_bpl kf_set_bpl
                                      [pred_ty, TConSingle (TKnownFoldedMaskId TyRep)]" and
    KnownFoldedSetBpl: "kf_set_bpl = pmask_upd_bpl kf_read_bpl e_r_bpl e_f_bpl (Lit (LBool True))
                                       [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
    KnownFoldedReadBpl: "kf_read_bpl = heap_read_bpl (Var (heap_var Tr)) (Var nullConst) e_ploc_bpl
                                         [pred_ty, TConSingle (TKnownFoldedMaskId TyRep)]" and

    PredType: "pred_snap_field_type TyRep pid = Some pred_ty" and

    PlocRel: "ploc_sm_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and
    RefExpRel: "exp_rel_vpr_bpl (\<lambda>\<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt_bpl e_r_vpr e_r_bpl" and
    FieldRelSingle: "field_rel_single Pr TyRep Tr f e_f_bpl \<tau>_bpl"
 and
    KFPosOffF: "\<not> kf_pos_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
  shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and>
                               pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr
                                 (Atomic (Acc e_r_vpr f (PureExp e_p_vpr))) \<omega>)
                     (\<lambda>\<omega> ns. R' \<omega> ns)
                     (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                     (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                     P ctxt_bpl
                     (BigBlock name ((Assign hvar h_upd_bpl) # cs) str tr, cont)
                     (BigBlock name cs str tr, cont)" (is "rel_general ?R\<^sub>0 _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule rel_intro; blast?)
  fix \<omega> ns \<omega>'
  assume "?R\<^sub>0 \<omega> ns" and "\<omega> = \<omega>'"
  hence "R \<omega> ns"
    by blast

  from \<open>?R\<^sub>0 \<omega> ns\<close>[THEN conjunct2, THEN pred_kfm_sat_premiseD]
  obtain nm_exh p\<^sub>s nm\<^sub>s where
    sub: "get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p\<^sub>s,nm\<^sub>s)" and
    "nm_exh \<le> nm\<^sub>s" and
    diff_sat: "sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (Atomic (Acc e_r_vpr f (PureExp e_p_vpr)))"
    by blast

  then obtain v_r_vpr v_p_vpr addr where
    v_r_eval: "ctxt_vpr, None \<turnstile> \<langle>e_r_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r_vpr)" and
    v_p_eval: "ctxt_vpr, None \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_vpr)" and
    "addr = the_address v_r_vpr" and
    mh: "if v_r_vpr = Null then v_p_vpr = 0 \<and> get_mh_nm nm_exh = zero_mask else get_mh_nm nm_exh = singleton_mh (addr,f) (Abs_preal v_p_vpr)"
    by (fastforce elim: SatAcc_case)

  hence "v_p_vpr > 0"
    using PermPosConstExpr eval_is_deterministic(1)
    by blast
  hence "get_mh_nm nm_exh (addr,f) > 0"
    using mh
    by (metis mh \<open>0 < v_p_vpr\<close> preal_not_0_gt_0 positive_real_preal less_numeral_extra(3) singleton_mh.simps)

  have "v_r_vpr = Address addr"
    by (metis \<open>0 < v_p_vpr\<close> \<open>addr = the_address v_r_vpr\<close> less_numeral_extra(3) mh ref.exhaust_sel)

  from PlocRel[unfolded ploc_sm_rel_vpr_bpl'_def] \<open>?R\<^sub>0 \<omega> ns\<close>[unfolded pred_kfm_sat_premise_def] evals_with_None
  have ploc_bpl_eval: "red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredKnownFoldedField (pid, v_args_vpr))))"
    by blast

  from FieldRelSingle obtain f_tr \<tau> where
    FieldRel: "field_translation Tr f = Some f_tr" and
    "e_f_bpl = Lang.Var f_tr" and
    FieldTy: "declared_fields Pr f = Some \<tau>" and
    FieldTyBpl: "vpr_to_bpl_ty TyRep \<tau> = Some \<tau>_bpl"
    by (auto elim: field_rel_single_elim)

  obtain hb where
    lookup_heap: "lookup_var (var_context ctxt_bpl) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
    lookup_heap_ty: "lookup_var_ty (var_context ctxt_bpl) (heap_var Tr) = Some (TConSingle (THeapId TyRep))" and
    heap_ty: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
    using state_rel_obtain_heap[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    by metis

  hence "\<forall>lp. \<exists>kfm. hb (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm))" and
        kfm_rel: "kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr)) \<Longrightarrow> heap_knownfolded_rel Pr (field_translation Tr) (get_nm_total_full \<omega>) hb"
    using state_rel_heap_knownfolded_var_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    unfolding heap_knownfolded_var_rel_def
    using lookup_heap
    by auto

  then obtain kfm where kfm:
    "hb (Null, PredKnownFoldedField (pid, v_args_vpr)) = Some (AbsV (AKnownFoldedMask kfm))"
    by blast

  have hb_normal_fields: "knownfolded_masks_normal_fields hb"
    by (rule heap_knownfolded_var_rel_masks_normal_fields
               [OF state_rel_heap_knownfolded_var_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>]] lookup_heap])

  let ?kfm' = "kfm((v_r_vpr, NormalField f_tr \<tau>) := True)"
  let ?hb' = "hb( (Null, PredKnownFoldedField (pid, v_args_vpr)) \<mapsto> AbsV (AKnownFoldedMask ?kfm') )"
  let ?ns' = "update_var (var_context ctxt_bpl) ns hvar (AbsV (AHeap ?hb'))"

  have new_kfm_normal: "\<And>r f. ?kfm' (r, f) \<Longrightarrow> is_NormalField f"
    using knownfolded_masks_normal_fields_elim[OF hb_normal_fields kfm]
    by (auto split: if_split_asm)

  have kf_read_eval: "red_expr_bpl ctxt_bpl kf_read_bpl ns (AbsV (AKnownFoldedMask kfm))"
    unfolding \<open>kf_read_bpl = _\<close>
    apply (rule heap_read_wf_apply[OF HeapReadWf, where ?h=hb and ?r=Null and ?f="PredKnownFoldedField (pid,v_args_vpr)"])
         apply fact
        apply (rule red_expr_red_exprs.RedVar)
        apply (simp add: lookup_heap)
       apply fact
      apply (rule red_expr_red_exprs.RedVar)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] NullConst
      apply force
     apply (simp add: ploc_bpl_eval)
    apply (simp add: PredType)
    done

  have kf_set_eval: "red_expr_bpl ctxt_bpl kf_set_bpl ns (AbsV (AKnownFoldedMask ?kfm'))"
    unfolding \<open>kf_set_bpl = _\<close>
    apply (rule pmask_update_wf_apply[OF PMaskUpdateWf])
        apply fact
    using exp_rel_vpr_bpl_elim[OF RefExpRel] ExpSyntax
       apply (metis \<open>R \<omega> ns\<close> v_r_eval val_rel_vpr_bpl.simps(3))
    unfolding \<open>e_f_bpl = _\<close>
      apply (rule red_expr_red_exprs.RedVar)
    using FieldRel FieldTy StateRelIn \<open>R \<omega> ns\<close> lookup_field_rel state_rel_field_rel
      apply blast
     apply (rule red_expr_red_exprs.RedLit)
    apply (simp add: FieldTyBpl)
    done

  have h_upd_eval: "red_expr_bpl ctxt_bpl h_upd_bpl ns (AbsV (AHeap ?hb'))"
    unfolding \<open>h_upd_bpl = _\<close>
    apply (rule heap_update_wf_apply[OF HeapUpdateWf, where ?h=hb and ?r=Null and ?f="PredKnownFoldedField (pid,v_args_vpr)"])
          apply (rule red_expr_red_exprs.RedVar)
          apply fact+
        apply (rule red_expr_red_exprs.RedVar)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] NullConst
        apply force
       apply (simp add: ploc_bpl_eval)
      apply (simp add: PredType)
     apply fact
    apply simp
    done

  have "get_mh_nm nm\<^sub>s \<ge> get_mh_nm nm_exh"
    by (simp add: \<open>nm_exh \<le> nm\<^sub>s\<close> less_eq_nested_maskD)
  hence "get_mh_nm nm\<^sub>s (addr, f) > 0"
    by (meson \<open>0 < get_mh_nm nm_exh (addr, f)\<close> le_fun_def order_less_le_trans)

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl
              ((BigBlock name (Assign hvar h_upd_bpl # cs) str tr, cont), Normal ns)
              ((BigBlock name cs str tr, cont), Normal ns') \<and>
              R' \<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (THeapId TyRep)" and ?v="AbsV (AHeap ?hb')"])
    using lookup_heap_ty \<open>hvar = _\<close>
       apply blast
      apply (simp add: TyInterpEq zero_knownfolded_mask_def)
      apply (meson heap_bpl_well_typed_elim heap_ty)
     apply (simp add: h_upd_eval)
    apply (rule StateRelOut)
    unfolding \<open>\<omega> = \<omega>'\<close>[symmetric] \<open>hvar = _\<close>
    apply (rule kfm_update_state_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>] lookup_heap])
      defer
    unfolding TyInterpEq
      apply simp
      apply (meson heap_bpl_well_typed_elim heap_ty)
     apply (rule HeapVarDefSame)
    using new_kfm_normal
      apply blast
     apply (rule KFPosOffF)
    unfolding heap_knownfolded_rel_def
    apply (rule allI)
    apply (rule allI)
    apply (rename_tac kfm')
    apply (intro allI)
    apply (intro impI)
    apply (case_tac "lp = (pid, v_args_vpr)")
     defer
    using kfm_rel
    unfolding heap_knownfolded_rel_def
     apply auto[1]
    apply simp
  proof -
    fix lp kfm' l field_ty_vpr field_bpl
    assume kf_on: "kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
      and 1: "kfm((v_r_vpr, NormalField f_tr \<tau>) := True) = kfm'"
      and 2: "declared_fields Pr (snd l) = Some field_ty_vpr"
      and 3: "field_translation Tr (snd l) = Some field_bpl"
      and 4: "kfm' (Address (fst l), NormalField field_bpl field_ty_vpr)"
      and "lp = (pid, v_args_vpr)"
    show "pred_folds_perm (pid, v_args_vpr) l (get_nm_total (get_total_full \<omega>))"
    proof (cases "l = (addr, f)")
      case True
      hence "field_ty_vpr = \<tau>" and "field_bpl = f_tr"
        using 2 3 FieldTy FieldRel
        by fastforce+
      show ?thesis
        apply (rule ContainsPermDirect)
        using sub[unfolded get_fnm_total_full.simps]
         apply force
        by (simp add: ContainsLocDirect True \<open>0 < get_mh_nm nm\<^sub>s (addr, f)\<close>)
    next
      case False
      have "inj_on (field_translation Tr) (dom (field_translation Tr))"
        using StateRelIn \<open>R \<omega> ns\<close> field_rel_def state_rel_field_rel
        by blast
      hence "(Address (fst l), NormalField field_bpl field_ty_vpr) \<noteq> (Address addr, NormalField f_tr \<tau>)"
        using 2 3 FieldTy FieldRel state_rel_disjoint[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
        by (metis False domI inj_onD ref.sel split_pairs2 vb_field.inject(1))
      hence "kfm (Address (fst l), NormalField field_bpl field_ty_vpr)"
        using 1 4
        unfolding \<open>v_r_vpr = _\<close>
        by auto
      show ?thesis
        using kfm_rel[OF kf_on]
        unfolding heap_knownfolded_rel_def
        using 2 3 \<open>kfm _\<close> kfm
        by fastforce
    qed
  qed
qed


lemma fold_knownfolded_star_upd_rel:
  assumes
    CtxtPredWf: "ctxt_pred_syn_wf ctxt_vpr" and
    StepLeft:
      "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr A \<omega>)
                   (\<lambda>\<omega> ns. R' \<omega> ns)
                   (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                   (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                   P ctxt_bpl \<gamma> \<gamma>\<^sub>2" and
    StepRight:
      "rel_general (\<lambda>\<omega> ns. R' \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr B \<omega>)
                   (\<lambda>\<omega> ns. R'' \<omega> ns)
                   (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                   (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                   P ctxt_bpl \<gamma>\<^sub>2 \<gamma>'"

  shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr (A && B) \<omega>)
                     (\<lambda>\<omega> ns. R'' \<omega> ns)
                     (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                     (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                     P ctxt_bpl \<gamma> \<gamma>'" (is "rel_general ?R\<^sub>0 _ _ _ _ _ _ _")

proof (rule rel_intro; blast?)
  fix \<omega> ns \<omega>'
  assume "?R\<^sub>0 \<omega> ns" and "\<omega> = \<omega>'"
  hence "R \<omega> ns"
    by blast

  from \<open>?R\<^sub>0 \<omega> ns\<close>[THEN conjunct2, THEN pred_kfm_sat_premiseD] obtain nm_exh p\<^sub>s nm\<^sub>s where
    red_args: "red_pure_exps_total ctxt_vpr None e_args_vpr \<omega> (Some v_args_vpr)" and
    ty_correct: "pred_ty_correct_premise ctxt_vpr pid v_args_vpr" and
    sub: "get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p\<^sub>s,nm\<^sub>s)" and
    "nm_exh \<le> nm\<^sub>s" and
    sat: "sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (A && B)" and
    extcons: "consistent_external ctxt_vpr (\<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_exh \<rparr>)" (is "consistent_external _ ?\<phi>")
    by blast

  then obtain mh\<^sub>A mh\<^sub>B mp\<^sub>A mp\<^sub>B where
    "mh_split (get_mh_nm nm_exh) mh\<^sub>A mh\<^sub>B" and
    "mp_split (get_mp_nm nm_exh) mp\<^sub>A mp\<^sub>B" and
    "sat ctxt_vpr \<omega> mh\<^sub>A mp\<^sub>A A" and
    "sat ctxt_vpr \<omega> mh\<^sub>B mp\<^sub>B B"
    by (auto elim: SatStar_case)

  then obtain nm_exh_A nm_exh_B where
    "mh\<^sub>A = get_mh_nm nm_exh_A" and
    "mp\<^sub>A = get_mp_nm nm_exh_A" and
    nm\<^sub>1_cons: "consistent_external ctxt_vpr (?\<phi>\<lparr> get_nm_total := nm_exh_A \<rparr>)" and
    "mh\<^sub>B = get_mh_nm nm_exh_B" and
    "mp\<^sub>B = get_mp_nm nm_exh_B" and
    nm\<^sub>2_cons: "consistent_external ctxt_vpr (?\<phi>\<lparr> get_nm_total := nm_exh_B \<rparr>)" and
    "nm_exh_A + nm_exh_B = get_nm_total ?\<phi>"
    using sat_extcons_star_decompose[OF CtxtPredWf extcons]
    by (metis get_mh_total.simps get_mp_total.simps total_state.select_convs(2))

  moreover hence "nm_exh_A \<le> nm\<^sub>s" and "nm_exh_B \<le> nm\<^sub>s"
    using \<open>nm_exh \<le> nm\<^sub>s\<close> add.commute calculation(7) dual_order.trans nm_sum_is_bigger
    by fastforce+

  have prem_left: "pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr A \<omega>"
    apply (rule pred_kfm_sat_premiseI[OF red_args ty_correct sub \<open>nm_exh_A \<le> nm\<^sub>s\<close>])
    using \<open>sat ctxt_vpr \<omega> mh\<^sub>A mp\<^sub>A A\<close> \<open>mh\<^sub>A = _\<close> \<open>mp\<^sub>A = _\<close>
     apply simp
    using nm\<^sub>1_cons total_state.update_convs(2)
    apply simp
    done

  ultimately obtain ns\<^sub>2 where bpl_step\<^sub>2: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2) \<and> R' \<omega>' ns\<^sub>2"
    using rel_success_elim[OF StepLeft] \<open>R \<omega> ns\<close> prem_left \<open>\<omega> = \<omega>'\<close>
    by blast

  have prem_right: "pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr B \<omega>"
    apply (rule pred_kfm_sat_premiseI[OF red_args ty_correct sub \<open>nm_exh_B \<le> nm\<^sub>s\<close>])
    using \<open>sat ctxt_vpr \<omega> mh\<^sub>B mp\<^sub>B B\<close> \<open>mh\<^sub>B = _\<close> \<open>mp\<^sub>B = _\<close>
     apply simp
    using nm\<^sub>2_cons total_state.update_convs(2)
    apply simp
    done

  then obtain ns' where "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>', Normal ns') \<and> R'' \<omega>' ns'"
    using rel_success_elim[OF StepRight] bpl_step\<^sub>2 prem_right \<open>\<omega> = \<omega>'\<close>
    by blast

  with bpl_step\<^sub>2 show "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R'' \<omega>' ns'"
    using red_ast_bpl_transitive
    by blast
qed


lemma fold_knownfolded_star_upd_rel':
  assumes
    CtxtPredWf: "ctxt_pred_syn_wf ctxt_vpr" and
    StepLeft:
      "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr A \<omega>)
                   (\<lambda>\<omega> ns. R \<omega> ns)
                   (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                   (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                   P ctxt_bpl \<gamma> \<gamma>\<^sub>2" and
    StepRight:
      "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr B \<omega>)
                   (\<lambda>\<omega> ns. R \<omega> ns)
                   (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                   (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                   P ctxt_bpl \<gamma>\<^sub>2 \<gamma>'"

  shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr (A && B) \<omega>)
                     (\<lambda>\<omega> ns. R \<omega> ns)
                     (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                     (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                     P ctxt_bpl \<gamma> \<gamma>'" (is "rel_general ?R\<^sub>0 _ _ _ _ _ _ _")
  using assms fold_knownfolded_star_upd_rel
  by blast


lemma fold_knownfolded_imp_upd_rel:
  assumes
    StateRelIn: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow>
                          state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns" and
    StateRelOut: "\<And>\<omega> ns. state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns \<Longrightarrow> R' \<omega> ns" and

    HeapVarDefSame: "heap_var_def Tr = heap_var Tr" and

    ExpSyntax: "supported_pred_expr e_cond_vpr \<and> no_unfolding_pure_exp e_cond_vpr" and

    TyInterpEq: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and

    EmptyElse: "is_empty_bigblock empty_else_block" and

    CondExpRel: "exp_rel_vpr_bpl (\<lambda>\<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt_bpl e_cond_vpr e_cond_bpl" and

    StepRHS:
      "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr A \<omega>)
                   (\<lambda>\<omega> ns. R' \<omega> ns)
                   (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                   (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                   P ctxt_bpl (thnHd, (convert_list_to_cont thnTl (KSeq next cont))) (next, cont)"
       (is "rel_general _ _ _ _ _ _ ?\<gamma>\<^sub>2 _")

  shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr (assert.Imp e_cond_vpr A) \<omega>)
                     (\<lambda>\<omega> ns. R' \<omega> ns)
                     (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                     (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                     P ctxt_bpl
                     (if_bigblock name (Some e_cond_bpl) (thnHd # thnTl) [empty_else_block], KSeq next cont)
                     (next, cont)" (is "rel_general ?R\<^sub>0 _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule rel_intro; blast?)
  fix \<omega> ns \<omega>'
  assume "?R\<^sub>0 \<omega> ns" and "\<omega> = \<omega>'"
  hence "R \<omega> ns"
    by blast

  from \<open>?R\<^sub>0 \<omega> ns\<close>[THEN conjunct2, THEN pred_kfm_sat_premiseD]
  obtain nm_exh p\<^sub>s nm\<^sub>s where
    red_args: "red_pure_exps_total ctxt_vpr None e_args_vpr \<omega> (Some v_args_vpr)" and
    ty_correct: "pred_ty_correct_premise ctxt_vpr pid v_args_vpr" and
    sub: "get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p\<^sub>s,nm\<^sub>s)" and
    "nm_exh \<le> nm\<^sub>s" and
    diff_sat: "sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (assert.Imp e_cond_vpr A)" and
    extcons: "consistent_external ctxt_vpr \<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_exh \<rparr>"
    by blast

  then consider (True) "ctxt_vpr, None \<turnstile> \<langle>e_cond_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt_vpr, None \<turnstile> \<langle>e_cond_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Imp_True_or_False
    by blast

  then show "\<exists>ns'. red_ast_bpl P ctxt_bpl (?\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
  proof cases
    case True

    have "sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) A"
      using diff_sat
      by (metis SatImp_case True ValueAndBasicState.val.inject(2) eval_is_deterministic_single extended_val.inject)
    hence "pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr A \<omega>"
      using pred_kfm_sat_premiseI[OF red_args ty_correct sub \<open>nm_exh \<le> nm\<^sub>s\<close> _ extcons]
      by blast

    then obtain ns' where
      "R' \<omega> ns'" and red_thn: "red_ast_bpl P ctxt_bpl (?\<gamma>\<^sub>2, Normal ns) ((next, cont), Normal ns')"
      using rel_success_elim[OF StepRHS] \<open>R \<omega> ns\<close>
      by blast

    have h_upd_eval: "red_expr_bpl ctxt_bpl e_cond_bpl ns (LitV (LBool True))"
      using exp_rel_vpr_bplD[OF CondExpRel] ExpSyntax \<open>R \<omega> ns\<close> True
      by fastforce

    have "red_ast_bpl P ctxt_bpl (?\<gamma>, Normal ns) (?\<gamma>', Normal ns')"
      unfolding red_ast_bpl_def
      apply (rule converse_rtranclp_into_rtranclp)
       apply rule
       apply (rule RedParsedIfTrue)
      using h_upd_eval
       apply force
      using red_thn
      unfolding red_ast_bpl_def
      by simp

   then show ?thesis
     using \<open>R' \<omega> ns'\<close> \<open>\<omega> = \<omega>'\<close>
     by blast
  next
    case False
    have h_upd_eval: "red_expr_bpl ctxt_bpl e_cond_bpl ns (LitV (LBool False))"
      using exp_rel_vpr_bplD[OF CondExpRel] ExpSyntax \<open>R \<omega> ns\<close> False
      by fastforce
    show ?thesis
      apply (rule exI[of _ ns])
      apply (intro conjI)
       apply (rule red_ast_bpl_empty_else)
        apply fact
       apply fact
      using StateRelIn StateRelOut \<open>R \<omega> ns\<close> \<open>\<omega> = \<omega>'\<close>
      by blast
  qed
qed



context begin
\<comment> \<open>Some Boogie Properties (TODO: move somewhere else)\<close>


lemma closed_shift_id:
  assumes "closed \<tau>"
  shows "shiftT n k \<tau> = \<tau>"
  using assms
proof (induction \<tau>)
  case (TCon _ tys)
  then show ?case
    by (metis Ball_set closed.simps(3) list.map_ident_strong shiftT.simps(3))
qed auto


lemma type_of_vbpl_val_closed:
  assumes "wf_ty_repr_bpl TyRep"
      and "type_of_vbpl_val TyRep v = ty"
    shows "closed ty"
  apply (cases v)
   apply (rename_tac l)
   apply (case_tac l; insert vbpl_absval_ty_opt_closed[OF assms(1)] assms(2); auto)
  apply (rename_tac a)
  using vbpl_absval_ty_opt_closed[OF assms(1)] assms(2)
  by (metis assms(1) tcon_to_bplty.simps type_of_val.simps(2) vbpl_absval_ty_closed)


lemma closed_implies_subst_one_closed:
  assumes "ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>"
      and "length \<Omega>\<^sub>p = k"
      and "closed (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) ty)"
    shows "closed (instantiate (\<Omega>\<^sub>p@\<Omega>) ty')"
  using assms(1,3)
proof (induction ty arbitrary: ty')
  case (TVar i)
  then show ?case
    apply (cases "k < i")
     apply (cases "i < length \<Omega>\<^sub>p")
    using assms(2)
      apply linarith
     apply (cases "i \<le> length \<Omega>\<^sub>p")
    using assms(2)
      apply linarith
     apply (cases "i < length (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>)")
      apply simp
      apply (metis (no_types, lifting) ext Suc_diff_Suc assms(2) diff_Suc_1' diff_Suc_Suc le_Suc_eq less_Suc_eq_0_disj nat_le_linear not_less0 nth_Cons_Suc nth_append_right)
     apply simp
    apply simp
    using closed_instantiate assms(2) closed_shift_id nat_neq_iff nth_append_left
    by fastforce
next
  case (TPrim x)
  then show ?case by simp
next
  case (TCon ctor tys)
  then obtain tys' where "ty' = TCon ctor tys'" and "tys' = map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>) tys"
    by (cases ty'; simp)
  have *: "\<And>xs P f. (\<And>x. x \<in> set xs \<Longrightarrow> P (f x)) \<Longrightarrow> list_all P (map f xs)" \<comment> \<open>a temporary lemma\<close>
    by (simp add: assms list_all_length)
  show ?case
    unfolding \<open>ty' = TCon ctor tys'\<close> \<open>tys' = _\<close>
    apply (simp del: List.map_map)
    apply (rule *)
  proof -
    fix t'
    assume "t' \<in> set (map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>) tys)"
    then obtain t where "t \<in> set tys" and "t' = t[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>"
      by auto
    show "closed (instantiate (\<Omega>\<^sub>p@\<Omega>) t')"
      apply (rule TCon.IH[OF \<open>t \<in> _\<close> \<open>t' = _\<close>])
      using TCon.prems(2)[simplified] \<open>t \<in> _\<close>
      by (metis Ball_set image_eqI list.set_map)
  qed
qed


lemma subst_one_closed_implies_closed:
  assumes "ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>"
      and "length \<Omega>\<^sub>p = k"
      and "closed \<tau>\<^sub>k"
      and "closed (instantiate (\<Omega>\<^sub>p@\<Omega>) ty')"
    shows "closed (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) ty)"
  using assms(1,4)
proof (induction ty arbitrary: ty')
  case (TVar i)
  then show ?case
    apply (cases "k < i")
     apply (cases "i < length \<Omega>\<^sub>p")
    using assms(2)
      apply linarith
     apply (cases "i \<le> length \<Omega>\<^sub>p")
    using assms(2)
      apply linarith
     apply (cases "i < length (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>)")
      apply simp
      apply (smt (verit, best) One_nat_def Suc_diff_Suc dec_less_imp_less_eq diff_Suc_1' diff_Suc_eq_diff_pred less_imp_Suc_add nat_less_le not_less_eq nth_Cons_Suc nth_append)
     apply simp
    using less_Suc_eq_0_disj
     apply auto[1]
    using assms(2) nat_neq_iff nth_append_left assms(3)
    by fastforce
next
  case (TPrim x)
  then show ?case
    by auto
next
  case (TCon ctor tys)
  then obtain tys' where "ty' = TCon ctor tys'" and "tys' = map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>) tys"
    by (cases ty'; simp)
  have *: "\<And>xs P f. (\<And>x. x \<in> set xs \<Longrightarrow> P (f x)) \<Longrightarrow> list_all P (map f xs)" \<comment> \<open>a temporary lemma\<close>
    by (simp add: assms list_all_length)
  show ?case
    apply (simp del: List.map_map)
    apply (rule *)
  proof -
    fix t
    assume "t \<in> set tys"
    then obtain t' where "t' \<in> set tys'" and "t' = t[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>"
      by (simp add: \<open>tys' = _\<close>)
    show "closed (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) t)"
      apply (rule TCon.IH[OF \<open>t \<in> _\<close> \<open>t' = _\<close>])
      using TCon.prems(2)[unfolded \<open>ty' = TCon ctor tys'\<close>, simplified] \<open>t' \<in> _\<close>
      by (metis Ball_set comp_def list.pred_map)
  qed
qed


lemma boogie_instantiate_subst_one_type_var:
  assumes "ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>"
      and "length \<Omega>\<^sub>p = k"
      and "closed (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) ty)"
      and "closed (instantiate (\<Omega>\<^sub>p@\<Omega>) ty')"
    shows "instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) ty = instantiate (\<Omega>\<^sub>p@\<Omega>) ty'"
  using assms(1,3,4)
proof (induction ty arbitrary: ty')
  case (TVar i)
  show ?case
  proof (cases "k < i")
    case True
    hence "ty' = TVar (i-1)"
      using TVar.prems(1)
      by auto
    show ?thesis
      unfolding \<open>ty' = TVar (i-1)\<close>
      apply (cases "i < length \<Omega>\<^sub>p")
       defer
       apply (cases "i \<le> length \<Omega>\<^sub>p")
        defer
        apply (cases "i < length (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>)")
         defer
      using TVar.prems(2)
         apply fastforce
      using True assms(2)
        apply fastforce
      using True assms(2)
       apply fastforce
    proof -
      assume "\<not> i < length \<Omega>\<^sub>p"
        and "\<not> i \<le> length \<Omega>\<^sub>p"
        and "i < length (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>)"
      hence "instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) (TVar i) = \<Omega> ! (i - length \<Omega>\<^sub>p - 1)"
        by (simp add: nth_append)
      moreover hence "instantiate (\<Omega>\<^sub>p@\<Omega>) (TVar (i - 1)) = \<Omega> ! (i - length \<Omega>\<^sub>p - 1)"
        apply simp
        by (metis One_nat_def TVar.prems(3) \<open>\<not> i \<le> length \<Omega>\<^sub>p\<close> \<open>ty' = TVar (i - 1)\<close> closed.simps(1) dec_less_imp_less_eq diff_Suc_eq_diff_pred instantiate.simps(1) length_append nth_append)
      finally show "instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) (TVar i) = instantiate (\<Omega>\<^sub>p@\<Omega>) (TVar (i - 1))"
        by auto
    qed
  next
    case False
    then show ?thesis
      by (metis BoogieInterface.closed_instantiate TVar.prems(1,2,3) assms(2) closed.simps(1) closed_shift_id instantiate.simps(1) linorder_neqE_nat nth_append_left nth_append_length substT.simps(1))
  qed
next
  case (TPrim x)
  then show ?case
    by auto
next
  case (TCon ctor tys)
  then obtain tys' where "ty' = TCon ctor tys'" and "tys' = map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>) tys"
    by (cases ty'; simp)
  have "\<And>x. x \<in> set tys \<Longrightarrow> closed (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) x)"
  proof -
    fix t
    assume "t \<in> set tys"
    thus "closed (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>) t)"
      using TCon.prems(2)[simplified]
      by (metis Ball_set image_eqI list.set_map)
  qed
  hence "\<And>x. x \<in> set tys \<Longrightarrow> closed (instantiate (\<Omega>\<^sub>p@\<Omega>) (x[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>))"
  proof -
    fix t
    assume "t \<in> set tys"
    thus "closed (instantiate (\<Omega>\<^sub>p@\<Omega>) (t[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>))"
      using TCon.prems(3)[unfolded \<open>ty' = TCon ctor tys'\<close> \<open>tys' = _\<close>, simplified]
      by (smt (verit, ccfv_SIG) comp_def in_set_conv_nth length_map list_all_length nth_map)
  qed
  show ?case
    unfolding \<open>ty' = TCon ctor tys'\<close> \<open>tys' = _\<close>
    apply simp
    apply standard+
    apply (rule TCon.IH)
       apply simp
      apply simp
    by fact+
qed


fun boogie_expr_prop_sat_rec :: "(expr \<Rightarrow> bool) \<Rightarrow> expr \<Rightarrow> bool" where
  "boogie_expr_prop_sat_rec P (Var i) = P (Var i)"
| "boogie_expr_prop_sat_rec P (BVar i) = P (BVar i)"
| "boogie_expr_prop_sat_rec P (Lit l) = P (Lit l)"
| "boogie_expr_prop_sat_rec P (UnOp uop e) = (P (UnOp uop e) \<and> boogie_expr_prop_sat_rec P e)"
| "boogie_expr_prop_sat_rec P (e1 \<guillemotleft>bop\<guillemotright> e2) = (P (e1 \<guillemotleft>bop\<guillemotright> e2) \<and> boogie_expr_prop_sat_rec P e1 \<and> boogie_expr_prop_sat_rec P e2)"
| "boogie_expr_prop_sat_rec P (FunExp f ty_args fargs) = (P (FunExp f ty_args fargs) \<and> list_all (boogie_expr_prop_sat_rec P) fargs)"
| "boogie_expr_prop_sat_rec P (CondExp cond thn els) = (P (CondExp cond els thn) \<and> boogie_expr_prop_sat_rec P cond \<and> boogie_expr_prop_sat_rec P thn \<and> boogie_expr_prop_sat_rec P els)"
| "boogie_expr_prop_sat_rec P (Old e) = (P (Old e) \<and> boogie_expr_prop_sat_rec P e)"
| "boogie_expr_prop_sat_rec P (Forall ty e) = (P (Forall ty e) \<and> boogie_expr_prop_sat_rec P e)"
| "boogie_expr_prop_sat_rec P (Exists ty e) = (P (Exists ty e) \<and> boogie_expr_prop_sat_rec P e)"
| "boogie_expr_prop_sat_rec P (ForallT e) = (P (ForallT e) \<and> boogie_expr_prop_sat_rec P e)"
| "boogie_expr_prop_sat_rec P (ExistsT e) = (P (ExistsT e) \<and> boogie_expr_prop_sat_rec P e)"


fun boogie_expr_used_funs_in_dom :: "fdecls \<Rightarrow> expr \<Rightarrow> bool" where
  "boogie_expr_used_funs_in_dom F (FunExp f _ fargs) = (map_of F f \<noteq> None \<and> list_all (boogie_expr_used_funs_in_dom F) fargs)"
| "boogie_expr_used_funs_in_dom F _ = True"


lemma boogie_expr_eval_subst_one_type_var:
  assumes "\<And>v ty. type_of_val A v = ty \<Longrightarrow> closed ty"
      and "fun_interp_wf A F \<Gamma>"
      and "closed \<tau>\<^sub>k"
    shows "A,\<Lambda>,\<Gamma>,\<Omega>' \<turnstile> \<langle>e',s\<rangle> \<Down> v \<Longrightarrow>
           \<Omega>' = \<Omega>\<^sub>p@\<Omega> \<Longrightarrow>
           e' = e[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k] \<Longrightarrow>
           length \<Omega>\<^sub>p = k \<Longrightarrow>
           boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom F) e \<Longrightarrow>
           A,\<Lambda>,\<Gamma>,\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega> \<turnstile> \<langle>e,s\<rangle> \<Down> v"
      and "A,\<Lambda>,\<Gamma>,\<Omega>' \<turnstile> \<langle>es',s\<rangle> [\<Down>] vs \<Longrightarrow>
           \<Omega>' = \<Omega>\<^sub>p@\<Omega> \<Longrightarrow>
           es' = map (\<lambda>e. e[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]) es \<Longrightarrow>
           length \<Omega>\<^sub>p = k \<Longrightarrow>
           list_all (boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom F)) es \<Longrightarrow>
           A,\<Lambda>,\<Gamma>,\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega> \<turnstile> \<langle>es,s\<rangle> [\<Down>] vs"
proof (induction arbitrary: \<Omega>\<^sub>p e k and \<Omega>\<^sub>p es k rule: red_expr_red_exprs.inducts)
  case H: (RedVar n_s x v \<Omega>)
  hence "e = Var x"
    by (cases e; simp)
  then show ?case
    by (simp add: H.IH RedVar)
next
  case H: (RedBVar n_s i v \<Omega>)
  hence "e = BVar i"
    by (cases e; simp)
  then show ?case
    by (simp add: H.hyps RedBVar)
next
  case H: (RedLit \<Omega> v n_s)
  hence "e = Lit v"
    by (cases e; simp)
  then show ?case
    by (simp add: RedLit)
next
  case H: (RedBinOp \<Omega> e1' n_s v1 e2' v2 bop v)
  then obtain e1 e2 where "e1' = e1[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e2' = e2[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = e1 \<guillemotleft>bop\<guillemotright> e2"
    by (cases e; simp)
  then show ?case
    using H.IH(2,4) H.prems(1,3,4) H.hyps
    by (fastforce intro: RedBinOp)
next
  case H: (RedUnOp \<Omega> f' n_s v uop v')
  then obtain f where "f' = f[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = UnOp uop f"
    by (cases e; simp)
  then show ?case
    using H.IH(2) H.prems(1,3,4) H.hyps
    by (fastforce intro: RedUnOp)
next
  case H: (RedFunOp f f_interp \<Omega>' args' n_s v_args ty_args' v)
  then obtain args ty_args where "args' = map (\<lambda>e. e[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]) args" and "ty_args' = map (\<lambda>e. e[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>) ty_args" and "e = FunExp f ty_args args"
    by (cases e; simp)
  obtain fd where fd: "map_of F f = Some fd"
    using H.prems(4) \<open>e = _\<close>
    by auto
  then obtain ff where "\<Gamma> f = Some ff" and "fun_interp_single_wf_2 A fd ff"
    using assms(2)[unfolded fun_interp_wf_def, THEN spec, THEN spec, of f fd, THEN mp, OF fd]
    by blast
  hence "list_all closed (map (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>)) ty_args)"
    apply (cases fd)
    apply simp
    by (smt (verit, best) H.IH(1) H.hyps H.prems(1,3) \<open>ty_args' = _\<close> assms(3) length_map list_all_length nth_map option.inject subst_one_closed_implies_closed)
  have "map (instantiate (\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega>)) ty_args = map (instantiate (\<Omega>\<^sub>p@\<Omega>)) ty_args'"
    apply (rule nth_equalityI)
     apply (simp add: \<open>ty_args' = _\<close>)
    apply (simp add: \<open>ty_args' = _\<close>)
    apply (rule boogie_instantiate_subst_one_type_var[OF _ H.prems(3)])
      apply force
     apply (metis \<open>list_all _ _\<close> length_map list_all_length nth_map)
    by (metis H.prems(3) \<open>list_all _ _\<close> closed_implies_subst_one_closed length_map list_all_length nth_map)
  show "A,\<Lambda>,\<Gamma>,\<Omega>\<^sub>p@\<tau>\<^sub>k#\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v"
    unfolding \<open>e = _\<close>
    apply (rule RedFunOp)
      apply fact
     apply (rule H.IH(3))
        apply fact+
    using H.prems(4) \<open>e = FunExp f ty_args args\<close>
     apply force
    using H.hyps H.prems(1) \<open>map _ _ = map _ _\<close>
    by auto
next
  case H: (RedCondExpTrue \<Omega> cond' n_s thn' v els')
  then obtain cond thn els where "thn' = thn[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "els' = els[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = CondExp cond thn els"
    by (cases e; simp)
  then show ?case
    using H.IH(2,4) H.prems
    by (auto intro: RedCondExpTrue)
next
  case H: (RedCondExpFalse \<Omega> cond' n_s els' v thn')
  then obtain cond thn els where "thn' = thn[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "els' = els[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = CondExp cond thn els"
    by (cases e; simp)
  then show ?case
    using H.IH(2,4) H.prems
    by (auto intro: RedCondExpFalse)
next
  case H: (RedOld \<Omega> f' n_s v)
  then obtain f where "f' = f[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = Old f"
    by (cases e; simp)
  then show ?case
    using H.IH(2) H.prems(1,3,4)
    by (auto intro: RedOld)
next
  case H: (RedExpListNil \<Omega> n_s)
  then show ?case
    by (simp add: RedExpListNil)
next
  case H: (RedExpListCons \<Omega> e' n_s v es' vs)
  then show ?case
    by (auto intro: RedExpListCons)
next
  case H: (RedForAllTrue \<Omega>' ty' f' n_s)
  then obtain f ty where "f' = f[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>" and "e = Forall ty f"
    by (cases e; simp)
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedForAllTrue)
    apply (rule H.IH(2)[OF _ _ \<open>f' = _\<close>])
       apply (unfold H.prems(1))
    using H assms(1) boogie_instantiate_subst_one_type_var
       apply (metis \<open>ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>\<close> closed_implies_subst_one_closed)
    using H
      apply (simp, simp)
    using H.prems(4) \<open>e = Forall ty f\<close>
    by auto
next
  case H: (RedForAllFalse v \<Omega>' ty' f' n_s)
  then obtain f ty where "f' = f[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>" and "e = Forall ty f"
    by (cases e; simp)
  have "closed (instantiate (\<Omega>\<^sub>p@\<Omega>) ty')"
    using H.IH(1) H.prems(1) assms
    by blast
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedForAllFalse)
     apply (subst H.IH(1))
     apply (subst \<open>\<Omega>' = _\<close>)
     apply (rule sym)
     apply (rule boogie_instantiate_subst_one_type_var)
        apply fact+
    using H.prems(3) \<open>closed (instantiate (\<Omega>\<^sub>p@\<Omega>) ty')\<close> \<open>ty' = _\<close> assms(3) subst_one_closed_implies_closed
      apply blast
     apply fact
    apply (rule H.IH(3))
       apply fact+
    using H.prems(4) \<open>e = _\<close>
    by auto
next
  case H: (RedExistsTrue v \<Omega>' ty' f' n_s)
  then obtain f ty where "f' = f[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>" and "e = Exists ty f"
    by (cases e; simp)
  have "closed (instantiate (\<Omega>\<^sub>p@\<Omega>) ty')"
    using H.IH(1) H.prems(1) assms
    by blast
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedExistsTrue)
     apply (subst H.IH(1))
     apply (subst \<open>\<Omega>' = _\<close>)
     apply (rule sym)
     apply (rule boogie_instantiate_subst_one_type_var)
        apply fact+
    using H.prems(3) \<open>closed (instantiate (\<Omega>\<^sub>p@\<Omega>) ty')\<close> \<open>ty' = _\<close> assms(3) subst_one_closed_implies_closed
      apply blast
     apply fact
    apply (rule H.IH(3))
       apply fact+
    using H.prems(4) \<open>e = _\<close>
    by auto
next
  case H: (RedExistsFalse \<Omega>' ty' f' n_s)
  then obtain f ty where "f' = f[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>" and "e = Exists ty f"
    by (cases e; simp)
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedExistsFalse)
    apply (rule H.IH(2)[OF _ _ \<open>f' = _\<close>])
       apply (unfold H.prems(1))
    using H assms(1) boogie_instantiate_subst_one_type_var
       apply (metis \<open>ty' = ty[k \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]\<^sub>\<tau>\<close> closed_implies_subst_one_closed)
    using H
      apply (simp, simp)
    using H.prems(4) \<open>e = _\<close>
    by auto
next
  case H: (RedForallT_True \<Omega>' f' n_s)
  then obtain f where "f' = f[k+1 \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = ForallT f"
    by (cases e; simp)
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedForallT_True)
    apply (frule_tac ?\<Omega>\<^sub>p="\<tau>#\<Omega>\<^sub>p" in H.IH(2)[OF _ _ \<open>f' = _\<close>])
    using H
       apply (simp, simp)
    using H.prems(4) \<open>e = _\<close>
    by auto
next
  case H: (RedForallT_False \<tau> \<Omega>' f' n_s)
  then obtain f where "f' = f[k+1 \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = ForallT f"
    by (cases e; simp)
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedForallT_False)
     apply (rule H.hyps)
    apply (cut_tac H.IH(2)[OF _ \<open>f' = _\<close>, where ?\<Omega>\<^sub>p="\<tau>#\<Omega>\<^sub>p"])
    using H
       apply (simp, simp, simp)
    using H.prems(4) \<open>e = _\<close>
    by auto
next
  case H: (RedExistsT_True \<tau> \<Omega>' f' n_s)
  then obtain f where "f' = f[k+1 \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = ExistsT f"
    by (cases e; simp)
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedExistsT_True)
     apply (rule H.hyps)
    apply (cut_tac H.IH(2)[OF _ \<open>f' = _\<close>, where ?\<Omega>\<^sub>p="\<tau>#\<Omega>\<^sub>p"])
    using H
       apply (simp, simp, simp)
    using H.prems(4) \<open>e = _\<close>
    by auto
next
  case H: (RedExistsT_False \<Omega>' f' n_s)
  then obtain f where "f' = f[k+1 \<mapsto>\<^sub>\<tau> \<tau>\<^sub>k]" and "e = ExistsT f"
    by (cases e; simp)
  show ?case
    unfolding \<open>e = _\<close>
    apply (rule RedExistsT_False)
    apply (frule_tac ?\<Omega>\<^sub>p="\<tau>#\<Omega>\<^sub>p" in H.IH(2)[OF _ _ \<open>f' = _\<close>])
    using H
       apply (simp, simp)
    using H.prems(4) \<open>e = _\<close>
    by auto
qed


fun boogie_expr_no_binder :: "expr \<Rightarrow> bool" where
  "boogie_expr_no_binder (BVar i) = False"
| "boogie_expr_no_binder (Old _) = False"
| "boogie_expr_no_binder (Forall _ _) = False"
| "boogie_expr_no_binder (Exists _ _) = False"
| "boogie_expr_no_binder (ForallT e) = False"
| "boogie_expr_no_binder (ExistsT e) = False"
| "boogie_expr_no_binder _ = True"


lemma boogie_expr_eval_binder_state:
    shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,s\<rangle> \<Down> v \<Longrightarrow>
           boogie_expr_prop_sat_rec boogie_expr_no_binder e \<Longrightarrow>
           A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,full_ext_env s w\<rangle> \<Down> v"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es,s\<rangle> [\<Down>] vs \<Longrightarrow>
           list_all (boogie_expr_prop_sat_rec boogie_expr_no_binder) es \<Longrightarrow>
           A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es,full_ext_env s w\<rangle> [\<Down>] vs"
proof (induction rule: red_expr_red_exprs.inducts)
  case H: (RedVar n_s x v \<Omega>)
  then show ?case
    by (simp add: lookup_var_binder_upd RedVar)
qed (auto intro: red_expr_red_exprs.intros)


fun boogie_expr_no_var :: "nat \<Rightarrow> expr \<Rightarrow> bool" where
  "boogie_expr_no_var n (Var i) = (n \<noteq> i)"
| "boogie_expr_no_var n (Old _) = False"
| "boogie_expr_no_var n (Forall _ _) = False"
| "boogie_expr_no_var n (Exists _ _) = False"
| "boogie_expr_no_var n _ = True"


lemma boogie_expr_eval_update_var:
    shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,s\<rangle> \<Down> v \<Longrightarrow>
           boogie_expr_prop_sat_rec (boogie_expr_no_var n) e \<Longrightarrow>
           A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,update_var \<Lambda> s n w\<rangle> \<Down> v"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es,s\<rangle> [\<Down>] vs \<Longrightarrow>
           list_all (boogie_expr_prop_sat_rec (boogie_expr_no_var n)) es \<Longrightarrow>
           A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es,update_var \<Lambda> s n w\<rangle> [\<Down>] vs"
proof (induction rule: red_expr_red_exprs.inducts)
  case H: (RedVar n_s x v \<Omega>)
  then show ?case
    by (simp add: RedVar)
next
  case H: (RedBVar n_s i v \<Omega>)
  then show ?case
    by (simp add: RedBVar update_var_binder_same)
qed (auto intro: red_expr_red_exprs.intros)


lemma closed_substT:
  assumes "closed \<tau>"
  shows "\<tau>[k \<mapsto>\<^sub>\<tau> \<tau>']\<^sub>\<tau> = \<tau>"
  using assms
proof (induction \<tau>)
  case (TCon x1a x2a)
  then show ?case
    apply simp
    by (meson Ball_set list.map_ident_strong)
qed auto


end



lemma sat_mh_mp_equiv:
  assumes "sat ctxt \<omega> mh mp B"
      and "B = syntactic_mult q A"
      and "sat ctxt' \<omega> mh' mp' B'"
      and "B' = syntactic_mult q' A"
      and "q > 0"
      and "q' > 0"
    shows "(mh l > 0 \<longleftrightarrow> mh' l > 0) \<and> (mp lp > 0 \<longleftrightarrow> mp' lp > 0)"
  using assms(1-4)
proof (induction arbitrary: A mh' mp' B')
  case H: (SatAcc e_r r e_p' p' a mh f mp)
  obtain e_p where "A = Atomic (Acc e_r f (PureExp e_p))" and "e_p' = Binop (ELit (LPerm q)) Mult e_p"
    using H.prems(1)
    apply (cases "(p',A)" rule: syntactic_mult.cases; simp?)
    apply (case_tac e_p)
    using assms(5)
    by auto

  obtain v1 v2 where
    3: "ctxt, None \<turnstile> \<langle>ELit (LPerm q); \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and
    eval_e_p: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and
    1: "eval_binop v1 Mult v2 = BinopNormal (VPerm p')"
    using H.hyps(2)[unfolded \<open>e_p' = _\<close>]
    by (auto elim: RedBinop_case)

  obtain r'' p'' a'' where
    eval_r'': "ctxt', None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r'')" and
    eval_p'': "ctxt', None \<turnstile> \<langle>Binop (ELit (LPerm q')) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p'')" and
    "a'' = the_address r''" and
    "p'' \<ge> 0" and
    4: "if r'' = Null then p'' = 0 \<and> mh' = zero_mask else mh' = singleton_mh (a'',f) (Abs_preal p'')" and
    "mp' = zero_mask"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified]
    by (auto elim: SatAcc_case)

  have "r = r''"
    using eval_context_irrelevant H.hyps(1) eval_r'' eval_is_deterministic_single
    by fastforce

  obtain v1' v2' where
    "ctxt', None \<turnstile> \<langle>ELit (LPerm q'); \<omega>\<rangle> [\<Down>]\<^sub>t Val v1'" and
    eval_v2': "ctxt', None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2'" and
    2: "eval_binop v1' Mult v2' = BinopNormal (VPerm p'')"
    using eval_p''
    by (auto elim: RedBinop_case)

  hence "v1' = VPerm q'"
    by (metis TotalExpressions.RedLit_case extended_val.inject val_of_lit.simps(3))
  hence "v1 = VPerm q"
    by (metis 3 TotalExpressions.RedLit_case extended_val.inject val_of_lit.simps(3))

  have "v2 = v2'"
    using eval_context_irrelevant eval_is_deterministic_single eval_v2' eval_e_p
    by blast

  have 5: "p'' > 0 \<longleftrightarrow> p' > 0"
    using 1 2
    unfolding \<open>v1 = _\<close> \<open>v1' = _\<close> \<open>v2 = v2'\<close>[symmetric]
    apply (cases v2; simp)
    using \<open>q > 0\<close> \<open>q' > 0\<close> H.hyps(4) \<open>0 \<le> p''\<close> no_zero_divisors
    by fastforce+

  show ?case
    apply (intro conjI)
     apply (smt (verit, best) "4" "5" H.hyps(3,4,5) \<open>0 \<le> p''\<close> \<open>a'' = _\<close> \<open>r = r''\<close> positive_real_preal preal_not_0_gt_0 singleton_mh.simps)
    by (simp add: H.hyps(6) \<open>mp' = zero_mask\<close>)
next
  case H: (SatAccWildcard e_r r a f mh mp)
  have "A = Atomic (Acc e_r f Wildcard)"
    using H.prems(1)
    apply (cases "(q,A)" rule: syntactic_mult.cases; simp?)
    apply (case_tac e_p)
    using assms(5)
    by auto

  obtain r' a' where
    eval_r': "ctxt', None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r')" and
    "a' = the_address r'"
    "is_singleton_mh (a',f) mh'"
    "mp' = zero_mask"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified] \<open>q' > 0\<close>
    by (fastforce elim: SatAccWildcard_case)

  have "r = r'"
    by (meson H.hyps(1) ValueAndBasicState.val.inject(4) eval_r' eval_context_irrelevant(1) eval_is_deterministic_single extended_val.inject)

  then show ?case
    by (metis H.hyps(2,4,5) \<open>a' = the_address r'\<close> \<open>is_singleton_mh (a', f) mh'\<close> \<open>mp' = zero_mask\<close> is_singleton_mh.simps singleton_mh.simps)
next
  case H: (SatAccPred e_args v_args e_p' p' mh mp pid pdecl pbody)
  obtain e_p where "A = Atomic (AccPredicate pid e_args (PureExp e_p))" and "e_p' = Binop (ELit (LPerm q)) Mult e_p"
    using H.prems(1)
    apply (cases "(q,A)" rule: syntactic_mult.cases; simp?)
    apply (case_tac e_p)
    using assms(5)
    by auto

  obtain v_args'' p'' where
    eval_args'': "red_pure_exps_total ctxt' None e_args \<omega> (Some v_args'')" and
    eval_p'': "ctxt', None \<turnstile> \<langle>Binop (ELit (LPerm q')) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p'')" and
    "p'' \<ge> 0" and
    "mh' = zero_mask" and
    "mp' = singleton_mp (pid,v_args'') (Abs_preal p'')"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified]
    by (auto elim: SatAccPred_case)

  obtain v1 v2 where
    eval_v1: "ctxt, None \<turnstile> \<langle>ELit (LPerm q); \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and
    eval_e_p: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and
    1: "eval_binop v1 Mult v2 = BinopNormal (VPerm p')"
    using H.hyps(2)[unfolded \<open>e_p' = _\<close>]
    by (auto elim: RedBinop_case)

  obtain v1' v2' where
    eval_v1': "ctxt', None \<turnstile> \<langle>ELit (LPerm q'); \<omega>\<rangle> [\<Down>]\<^sub>t Val v1'" and
    eval_v2': "ctxt', None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2'" and
    2: "eval_binop v1' Mult v2' = BinopNormal (VPerm p'')"
    using eval_p''
    by (auto elim: RedBinop_case)

  have "v_args = v_args''"
    using H.hyps(1) eval_args'' eval_context_irrelevant(2) eval_is_deterministic(2)
    by blast

  have "v1 = VPerm q"
    by (metis TotalExpressions.RedLit_case eval_v1 extended_val.inject val_of_lit.simps(3))
  have "v1' = VPerm q'"
    by (metis TotalExpressions.RedLit_case eval_v1' extended_val.inject val_of_lit.simps(3))

  have "v2 = v2'"
    using eval_context_irrelevant eval_is_deterministic_single eval_v2' eval_e_p
    by blast

  have 3: "p'' > 0 \<longleftrightarrow> p' > 0"
    using 1 2
    unfolding \<open>v1 = _\<close> \<open>v1' = _\<close> \<open>v2 = v2'\<close>[symmetric]
    apply (cases v2; simp)
    using \<open>q > 0\<close> \<open>q' > 0\<close> \<open>0 \<le> p''\<close> H.hyps(3) no_zero_divisors
    by fastforce+

  show ?case
    apply (intro conjI)
    using H.hyps(4) \<open>mh' = zero_mask\<close>
     apply force
    using 3 H.hyps(3,5) \<open>0 \<le> p''\<close> \<open>mp' = _\<close> \<open>v_args = v_args''\<close> positive_real_preal pperm_pnone_pgt
    by auto
next
  case H: (SatAccPredWildcard e_args v_args mh pid mp pdecl pbody)
  have "A = Atomic (AccPredicate pid e_args Wildcard)"
    using H.prems(1)
    apply (cases "(q,A)" rule: syntactic_mult.cases; simp?)
    apply (case_tac e_p)
    using assms(5)
    by auto

  obtain v_args' where
    eval_args': "red_pure_exps_total ctxt' None e_args \<omega> (Some v_args')" and
    "mh' = zero_mask" and
    "is_singleton_mp (pid,v_args') mp'"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified] \<open>q' > 0\<close>
    by (fastforce elim: SatAccPredWildcard_case)

  have "v_args = v_args'"
    using H.hyps(1) eval_args' eval_context_irrelevant(2) eval_is_deterministic(2)
    by blast

  then show ?case
    by (metis H.hyps(2,3) \<open>is_singleton_mp (pid, v_args') mp'\<close> \<open>mh' = zero_mask\<close> is_singleton_mp.simps singleton_mp.elims)
next
  case H: (SatPure e mh mp)
  moreover hence "A = Atomic (Pure e)"
    by (cases "(q,A)" rule: syntactic_mult.cases; simp?)
  moreover have "mh' = zero_mask" and "mp' = zero_mask"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>]
    by (auto elim: SatPure_case)
  ultimately show ?case
    by fastforce
next
  case H: (SatStar mh mh\<^sub>1 mh\<^sub>2 mp mp\<^sub>1 mp\<^sub>2 C D)
  obtain A1 A2 where "A = A1 && A2" and "C = syntactic_mult q A1" and "D = syntactic_mult q A2"
    using H.prems(1)
    by (cases "(q,A)" rule: syntactic_mult.cases; simp?)
  then obtain mh\<^sub>1' mh\<^sub>2' mp\<^sub>1' mp\<^sub>2' where
    3: "mh_split mh' mh\<^sub>1' mh\<^sub>2'" and
    4: "mp_split mp' mp\<^sub>1' mp\<^sub>2'" and
    1: "sat ctxt' \<omega> mh\<^sub>1' mp\<^sub>1' (syntactic_mult q' A1)" and
    2: "sat ctxt' \<omega> mh\<^sub>2' mp\<^sub>2' (syntactic_mult q' A2)"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified]
    by (auto elim: SatStar_case)
  show ?case
    using H.IH(1)[OF \<open>C = _\<close> 1] H.IH(2)[OF \<open>D = _\<close> 2] 3 4 H.hyps(1,2)
    apply (simp add: add_masks_def)
    by (smt (verit, best) add_0 padd_pos preal_not_0_gt_0)
next
  case H: (SatImpTrue e mh mp C')
  obtain C where "A = ViperLang.Imp e C" and "C' = syntactic_mult q C"
    using H.prems(1)
    by (cases "(q,A)" rule: syntactic_mult.cases; simp?)
  have "sat ctxt' \<omega> mh' mp' (syntactic_mult q' C)"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified] H.hyps(1)[THEN eval_context_irrelevant(1), THEN eval_is_deterministic_single]
    by (auto elim: SatImp_case)
  then show ?case
    using H.IH \<open>C' = _\<close>
    by presburger
next
  case H: (SatImpFalse e mh mp C')
  obtain C where "A = ViperLang.Imp e C" and "C' = syntactic_mult q C"
    using H.prems(1)
    by (cases "(q,A)" rule: syntactic_mult.cases; simp?)
  have "mh' = zero_mask" and "mp' = zero_mask"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified] H.hyps(1)[THEN eval_context_irrelevant(1), THEN eval_is_deterministic_single]
    by (auto elim: SatImp_case)
  then show ?case
    using H.hyps(2,3)
    by presburger
next
  case H: (SatCondTrue e mh mp C' D')
  obtain C D where "A = ViperLang.CondAssert e C D" and "C' = syntactic_mult q C" and "D' = syntactic_mult q D"
    using H.prems(1)
    by (cases "(q,A)" rule: syntactic_mult.cases; simp?)
  have "sat ctxt' \<omega> mh' mp' (syntactic_mult q' C)"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified] H.hyps(1)[THEN eval_context_irrelevant(1), THEN eval_is_deterministic_single]
    by (auto elim: SatCond_case)
  then show ?case
    using H.IH \<open>C' = _\<close>
    by presburger
next
  case H: (SatCondFalse e mh mp D' C')
  obtain C D where "A = ViperLang.CondAssert e C D" and "C' = syntactic_mult q C" and "D' = syntactic_mult q D"
    using H.prems(1)
    by (cases "(q,A)" rule: syntactic_mult.cases; simp?)
  have "sat ctxt' \<omega> mh' mp' (syntactic_mult q' D)"
    using H.prems(2)[unfolded \<open>B' = _\<close> \<open>A = _\<close>, simplified] H.hyps(1)[THEN eval_context_irrelevant(1), THEN eval_is_deterministic_single]
    by (auto elim: SatCond_case)
  then show ?case
    using H.IH \<open>D' = _\<close>
    by presburger
qed


lemma extcons_loc_set_equal:
  assumes "consistent_external_wrt_ploc ctxt \<phi> (pid,vs) q"
      and "contains_heap_loc l (get_nm_total \<phi>)"
      and "consistent_external_wrt_ploc ctxt' \<phi>' (pid,vs) q'"
      and "q > 0"
      and "q' > 0"
      and "get_hh_total \<phi> = get_hh_total \<phi>'"
      and "program_total ctxt = program_total ctxt'"
    shows "contains_heap_loc l (get_nm_total \<phi>')"
  using assms(1-6)
proof (induction "get_nm_total \<phi>" arbitrary: \<phi> \<phi>' pid vs q q')
  case (NM mh fnm)
  then obtain pdecl pbody where
    "ViperLang.predicates (program_total ctxt) pid = Some pdecl" and
    "vals_well_typed (absval_interp_total ctxt) vs (ViperLang.predicate_decl.args pdecl)" and
    "ViperLang.predicate_decl.body pdecl = Some pbody" and
    sat1:
    "sat ctxt
         \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = \<phi>\<lparr> get_nm_total := 0 \<rparr> \<rparr>
         (get_mh_total \<phi>) (get_mp_total \<phi>)
         (syntactic_mult (Rep_preal q) pbody)" and
    "consistent_external ctxt \<phi>" and
    sat2:
    "sat ctxt'
         \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = \<phi>'\<lparr> get_nm_total := 0 \<rparr> \<rparr>
         (get_mh_total \<phi>') (get_mp_total \<phi>')
         (syntactic_mult (Rep_preal q') pbody)" and
    "consistent_external ctxt' \<phi>'"
    by (fastforce simp: assms(7) elim: SatStep_case)

  have \<phi>_eq: "\<phi>\<lparr> get_nm_total := 0 \<rparr> = \<phi>'\<lparr> get_nm_total := 0 \<rparr>"
    using NM.prems(6)
    by auto

  have *: "\<And>l. get_mh_total \<phi> l > 0 \<longleftrightarrow> get_mh_total \<phi>' l > 0" and
      **: "\<And>lp. get_mp_total \<phi> lp > 0 \<longleftrightarrow> get_mp_total \<phi>' lp > 0"
     apply (rule sat_mh_mp_equiv[THEN conjunct1])
          apply (rule sat1)
         apply simp
        apply (rule sat2[unfolded \<phi>_eq[symmetric]])
    using NM.prems(4,5) less_preal.rep_eq zero_preal.rep_eq
       apply (simp, simp)
    using NM.prems(5) less_preal.rep_eq zero_preal.rep_eq
     apply force
    apply (rule sat_mh_mp_equiv[THEN conjunct2])
         apply (rule sat1)
        apply simp
       apply (rule sat2[unfolded \<phi>_eq[symmetric]])
      apply simp
    using NM.prems(4,5) less_preal.rep_eq zero_preal.rep_eq
    by auto

  from NM.prems(2) show ?case
  proof cases
    case H: ContainsLocDirect
    show ?thesis
      apply (rule ContainsLocDirect)
      using * H
      by auto
  next
    case H: (ContainsLocNested lp p\<^sub>s nm\<^sub>s)
    then obtain p\<^sub>s' nm\<^sub>s' where "get_fnm_nm (get_nm_total \<phi>') lp = Some (p\<^sub>s', nm\<^sub>s')"
      using **
      by (metis get_mp_0_implies_fnm_None get_mp_total.simps obtain_lpm_from_mp preal_not_0_gt_0)

    hence extcons2: "consistent_external_wrt_ploc ctxt' (\<phi>'\<lparr> get_nm_total := nm\<^sub>s' \<rparr>) lp (Rep_posreal p\<^sub>s')"
      by (metis SatAll_case \<open>consistent_external ctxt' \<phi>'\<close> surj_pair)
    have extcons1: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm\<^sub>s \<rparr>) lp (Rep_posreal p\<^sub>s)"
      by (metis H(1) SatAll_case \<open>consistent_external ctxt \<phi>\<close> surj_pair)

    obtain pid\<^sub>s vs\<^sub>s where "lp = (pid\<^sub>s,vs\<^sub>s)"
      by fastforce

    show ?thesis
      apply (rule ContainsLocNested)
       apply fact
      apply (rule NM.hyps(1)[where ?\<phi>'="\<phi>'\<lparr> get_nm_total := nm\<^sub>s' \<rparr>", simplified, of "Some (p\<^sub>s,nm\<^sub>s)" "(p\<^sub>s, nm\<^sub>s)" "\<phi>\<lparr> get_nm_total := nm\<^sub>s \<rparr>"])
              apply (metis H(1) NM.hyps(2) get_fnm_nm.simps rangeI)
             apply simp
            apply simp
           apply (rule extcons1[unfolded \<open>lp = _\<close>])
          apply simp
          apply fact
         apply (rule extcons2[unfolded \<open>lp = _\<close>])
      using Rep_posreal
        apply (force, force)
      apply simp
      by fact
  qed
qed


lemma extcons_loc_set_equal_rec:
  assumes "consistent_external ctxt \<phi>"
      and "pred_folds_perm lp l nm"
      and "nm = get_nm_total \<phi>"
      and "consistent_external_wrt_ploc ctxt' \<phi>' lp q"
      and "q > 0"
      and "get_hh_total \<phi> = get_hh_total \<phi>'"
      and "program_total ctxt = program_total ctxt'"
    shows "contains_heap_loc l (get_nm_total \<phi>')"
  using assms(2) assms(1,3,6)
proof (induction arbitrary: \<phi> rule: pred_folds_perm.inducts)
  case (ContainsPermDirect nm p' nm')
  hence extcons1: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm' \<rparr>) lp (Rep_posreal p')"
    by (metis SatAll_case surj_pair)
  obtain pid vs where "lp = (pid,vs)"
    by fastforce
  show ?case
    apply (rule extcons_loc_set_equal)
          apply (rule extcons1[unfolded \<open>lp = _\<close>])
         apply simp
         apply (rule ContainsPermDirect.hyps(2))
        apply (rule assms(4)[unfolded \<open>lp = _\<close>])
    using Rep_posreal
       apply blast
      apply fact
     apply (simp add: ContainsPermDirect.prems(3))
    by fact
next
  case (ContainsPermNested nm lp' p' nm')
  hence extcons1: "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm' \<rparr>)"
    by (metis SatAll_case SatStep_case surj_pair)
  show ?case
    apply (rule ContainsPermNested.IH)
      apply (rule extcons1)
     apply simp
    by (simp add: ContainsPermNested.prems(3))
qed


lemma fold_knownfolded_pred_upd_rel:
  assumes
    StateRelIn: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow>
                          state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns" and
    StateRelOut: "\<And>\<omega> ns. state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns \<Longrightarrow> R' \<omega> ns" and

    HeapVarDefSame: "heap_var_def Tr = heap_var Tr" and

    TyInterpEq: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and
    WfTyRep: "wf_ty_repr_bpl TyRep" and
    ProgEq: "program_total ctxt_vpr = Pr" and
    FunInterp: "fun_interp_wf (vbpl_absval_ty TyRep) fun_decls (fun_interp ctxt_bpl)" and

    NullConst: "const_repr Tr CNull = nullConst" and
    HeapVar: "hvar = heap_var Tr" and

    HeapUpdateWf: "heap_update_wf TyRep ctxt_bpl heap_upd_bpl" and
    HeapReadWf: "heap_read_wf TyRep ctxt_bpl heap_read_bpl" and
    PMaskReadWf: "pmask_read_wf TyRep ctxt_bpl pmask_read_bpl" and

    NewKFMPropBpl: "new_kfm_prop_bpl = ForallT (ForallT (Forall (TConSingle (TRefId TyRep)) (Forall (TCon (TFieldId TyRep) [TVar 1, TVar 0]) new_kfm_prop_body_bpl)))" and
    NewKFMPropBodyBpl: "new_kfm_prop_body_bpl = new_kfm_prop_lhs_bpl \<guillemotleft>Imp\<guillemotright> new_kfm_prop_rhs_bpl" and
    NewKFMPropLHSBpl: "new_kfm_prop_lhs_bpl = new_kfm_prop_orig_bpl \<guillemotleft>Or\<guillemotright> new_kfm_prop_fold_bpl" and
    KFMOrigTrueBpl: "new_kfm_prop_orig_bpl = pmask_read_bpl pmask_orig_bpl (BVar 1) (BVar 0) [TVar 1, TVar 0]" and
    KFMFoldTrueBpl: "new_kfm_prop_fold_bpl = pmask_read_bpl pmask_fold_bpl (BVar 1) (BVar 0) [TVar 1, TVar 0]" and
    KFMOrigReadBpl: "pmask_orig_bpl = heap_read_bpl (Var hvar) (Var nullConst) e_ploc_bpl [pred_ty, TConSingle (TKnownFoldedMaskId TyRep)]" and
    KFMFoldReadBpl: "pmask_fold_bpl = heap_read_bpl (Var hvar) (Var nullConst) e_ploc_fold_bpl [pred_fold_ty, TConSingle (TKnownFoldedMaskId TyRep)]" and
    KnownFoldedReadBpl: "new_kfm_prop_rhs_bpl = pmask_read_bpl (Var new_kfm_var) (BVar 1) (BVar 0) [TVar 1, TVar 0]" and
    KnownFoldedUpdBpl: "h_upd_bpl = heap_upd_bpl (Var (heap_var Tr)) (Var nullConst) e_ploc_bpl (Var new_kfm_var)
                                      [pred_ty, TConSingle (TKnownFoldedMaskId TyRep)]" and

    KFMOrigTrueSynProp1: "\<And>\<tau>. boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom fun_decls) (new_kfm_prop_orig_bpl[0 \<mapsto>\<^sub>\<tau> \<tau>])" and
    KFMOrigTrueSynProp2: "\<And>\<tau>. boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom fun_decls) new_kfm_prop_orig_bpl" and
    KFMFoldTrueSynProp1: "\<And>\<tau>. boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom fun_decls) (new_kfm_prop_fold_bpl[0 \<mapsto>\<^sub>\<tau> \<tau>])" and
    KFMFoldTrueSynProp2: "\<And>\<tau>. boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom fun_decls) new_kfm_prop_fold_bpl" and
    KFMNewTrueSynProp1: "\<And>\<tau>. boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom fun_decls) (new_kfm_prop_rhs_bpl[0 \<mapsto>\<^sub>\<tau> \<tau>])" and
    KFMNewTrueSynProp2: "\<And>\<tau>. boogie_expr_prop_sat_rec (boogie_expr_used_funs_in_dom fun_decls) new_kfm_prop_rhs_bpl" and

    LookupTyTemp: "lookup_var_decl (var_context ctxt_bpl) new_kfm_var = Some (TConSingle (TKnownFoldedMaskId TyRep), None)" and

    PredType: "pred_snap_field_type TyRep pid = Some pred_ty" and
    PredTypeSynProp: "\<And>\<tau>. pred_ty[0 \<mapsto>\<^sub>\<tau> \<tau>]\<^sub>\<tau> = pred_ty" and
    PredTypeFold: "pred_snap_field_type TyRep pid_fold = Some pred_fold_ty" and
    PredTypeFoldSynProp: "\<And>\<tau>. pred_fold_ty[0 \<mapsto>\<^sub>\<tau> \<tau>]\<^sub>\<tau> = pred_fold_ty" and

    PlocRel: "ploc_sm_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and
    PlocSynProp1: "\<And>\<tau>. e_ploc_bpl[0 \<mapsto>\<^sub>\<tau> \<tau>] = e_ploc_bpl" and
    PlocSynProp2: "boogie_expr_prop_sat_rec (boogie_expr_no_var new_kfm_var) e_ploc_bpl" and
    PlocSynProp3: "boogie_expr_prop_sat_rec boogie_expr_no_binder e_ploc_bpl" and

    PlocFoldRel: "ploc_sm_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_fold_vpr pid_fold e_ploc_fold_bpl" and
    PlocFoldSynProp1: "\<And>\<tau>. e_ploc_fold_bpl[0 \<mapsto>\<^sub>\<tau> \<tau>] = e_ploc_fold_bpl" and
    PlocFoldSynProp2: "boogie_expr_prop_sat_rec (boogie_expr_no_var new_kfm_var) e_ploc_fold_bpl" and
    PlocFoldSynProp3: "boogie_expr_prop_sat_rec boogie_expr_no_binder e_ploc_fold_bpl" and

    \<comment> \<open>The above required properties could be lifted. The reason for these properties is we
        require @{const ploc_sm_rel_vpr_bpl'} too soon, instead of proving it after we already
        update \<open>new_kfm_var\<close>.\<close>

    PMaskReadSubstWf: "\<And>a b c d \<tau>. pmask_read_bpl a b c d[0 \<mapsto>\<^sub>\<tau> \<tau>] = pmask_read_bpl (a[0 \<mapsto>\<^sub>\<tau> \<tau>]) (b[0 \<mapsto>\<^sub>\<tau> \<tau>]) (c[0 \<mapsto>\<^sub>\<tau> \<tau>]) (map (\<lambda>x. x[0 \<mapsto>\<^sub>\<tau> \<tau>]\<^sub>\<tau>) d)" and
    HeapReadSubstWf: "\<And>a b c d \<tau>. heap_read_bpl a b c d[0 \<mapsto>\<^sub>\<tau> \<tau>] = heap_read_bpl (a[0 \<mapsto>\<^sub>\<tau> \<tau>]) (b[0 \<mapsto>\<^sub>\<tau> \<tau>]) (c[0 \<mapsto>\<^sub>\<tau> \<tau>]) (map (\<lambda>x. x[0 \<mapsto>\<^sub>\<tau> \<tau>]\<^sub>\<tau>) d)" and

    KFMOrigReadSubstWf: "\<And>\<tau>. pmask_orig_bpl[0 \<mapsto>\<^sub>\<tau> \<tau>] = pmask_orig_bpl" and

    TempFresh: "new_kfm_var \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union>
                              ran (var_translation Tr) \<union>
                              ran (field_translation Tr) \<union>
                              range (const_repr Tr) \<union>
                              dom AuxPred" and

    StateConsOn: "consistent_state_rel_opt (state_rel_opt Tr)" and

    PermPosConstExpr: "\<And>\<omega>. ctxt_vpr, None \<turnstile> \<langle>e_p_fold_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> p > 0"
 and
    KFPosOffP: "\<not> kf_pos_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
  shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and>
                               pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr
                                 (Atomic (AccPredicate pid_fold e_args_fold_vpr (PureExp e_p_fold_vpr))) \<omega>)
                     (\<lambda>\<omega> ns. R' \<omega> ns)
                     (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                     (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                     P ctxt_bpl
                     (BigBlock name (Havoc new_kfm_var #
                                     Assume new_kfm_prop_bpl #
                                     Assign hvar h_upd_bpl #
                                     cs) str tr, cont)
                     (BigBlock name cs str tr, cont)" (is "rel_general ?R\<^sub>0 _ _ _ _ _ ?\<gamma> ?\<gamma>'")

proof (rule rel_intro; blast?)
  fix \<omega> ns \<omega>'
  assume "?R\<^sub>0 \<omega> ns" and "\<omega> = \<omega>'"
  hence "R \<omega> ns"
    by blast

  from \<open>?R\<^sub>0 \<omega> ns\<close>[THEN conjunct2, THEN pred_kfm_sat_premiseD]
  obtain nm_exh p\<^sub>s nm\<^sub>s where
    sub: "get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p\<^sub>s,nm\<^sub>s)" and
    "nm_exh \<le> nm\<^sub>s" and
    diff_sat: "sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (Atomic (AccPredicate pid_fold e_args_fold_vpr (PureExp e_p_fold_vpr)))" and
    diff_extcons: "consistent_external ctxt_vpr (\<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_exh \<rparr>)"
    by blast

  then obtain v_args_fold_vpr v_p_fold_vpr pdecl_fold pbody_fold where
    e_args_fold_eval: "red_pure_exps_total ctxt_vpr None e_args_fold_vpr \<omega> (Some v_args_fold_vpr)" and
    e_p_fold_eval: "ctxt_vpr, None \<turnstile> \<langle>e_p_fold_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_fold_vpr)" and
    "v_p_fold_vpr \<ge> 0" and
    "get_mh_nm nm_exh = zero_mask" and
    "get_mp_nm nm_exh = singleton_mp (pid_fold,v_args_fold_vpr) (Abs_preal v_p_fold_vpr)" and
    "ViperLang.predicates (program_total ctxt_vpr) pid_fold = Some pdecl_fold" and
    v_args_fold_typed: "vals_well_typed (absval_interp_total ctxt_vpr) v_args_fold_vpr (ViperLang.predicate_decl.args pdecl_fold)" and
    pdecl_fold_body: "predicate_decl.body pdecl_fold = Some pbody_fold"
    by (fastforce elim: SatAccPred_case)

  obtain hb where
    lookup_heap: "lookup_var (var_context ctxt_bpl) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
    lookup_heap_ty: "lookup_var_ty (var_context ctxt_bpl) (heap_var Tr) = Some (TConSingle (THeapId TyRep))" and
    heap_ty: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
    using state_rel_obtain_heap[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    by metis
  then obtain kfm kfm_fold where
    kfm: "hb (Null, PredKnownFoldedField (pid, v_args_vpr)) = Some (AbsV (AKnownFoldedMask kfm))" and
    kfm_fold: "hb (Null, PredKnownFoldedField (pid_fold, v_args_fold_vpr)) = Some (AbsV (AKnownFoldedMask kfm_fold))"
    using state_rel_heap_knownfolded_var_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    unfolding heap_knownfolded_var_rel_def
    using lookup_heap
    by fastforce+

  have hb_normal_fields: "knownfolded_masks_normal_fields hb"
    by (rule heap_knownfolded_var_rel_masks_normal_fields
               [OF state_rel_heap_knownfolded_var_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>]] lookup_heap])

  let ?new_kfm = "\<lambda>l. kfm l \<or> kfm_fold l"
  let ?ns' = "update_var (var_context ctxt_bpl) ns new_kfm_var (AbsV (AKnownFoldedMask ?new_kfm))"

  have new_kfm_normal: "\<And>r f. ?new_kfm (r, f) \<Longrightarrow> is_NormalField f"
    using knownfolded_masks_normal_fields_elim[OF hb_normal_fields kfm]
          knownfolded_masks_normal_fields_elim[OF hb_normal_fields kfm_fold]
    by blast

  have "\<And>\<tau> \<tau>' r.
          type_of_val (type_interp ctxt_bpl) r = instantiate (\<tau>' # \<tau> # rtype_interp ctxt_bpl) (TConSingle (TRefId TyRep)) \<Longrightarrow>
          \<exists>!x. r = AbsV (ARef x)"
    apply (simp add: TyInterpEq)
    using all_inversion_type_of_vbpl_val[OF WfTyRep]
    by blast+

  have "\<And>\<tau> \<tau>' r.
          type_of_val (type_interp ctxt_bpl) r = instantiate (\<tau>' # \<tau> # rtype_interp ctxt_bpl) (TCon (TFieldId TyRep) [TVar 1, TVar 0]) \<Longrightarrow>
          \<exists>!x. r = AbsV (AField x)"
    apply (simp add: TyInterpEq)
    using all_inversion_type_of_vbpl_val[OF WfTyRep]
    by blast+

  from PlocRel[unfolded ploc_sm_rel_vpr_bpl'_def] \<open>?R\<^sub>0 \<omega> ns\<close>[unfolded pred_kfm_sat_premise_def]
  have ploc_bpl_eval: "red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredKnownFoldedField (pid, v_args_vpr))))"
    using evals_with_None
    by blast

  from PlocFoldRel[unfolded ploc_sm_rel_vpr_bpl'_def] \<open>?R\<^sub>0 \<omega> ns\<close>[unfolded pred_kfm_sat_premise_def] e_args_fold_eval
  have ploc_fold_bpl_eval: "red_expr_bpl ctxt_bpl e_ploc_fold_bpl ns (AbsV (AField (PredKnownFoldedField (pid_fold, v_args_fold_vpr))))"
    unfolding pred_ty_correct_premise_def
    using \<open>program.predicates (program_total ctxt_vpr) pid_fold = Some pdecl_fold\<close> v_args_fold_typed
    by blast

  have "red_ast_bpl P ctxt_bpl (?\<gamma>, Normal ns) ((BigBlock name (Assign hvar h_upd_bpl # cs) str tr, cont), Normal (update_var (var_context ctxt_bpl) ns new_kfm_var (AbsV (AKnownFoldedMask ?new_kfm))))"
    apply (rule red_ast_bpl_havoc_assume)
       apply fact
      apply (simp add: TyInterpEq)
     apply simp
    apply (unfold \<open>new_kfm_prop_bpl = _\<close>)
    apply (rule RedForallT_True)
    apply (rule RedForallT_True)
    apply (rule RedForAllTrue)
    apply (rename_tac rr)
    apply (rule RedForAllTrue)
    apply (rename_tac ff)
    apply (simp del: full_ext_env.simps)
    apply (subst (asm) TyInterpEq)
    apply (subst (asm) TyInterpEq)
    apply (frule ref_inversion_type_of_vbpl_val[OF WfTyRep])
    apply (erule exE)
    apply (rename_tac r)
    apply (frule field_inversion_type_of_vbpl_val[OF WfTyRep])
     apply simp
    apply (erule exE)
    apply (rename_tac f)
    apply (unfold \<open>new_kfm_prop_body_bpl = _\<close>)
    apply (rule_tac ?v1.0="LitV (LBool (?new_kfm (r,f)))" in RedBinOp)
      apply (unfold \<open>new_kfm_prop_lhs_bpl = _\<close>)
      apply (rule_tac ?v1.0="LitV (LBool (kfm (r,f)))" in RedBinOp)
        apply (rule boogie_expr_eval_subst_one_type_var(1)[where ?\<Omega>\<^sub>p="[]" and ?k=0, unfolded append_Nil])
    using TyInterpEq WfTyRep type_of_vbpl_val_closed
               apply auto[1]
    using FunInterp TyInterpEq
              apply force
             apply simp
            prefer 2
            apply simp
           prefer 2
           apply simp

\<comment> \<open>LHS of OR\<close>
          apply (rule boogie_expr_eval_subst_one_type_var(1)[where ?\<Omega>\<^sub>p="[]" and ?k=0, unfolded append_Nil])
    using TyInterpEq WfTyRep type_of_vbpl_val_closed
                 apply auto[1]
    using FunInterp TyInterpEq
                apply force
               apply simp
              prefer 2
              apply simp
             prefer 2
             apply simp
            apply (subst \<open>new_kfm_prop_orig_bpl = _\<close>)
            apply (simp add: PMaskReadSubstWf del: full_ext_env.simps type_of_val.simps)
            apply (rule_tac ?r=r and ?f=f in pmask_read_wf_apply[OF PMaskReadWf, where ?m=kfm and ?field_tcon="TFieldId TyRep"])
                apply simp
               apply (unfold \<open>pmask_orig_bpl = _\<close>)
               apply (simp add: HeapReadSubstWf del: full_ext_env.simps type_of_val.simps)
               apply (rule_tac ?r=Null and ?f="PredKnownFoldedField (pid, v_args_vpr)" in heap_read_wf_apply[OF HeapReadWf, where ?h=hb])
                    apply (simp add: kfm)
                   apply (rule RedVar)
                   apply (simp add: lookup_var_binder_upd)
    using HeapVar TempFresh lookup_heap
                   apply fastforce
    using heap_ty
                  apply fastforce
                 apply (rule RedVar)
                 apply (simp add: lookup_var_binder_upd)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] NullConst TempFresh
                 apply fastforce
                apply (simp add: PlocSynProp1 del: full_ext_env.simps type_of_val.simps)
                apply (rule boogie_expr_eval_binder_state(1))
                 apply (rule boogie_expr_eval_binder_state(1))
                  apply (rule boogie_expr_eval_update_var(1))
                   apply (rule ploc_bpl_eval)
                  apply (rule PlocSynProp2)
                 apply (rule PlocSynProp3)
                apply (rule PlocSynProp3)
               apply (simp add: PredTypeSynProp PredType)
              apply (rule RedBVar)
              apply simp
             apply (rule RedBVar)
    using TyInterpEq WfTyRep field_inversion_type_of_vbpl_val
             apply fastforce
            apply (cut_tac ?k=0 and ?\<tau>=\<tau>' and ?\<tau>'=\<tau> in closed_substT)
             apply simp
            apply simp
            apply (metis list.distinct(1) snd_conv surjective_pairing vbpl_absval_ty.simps vbpl_absval_ty_not_dummy vbpl_absval_ty_opt.simps(2))
           apply simp
          apply (rule KFMOrigTrueSynProp1)
         apply simp
        apply (rule KFMOrigTrueSynProp2)

\<comment> \<open>RHS of OR\<close>
       apply (rule boogie_expr_eval_subst_one_type_var(1)[where ?\<Omega>\<^sub>p="[]" and ?k=0, unfolded append_Nil])
    using TyInterpEq WfTyRep type_of_vbpl_val_closed
              apply auto[1]
    using FunInterp TyInterpEq
             apply force
            apply simp
           prefer 2
           apply simp
          prefer 2
          apply simp
         apply (rule boogie_expr_eval_subst_one_type_var(1)[where ?\<Omega>\<^sub>p="[]" and ?k=0, unfolded append_Nil])
    using TyInterpEq WfTyRep type_of_vbpl_val_closed
                apply auto[1]
    using FunInterp TyInterpEq
               apply force
              apply simp
             prefer 2
             apply simp
            prefer 2
            apply simp
           apply (subst \<open>new_kfm_prop_fold_bpl = _\<close>)
           apply (simp add: PMaskReadSubstWf del: full_ext_env.simps type_of_val.simps)
           apply (rule_tac ?r=r and ?f=f in pmask_read_wf_apply[OF PMaskReadWf, where ?m=kfm_fold and ?field_tcon="TFieldId TyRep"])
               apply simp
              apply (unfold \<open>pmask_fold_bpl = _\<close>)
              apply (simp add: HeapReadSubstWf del: full_ext_env.simps type_of_val.simps)
              apply (rule_tac ?r=Null and ?f="PredKnownFoldedField (pid_fold, v_args_fold_vpr)" in heap_read_wf_apply[OF HeapReadWf, where ?h=hb])
                   apply (simp add: kfm_fold)
                  apply (rule RedVar)
                  apply (simp add: lookup_var_binder_upd)
    using HeapVar TempFresh lookup_heap
                  apply fastforce
    using heap_ty
                 apply fastforce
                apply (rule RedVar)
                apply (simp add: lookup_var_binder_upd)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] NullConst TempFresh
                apply fastforce
               apply (simp add: PlocFoldSynProp1 del: full_ext_env.simps type_of_val.simps)
               apply (rule boogie_expr_eval_binder_state(1))
                apply (rule boogie_expr_eval_binder_state(1))
                 apply (rule boogie_expr_eval_update_var(1))
                  apply (rule ploc_fold_bpl_eval)
                 apply (rule PlocFoldSynProp2)
                apply (rule PlocFoldSynProp3)
               apply (rule PlocFoldSynProp3)
              apply (simp add: PredTypeFoldSynProp PredTypeFold)
             apply (rule RedBVar)
             apply simp
            apply (rule RedBVar)
    using TyInterpEq WfTyRep field_inversion_type_of_vbpl_val
            apply fastforce
           apply (cut_tac ?k=0 and ?\<tau>=\<tau>' and ?\<tau>'=\<tau> in closed_substT)
            apply simp
           apply simp
           apply (metis list.distinct(1) snd_conv surjective_pairing vbpl_absval_ty.simps vbpl_absval_ty_not_dummy vbpl_absval_ty_opt.simps(2))
          apply simp
         apply (rule KFMFoldTrueSynProp1)
        apply simp
       apply (rule KFMFoldTrueSynProp2)
      apply simp

\<comment> \<open>RHS of IMP\<close>
     apply (rule boogie_expr_eval_subst_one_type_var(1)[where ?\<Omega>\<^sub>p="[]" and ?k=0, unfolded append_Nil])
    using TyInterpEq WfTyRep type_of_vbpl_val_closed
            apply auto[1]
    using FunInterp TyInterpEq
           apply force
          apply simp
         prefer 2
         apply simp
        prefer 2
        apply simp
       apply (rule boogie_expr_eval_subst_one_type_var(1)[where ?\<Omega>\<^sub>p="[]" and ?k=0, unfolded append_Nil])
    using TyInterpEq WfTyRep type_of_vbpl_val_closed
              apply auto[1]
    using FunInterp TyInterpEq
             apply force
            apply simp
           prefer 2
           apply simp
          prefer 2
          apply simp
         apply (subst \<open>new_kfm_prop_rhs_bpl = _\<close>)
         apply (simp add: PMaskReadSubstWf del: full_ext_env.simps type_of_val.simps)
         apply (rule_tac ?r=r and ?f=f in pmask_read_wf_apply[OF PMaskReadWf, where ?m="?new_kfm" and ?field_tcon="TFieldId TyRep"])
             apply simp
            apply (rule RedVar)
            apply (simp add: lookup_var_binder_upd)
           apply (rule RedBVar)
           apply simp
          apply (rule RedBVar)
    using TyInterpEq WfTyRep field_inversion_type_of_vbpl_val
          apply fastforce
         apply (cut_tac ?k=0 and ?\<tau>=\<tau>' and ?\<tau>'=\<tau> in closed_substT)
          apply simp
         apply simp
         apply (metis list.distinct(1) snd_conv surjective_pairing vbpl_absval_ty.simps vbpl_absval_ty_not_dummy vbpl_absval_ty_opt.simps(2))
        apply simp
       apply (rule KFMNewTrueSynProp1)
      apply simp
     apply (rule KFMNewTrueSynProp2)
    apply simp
    done

  let ?hb'' = "hb( (Null, PredKnownFoldedField (pid, v_args_vpr)) \<mapsto> AbsV (AKnownFoldedMask ?new_kfm) )"
  let ?ns'' = "update_var (var_context ctxt_bpl) ns hvar (AbsV (AHeap ?hb''))"

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl (?\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_transitive)
      apply fact
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (THeapId TyRep)" and ?v="AbsV (AHeap ?hb'')"])
    using lookup_heap_ty \<open>hvar = _\<close>
       apply blast
      apply (simp add: TyInterpEq)
      apply (meson heap_bpl_well_typed_elim heap_ty)
    unfolding \<open>h_upd_bpl = _\<close>
     apply (rule heap_update_wf_apply[OF HeapUpdateWf, where ?h=hb and ?r=Null and ?f="PredKnownFoldedField (pid,v_args_vpr)"])
           apply (rule RedVar)
    using HeapVar TempFresh lookup_heap
           apply auto[1]
          apply fact
         apply (rule RedVar)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] NullConst TempFresh
         apply auto[1]
        apply (simp add: PlocSynProp2 boogie_expr_eval_update_var(1) ploc_bpl_eval)
       apply (simp add: PredType)
      apply (rule RedVar)
      apply simp
     apply simp
    apply (rule StateRelOut)
    apply (subst \<open>hvar = _\<close>)
    apply (rule kfm_update_state_rel)
        apply (rule state_rel_independent_var)
    using StateRelIn \<open>R \<omega> ns\<close> \<open>\<omega> = \<omega>'\<close>
            apply blast
           apply (rule TempFresh)
          apply (simp add: TyInterpEq)
         apply (simp add: lookup_var_ty_def LookupTyTemp)
        apply (simp add: TyInterpEq)
    using TempFresh lookup_heap
       apply force
    subgoal
      unfolding heap_knownfolded_rel_def
    proof (rule allI | rule impI)+
      fix lp kfm\<^sub>c l field_ty_vpr field_bpl
      assume 1: "kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))"
         and 2: "?hb'' (Null, PredKnownFoldedField lp) = Some (AbsV (AKnownFoldedMask kfm\<^sub>c))"
         and 3: "declared_fields Pr (snd l) = Some field_ty_vpr"
         and 4: "field_translation Tr (snd l) = Some field_bpl"
         and 5: "kfm\<^sub>c (Address (fst l), NormalField field_bpl field_ty_vpr)"
      hence hb_kfm_rel: "heap_knownfolded_rel Pr (field_translation Tr) (get_nm_total_full \<omega>') hb"
        using state_rel_heap_knownfolded_var_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
        unfolding heap_knownfolded_var_rel_def
        by (simp add: \<open>\<omega> = \<omega>'\<close> lookup_heap)
      show "pred_folds_perm lp l (get_nm_total_full \<omega>')"
      proof (cases "lp = (pid, v_args_vpr)")
        case True
        hence "kfm\<^sub>c = ?new_kfm"
          using 2
          by auto
        from 5[unfolded \<open>kfm\<^sub>c = _\<close>]
        show ?thesis
        proof (elim disjE)
          assume "kfm (Address (fst l), NormalField field_bpl field_ty_vpr)"
          thus ?thesis
            using 3 4 True hb_kfm_rel kfm
            unfolding heap_knownfolded_rel_def
            by blast
        next
          assume "kfm_fold (Address (fst l), NormalField field_bpl field_ty_vpr)"
          hence loc_fold: "pred_folds_perm (pid_fold, v_args_fold_vpr) l (get_nm_total_full \<omega>')"
            using 3 4 hb_kfm_rel kfm_fold
            unfolding heap_knownfolded_rel_def
            by blast
          have \<omega>_extcons: "consistent_external (total_context.make Pr (\<lambda>_. None) (domain_type TyRep)) (get_total_full \<omega>')"
            using StateConsOn StateRelIn \<open>R \<omega> ns\<close> state_rel_consistent \<open>\<omega> = \<omega>'\<close>
            by blast
          have "v_p_fold_vpr = p"
            using PermPosConstExpr e_p_fold_eval eval_is_deterministic(1)
            by blast
          then obtain nm_exh_sub where nm_exh_sub: "get_fnm_nm nm_exh (pid_fold, v_args_fold_vpr) = Some (Abs_posreal (Abs_preal p), nm_exh_sub)"
            using fun_cong[OF \<open>get_mp_nm nm_exh = _\<close>, of "(pid_fold, v_args_fold_vpr)", simplified]
            by (metis PermPosConstExpr comp_def get_mp_nm.simps obtain_lpm_from_mp positive_real_preal preal_not_0_gt_0)
          have fold_extcons: "consistent_external_wrt_ploc ctxt_vpr (\<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = nm_exh_sub \<rparr>) (pid_fold, v_args_fold_vpr) (Abs_preal v_p_fold_vpr)"
            using diff_extcons SatAll_case nm_exh_sub \<open>v_p_fold_vpr = p\<close>
            by (metis (mono_tags, lifting) \<open>get_mp_nm nm_exh = _\<close> comp_apply fst_conv get_mp_nm.simps option_fold.simps(1) singleton_mp.elims total_state.select_convs(2) total_state.update_convs(2))
          obtain p\<^sub>s' nm\<^sub>s' where "get_fnm_nm nm\<^sub>s (pid_fold, v_args_fold_vpr) = Some (p\<^sub>s',nm\<^sub>s')" and "nm_exh_sub \<le> nm\<^sub>s'"
            using \<open>nm_exh \<le> nm\<^sub>s\<close>[unfolded less_eq_nested_mask_def] nm_larger_sub_larger_not_None[OF \<open>nm_exh \<le> nm\<^sub>s\<close> nm_exh_sub]
            by blast
          show ?thesis
            unfolding \<open>lp = _\<close>
            apply (rule ContainsPermDirect)
            using sub
             apply (simp add: \<open>\<omega> = \<omega>'\<close>)
            apply (rule ContainsLocNested)
             apply fact
            apply (rule contains_heap_loc_stable_larger_nm)
             prefer 2
             apply fact
            apply (rule extcons_loc_set_equal_rec[OF \<omega>_extcons loc_fold[simplified] _ fold_extcons, simplified])
            using PermPosConstExpr \<open>v_p_fold_vpr = p\<close> positive_real_preal preal_not_0_gt_0
              apply force
             apply (simp add: \<open>\<omega> = \<omega>'\<close>)
            using ProgEq total_context.simps(1) total_context.defs(1)
            by metis
        qed
      next
        case False
        hence "hb (Null, PredKnownFoldedField lp) = ?hb'' (Null, PredKnownFoldedField lp)"
          by simp
        then show ?thesis
          using hb_kfm_rel 2 3 4 5
          unfolding heap_knownfolded_rel_def
          by presburger
      qed
    qed
     apply (simp add: TyInterpEq)
    using heap_bpl_well_typed_elim heap_ty
     apply fastforce
    apply (simp add: HeapVarDefSame)
    using new_kfm_normal
     apply blast
    apply (rule KFPosOffP)
    done
qed


end
