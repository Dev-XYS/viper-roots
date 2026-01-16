theory PredicateRel
  imports InhaleRel ExhaleRel StmtRel TotalExtConsPreservation BoogieSyntaxBasedProperties
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
      by (metis (no_types, lifting) * Abs_preal_inverse MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def mem_Collect_eq plus_preal.rep_eq prod.inject vb_field.simps(2))

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
      using state_rel_heap_knownfolded_var_rel[OF InitRel] LookupMask \<open>\<omega>' = _\<close>
      by (metis (no_types, lifting) InitRel' MaskVar heap_knownfolded_var_rel_stable_larger_\<omega> mask_var_disjoint state_rel_state_rel0 update_var_other)

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
      and SelfFraming: "\<And>q. assertion_self_framing_store ctxt StateCons (syntactic_mult q pbody) (nth_option vs)"
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

  have Framed: "\<And>q. assertion_framing_state ctxt StateCons (syntactic_mult q pbody)
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
         apply (simp add: assms(9))
        apply simp
    using final_intcons WfCons[simplified wf_total_consistency_def]
       apply (simp add: assms(10))
    using WfCons[unfolded wf_total_consistency_def]
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
  with SelfFraming have FramingArgs: "\<And>p. assertion_self_framing_store ctxt_vpr StateCons (syntactic_mult p pbody) (nth_option v_args)"
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
    using FramingArgs[of p, unfolded assertion_self_framing_store_def, simplified]
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
                    exhale_pred_acc_rel_assms ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args v_p \<omega> \<omega> \<and>
                    exhale_pred_acc_rel_perm_success ctxt_vpr StateCons \<omega> pred_id v_args v_p)
                 (\<lambda>\<omega>.
                    exhale_pred_acc_rel_assms ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args v_p \<omega> \<omega> \<and>
                    \<not> exhale_pred_acc_rel_perm_success ctxt_vpr StateCons \<omega> pred_id v_args v_p)
                 P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and UpdExhRel:
            "\<And>v_args v_p.
               rel_general (R' v_args v_p) R  \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                 (\<lambda>\<omega> \<omega>'. exhale_pred_acc_normal_premise ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args v_p \<omega> \<omega> \<omega>')
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

  have eval_ok: "exhale_pred_acc_rel_assms ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args p \<omega> \<omega>"
    by (simp add: args_well_ty eval_e_args eval_e_p exhale_pred_acc_rel_assms_def pdecl pred_ty_correct_premise_def)
  moreover have perm_ok: "exhale_pred_acc_rel_perm_success ctxt_vpr StateCons \<omega> pred_id v_args p"
    unfolding exhale_pred_acc_rel_perm_success_def
    by (metis (full_types) Abs_preal_inverse \<open>RNormal \<omega>' = _\<close> \<open>mp = _\<close> exh_if_total_normal less_eq_preal.rep_eq mem_Collect_eq)
  ultimately obtain ns\<^sub>3 where "R' v_args p \<omega> ns\<^sub>3" and Red3: "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>\<^sub>3, Normal ns\<^sub>3)"
    using rel_success_elim[OF CorrectPermRel \<open>R \<omega> ns\<^sub>2\<close>]
    by blast

  have "exhale_pred_acc_normal_premise ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args p \<omega> \<omega> \<omega>'"
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

  shows "rel_general R R'
           (\<lambda>\<omega> \<omega>'. exhale_pred_acc_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr p \<omega> \<omega> \<omega>')
           (\<lambda>_. False) P ctxt_bpl
           (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
           (BigBlock name cs str tr, cont)"

  apply (rule rel_intro)
   prefer 2
   apply blast
proof -
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and *: "exhale_pred_acc_normal_premise ctxt_vpr StateCons pid e_args_vpr e_p_vpr v_args_vpr p \<omega> \<omega> \<omega>'"

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
    using total_consistency_ctxt_wf(1)[OF WfCons] ProgEq
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
    using KFRelOff heap_knownfolded_var_rel_def
            apply (metis InitRel' MaskVar heap_var_disjoint state_rel_heap_knownfolded_var_rel state_rel_state_rel0 update_var_apply)
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
     \<forall>\<omega>def \<omega> ns v_args_vpr. R \<omega> ns \<longrightarrow>
         red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr) \<longrightarrow>
         pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<longrightarrow>
         red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredKnownFoldedField (pid,v_args_vpr))))"


lemma exp_result_predicate_loc_sm':
  assumes
    CtxtFunWf: "ctxt_wf Pr TyRep F FunMap FunDom ctxt_bpl" and
    StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>_def \<omega> ns" and
    RedArgsVpr: "red_pure_exps_total ctxt_vpr (Some \<omega>_def1) e_args_vpr \<omega> (Some v_args_vpr)" and
    ArgsWellTy: "pred_ty_correct_premise ctxt_vpr pid v_args_vpr" and
    FunName: "FunMap (FPredicateSMLoc pid tys_bpl) = pred_loc_fun_name \<and> FPredicateSMLoc pid tys_bpl \<in> FunDom" and
    PredDecl: "program.predicates (program_total ctxt_vpr) pid = Some pdecl" and
    VprArgsTy: "predicate_decl.args pdecl = tys_vpr" and
    ArgsTyRel: "map (vpr_to_bpl_ty TyRep) tys_vpr = map Some tys_bpl" and
    ArgsRel: "list_all2 (exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl) ctxt_vpr ctxt_bpl) e_args_vpr e_args_bpl" and
    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep"
  shows "red_expr_bpl ctxt_bpl (FunExp pred_loc_fun_name [] e_args_bpl) ns (AbsV (AField (PredKnownFoldedField (pid,v_args_vpr))))"
proof -
  have "list_all2 (\<lambda>e v. ctxt_vpr, Some \<omega>_def1 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) e_args_vpr v_args_vpr"
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
      and "heap_knownfolded_var_rel (\<lparr> kf_turned_on = True \<rparr>) Pr (var_context ctxt_bpl) (field_translation Tr) (heap_var Tr) \<omega> ns"
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
    unfolding heap_knownfolded_var_rel_def
     apply (simp add: assms(2))
    using assms(3)
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
           apply (simp add: \<open>get_mh_nm nm'\<^sub>f l > 0\<close>)
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
                          state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega> ns" and
    StateRelOut: "\<And>\<omega> ns. state_rel_def_same Pr StateCons TyRep (enable_knownfolded_rel_opt Tr) AuxPred ctxt_bpl \<omega> ns \<Longrightarrow> R' \<omega> ns" and

    KFMOptTurnedOff: "\<not> kf_turned_on (knownfolded_state_rel_opt (state_rel_opt Tr))" and
    KFMNewOpt: "kf_turned_on kf_opt" and
    HeapVarDefSame: "heap_var_def Tr = heap_var Tr" and

    PlocRel: "ploc_sm_rel_vpr_bpl' R ctxt_vpr ctxt_bpl e_args_vpr pid e_ploc_bpl" and

    TyInterpEq: "type_interp ctxt_bpl = vbpl_absval_ty TyRep" and

    NullConst: "const_repr Tr CNull = nullConst" and
    ZeroPMaskConst: "const_repr Tr CKnownFoldedZeroMask = zeroPMask" and
    HeapVar: "hvar = heap_var Tr" and

    PredType: "pred_snap_field_type TyRep pid = Some pred_ty" and

    HeapUpdateWf: "heap_update_wf TyRep ctxt_bpl heap_upd_bpl" and

    KnownFoldedUpdBpl: "h_upd_bpl = heap_upd_bpl (Var (heap_var Tr)) (Var nullConst) e_ploc_bpl (Var zeroPMask)
                                      [pred_ty, TConSingle (TKnownFoldedMaskId TyRep)]"

  shows "rel_general (uncurry (\<lambda>\<omega>\<^sub>0 \<omega> ns. R \<omega> ns \<and>
                                         ctxt_vpr, (Some \<omega>\<^sub>0) \<turnstile> \<langle>e_p_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_vpr) \<and>
                                         red_pure_exps_total ctxt_vpr (Some \<omega>\<^sub>0) e_args_vpr \<omega> (Some v_args_vpr) \<and>
                                         pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
                                         unfold_rel ctxt_vpr pid v_args_vpr (Abs_preal v_p_vpr) (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>) \<and>
                                         heap_knownfolded_var_rel kf_opt Pr (var_context ctxt_bpl) (field_translation Tr) (heap_var Tr) \<omega>\<^sub>0 ns))
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
    "heap_knownfolded_var_rel kf_opt Pr (var_context ctxt_bpl) (field_translation Tr) (heap_var Tr) \<omega>\<^sub>0 ns"
    by (simp_all add: \<open>\<omega>\<^sub>0_\<omega> = (\<omega>\<^sub>0, \<omega>)\<close> \<open>hvar = _\<close>)

  with PlocRel[unfolded ploc_sm_rel_vpr_bpl'_def]
  have ploc_bpl_eval: "red_expr_bpl ctxt_bpl e_ploc_bpl ns (AbsV (AField (PredKnownFoldedField (pid, v_args_vpr))))"
    by blast

  obtain hb where
    lookup_heap: "lookup_var (var_context ctxt_bpl) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
    lookup_heap_ty: "lookup_var_ty (var_context ctxt_bpl) (heap_var Tr) = Some (TConSingle (THeapId TyRep))" and
    heap_ty: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
    using state_rel_obtain_heap[OF StateRelIn[OF \<open>R \<omega> ns\<close>]]
    by metis

  hence "heap_knownfolded_rel Pr (field_translation Tr) (get_nm_total (get_total_full \<omega>\<^sub>0)) hb"
    by (metis (no_types, opaque_lifting) Semantics.val.inject(2) \<open>heap_knownfolded_var_rel _ _ _ _ _ _ _\<close> get_nm_total_full.simps heap_knownfolded_var_rel_def option.inject vbpl_absval.inject(4) KFMNewOpt)

  let ?hb' = "hb( (Null, PredKnownFoldedField (pid, v_args_vpr)) \<mapsto> zero_knownfolded_mask )"

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
     apply (rule red_expr_red_exprs.RedVar)
    using state_rel_boogie_const_rel[OF StateRelIn[OF \<open>R \<omega> ns\<close>], unfolded boogie_const_rel_def] ZeroPMaskConst
    unfolding zero_knownfolded_mask_def
     apply fastforce
    apply simp
    done

  show "\<exists>ns'. red_ast_bpl P ctxt_bpl (?\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> uncurry (\<lambda>\<omega>\<^sub>0_\<omega>. R') \<omega>\<^sub>0_\<omega>' ns'"
    apply (rule exI, intro conjI)
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule RedAssign[where ?ty="TConSingle (THeapId TyRep)" and ?v="AbsV (AHeap ?hb')"])
    using lookup_heap_ty \<open>hvar = _\<close>
       apply blast
      apply (simp add: TyInterpEq zero_knownfolded_mask_def)
      apply (meson heap_bpl_well_typed_elim heap_ty)
     apply (simp add: h_upd_eval)
    unfolding \<open>\<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>'\<close>[symmetric] \<open>\<omega>\<^sub>0_\<omega> = (_, _)\<close>
    apply simp
    apply (rule StateRelOut)
    apply (rule turn_on_knownfolded_rel)
    unfolding zero_knownfolded_mask_def \<open>hvar = _\<close>
     apply (rule kfm_update_state_rel)
         apply (rule StateRelIn[OF \<open>R \<omega> ns\<close>])
        apply fact
    using KFMOptTurnedOff
       apply blast
    unfolding TyInterpEq
      apply simp
      apply (meson heap_bpl_well_typed_elim heap_ty)
     apply fact
    unfolding heap_knownfolded_var_rel_def
    apply (rule exI[of _ ?hb'])
    apply (intro conjI)
      apply (simp add: zero_knownfolded_mask_def)
    using \<open>heap_knownfolded_var_rel _ _ _ _ _ _ _\<close>
    unfolding heap_knownfolded_var_rel_def zero_knownfolded_mask_def
     apply (simp add: lookup_heap)
    apply simp
    apply (rule unfold_set_kfm_to_zero)
     apply fact+
    done
qed



subsection \<open>Fold\<close>


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

    hence direct_expr_eval_nofail: "\<And>res. red_pure_exps_total ctxt_vpr (Some ?\<omega>def_subst) (direct_sub_expressions_assertion A) ?\<omega>_subst res \<Longrightarrow> res \<noteq> None"
      sorry

    have "es = map (\<lambda>e. substitute_args_expr e e_args_vpr) (direct_sub_expressions_assertion A)"
      by (simp add: assms(3) substitute_subexpr_assertion_commute)

    from eval_with_substitution_rev(2)[OF args_eval _ _ _ _ direct_expr_eval_assms this]
    show False
      by (metis ArgsConstraint AssertionConstraint Ball_set_list_all direct_expr_eval_nofail assert_pred_subexp)
  qed
qed


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
      and BodyNoUnfolding: "no_unfolding_assertion (syntactic_mult p pbody)"  \<comment> \<open>Should be lifted soon.\<close>
      and PermSimp: "e_p_vpr = ELit (LPerm p)" \<comment> \<open>We only support literals as the permission.\<close>
      and PermPos: "p > 0"
      and StepWfSubexp: "exprs_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt_bpl (e_args_vpr @ [e_p_vpr]) \<gamma> \<gamma>\<^sub>2"
      and StepPermPos: "rel_general R R (=) (\<lambda>_. False) P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and StepExhale:
            "\<And>v_args_vpr v_p_vpr.
                exhale_rel (rel_ext_eq R) (\<lambda>\<omega>def \<omega> ns. R'' \<omega>def \<omega> ns)
                  (\<lambda>_ \<omega>def \<omega>. framing_exh ctxt_vpr StateCons (syntactic_mult p pbody) (\<omega>def\<lparr> get_store_total := nth_option v_args_vpr \<rparr>) (\<omega>\<lparr> get_store_total := nth_option v_args_vpr \<rparr>) \<and>
                              red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr))
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
                                    (\<exists>\<omega>def. red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr)) \<and>
                                    pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
                                    (\<exists>\<omega>1 nm_exh. \<omega> = add_to_lpm_nonzero_total_full \<omega>1 (pid,v_args_vpr) (Abs_posreal (Abs_preal v_p_vpr)) nm_exh \<and>
                                         sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr)))
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
      apply (metis CtxtPredSF PredBody PredDecl \<open>pdecl' = pdecl\<close> assertion_self_framing_def assertion_self_framing_store_def ctxt_pred_self_framing_inh_def full_total_state.cases_scheme full_total_state.select_convs(1) full_total_state.update_convs(1) update_nm_total_full_store_unchanged update_store_total.simps v_args_ty)
    unfolding plus_full_total_state_ext_def
     apply simp
    unfolding plus_total_state_ext_def
     apply simp
     apply (simp add: commutative core_is_smaller core_total_state_ext_def defined_def option.discI)
    using succ_refl
    by blast

  moreover have exh_subst: "red_exhale ctxt_vpr \<omega> (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega> (RNormal \<omega>1)"
    apply (rule exhale_with_substitution)
               apply (rule exh[unfolded \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close>])
              apply (rule \<open>\<omega>0 = _\<close>)+
            apply simp
           apply (rule v_args_eval)
          apply (simp add: \<open>\<omega>1 = _\<close>)
         apply (simp add: \<open>\<omega>1 = _\<close>)
        apply (simp add: \<open>\<omega>1 = _\<close>)
    using PredDecl WfCons \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close> \<open>pdecl' = pdecl\<close> \<open>predicate_decl.body pdecl' = Some pbody'\<close> ctxt_pred_syn_wf_def prat_non_negative syntactic_mult_supported total_consistency_ctxt_wf(1)
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
  moreover have "\<exists>\<omega>1 nm_exh. \<omega>' = add_to_lpm_nonzero_total_full \<omega>1 (pid,v_args) (Abs_posreal (Abs_preal v_p)) nm_exh \<and>
                             sat ctxt_vpr \<omega>' (get_mh_nm nm_exh) (get_mp_nm nm_exh) (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr)"
    apply (rule exI[of _ \<omega>1])
    apply (rule exI[of _ nm_exh])
    apply (intro conjI)
     apply fact
    apply (rule sat_nm_does_not_matter_for_supported_pred[where ?\<omega>\<^sub>1="\<omega>\<lparr> get_total_full := get_total_full \<omega>\<lparr> get_nm_total := 0 \<rparr> \<rparr>"])
       apply (rule exhale_diff_sat')
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
       apply (subst \<open>get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0\<close>)
    using \<open>\<omega>0 = \<omega>\<lparr>get_store_total := nth_option v_args\<rparr>\<close>
       apply simp
      apply simp
      apply (metis fold_rel_normal_only_changes_mask fold_rel)
     apply simp
     apply (metis fold_rel_normal_only_changes_mask fold_rel get_hh_total_full.simps)
    by fact
  have ns'_exists: "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>5, Normal ns\<^sub>5) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    apply (rule StepKFUpdate[THEN rel_success_elim, where ?\<omega>=\<omega>' and ?\<omega>'=\<omega>' and ?ns=ns\<^sub>5 and ?v_args_vpr1=v_args])
     prefer 2
     apply simp
    apply (intro conjI)
    using conjunct2[OF ns\<^sub>5]
       apply blast
      apply (rule exI[of _ \<omega>])
      apply (rule red_pure_exp_only_differ_on_mask(2)[where ?\<omega>'=\<omega>', OF v_args_eval])
    using ArgsRestriction
       apply (simp add: list_all_length)
      apply (metis fold_rel fold_rel_normal_only_changes_mask)
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
        apply (metis CtxtPredSF PredBody PredDecl \<open>pdecl' = pdecl\<close> assertion_self_framing_def assertion_self_framing_store_def ctxt_pred_self_framing_inh_def full_total_state.cases_scheme full_total_state.select_convs(1) full_total_state.update_convs(1) update_nm_total_full_store_unchanged update_store_total.simps v_args_ty)
      unfolding plus_full_total_state_ext_def
       apply simp
      unfolding plus_total_state_ext_def
       apply simp
       apply (simp add: commutative core_is_smaller core_total_state_ext_def defined_def option.discI)
      using succ_refl
      by blast

    moreover have exh_subst: "red_exhale ctxt_vpr \<omega> (substitute_args_assertion (syntactic_mult p pbody) e_args_vpr) \<omega> RFailure"
      apply (rule exhale_with_substitution_failure)
              apply (rule exh[unfolded \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close>])
             apply (rule \<open>\<omega>0 = _\<close>)+
           apply simp
          apply (rule v_args_eval)
      using PredDecl WfCons \<open>Rep_preal (Abs_preal v_p) = p\<close> \<open>pbody' = pbody\<close> \<open>pdecl' = pdecl\<close> \<open>predicate_decl.body pdecl' = Some pbody'\<close> ctxt_pred_syn_wf_def prat_non_negative syntactic_mult_supported total_consistency_ctxt_wf(1)
         apply blast
      using BodyNoUnfolding
        apply auto[1]
      by (simp_all add: ArgsRestriction)

    ultimately show ?thesis
      using StepExhale[THEN exhale_rel_failure_elim]
      by (metis ns\<^sub>2 ns\<^sub>3 red_ast_bpl_transitive snd_conv v_args_eval)
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
    ProgEq: "program_total ctxt_vpr = Pr"

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
    subgoal sorry
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
      by (metis (no_types, lifting) * Abs_preal_inverse MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def mem_Collect_eq plus_preal.rep_eq prod.inject vb_field.simps(2))

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

  shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and>
                               (\<exists>\<omega>def. red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr)) \<and>
                               pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
                               (\<exists>\<omega>1 nm_exh. \<omega> = add_to_lpm_nonzero_total_full \<omega>1 (pid,v_args_vpr) (Abs_posreal (Abs_preal v_p_vpr)) nm_exh \<and>
                                  sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (Atomic (Acc e_r_vpr f (PureExp e_p_vpr)))))
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

  from \<open>?R\<^sub>0 \<omega> ns\<close>
  obtain \<omega>1 nm_exh where
    \<omega>_is_add: "\<omega> = add_to_lpm_nonzero_total_full \<omega>1 (pid, v_args_vpr) (Abs_posreal (Abs_preal v_p_vpr)) nm_exh" and
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

  from PlocRel[unfolded ploc_sm_rel_vpr_bpl'_def] \<open>?R\<^sub>0 \<omega> ns\<close>
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

  let ?kfm' = "kfm((v_r_vpr, NormalField f_tr \<tau>) := True)"
  let ?hb' = "hb( (Null, PredKnownFoldedField (pid, v_args_vpr)) \<mapsto> AbsV (AKnownFoldedMask ?kfm') )"
  let ?ns' = "update_var (var_context ctxt_bpl) ns hvar (AbsV (AHeap ?hb'))"

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
    using exp_rel_vpr_bpl_elim[OF RefExpRel] eval_with_None_exists_\<omega>def[OF v_r_eval] ExpSyntax
       apply (metis \<open>R \<omega> ns\<close> val_rel_vpr_bpl.simps(3))
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

  from \<omega>_is_add
  obtain p nm where nm: "get_fnm_total_full \<omega> (pid, v_args_vpr) = Some (p, nm)"
    by fastforce
  hence "nm \<ge> nm_exh"
    unfolding \<omega>_is_add
    apply (cases "get_fnm_total_full \<omega>1 (pid, v_args_vpr)")
     apply simp_all
    using add.commute nm_sum_is_bigger
    by blast
  hence "get_mh_nm nm \<ge> get_mh_nm nm_exh"
    by (simp add: less_eq_nested_maskD)
  hence "get_mh_nm nm (addr, f) > 0"
    by (meson \<open>get_mh_nm nm_exh (addr, f) > 0\<close> dual_order.strict_trans1 le_funE)

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
        using nm[unfolded get_fnm_total_full.simps]
         apply force
        using True \<open>get_mh_nm nm (addr, f) > 0\<close>
        by blast
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
    StepLeft:
      "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and>
                             (\<exists>\<omega>def. red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr)) \<and>
                             pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
                             (\<exists>\<omega>1 nm_exh. \<omega> = add_to_lpm_nonzero_total_full \<omega>1 (pid,v_args_vpr) (Abs_posreal (Abs_preal v_p_vpr)) nm_exh \<and>
                                sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) A))
                   (\<lambda>\<omega> ns. R' \<omega> ns)
                   (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                   (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                   P ctxt_bpl \<gamma> \<gamma>\<^sub>2" and
    StepRight:
      "rel_general (\<lambda>\<omega> ns. R' \<omega> ns \<and>
                             (\<exists>\<omega>def. red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr)) \<and>
                             pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
                             (\<exists>\<omega>1 nm_exh. \<omega> = add_to_lpm_nonzero_total_full \<omega>1 (pid,v_args_vpr) (Abs_posreal (Abs_preal v_p_vpr)) nm_exh \<and>
                                sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) B))
                   (\<lambda>\<omega> ns. R'' \<omega> ns)
                   (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                   (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                   P ctxt_bpl \<gamma>\<^sub>2 \<gamma>'"

  shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and>
                               (\<exists>\<omega>def. red_pure_exps_total ctxt_vpr (Some \<omega>def) e_args_vpr \<omega> (Some v_args_vpr)) \<and>
                               pred_ty_correct_premise ctxt_vpr pid v_args_vpr \<and>
                               (\<exists>\<omega>1 nm_exh. \<omega> = add_to_lpm_nonzero_total_full \<omega>1 (pid,v_args_vpr) (Abs_posreal (Abs_preal v_p_vpr)) nm_exh \<and>
                                  sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (A && B)))
                     (\<lambda>\<omega> ns. R'' \<omega> ns)
                     (\<lambda>\<omega>\<^sub>0_\<omega> \<omega>\<^sub>0_\<omega>'. \<omega>\<^sub>0_\<omega> = \<omega>\<^sub>0_\<omega>')
                     (\<lambda>\<omega>\<^sub>0_\<omega>. False)
                     P ctxt_bpl \<gamma> \<gamma>'" (is "rel_general ?R\<^sub>0 _ _ _ _ _ _ _")

proof (rule rel_intro; blast?)
  fix \<omega> ns \<omega>'
  assume "?R\<^sub>0 \<omega> ns" and "\<omega> = \<omega>'"
  hence "R \<omega> ns"
    by blast

  from \<open>?R\<^sub>0 \<omega> ns\<close>
  obtain \<omega>1 nm_exh where
    \<omega>_is_add: "\<omega> = add_to_lpm_nonzero_total_full \<omega>1 (pid, v_args_vpr) (Abs_posreal (Abs_preal v_p_vpr)) nm_exh" and
    diff_sat: "sat ctxt_vpr \<omega> (get_mh_nm nm_exh) (get_mp_nm nm_exh) (A && B)"
    by blast

  then obtain mh\<^sub>A mp\<^sub>A mh\<^sub>B mp\<^sub>B where
    "mh_split (get_mh_nm nm_exh) mh\<^sub>A mh\<^sub>B" and
    "mp_split (get_mp_nm nm_exh) mp\<^sub>A mp\<^sub>B" and
    "sat ctxt_vpr \<omega> mh\<^sub>A mp\<^sub>A A" and
    "sat ctxt_vpr \<omega> mh\<^sub>B mp\<^sub>B B"
    by (auto elim: SatStar_case)

  from rel_success_elim[OF StepLeft] show
    "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R'' \<omega>' ns'"
    sorry
qed

end
