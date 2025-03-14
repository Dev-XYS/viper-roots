theory PredicateRel
  imports InhaleRel ExhaleRel StmtRel TotalExtConsPreservation
begin


subsection \<open>Inhale\<close>

definition pred_ty_correct_premise where
  "pred_ty_correct_premise ctxt pred_id vs \<equiv>
     \<exists>pred_decl. program.predicates (program_total ctxt) pred_id = Some pred_decl \<and>
                 vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pred_decl)"


lemma inhale_pred_non_empty_implies_well_typed:
  assumes "inhale_perm_single_pred ctxt StateCons \<omega> (pid,vs) p_opt \<noteq> {}"
  shows "pred_ty_correct_premise ctxt pid vs"
  using assms[unfolded inhale_perm_single_pred_def]
  unfolding pred_ty_correct_premise_def consistent_external_wrt_ploc.simps
  by fastforce


definition inhale_pred_normal_premise
  where "inhale_pred_normal_premise ctxt StateCons pred_id e_args e_p vs p \<omega> \<omega>' \<equiv>
       pred_ty_correct_premise ctxt pred_id vs \<and>
       red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some vs) \<and>
       ctxt, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and>
       p \<ge> 0 \<and>
       (let W' = inhale_perm_single_pred ctxt StateCons \<omega> (pred_id, vs) (Some (Abs_preal p)) in
         (W' \<noteq> {} \<and> \<omega>' \<in> W'))"


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
                         (inhale_pred_normal_premise ctxt_vpr StateCons pred_id e_args e_p vs p)
                         (\<lambda> \<omega>. False) P ctxt \<gamma>3 \<gamma>'" 
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
    have InhNormalPremise: "inhale_pred_normal_premise ctxt_vpr StateCons pred_id e_args e_p v_args p \<omega> \<omega>'"
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


lemma inhale_rel_pred_acc_upd_rel:
  assumes
    StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow>
                         state_rel_def_same Pr StateCons TyRep Tr
                           (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt \<omega> ns" and
              "temp_perm \<notin> dom AuxPred" and

    WfTyRep: "wf_ty_repr_bpl TyRep" and
    MaskVarDefSame: "mask_var_def Tr = mask_var Tr" and
    TyInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and

    NullConst: "const_repr Tr CNull = nullConst" and
    MaskVar: "m_bpl = mask_var Tr" and
    PredLocBpl: "e_ploc_bpl = FunExp ''P'' [] [e_arg_bpl]" and

    MaskUpdateWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    MaskReadWf: "mask_read_wf TyRep ctxt mask_read_bpl" and

    NewPermBpl: "new_perm = (mask_read_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl
                                  [TConSingle ''PredicateType_P'', TPrim TBool]) \<guillemotleft>Add\<guillemotright> (Var temp_perm)" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Var m_bpl) (Var nullConst) e_ploc_bpl new_perm
                                  [TConSingle ''PredicateType_P'', TPrim TBool]" and

    ArgRel: "exp_rel_vpr_bpl
                (state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt)
                ctxt_vpr ctxt e_arg_vpr e_arg_bpl" and

    PredFunInterp: "fun_interp ctxt ''P'' = Some (lift_fun_bpl (vbpl_absval_ty TyRep) (0, [TConSingle (TRefId TyRep)], TCon (TFieldId TyRep) [TCon ''PredicateType_P'' [], TPrim TBool]) predicate_loc_P)" and
    PredName: "pred_id = ''P''" and
    PredLookup: "ViperLang.predicates (program_total ctxt_vpr) pred_id = Some pdecl" and
    PredTyArgsLookup: "predicate_decl.args pdecl = [TRef]" and
    AbsInterpEq: "absval_interp_total ctxt_vpr = domain_type TyRep" and
    ProgEq: "program_total ctxt_vpr = Pr"

  shows "rel_general R
           (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt)
           (\<lambda> \<omega> \<omega>'. inhale_pred_normal_premise ctxt_vpr StateCons pred_id [e_arg_vpr] e_p_vpr vs p \<omega> \<omega>')
           (\<lambda> \<omega>. False) P ctxt
           (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
           (BigBlock name cs str tr, cont)"

  apply (rule rel_intro)
   prefer 2
   apply blast
proof -
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and *: "inhale_pred_normal_premise ctxt_vpr StateCons pred_id [e_arg_vpr] e_p_vpr vs p \<omega> \<omega>'"

  hence InitRel: "state_rel_def_same Pr StateCons TyRep Tr
                                     (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt \<omega> ns"
    using StateRel
    by blast

  hence InitRel': "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
    apply (rule state_rel_aux_pred_remove[where ?AuxPred="AuxPred(temp_perm \<mapsto> pred_eq (RealV p))" and ?AuxPred'=AuxPred])
    by (simp add: assms(2) map_le_def)

  from * have "length vs = 1"
    by (metis One_nat_def add.right_neutral add_Suc_right inhale_pred_normal_premise_def list.size(3) list.size(4) red_pure_exps_total_Some_lengthD)
  then obtain arg where "vs = [arg]"
    by (metis One_nat_def Suc_le_eq impossible_Cons length_greater_0_conv list.exhaust list.size(3) n_not_Suc_n)
  with * have 1: "inhale_pred_normal_premise ctxt_vpr StateCons pred_id [e_arg_vpr] e_p_vpr [arg] p \<omega> \<omega>'"
    by fast

  let ?ploc = "(pred_id,[arg])"

  obtain \<phi>_inh where \<omega>':
    "(p > 0 \<longrightarrow> consistent_external_wrt_ploc ctxt_vpr \<phi>_inh ?ploc (Abs_preal p)) \<and>
     get_hh_total \<phi>_inh = get_hh_total_full \<omega> \<and>
     \<omega>' = (if p = 0 then \<omega> else add_to_lpm_nonzero_total_full \<omega> ?ploc (Abs_posreal (Abs_preal p)) (get_nm_total \<phi>_inh)) \<and>
     StateCons \<omega>'"
    using 1[simplified inhale_pred_normal_premise_def inhale_perm_single_pred_def Let_def]
    by (smt (verit) mem_Collect_eq option_fold.simps(1) positive_real_preal pperm_pnone_pgt zero_preal.abs_eq)

  hence mh_same: "get_mh_total_full \<omega> = get_mh_total_full \<omega>'" and
        mp_rel: "get_mp_total_full \<omega>' = (get_mp_total_full \<omega>)( ?ploc := get_mp_total_full \<omega> ?ploc + Abs_preal p )"
     apply simp
    apply (cases "p = 0")
    using \<omega>' zero_preal_def
     apply force
    using \<omega>'[THEN conjunct2, THEN conjunct2, THEN conjunct1]
    apply (simp del: add_to_lpm_nonzero_total_full.simps get_mp_total_full.simps)
    using add_to_lpm_nonzero_total_full__mp
    by (metis 1 all_pos inhale_pred_normal_premise_def mem_Collect_eq order_le_less positive_real_preal posreal_to_preal(8))

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
      using 1 \<omega>' \<open>p \<noteq> 0\<close> inhale_pred_normal_premise_def
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
    LookupMask: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
    LookupMaskTy: "lookup_var_ty (var_context ctxt) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
    MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) (get_mp_total_full \<omega>) mb"
    using state_rel_obtain_mask[OF StateRel[OF \<open>R \<omega> ns\<close>]]
    by blast

  \<comment> \<open>Construct the value of the new permission from the Viper state.\<close>
  let ?np = "Rep_preal (get_mp_total_full \<omega> (pred_id,[arg])) + p"

  have LookupTempPerm: "lookup_var (var_context ctxt) ns temp_perm = Some (RealV p)"
    using state_rel_aux_pred_sat_lookup_2[OF StateRel[OF \<open>R \<omega> ns\<close>]]
    unfolding pred_eq_def
    by (metis (full_types) fun_upd_same)

  have null_eval: "red_expr_bpl ctxt (Var nullConst) ns (AbsV (ARef Null))"
    apply (rule red_expr_red_exprs.RedVar)
    by (metis NullConst StateRel \<open>R \<omega> ns\<close> boogie_const_rel_lookup boogie_const_val.simps(3) state_rel_boogie_const_rel)

  have e_arg_eval: "red_expr_bpl ctxt e_arg_bpl ns (val_rel_vpr_bpl arg)"
    using ArgRel[simplified exp_rel_vpr_bpl_def exp_rel_vb_single_def]
    by (metis 1 InitRel inhale_pred_normal_premise_def list.simps(3) nth_Cons_0 red_exp_list_normal_elim)

  have e_arg_type: "get_type (absval_interp_total ctxt_vpr) arg = TRef"
    using 1[simplified inhale_pred_normal_premise_def vals_well_typed_def, unfolded pred_ty_correct_premise_def vals_well_typed_def]
          PredTyArgsLookup PredLookup
    by auto
  then obtain arg_bpl where arg_bpl: "val_rel_vpr_bpl arg = AbsV (ARef arg_bpl)"
    by (metis has_type_get_type has_type_simps(8) val_rel_vpr_bpl.simps(3))

  have ploc_eval: "red_expr_bpl ctxt e_ploc_bpl ns (AbsV (AField (PredSnapshotField (pred_id, [arg]))))"
    apply (simp add: PredLocBpl)
    apply (rule red_expr_red_exprs.RedFunOp)
    using PredFunInterp
      apply blast
     apply (rule red_expr_red_exprs.RedExpListCons)
    using e_arg_eval
      apply blast
     apply (rule red_expr_red_exprs.RedExpListNil)
    apply (simp add: arg_bpl)
    using arg_bpl PredName e_arg_type has_type_get_type
    apply (simp add: lift_fun_bpl_def)
    by force

  have new_perm_eval: "red_expr_bpl ctxt new_perm ns (LitV (LReal ?np))"
    apply (simp add: NewPermBpl)
    apply (rule red_expr_red_exprs.RedBinOp[where ?v1.0="LitV (LReal (Rep_preal (get_mp_total_full \<omega> (pred_id,[arg]))))" and ?v2.0="LitV (LReal p)"])
      apply (rule mask_read_wf_apply[OF MaskReadWf, where ?m=mb and ?r=Null and ?f="PredSnapshotField (pred_id,[arg])"])
          apply (metis MaskRel mask_rel_def)
         apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
        apply (simp add: null_eval)
       apply (simp add: ploc_eval)
      apply force
     apply (fastforce intro: RedVar LookupTempPerm)
    by simp

  \<comment> \<open>Construct the new Boogie heap.\<close>
  let ?mb' = "mb( (Null, PredSnapshotField (pred_id,[arg])) := ?np )"

  have m_upd_bpl_red: "red_expr_bpl ctxt m_upd_bpl ns (AbsV (AMask ?mb'))"
    apply (subst \<open>m_upd_bpl = _\<close>)
    apply (rule mask_update_wf_apply[OF MaskUpdateWf])
        apply (simp add: LookupMask MaskVar red_expr_red_exprs.RedVar)
       apply (simp add: null_eval)
      apply (simp add: ploc_eval)
    using new_perm_eval
     apply blast
    by simp

  have "valid_heap_mask (get_mh_total_full \<omega>)"
    using InitRel state_rel_wf_mask_simple by blast

  have Disj: "disjoint_list [ {heap_var Tr, heap_var_def Tr},
                              {mask_var Tr, mask_var_def Tr},
                              ran (var_translation Tr),
                              ran (field_translation Tr),
                              range (const_repr Tr), dom AuxPred]"
    using InitRel' state_rel_disjoint
    by blast

  show "\<exists>ns'. red_ast_bpl P ctxt
                ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns)
                ((BigBlock name cs str tr, cont), Normal ns') \<and>
              state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega>' ns'"
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
    using \<omega>'_extcons \<omega>'
                  apply blast
                 apply (simp add: TyInterp)
                apply (rule store_rel_stable[where ?\<omega>=\<omega> and ?ns=ns])
    using InitRel state_rel_store_rel
                  apply blast
                 apply (metis 1 inhale_perm_single_pred_store_same inhale_pred_normal_premise_def)
                apply (metis InitRel MaskVar state_rel_disj_mask_store update_var_other)
               apply (simp add: Disj)
              apply (simp, simp, simp)
           defer defer defer defer
           apply (metis InitRel MaskVar field_rel_stable mask_var_disjoint state_rel_field_rel state_rel_state_rel0 update_var_other)
          apply (metis InitRel MaskVar boogie_const_rel_stable mask_var_disjoint state_rel_boogie_const_rel state_rel_state_rel0 update_var_other)
         defer
         apply (metis (no_types, lifting) InitRel' MaskVar aux_vars_pred_sat_def domI mask_var_disjoint state_rel_aux_pred_sat_lookup state_rel_state_rel0 update_var_other)
  proof -
    let ?ns' = "update_var (var_context ctxt) ns m_bpl
                  (AbsV (AMask (mb((Null, PredSnapshotField (pred_id, [arg])) :=
                                   Rep_preal (get_mp_total_full \<omega> (pred_id, [arg])) + p))))"

    \<comment> \<open>Prove \<^const>\<open>heap_var_rel\<close>\<close>
    show HeapRel: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel0_heap_var_rel[OF InitRel[simplified state_rel_def]]])
       apply (metis 1 inhale_perm_single_pred_heap_same inhale_pred_normal_premise_def)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    \<comment> \<open>Prove \<^const>\<open>mask_var_rel\<close>\<close>
    show MaskRel: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var Tr) \<omega>' ?ns'"
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
       apply (smt (verit, best) 1 MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def is_bounded_field_bpl.simps(1) prod.sel(2))
      apply (subst \<open>get_mp_total_full \<omega>' = _\<close>)
      by (metis (no_types, lifting) 1 Abs_preal_inverse MaskRel[simplified mask_rel_def] fun_upd_apply inhale_pred_normal_premise_def mem_Collect_eq plus_preal.rep_eq prod.inject vb_field.simps(2))

    show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var_def Tr) \<omega>' ?ns'"
      apply (rule heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF InitRel]])
       apply (metis 1 inhale_perm_single_pred_heap_same inhale_pred_normal_premise_def)
      by (metis InitRel MaskVar mask_var_disjoint state_rel_state_rel0 update_var_other)

    show MaskRel: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var_def Tr) \<omega>' ?ns'"
      apply (subst MaskVarDefSame)
      using MaskRel
      by blast

    show "state_well_typed (type_interp ctxt) (var_context ctxt) [] ?ns'"
      apply (rule state_well_typed_upd_2)
      using InitRel state_rel_state_well_typed
       apply blast
      by (simp add: TyInterp LookupMaskTy MaskVar)
  qed
qed


subsection \<open>External Consistent State \<Longrightarrow> Inhaled State\<close>

lemma get_mp_0_implies_fnm_None:
  assumes "get_mp_nm nm lp = 0"
  shows "get_fnm_nm nm lp = None"
  using assms
  apply simp
  by (metis Rep_posreal comp_apply mem_Collect_eq option.exhaust_sel option_fold.simps(1) pperm_pgt_pnone)


lemma extcons_state_can_be_inhaled_assertion:
  assumes Sat: "sat ctxt \<omega>\<^sub>0 mh mp A"
      and mh_nm: "mh = get_mh_nm nm"
      and mp_nm: "mp = get_mp_nm nm"
      and ExtCons: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr>"
      and \<omega>hh: "get_hh_total_full \<omega> = hh"
      and \<omega>\<^sub>0hh: "get_hh_total_full \<omega>\<^sub>0 = hh"
      and SameStore: "get_store_total \<omega> = get_store_total \<omega>\<^sub>0"
      and Framed: "assertion_framing_state ctxt StateCons A \<omega>"
      and SupPred: "supported_pred_body A"
      and FinalIntCons: "StateCons (add_to_nm_total_full \<omega> nm)"
      and WfCons: "mono_prop_downward StateCons"
      and WfCtxt: "ctxt_pred_syn_wf ctxt"
    shows "red_inhale ctxt StateCons A \<omega> (RNormal (add_to_nm_total_full \<omega> nm))"

  using Sat mh_nm mp_nm ExtCons \<omega>hh SameStore Framed SupPred FinalIntCons
proof (induction A arbitrary: \<omega> nm)

  case IH: (SatAcc e_r r e_p p a mh f mp)
  hence "supported_pred_expr e_r" and "supported_pred_expr e_p"
    by simp+

  obtain r_r where "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t r_r"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>supported_pred_expr e_r\<close> eval_ok_no_type_error(1))
  obtain r_p where "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t r_p"
    by (metis IH.hyps(2) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>supported_pred_expr e_p\<close> eval_ok_no_type_error(1))

  have "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
    using IH.prems(6) RedExpListFailure assertion_framing_state_sub_exps_not_failure
    by fastforce
  hence eval_e_r: "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t r_r\<close> \<open>supported_pred_expr e_r\<close> eval_with_same_store_same_hh(1) extended_val.exhaust_sel)

  have "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
    using IH.prems(6) RedExpListCons RedExpListFailure assertion_framing_state_sub_exps_not_failure eval_e_r red_pure_exps_total.simps
    by fastforce

  hence eval_e_p: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    by (metis IH(2) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>\<And>thesis. (\<And>r_p. ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t r_p \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>supported_pred_expr e_p\<close> eval_with_same_store_same_hh(1) extended_val.exhaust)

  define W where "W = (if r = Null
                       then {\<omega>}
                       else inhale_perm_single StateCons \<omega> (the_address r, f) (Some (Abs_preal p)))"

  show ?case
    apply standard
    using eval_e_r eval_e_p W_def
       apply blast+
  proof (cases "r = Null")
    case True
    with IH have "p = 0"
      by presburger
    from True W_def have "W = {\<omega>}"
      by auto
    have "nm = 0"
      apply (rule nested_mask_equality)
        apply (simp_all add: zero_nested_mask_def)
      using IH.hyps(5) IH.prems(1) True
        apply auto[1]
      using IH.hyps(6) IH.prems(2)
        apply auto[1]
      using zero_mask_def
      by (metis (no_types, lifting) Rep_posreal comp_apply mem_Collect_eq option.exhaust_sel option_fold.simps(1) pperm_pgt_pnone)
    show "th_result_rel (0 \<le> p) (W \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W (RNormal (add_to_nm_total_full \<omega> nm))"
      apply (simp add: \<open>p = 0\<close> \<open>W = {\<omega>}\<close> True th_result_rel.simps)
      by (simp add: zero_nested_mask_def[symmetric] \<open>nm = 0\<close>)
  next
    case False
    have mh: "get_mh_nm nm = singleton_mh (a, f) (Abs_preal p)"
      using False IH.hyps(5) IH.prems(1) by presburger
    have fnm: "get_fnm_nm nm = (\<lambda>_. None)"
      by (metis (mono_tags, lifting) IH.hyps(6) IH.prems(2) Rep_posreal comp_eq_dest_lhs get_mp_nm.simps mem_Collect_eq option.exhaust_sel option_fold.simps(1) preal_not_0_gt_0 zero_mask_def)
    have intcons: "StateCons (upd_mh_loc_total_full \<omega> (the_address r, f) (get_mh_total_full \<omega> (the_address r, f) + Abs_preal p))"
    proof -
      have "upd_mh_loc_total_full \<omega> (the_address r, f) (get_mh_total_full \<omega> (the_address r, f) + Abs_preal p) =
            add_to_nm_total_full \<omega> nm"
        apply (rule full_total_state.equality; simp_all)
        apply (rule total_state.equality; simp_all)
        apply (rule nested_mask_equality; standard; simp add: add_masks_def)
         apply (simp add: mh IH(3))
        unfolding plus_nested_mask_def
        apply (cases "get_nm_total_full \<omega>", cases nm)
        apply simp
        by (metis (no_types, lifting) combine_options_simps(2) fnm get_fnm_nm.simps pfun_comb_def)
      thus ?thesis
        using IH.prems(8) by presburger
    qed
    show "th_result_rel (0 \<le> p) (W \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W (RNormal (add_to_nm_total_full \<omega> nm))"
      apply (simp add: IH(4) W_def inhale_perm_single_def False intcons[simplified])
      apply (rule THResultNormal)
      apply (rule Set.CollectI)
      apply (intro conjI)
       apply (rule full_total_state.equality)
          apply simp_all
       apply (rule total_state.equality)
         apply simp_all
       apply (rule nested_mask_equality)
        apply simp_all
        apply (simp add: mh)
        apply standard
        apply simp
        apply (simp add: IH.hyps(3) add_masks_def)
      unfolding plus_nested_mask_def
       apply (cases "get_nm_total_full \<omega>", cases nm)
       apply standard
       apply (simp add: pfun_comb_def)
      using fnm
       apply fastforce
      by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)
  qed

next
  case IH: (SatAccWildcard e_r r a f mh mp)

  hence e_r_sup: "supported_pred_expr e_r"
    by auto
  obtain r_r where "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t r_r"
    using eval_ok_no_type_error(1) IH(1,9,10) \<omega>\<^sub>0hh e_r_sup
    by metis
  moreover have "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
    using IH.prems(6) RedExpListFailure assertion_framing_state_sub_exps_not_failure
    by fastforce
  ultimately have e_r_eval: "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_r_sup eval_with_same_store_same_hh(1) extended_val.exhaust)

  define W where "W = inhale_perm_single StateCons \<omega> (the_address r, f) None"

  have "is_singleton_mh (a,f) (get_mh_nm nm)"
    using IH.hyps(4) IH.prems(1)
    by auto
  have "get_mp_nm nm = zero_mask"
    using IH.hyps(5) IH.prems(2)
    by presburger
  hence "get_fnm_nm nm = (\<lambda>_. None)"
    using SatAll_case[OF IH(8)]
    by (metis (mono_tags, lifting) Rep_posreal comp_eq_dest_lhs get_mp_nm.simps mem_Collect_eq option.exhaust option_fold.simps(1) preal_not_0_gt_0 zero_mask_def)

  have "add_to_nm_total_full \<omega> nm \<in> W"
    apply (simp add: W_def inhale_perm_single_def)
    apply (rule exI[of _ "get_mh_nm nm (a,f)"])
    apply (intro conjI)
    using \<open>is_singleton_mh (a, f) (get_mh_nm nm)\<close>
       apply fastforce
     apply (rule full_total_state.equality, simp_all)
     apply (rule total_state.equality, simp_all)
     apply (rule nested_mask_equality, simp_all; standard)
      apply (simp_all add: add_masks_def)
    using IH.hyps(2) \<open>is_singleton_mh (a, f) (get_mh_nm nm)\<close>
      apply force
    unfolding plus_nested_mask_def
     apply (cases "get_nm_total_full \<omega>", cases nm)
     apply (simp add: pfun_comb_def)
    using \<open>get_fnm_nm nm = (\<lambda>_. None)\<close>
     apply auto[1]
    by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)
  hence "W \<noteq> {}"
    by fast

  show ?case
    apply (rule InhAccWildcard[where ?W'=W])
    using e_r_eval
      apply simp
    using W_def
     apply force
    using IH.hyps(3) THResultNormal \<open>W \<noteq> {}\<close> \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
    by auto

next
  case IH: (SatAccPred e_args v_args e_p p mh mp pred_id pred_decl)

  hence e_args_sup: "list_all supported_pred_expr e_args" and
        e_p_sup: "supported_pred_expr e_p"
    by (simp add: list_all_length)+
  then obtain r_vs r_p where
    e_args_res: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> r_vs" and
    e_p_res: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t r_p"
    using eval_ok_no_type_error IH(1,2,9,10) \<omega>\<^sub>0hh
    by (metis (full_types) IH.prems(4) IH.prems(5))
  have e_args_ok: "\<And>res. red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> res \<Longrightarrow> res \<noteq> None" and
          e_p_ok: "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
     apply (metis IH.prems(6) assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure sub_expressions_atomic.simps(3))
    by (metis IH.prems(6) RedExpListFailure e_args_res assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure red_pure_exps_total_append_failure_2 split_option_ex sub_expressions_atomic.simps(3) sub_expressions_exp_or_wildcard.simps(1))
  have e_args_eval: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)" and
          e_p_eval: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    using IH(1) eval_with_same_store_same_hh(2)[OF IH(1)]
    apply (metis IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_args_sup not_Some_eq e_args_ok e_args_res)
    by (metis IH(2) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_p_res e_p_ok e_p_sup eval_with_same_store_same_hh(1) extended_val.exhaust)

  define W where "W = inhale_perm_single_pred ctxt StateCons \<omega> (pred_id,v_args) (Some (Abs_preal p))"

  have "get_mh_nm nm = zero_mask"
    using IH.hyps(4) IH.prems(1)
    by auto
  have "get_mp_nm nm = singleton_mp (pred_id,v_args) (Abs_preal p)"
    using IH.hyps(5) IH.prems(2)
    by order
  hence "get_mp_nm nm (pred_id,v_args) = Abs_preal p"
    by simp

  have sat: "sat ctxt \<omega>\<^sub>0 mh mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
    using IH
    by (meson SatAccPred)

  obtain nm_pred where
    p_nonzero: "p > 0 \<longrightarrow> get_fnm_nm nm (pred_id,v_args) = Some (Abs_posreal (Abs_preal p), nm_pred)" and
    p_zero: "p = 0 \<longrightarrow> nm_pred = 0"
    using \<open>get_mp_nm nm = _\<close>[THEN fun_cong, of "(pred_id,v_args)", simplified]
    apply (cases "get_fnm_nm nm (pred_id,v_args)"; simp)
    using positive_real_preal
     apply blast
    by (metis Rep_posreal_inverse fstI order_less_irrefl surj_pair)

  have nm_pred_extcons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr> (pred_id,v_args) (Abs_preal p)"
    apply (cases "p > 0")
     apply (metis IH.prems(3) SatAll_case \<open>get_mp_nm nm (pred_id, v_args) = Abs_preal p\<close> comp_apply get_mp_nm.simps old.prod.inject option_fold.simps(1) p_nonzero prod.collapse total_state.select_convs(2) total_state.update_convs(2))
    apply (subgoal_tac "p = 0")
     prefer 2
    using IH.hyps(3)
     apply fastforce
    apply (thin_tac _)
    apply (rule SatStep)
         apply (rule IH(6))
        apply (rule IH(7))
       apply (rule IH(8))
      apply (simp add: p_zero)
     apply (simp add: zero_preal_def)
    by (simp add: empty_consistent_external p_zero)

  have "p = 0 \<Longrightarrow> nm = 0"
    apply (rule nested_mask_equality)
     apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> zero_nested_mask_def)
    apply standard
    apply (rename_tac lp)
    apply (cut_tac ?x=lp in \<open>get_mp_nm nm = _\<close>[THEN fun_cong])
    apply (case_tac "get_fnm_nm nm lp"; simp add: zero_nested_mask_def)
    by (metis Rep_posreal mem_Collect_eq pperm_pgt_pnone zero_preal.abs_eq)

  have "Abs_preal p \<noteq> 0 \<Longrightarrow> nm = NM zero_mask [(pred_id,v_args) \<mapsto> (Abs_posreal (Abs_preal p), nm_pred)]"
    apply (rule nested_mask_equality)
     apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> zero_nested_mask_def)
    apply standard
    apply (rename_tac lp)
    apply (cut_tac ?x=lp in \<open>get_mp_nm nm = _\<close>[THEN fun_cong])
    apply (case_tac "get_fnm_nm nm lp")
     apply fastforce
    using IH.hyps(3) Rep_posreal map_upd_Some_unfold mem_Collect_eq option_fold.simps(1) p_nonzero pperm_pgt_pnone zero_preal.abs_eq
    by fastforce

  have "add_to_nm_total_full \<omega> nm \<in> W"
    unfolding W_def inhale_perm_single_pred_def option_fold.simps
    apply (rule CollectI)
    apply simp
    apply (rule exI[of _ "\<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr>"])
    apply (intro conjI)
     apply (intro impI)
     apply (intro conjI)
    using nm_pred_extcons
        apply auto[1]
    using IH.prems(4)
       apply auto[1]
      apply (rule full_total_state.equality; simp)
      apply (rule total_state.equality; simp)
    using IH.hyps(3) \<open>p = 0 \<Longrightarrow> nm = 0\<close> positive_real_preal
      apply fastforce
    using IH.prems(8)
     apply auto[1]
    apply (intro impI)
    apply (intro conjI)
    using nm_pred_extcons IH.hyps(3) zero_preal.abs_eq
       apply fastforce
    using IH.prems(4)
      apply auto[1]
     apply (rule full_total_state.equality; simp)
     apply (rule total_state.equality; simp)
     apply (rule nested_mask_equality; simp)
      apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> add_masks_zero_mask)
    using \<open>Abs_preal p \<noteq> 0 \<Longrightarrow> _\<close>
     apply simp
     apply standard
     apply (rename_tac lp)
     apply (cases "get_nm_total_full \<omega>", simp)
     apply (rename_tac mh fnm)
    unfolding plus_nested_mask_def
     apply simp
     apply (case_tac "lp = (pred_id,v_args)"; case_tac "fnm lp"; simp add: pfun_comb_def)
    by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)

  show ?case
    apply (rule InhAccPred[where ?W'=W])
    using e_args_eval e_p_eval
       apply simp+
    using W_def
     apply force
    using IH.hyps(3) THResultNormal \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
    by (metis (full_types) empty_iff)

next
  case IH: (SatAccPredWildcard e_args v_args mh pred_id mp)

  hence e_args_sup: "list_all supported_pred_expr e_args"
    by (simp add: list_all_length)
  then obtain r_vs where
    e_args_res: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> r_vs"
    using eval_ok_no_type_error(2) IH(1,7,8,10) \<omega>\<^sub>0hh
    by (metis (full_types) IH.prems(5))
  have e_args_ok: "\<And>res. red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> res \<Longrightarrow> res \<noteq> None"
    by (metis IH.prems(6) assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure sub_expressions_atomic.simps(3))
  have e_args_eval: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)"
    using IH(1) eval_with_same_store_same_hh(2)[OF IH(1)]
    by (metis IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_args_sup not_Some_eq e_args_ok e_args_res)

  define W where "W = inhale_perm_single_pred ctxt StateCons \<omega> (pred_id,v_args) None"

  have "get_mh_nm nm = zero_mask"
    using IH.hyps(2) IH.prems(1)
    by auto
  have "is_singleton_mp (pred_id,v_args) (get_mp_nm nm)"
    using IH.hyps(3) IH.prems(2)
    by meson
  then obtain p where p: "get_mp_nm nm = singleton_mp (pred_id,v_args) p" and "p > 0"
    by auto

  have sat: "sat ctxt \<omega>\<^sub>0 mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"
    using IH
    by (meson SatAccPredWildcard)

  obtain nm_pred where
    p_nonzero: "p > 0 \<longrightarrow> get_fnm_nm nm (pred_id,v_args) = Some (Abs_posreal p, nm_pred)" and
    p_zero: "p = 0 \<longrightarrow> nm_pred = 0"
    using \<open>get_mp_nm nm = _\<close>[THEN fun_cong, of "(pred_id,v_args)", simplified]
    apply (cases "get_fnm_nm nm (pred_id,v_args)"; simp)
    by (metis Rep_posreal_inverse fstI order_less_irrefl surj_pair)

  have nm_pred_extcons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr> (pred_id,v_args) p"
    apply (cases "p > 0")
     apply (metis IH.prems(3) SatAll_case mem_Collect_eq p_nonzero posreal_to_preal(8) total_state.select_convs(2) total_state.update_convs(2))
    apply (subgoal_tac "p = 0")
     prefer 2
     apply (simp add: \<open>0 < p\<close>)
    apply (thin_tac _)
    apply (rule SatStep)
         apply (rule IH(4))
        apply (rule IH(5))
       apply (rule IH(6))
      apply (simp add: p_zero)
     apply (simp add: zero_preal_def)
    by (simp add: empty_consistent_external p_zero)

  have "p \<noteq> 0 \<Longrightarrow> nm = NM zero_mask [(pred_id,v_args) \<mapsto> (Abs_posreal p, nm_pred)]"
    apply (rule nested_mask_equality)
     apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> zero_nested_mask_def)
    apply standard
    apply (rename_tac lp)
    apply (cut_tac ?x=lp in \<open>get_mp_nm nm = _\<close>[THEN fun_cong])
    apply (case_tac "get_fnm_nm nm lp")
     apply fastforce
    using IH.hyps(3) Rep_posreal map_upd_Some_unfold mem_Collect_eq option_fold.simps(1) p_nonzero pperm_pgt_pnone zero_preal.abs_eq
    by (metis (mono_tags, lifting) comp_apply get_fnm_nm.simps get_mp_nm.simps singleton_mp.elims)

  have "add_to_nm_total_full \<omega> nm \<in> W"
    unfolding W_def inhale_perm_single_pred_def option_fold.simps
    apply (rule CollectI)
    apply simp
    apply (rule exI[of _ "\<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr>"])
    apply (rule exI[of _ p])
    apply (intro conjI)
    using \<open>pos_perm_class.pnone < p\<close>
     apply force
    apply (intro impI)
    apply (intro conjI)
    using nm_pred_extcons
       apply presburger
    using IH.prems(4)
      apply auto[1]
     apply (rule full_total_state.equality; simp)
     apply (rule total_state.equality; simp)
     apply (rule nested_mask_equality; simp)
      apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> add_masks_zero_mask)
    using \<open>p \<noteq> 0 \<Longrightarrow> _\<close>
     apply simp
     apply standard
     apply (rename_tac lp)
     apply (cases "get_nm_total_full \<omega>", simp)
     apply (rename_tac mh fnm)
    unfolding plus_nested_mask_def
     apply simp
     apply (case_tac "lp = (pred_id,v_args)"; case_tac "fnm lp"; simp add: pfun_comb_def)
    by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)

  show ?case
    apply (rule InhAccPredWildcard[where ?W'=W])
    using e_args_eval
      apply simp
    using W_def
     apply force
    using IH.hyps(3) THResultNormal \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
    by (metis (full_types) ex_in_conv)

next
  case IH: (SatPure e mh mp)
  hence "supported_pred_expr e"
    by simp
  then obtain res where \<omega>_eval: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) eval_ok_no_type_error(1) \<omega>\<^sub>0hh)
  show ?case
  proof (cases res)
    case (Val v)
    then have "v = VBool True"
      using eval_with_same_store_same_hh(1)[OF IH(1)] IH(10) IH(7) IH(8) \<omega>\<^sub>0hh \<omega>_eval \<open>supported_pred_expr e\<close>
      apply simp
      by presburger
    have "nm = 0"
      apply (rule nested_mask_equality)
       apply (metis IH.hyps(2) IH.prems(1) zero_nested_mask_def get_mh_nm.simps)
      apply (simp add: zero_nested_mask_def)
      apply standard
      using IH(5)
      by (metis IH.hyps(3) get_mp_0_implies_fnm_None zero_mask_def)
    hence "add_to_nm_total_full \<omega> nm = \<omega>"
      by (simp add: zero_nested_mask_def[symmetric])
    then show ?thesis
      by (metis Val \<omega>_eval \<open>v = VBool True\<close> inh_pure_normal)
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) RedExpListFailure \<omega>_eval assertion_framing_state_sub_exps_not_failure by fastforce
  qed

next
  case IH: (SatStar mh mh\<^sub>1 mh\<^sub>2 mp mp\<^sub>1 mp\<^sub>2 A B)

  hence A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    by simp+

  obtain fnm where fnm: "fnm = get_fnm_nm nm"
    by simp
  obtain fnm\<^sub>1 where fnm\<^sub>1: "\<And>lp. fnm\<^sub>1 lp = (if mp\<^sub>1 lp = 0 then None else Some (Abs_posreal (mp\<^sub>1 lp), (mp\<^sub>1 lp / mp lp) *\<^sub>s (snd (the (fnm lp)))))"
    by simp
  obtain fnm\<^sub>2 where fnm\<^sub>2: "\<And>lp. fnm\<^sub>2 lp = (if mp\<^sub>2 lp = 0 then None else Some (Abs_posreal (mp\<^sub>2 lp), (mp\<^sub>2 lp / mp lp) *\<^sub>s (snd (the (fnm lp)))))"
    by simp
  obtain nm\<^sub>1 where nm\<^sub>1: "nm\<^sub>1 = NM mh\<^sub>1 fnm\<^sub>1"
    by simp
  obtain nm\<^sub>2 where nm\<^sub>2: "nm\<^sub>2 = NM mh\<^sub>2 fnm\<^sub>2"
    by simp

  have "mp\<^sub>1 = get_mp_nm nm\<^sub>1"
    unfolding nm\<^sub>1
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>1 lp"; cut_tac ?lp=lp in fnm\<^sub>1; simp)
     apply (metis option.distinct(1))
    by (metis Abs_posreal_inverse Some_Some_ifD fst_eqD mem_Collect_eq option.inject pperm_pnone_pgt)
  have "mp\<^sub>2 = get_mp_nm nm\<^sub>2"
    unfolding nm\<^sub>2
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>2 lp"; cut_tac ?lp=lp in fnm\<^sub>2; simp)
     apply (metis option.distinct(1))
    by (metis Abs_posreal_inverse Some_Some_ifD fst_eqD mem_Collect_eq option.inject pperm_pnone_pgt)
  
  have nm\<^sub>1_cons: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>"
  proof
    fix pid vs q nm'
    assume lpm: "Some (q,nm') = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr> (pid,vs)"
    have "q = Abs_posreal (mp\<^sub>1 (pid,vs))" and
         "nm' = (mp\<^sub>1 (pid,vs) / mp (pid,vs)) *\<^sub>s (snd (the (fnm (pid,vs))))"
      using lpm[unfolded nm\<^sub>1, simplified, simplified fnm\<^sub>1]
      by (cases "mp\<^sub>1 (pid,vs) = 0"; simp)+

    have "mp (pid,vs) \<ge> mp\<^sub>1 (pid,vs)"
      by (meson IH.hyps(2) le_funD split_implies_le(1))
    then obtain q\<^sub>a nm'\<^sub>a where "Some (q\<^sub>a,nm'\<^sub>a) = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr> (pid,vs)"
      by (metis IH.prems(2) dual_order.strict_trans1 fnm\<^sub>1 get_fnm_nm.simps get_fnm_total.simps lpm nm\<^sub>1 obtain_lpm_from_mp option.distinct(1) preal_not_0_gt_0 total_state.select_convs(2))

    hence extcons\<^sub>a: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm'\<^sub>a \<rparr> (pid,vs) (Rep_posreal q\<^sub>a)"
      by (metis IH.prems(3) consistent_external.cases total_state.update_convs(2))

    have the_eq: "snd (the (fnm (pid,vs))) = nm'\<^sub>a"
      by (metis \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> fnm get_fnm_total.simps option.sel sndI total_state.select_convs(2))

    have q_pos: "mp\<^sub>1 (pid,vs) > 0"
      using fnm\<^sub>1 lpm nm\<^sub>1 preal_not_0_gt_0
      by fastforce

    have "Rep_posreal q\<^sub>a = mp (pid,vs)"
      by (metis Abs_posreal_inverse IH.prems(2) \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> \<open>mp\<^sub>1 (pid, vs) \<le> mp (pid, vs)\<close> dual_order.strict_trans1 fst_conv get_fnm_total.simps mem_Collect_eq obtain_lpm_from_mp option.sel q_pos total_state.select_convs(2))

    show "consistent_external_wrt_ploc ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>\<lparr> get_nm_total := nm' \<rparr>) (pid,vs) (Rep_posreal q)"
      apply simp
      unfolding \<open>nm' = _\<close> the_eq \<open>q = _\<close> Abs_posreal_inverse[of "mp\<^sub>1 (pid,vs)", simplified, OF q_pos]
      using fraction_consistent_external(1)[OF WfCtxt extcons\<^sub>a, of "mp\<^sub>1 (pid, vs) / mp (pid, vs)", unfolded \<open>Rep_posreal q\<^sub>a = _\<close>, simplified]
      by (metis (mono_tags, lifting) Rep_preal_inject \<open>mp\<^sub>1 (pid, vs) \<le> mp (pid, vs)\<close> divide_preal.rep_eq dual_order.strict_trans1 nonzero_eq_divide_eq pperm_pgt_pnone q_pos times_preal.rep_eq zero_preal.rep_eq)
  qed

  have nm\<^sub>2_cons: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>"
  proof
    fix pid vs q nm'
    assume lpm: "Some (q,nm') = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr> (pid,vs)"
    have "q = Abs_posreal (mp\<^sub>2 (pid,vs))" and
         "nm' = (mp\<^sub>2 (pid,vs) / mp (pid,vs)) *\<^sub>s (snd (the (fnm (pid,vs))))"
      using lpm[unfolded nm\<^sub>2, simplified, simplified fnm\<^sub>2]
      by (cases "mp\<^sub>2 (pid,vs) = 0"; simp)+

    have "mp (pid,vs) \<ge> mp\<^sub>2 (pid,vs)"
      by (meson IH.hyps(2) le_funE split_implies_le(2))
    then obtain q\<^sub>a nm'\<^sub>a where "Some (q\<^sub>a,nm'\<^sub>a) = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr> (pid,vs)"
      by (metis IH.prems(2) dual_order.strict_trans1 fnm\<^sub>2 get_fnm_nm.simps get_fnm_total.simps lpm nm\<^sub>2 obtain_lpm_from_mp option.distinct(1) preal_not_0_gt_0 total_state.select_convs(2))

    hence extcons\<^sub>a: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm'\<^sub>a \<rparr> (pid,vs) (Rep_posreal q\<^sub>a)"
      by (metis IH.prems(3) consistent_external.cases total_state.update_convs(2))

    have the_eq: "snd (the (fnm (pid,vs))) = nm'\<^sub>a"
      by (metis \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> fnm get_fnm_total.simps option.sel sndI total_state.select_convs(2))

    have q_pos: "mp\<^sub>2 (pid,vs) > 0"
      using fnm\<^sub>2 lpm nm\<^sub>2 preal_not_0_gt_0
      by fastforce

    have "Rep_posreal q\<^sub>a = mp (pid,vs)"
      by (metis Abs_posreal_inverse IH.prems(2) \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> \<open>mp\<^sub>2 (pid, vs) \<le> mp (pid, vs)\<close> dual_order.strict_trans1 fst_conv get_fnm_total.simps mem_Collect_eq obtain_lpm_from_mp option.sel q_pos total_state.select_convs(2))

    show "consistent_external_wrt_ploc ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>\<lparr> get_nm_total := nm' \<rparr>) (pid,vs) (Rep_posreal q)"
      apply simp
      unfolding \<open>nm' = _\<close> the_eq \<open>q = _\<close> Abs_posreal_inverse[of "mp\<^sub>2 (pid,vs)", simplified, OF q_pos]
      using fraction_consistent_external(1)[OF WfCtxt extcons\<^sub>a, of "mp\<^sub>2 (pid, vs) / mp (pid, vs)", unfolded \<open>Rep_posreal q\<^sub>a = _\<close>, simplified]
      by (metis (mono_tags, lifting) Rep_preal_inject \<open>mp\<^sub>2 (pid, vs) \<le> mp (pid, vs)\<close> divide_preal.rep_eq dual_order.strict_trans1 nonzero_eq_divide_eq pperm_pgt_pnone q_pos times_preal.rep_eq zero_preal.rep_eq)
  qed

  have "nm\<^sub>1 + nm\<^sub>2 = nm"
    unfolding plus_nested_mask_def nm\<^sub>1 nm\<^sub>2
    apply simp
    apply (rule nested_mask_equality)
    using IH.hyps(1) IH.prems(1)
     apply auto[1]
    unfolding fnm[symmetric]
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>1 lp"; case_tac "fnm\<^sub>2 lp"; simp add: pfun_comb_def)
    subgoal for lp
      apply (subgoal_tac "mp lp = 0")
       apply (metis IH.prems(2) fnm get_mp_0_implies_fnm_None)
      apply (subgoal_tac "mp\<^sub>1 lp = 0 \<and> mp\<^sub>2 lp = 0")
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
       apply fastforce
      using fnm\<^sub>1[of lp] fnm\<^sub>2[of lp]
      by (metis option.distinct(1))
    subgoal for lp lpm\<^sub>2
      apply (subgoal_tac "mp\<^sub>1 lp = 0 \<and> mp\<^sub>2 lp = mp lp \<and> mp\<^sub>2 lp > 0")
      using fnm\<^sub>2[of lp, simplified]
       apply (metis IH.prems(2) PosReal.field_divide_inverse PosReal.field_inverse Some_Some_ifD fnm obtain_lpm_from_mp option.sel pos_perm_class.pmult_comm preal_semimodule_class.scale_one snd_conv)
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
      by (metis add.commute fnm\<^sub>1 fnm\<^sub>2 option.distinct(1) padd_pnone preal_not_0_gt_0)
    subgoal for lp lpm\<^sub>1
      apply (subgoal_tac "mp\<^sub>2 lp = 0 \<and> mp\<^sub>1 lp = mp lp \<and> mp\<^sub>1 lp > 0")
      using fnm\<^sub>2[of lp, simplified]
       apply (metis IH.prems(2) PosReal.field_divide_inverse PosReal.field_inverse fnm fnm\<^sub>1 obtain_lpm_from_mp option.sel order_less_le pos_perm_class.pmult_comm preal_semimodule_class.scale_one snd_conv)
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
      by (metis fnm\<^sub>1 fnm\<^sub>2 option.distinct(1) padd_pnone preal_not_0_gt_0)
    subgoal for lp lpm\<^sub>1 lpm\<^sub>2
    proof -
      assume "fnm\<^sub>1 lp = Some lpm\<^sub>1"
        and "fnm\<^sub>2 lp = Some lpm\<^sub>2"
      have "Rep_posreal (fst lpm\<^sub>1) = mp\<^sub>1 lp"
        using \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> \<open>mp\<^sub>1 = get_mp_nm nm\<^sub>1\<close> nm\<^sub>1 by auto
      have "Rep_posreal (fst lpm\<^sub>2) = mp\<^sub>2 lp"
        using \<open>fnm\<^sub>2 lp = Some lpm\<^sub>2\<close> \<open>mp\<^sub>2 = get_mp_nm nm\<^sub>2\<close> nm\<^sub>2 by auto
      have "mp lp > 0"
        by (metis IH.hyps(2) \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> fnm\<^sub>1 le_funD option.distinct(1) order_less_imp_not_less order_less_le preal_not_0_gt_0 split_implies_le(1))
      hence 1: "fnm lp = Some (Abs_posreal (mp lp), snd (the (fnm lp)))"
        by (metis IH.prems(2) fnm obtain_lpm_from_mp option.sel split_pairs)
      have 2: "snd lpm\<^sub>1 = (mp\<^sub>1 lp / mp lp) *\<^sub>s snd (the (fnm lp))"
        by (metis \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> fnm\<^sub>1 option.discI option.sel split_pairs)
      have 3: "snd lpm\<^sub>2 = (mp\<^sub>2 lp / mp lp) *\<^sub>s snd (the (fnm lp))"
        by (metis \<open>fnm\<^sub>2 lp = Some lpm\<^sub>2\<close> fnm\<^sub>2 option.discI option.sel split_pairs)
      show "Some (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2)) = fnm lp"
        apply (subst 1)
        apply standard+
         apply (rule Rep_posreal_inject[THEN iffD1])
        unfolding plus_posreal.rep_eq
         apply (metis Abs_posreal_inject IH.hyps(2) Rep_posreal Rep_posreal_inverse \<open>Rep_posreal (fst lpm\<^sub>1) = mp\<^sub>1 lp\<close> \<open>Rep_posreal (fst lpm\<^sub>2) = mp\<^sub>2 lp\<close> \<open>pos_perm_class.pnone < mp lp\<close> add_masks_def mem_Collect_eq mp_split.simps)
        unfolding plus_nested_mask_def[symmetric] 2 3
        unfolding preal_semimodule_class.scale_add_left[symmetric]
        using preal_semimodule_class.scale_one IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
        by (metis PosReal.field_divide_inverse PosReal.field_inverse PosReal.pmult_comm \<open>pos_perm_class.pnone < mp lp\<close> distrib_right preal_not_0_gt_0)
    qed
    done

  define \<omega>\<^sub>A where "\<omega>\<^sub>A = add_to_nm_total_full \<omega> nm\<^sub>1"
  have 1: "add_to_nm_total_full \<omega>\<^sub>A nm\<^sub>2 = add_to_nm_total_full \<omega> nm"
    apply (rule full_total_state.equality; simp_all add: IH \<omega>\<^sub>A_def)
    apply (rule total_state.equality; simp_all add: IH \<omega>\<^sub>A_def)
    using \<open>nm\<^sub>1 + nm\<^sub>2 = nm\<close> ab_semigroup_add_class.add_ac(1)
    by blast

  have "add_to_nm_total_full \<omega> nm \<succeq> add_to_nm_total_full \<omega> nm\<^sub>1"
    apply (simp add: greater_def)
    apply (rule exI[of _ "upd_nm_total_full \<omega> nm\<^sub>2"])
    apply (simp add: plus_full_total_state_ext_def)
    apply standard+
     apply (metis (no_types, lifting) \<open>nm\<^sub>1 + nm\<^sub>2 = nm\<close> ab_semigroup_add_class.add_ac(1) option.sel plus_total_state_ext_def total_state.ext_inject total_state.surjective total_state.update_convs(2))
    by (simp add: defined_def plus_total_state_ext_def)
  hence A_mask_intcons: "StateCons (add_to_nm_total_full \<omega> nm\<^sub>1)"
    using IH(14) WfCons mono_prop_downwardD
    by blast

  show ?case
    apply (rule InhStarNormal[where ?\<omega>''=\<omega>\<^sub>A])
    unfolding \<open>\<omega>\<^sub>A = _\<close>
    using IH(5)[of nm\<^sub>1 \<omega>]
    apply (metis A_mask_intcons A_sup IH.prems(4) IH.prems(5) IH.prems(6) \<open>mp\<^sub>1 = _\<close> assertion_framing_star get_mh_nm.simps nm\<^sub>1 nm\<^sub>1_cons)
    using IH(6)[of nm\<^sub>2 \<omega>\<^sub>A, OF _ _ nm\<^sub>2_cons] 1
    by (metis A_mask_intcons A_sup B_sup IH.IH(1) IH.prems(4) IH.prems(5) IH.prems(6) IH.prems(8) \<omega>\<^sub>A_def \<open>mp\<^sub>1 = _\<close> \<open>mp\<^sub>2 = _\<close> assertion_framing_star get_mh_nm.simps inhale_only_changes_mask nm\<^sub>1 nm\<^sub>1_cons nm\<^sub>2)

next
  case IH: (SatImpTrue e mh mp A)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool True"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhImpTrue)
      using Val \<open>v\<^sub>2 = VBool True\<close> res
       apply blast
      using IH(3)[OF IH(4-8)] A_sup Val \<open>v\<^sub>2 = VBool True\<close> assertion_framing_imp res IH.prems(6,8)
      by blast
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_imp_failure by blast
  qed

next
  case IH: (SatImpFalse e mh mp A)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  have "nm = 0"
    apply (simp add: zero_nested_mask_def)
    apply (rule nested_mask_equality, simp_all)
    using IH.hyps(2) IH.prems(1) zero_mask_def
      apply fastforce
    using IH.hyps(3) IH.prems(2) zero_mask_def
    by (metis get_mp_0_implies_fnm_None)

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool False"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhImpFalse)
      using Val \<open>v\<^sub>2 = VBool False\<close> res
       apply blast
      by (simp add: \<open>nm = 0\<close>)
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_imp_failure by blast
  qed

next
  case IH: (SatCondTrue e mh mp A B)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool True"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhCondAssertTrue)
      using Val \<open>v\<^sub>2 = VBool True\<close> res
       apply blast
      using IH(3)[OF IH(4-8)] A_sup Val \<open>v\<^sub>2 = VBool True\<close> assertion_framing_cond_assert_true res IH.prems(6,8)
      by blast
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_cond_assert_failure by blast
  qed

next
  case IH: (SatCondFalse e mh mp B A)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool False"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhCondAssertFalse)
      using Val \<open>v\<^sub>2 = VBool False\<close> res
       apply blast
      by (metis B_sup IH.IH IH.prems(1-6,8) Val \<open>v\<^sub>2 = VBool False\<close> assertion_framing_cond_assert_false res)
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_cond_assert_failure by blast
  qed
qed


lemma extcons_state_can_be_inhaled:
  assumes PredDecl: "ViperLang.predicates (program_total ctxt) pid = Some pdecl"
      and PredBody: "ViperLang.predicate_decl.body pdecl = Some pbody"
      and SupPred: "supported_pred_body pbody"
      and SelfFraming: "\<And>q. assertion_framing_state ctxt StateCons (syntactic_mult q pbody) \<omega>"
      and ExtCons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr> (pid,vs) p"
      and \<omega>hh: "get_hh_total_full \<omega> = hh"
      and \<omega>Store: "get_store_total \<omega> = nth_option vs"
      and FinalIntCons: "StateCons (add_to_nm_total_full \<omega> nm)"
      and WfCons: "wf_total_consistency ctxt StateCons StateCons_t"
      and WfCtxt: "ctxt_pred_syn_wf ctxt"
      and "p > 0"
    shows "red_inhale ctxt StateCons (syntactic_mult (Rep_preal p) pbody) \<omega> (RNormal (add_to_nm_total_full \<omega> nm))"
proof -
  have
    "p = 0 \<Longrightarrow> nm = 0" and
    "p > 0 \<Longrightarrow> sat ctxt \<lparr> get_store_total = nth_option vs,
                   get_trace_total = Map.empty,
                   get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr>
            (get_mh_nm nm) (get_mp_nm nm)
            (syntactic_mult (Rep_preal p) pbody)" and
    "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr>"
    using SatStep_case PredDecl PredBody ExtCons
    by fastforce+
  moreover have "assertion_framing_state ctxt StateCons (syntactic_mult (Rep_preal p) pbody) \<omega>"
    using SelfFraming
    by auto
  ultimately show ?thesis
    apply (cases "p > 0")
    using \<omega>Store \<omega>hh extcons_state_can_be_inhaled_assertion FinalIntCons wf_total_consistency_trace_mono_downwardD[OF WfCons]
     apply (metis SupPred WfCtxt full_total_state.select_convs(1) full_total_state.select_convs(3) get_hh_total_full.simps prat_non_negative syntactic_mult_supported total_state.select_convs(1))
    apply (subgoal_tac "p = 0")
     prefer 2
    using preal_not_0_gt_0
     apply blast
    apply simp
    using assms(11)
    by blast
qed


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
    using WfCons
      apply simp
    by fact+
qed


subsection \<open>Relation between Two Self-Framing Definitions\<close>


lemma ctxt_pred_self_framing_inh_implies_sat:
  assumes "ctxt_pred_self_framing_inh ctxt StateCons"
  shows "ctxt_pred_self_framing_sat ctxt StateCons_t"
  unfolding ctxt_pred_self_framing_sat_def pred_self_framing_def
  sorry



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
      and CtxtWfPred: "ctxt_pred_syn_wf ctxt_vpr"
      and ArgsSimp: "e_args = [pure_exp.Var 0]" \<comment> \<open>We only support one predicate argument, which must be the first method argument.\<close>
      and PermSimp: "e_p = ELit (LPerm 1)" \<comment> \<open>We only support a literal 1 as the permission.\<close>
      and StepExhale:
          "rel_general R R'
             (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> (RNormal \<omega>'))
             (\<lambda>\<omega>. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> RFailure)
             P ctxt_bpl \<gamma> \<gamma>\<^sub>2"
      and StepInhale: "inhale_rel R' (\<lambda>_ _. True) ctxt_vpr StateCons P ctxt_bpl (syntactic_mult 1 pbody) \<gamma>\<^sub>2 \<gamma>'"
    shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt_bpl (Unfold pid e_args (PureExp e_p)) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro)
  \<comment> \<open>Specialize predicate body restrictions and self-framing to the predicate in consideration\<close>
  have SupportedPredBody: "supported_pred_body pbody"
    using CtxtWfPred PredBody PredDecl ctxt_pred_syn_wf_def
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
  from StateRelImpliesExtCons \<open>R \<omega> ns\<close> have "consistent_external ctxt_vpr (get_total_full \<omega>)"
    by simp
  have "v_p > 0"
    using PermSimp TotalExpressions.RedLit_case e_p_eval
    by fastforce
  have perm_suff: "get_mp_total_full \<omega> (pid,v_args) \<ge> Abs_preal v_p"
    using unfold_rel_perm_sufficient[OF UnfoldRel]
    by simp

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

  from inhale_simulates_unfold[OF UnfoldRel ExtCons WfCons Cons_t PredDecl PredBody CtxtWfPred FramingArgs _ LabelCons]
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

  hence step_exh: "red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> (RNormal ?\<omega>\<^sub>d)"
    using ExhAccPred
    by (metis PredArgs PredBody PredDecl args_well_ty e_args_eval e_p_eval)

  obtain ns\<^sub>2 where bpl_step_exh: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2) \<and> R' ?\<omega>\<^sub>d ns\<^sub>2"
    using rel_success_elim[OF StepExhale \<open>R \<omega> ns\<close> step_exh]
    by blast

  \<comment> \<open>Step 2: inhale\<close>

  have step_inhale:
    "red_inhale ctxt_vpr StateCons (syntactic_mult (Rep_preal (Abs_preal v_p)) pbody)
                \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>
       (RNormal \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>' \<rparr>)"
  proof -
    obtain var0 where "get_store_total \<omega> 0 = Some var0 \<and> v_args = [var0]"
      using RedExpList_case[OF e_args_eval[simplified ArgsSimp RedExpList_case]]
      by (metis ArgsSimp Some_Some_ifD TotalExpressions.RedVar_case e_args_eval option.inject red_pure_exps_total_singleton)
    show ?thesis
      apply (rule inhale_with_more_variables[where ?\<omega>\<^sub>1="\<lparr> get_store_total = nth_option v_args, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>"])
      using step_inhale'
          apply simp
         apply simp
         apply (metis Some_Some_ifD \<open>get_store_total \<omega> 0 = Some var0 \<and> v_args = [var0]\<close> length_Suc_conv less_Suc0 list.size(3) nth_Cons_0)
      by simp_all
  qed

  \<comment> \<open>Simplification: permission = 1\<close>
  have "v_p = 1"
    using TotalExpressions.RedLit_case[OF e_p_eval[simplified PermSimp]]
    by auto
  hence inh_perm_1: "Rep_preal (Abs_preal v_p) = 1"
    using one_preal.rep_eq one_preal_def
    by force

  have \<omega>'_rel: "\<omega>' = \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>' \<rparr>"
    by (simp add: \<open>\<omega>' = _\<close>)
  have \<omega>\<^sub>d_rel: "\<omega>\<lparr> get_total_full := \<phi>\<^sub>d \<rparr> = \<lparr> get_store_total = get_store_total \<omega>, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>"
    by simp

  obtain ns' where "red_ast_bpl P ctxt_bpl (\<gamma>\<^sub>2, Normal ns\<^sub>2) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    using inhale_rel_normal_elim[OF StepInhale bpl_step_exh[THEN conjunct2] TrueI, unfolded \<omega>\<^sub>d_rel, OF step_inhale[unfolded inh_perm_1, simplified]]
    unfolding \<omega>'_rel
    by presburger

  thus "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    using bpl_step_exh red_ast_bpl_transitive
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
      using PermSimp TotalExpressions.RedLit_case e_p_eval
      by fastforce

    have step_exhale: "red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> RFailure"
      using ExhAccPred[OF _ e_args_eval e_p_eval PredDecl _ PredBody, where ?mp="get_mp_total_full \<omega>"] v_p_fail' PredDecl args_well_ty pdecl'
      by auto
    show ?thesis
      using rel_failure_elim[OF StepExhale \<open>R \<omega> ns\<close> step_exhale]
      by blast
  next
    case RedSubExpressionFailure
    have step_exhale: "red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pid e_args (PureExp e_p))) \<omega> RFailure"
      apply (rule ExhSubExpFailure)
      using RedSubExpressionFailure
      by simp_all
    show ?thesis
      using rel_failure_elim[OF StepExhale \<open>R \<omega> ns\<close> step_exhale]
      by blast
  qed
qed


lemma unfold_exhale_pred_rel:
  assumes WfSubexp: "exprs_wf_rel
                       (\<lambda>\<omega>def \<omega> ns. R \<omega> ns \<and> \<omega>def = \<omega> \<and>
                          Q (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega>)
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
                 (\<lambda> \<omega> \<omega>'. exhale_pred_acc_normal_premise ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args v_p \<omega> \<omega> \<omega>')
                 (\<lambda>_. False)
                 P ctxt_bpl \<gamma>\<^sub>3 \<gamma>'"
    shows "rel_general R R
             (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> (RNormal \<omega>'))
             (\<lambda>\<omega>. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> RFailure)
             P ctxt_bpl \<gamma> \<gamma>'"
  sorry

lemma exp_rel_perm_pred_access_2:
  assumes
    MaskReadWf: "mask_read_wf TyRep ctxt_bpl mask_read_bpl" and
    StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt_bpl \<omega>def \<omega> ns" and
    RedArgsVpr: "red_pure_exps_total ctxt_vpr (Some \<omega>def_opt) e_args_vpr \<omega> (Some v_args_vpr)" and
    (* RedArgVpr: "ctxt_vpr, Some \<omega>def_opt \<turnstile> \<langle>e_arg_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v_arg_vpr" and *)
      "e_args_vpr = [e_arg_vpr]" and
    ArgRel: "exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr ctxt_bpl e_arg_vpr e_arg_bpl" and
      "mvar = mask_var Tr" and
      "nullConst = const_repr Tr CNull" and
      "e_ploc_bpl = FunExp ''P'' [] [e_arg_bpl]" and
      "e_bpl = mask_read_bpl (expr.Var mvar) (expr.Var nullConst) e_ploc_bpl [TConSingle ''PredicateType_P'', TPrim TBool]"
    shows "red_expr_bpl ctxt_bpl e_bpl ns (RealV (Rep_preal (get_mp_total_full \<omega> (''P'',v_args_vpr))))"
  sorry


end
