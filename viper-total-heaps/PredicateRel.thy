theory PredicateRel
  imports TotalSemanticsProperties InhaleRel ExhaleRel StmtRel
begin


subsection \<open>Inhale\<close>

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
    PredTyArgsLookup: "predicate_decl.args pdecl = ty_args" and
    PredTyArgs: "ty_args = [TRef]"

  shows "rel_general R
           (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt)
           (\<lambda> \<omega> \<omega>'. inhale_pred_normal_premise ctxt_vpr StateCons pred_id ty_args [e_arg_vpr] e_p_vpr vs p \<omega> \<omega>')
           (\<lambda> \<omega>. False) P ctxt
           (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
           (BigBlock name cs str tr, cont)"

  apply (rule rel_intro)
   prefer 2
   apply blast
proof -
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and *: "inhale_pred_normal_premise ctxt_vpr StateCons pred_id ty_args [e_arg_vpr] e_p_vpr vs p \<omega> \<omega>'"

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
  with * have 1: "inhale_pred_normal_premise ctxt_vpr StateCons pred_id ty_args [e_arg_vpr] e_p_vpr [arg] p \<omega> \<omega>'"
    by fast

  let ?ploc = "(pred_id,[arg])"

  obtain \<phi>_inh where \<omega>':
    "(p > 0 \<longrightarrow> consistent_external_wrt_ploc ctxt_vpr \<phi>_inh ?ploc (Abs_preal p)) \<and>
     get_hh_total \<phi>_inh = get_hh_total_full \<omega> \<and>
     \<omega>' = (if p = 0 then \<omega> else add_to_nm_loc_total_full (inc_mp_loc_total_full \<omega> ?ploc (Abs_preal p)) ?ploc (get_nm_total \<phi>_inh)) \<and>
     StateCons \<omega>'"
    using 1[simplified inhale_pred_normal_premise_def inhale_perm_single_pred_def]
    by (smt (verit, ccfv_threshold) mem_Collect_eq option_fold.simps(1) positive_real_preal pperm_pnone_pgt zero_preal.abs_eq)

  hence mh_same: "get_mh_total_full \<omega> = get_mh_total_full \<omega>'" and
    mp_rel: "get_mp_total_full \<omega>' = (get_mp_total_full \<omega>)( ?ploc := get_mp_total_full \<omega> ?ploc + Abs_preal p )"
     apply simp
    apply (cases "p = 0")
    using \<omega>' zero_preal_def
     apply force
    apply (subgoal_tac "\<omega>' = add_to_nm_loc_total_full (inc_mp_loc_total_full \<omega> ?ploc (Abs_preal p)) ?ploc (get_nm_total \<phi>_inh)")
     apply simp
    by (meson \<omega>')

  have \<omega>'_extcons: "consistent_external ctxt_vpr (get_total_full \<omega>')"
    sorry

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
    using 1[simplified inhale_pred_normal_premise_def vals_well_typed_def PredTyArgs]
    by blast
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
    using \<omega>' \<omega>'_extcons
    subgoal sorry
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


subsection \<open>Unfold\<close>

lemma extcons_pred_well_typed:
  assumes "consistent_external ctxt \<phi>"
      and "get_mp_total \<phi> (pid,vs) > 0"
      and "ViperLang.predicates (program_total ctxt) pid = Some pred_decl"
      and "ViperLang.predicate_decl.args pred_decl = ty_args"
    shows "vals_well_typed (absval_interp_total ctxt) vs ty_args"
proof -
  obtain \<phi>' where "consistent_external_wrt_ploc ctxt \<phi>' (pid,vs) (get_mp_total \<phi> (pid,vs))"
    using SatAll_case[OF assms(1)]
    by (metis assms(2) get_mp_total.simps option.exhaust preal_not_0_gt_0)
  thus ?thesis
    by (metis SatStep_case assms(3) assms(4) option.sel)
qed
  

lemma unfold_stmt_rel:
  assumes PredDecl: "ViperLang.predicates (program_total ctxt_vpr) pred_id = Some pred_decl"
      and PredArgs: "ViperLang.predicate_decl.args pred_decl = ty_args"
      and PredBody: "ViperLang.predicate_decl.body pred_decl = Some pred_body"
      and SupportedPredBody: "supported_pred_body pred_body"
      and SelfFraming: "assertion_self_framing ctxt_vpr StateCons pred_body ty_args"
      and WfCons: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and IntConsImpliesWfMask: "\<And>\<omega>. StateCons \<omega> \<Longrightarrow> valid_heap_mask (get_mh_total_full \<omega>)"
      and StateRelImpliesIntCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"
      and StateRelImpliesExtCons: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> consistent_external ctxt_vpr (get_total_full \<omega>)"
      and CtxtWfPred: "ctxt_wf_pred ctxt_vpr"
      and ArgsSimp: "e_args = [pure_exp.Var 0]" \<comment> \<open>We only support one predicate argument, which must be the first method argument.\<close>
      and PermSimp: "e_p = ELit (LPerm 1)" \<comment> \<open>We only support a literal 1 as the permission.\<close>
      and StepExhale:
          "rel_general R R'
             (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> (RNormal \<omega>'))
             (\<lambda>\<omega>. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> RFailure)
             P ctxt_bpl \<gamma> \<gamma>\<^sub>2"
      and StepInhale: "inhale_rel R' (\<lambda>_ _. True) ctxt_vpr StateCons P ctxt_bpl (syntactic_mult 1 pred_body) \<gamma>\<^sub>2 \<gamma>'"
    shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt_bpl (Unfold pred_id e_args (PureExp e_p)) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
     and red_stmt: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
  then obtain v_args v_p \<phi>' where
    e_args_eval: "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args \<omega> (Some v_args)" and
    e_p_eval: "ctxt_vpr, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    "v_p \<ge> 0" and
    UnfoldRel: "unfold_rel ctxt_vpr pred_id v_args (Abs_preal v_p) (get_total_full \<omega>) \<phi>'" and
    "\<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr>"
    by (blast elim: RedUnfold_case)
  from StateRelImpliesExtCons \<open>R \<omega> ns\<close> have "consistent_external ctxt_vpr (get_total_full \<omega>)"
    by simp

  from \<open>R \<omega> ns\<close> have ExtCons: "consistent_external ctxt_vpr (get_total_full \<omega>)"
    using StateRelImpliesExtCons
    by auto
  have "vals_well_typed (absval_interp_total ctxt_vpr) v_args ty_args"
  proof -
    have "v_p > 0"
      using PermSimp TotalExpressions.RedLit_case e_p_eval
      by fastforce
    have "get_mp_total_full \<omega> (pred_id,v_args) \<ge> Abs_preal v_p"
      using unfold_rel_perm_sufficient[OF UnfoldRel]
      by simp
    thus ?thesis
      using extcons_pred_well_typed ExtCons PredArgs PredDecl \<open>0 < v_p\<close> order_le_imp_less_or_eq order_less_trans positive_real_preal preal_not_0_gt_0
      by fastforce
  qed
  with SelfFraming have FramingArgs: "\<And>p. assertion_self_framing_store ctxt_vpr StateCons (syntactic_mult p pred_body) (nth_option v_args)"
    using assertion_self_framing_def
    by blast

  have Cons_t: "StateCons_t (get_total_full \<omega>)"
    using WfCons[simplified wf_total_consistency_def]
    by (meson StateRelImpliesIntCons \<open>R \<omega> ns\<close>)
  have LabelCons: "\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> StateCons_t \<phi>"
    by (metis StateRelImpliesIntCons WfCons \<open>R \<omega> ns\<close> wf_total_consistency_def)

  from inhale_simulates_unfold[OF UnfoldRel ExtCons WfCons Cons_t PredDecl PredBody CtxtWfPred FramingArgs _ ]
  obtain \<phi>\<^sub>d where
    \<phi>\<^sub>d: "\<phi>\<^sub>d = dec_mp_loc_total (mult_rm_nm_loc_total (get_total_full \<omega>) (pred_id,v_args) (Abs_preal v_p)) (pred_id,v_args) (Abs_preal v_p)" and
    step_inhale': "red_inhale ctxt_vpr StateCons (syntactic_mult (Rep_preal (Abs_preal v_p)) pred_body)
                     \<lparr> get_store_total = nth_option v_args, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>\<^sub>d \<rparr>
            (RNormal \<lparr> get_store_total = nth_option v_args, get_trace_total = get_trace_total \<omega>, get_total_full = \<phi>' \<rparr>)"
    using IntConsImpliesWfMask LabelCons
    by blast

  from UnfoldRel have perm_suff: "get_mp_total_full \<omega> (pred_id,v_args) \<ge> Abs_preal v_p"
    apply (simp add: unfold_rel.simps shift_up.simps)
    by force
  let ?\<omega>\<^sub>d = "\<omega>\<lparr> get_total_full := \<phi>\<^sub>d \<rparr>"
  have "exh_if_total (v_p \<ge> 0 \<and> get_mp_total_full \<omega> (pred_id,v_args) \<ge> Abs_preal v_p)
                     (exhale_pred \<omega> (pred_id,v_args) (Abs_preal v_p))
        = RNormal ?\<omega>\<^sub>d"
    apply (simp only: perm_suff \<open>v_p \<ge> 0\<close>)
    by (simp add: exhale_pred_def \<phi>\<^sub>d)

  hence step_exh: "red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> (RNormal ?\<omega>\<^sub>d)"
    using ExhAccPred
    by (metis e_args_eval e_p_eval)

  obtain ns\<^sub>2 where bpl_step_exh: "red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>\<^sub>2, Normal ns\<^sub>2) \<and> R' ?\<omega>\<^sub>d ns\<^sub>2"
    using rel_success_elim[OF StepExhale \<open>R \<omega> ns\<close> step_exh]
    by blast

  \<comment> \<open>Step 2: inhale\<close>

  have step_inhale:
    "red_inhale ctxt_vpr StateCons (syntactic_mult (Rep_preal (Abs_preal v_p)) pred_body)
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
    by (metis StepInhale \<omega>'_rel \<omega>\<^sub>d_rel bpl_step_exh inh_perm_1 inhale_rel_normal_elim step_inhale)

  thus "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    using bpl_step_exh red_ast_bpl_transitive
    by blast

next

  fix \<omega> ns
  assume "R \<omega> ns"
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Unfold pred_id e_args (PureExp e_p)) \<omega> RFailure"

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) c'"
  proof cases
    case RedExhaleFailure
    fix v_args v_p
    assume e_args_eval: "red_pure_exps_total ctxt_vpr (Some \<omega>) e_args \<omega> (Some v_args)" and
           e_p_eval: "ctxt_vpr, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
           v_p_fail: "v_p \<le> 0 \<or> Rep_preal (get_mp_total_full \<omega> (pred_id, v_args)) < v_p"
    from v_p_fail have v_p_fail': "\<not> (0 \<le> v_p \<and> Abs_preal v_p \<le> (get_mp_total_full \<omega>) (pred_id,v_args))"
      apply (simp add: preal_to_real)
      using PermSimp TotalExpressions.RedLit_case e_p_eval
      by fastforce
    have step_exhale: "red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> RFailure"
      using ExhAccPred[OF _ e_args_eval e_p_eval, where ?mp="get_mp_total_full \<omega>"] v_p_fail'
      by (smt (verit) exh_if_total.simps(1))
    show ?thesis
      using rel_failure_elim[OF StepExhale \<open>R \<omega> ns\<close> step_exhale]
      by blast
  next
    case RedSubExpressionFailure
    have step_exhale: "red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> RFailure"
      apply (rule ExhSubExpFailure)
      using RedSubExpressionFailure
      by simp_all
    show ?thesis
      using rel_failure_elim[OF StepExhale \<open>R \<omega> ns\<close> step_exhale]
      by blast
  qed
qed

lemma unfold_exhale_rel_rel:
  assumes "rel_general (uncurry (\<lambda>\<omega>0 \<omega> ns. \<omega>0 = \<omega> \<and> R \<omega> ns)) (uncurry (\<lambda>\<omega>0 \<omega> ns. \<omega>0 = \<omega> \<and> R \<omega> ns))
             (\<lambda>\<omega>0_\<omega> \<omega>0_\<omega>'. red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) (snd \<omega>0_\<omega>) (RNormal (snd \<omega>0_\<omega>')))
             (\<lambda>\<omega>0_\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) (snd \<omega>0_\<omega>) RFailure)
             P ctxt_bpl \<gamma> \<gamma>'"
    shows "rel_general R R
             (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> (RNormal \<omega>'))
             (\<lambda>\<omega>. red_exhale ctxt_vpr StateCons \<omega> (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega> RFailure)
             P ctxt_bpl \<gamma> \<gamma>'"
  by (smt (verit, ccfv_SIG) assms rel_general_conseq rel_general_convert_2 uncurry.elims)

lemma unfold_exhale_pred_rel:
  assumes WfSubexp: "exprs_wf_rel
                       (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and>
                          Q (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) \<omega>def \<omega>)
                       ctxt_vpr StateCons P ctxt_bpl (e_args_vpr @ [e_p_vpr]) \<gamma> \<gamma>\<^sub>2"
      and CorrectPermRel:
            "\<And>v_args v_p.
               rel_general (uncurry R) (R' v_args v_p)
                 (\<lambda>\<omega>0_\<omega> \<omega>0_\<omega>'. \<omega>0_\<omega> = \<omega>0_\<omega>' \<and>
                    exhale_pred_acc_rel_assms ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) \<and>
                    exhale_pred_acc_rel_perm_success ctxt_vpr StateCons (snd \<omega>0_\<omega>) pred_id v_args v_p)
                 (\<lambda>\<omega>0_\<omega>.
                    exhale_pred_acc_rel_assms ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) \<and>
                    \<not> exhale_pred_acc_rel_perm_success ctxt_vpr StateCons (snd \<omega>0_\<omega>) pred_id v_args v_p)
                 P ctxt_bpl \<gamma>\<^sub>2 \<gamma>\<^sub>3"
      and UpdExhRel:
            "\<And>v_args v_p.
               rel_general (R' v_args v_p) (uncurry R) \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                 (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. fst \<omega>0_\<omega> = fst \<omega>0_\<omega>' \<and> exhale_pred_acc_normal_premise ctxt_vpr StateCons pred_id e_args_vpr e_p_vpr v_args v_p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) (snd \<omega>0_\<omega>'))
                 (\<lambda>_. False)
                 P ctxt_bpl \<gamma>\<^sub>3 \<gamma>'"
    shows "rel_general (uncurry R) (uncurry R)
             (\<lambda>\<omega>0_\<omega> \<omega>0_\<omega>'. red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) (snd \<omega>0_\<omega>) (RNormal (snd \<omega>0_\<omega>')))
             (\<lambda>\<omega>0_\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) (Atomic (AccPredicate pred_id e_args_vpr (PureExp e_p_vpr))) (snd \<omega>0_\<omega>) RFailure)
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
