theory PredicateRel
  imports InhaleRel
begin

lemma case_inside:
  assumes "\<And>x. P x \<Longrightarrow> Q x"
      and "\<And>x. \<not> P x \<Longrightarrow> Q x"
    shows "\<And>x. Q x"
  using assms
  by blast

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
    using \<omega>'
                  apply fastforce
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


end
