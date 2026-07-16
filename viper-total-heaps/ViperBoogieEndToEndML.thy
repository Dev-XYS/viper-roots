theory ViperBoogieEndToEndML
imports TotalViperSimulation.ViperBoogieEndToEnd CPGHelperML ViperBoogieHelperML TotalViperSimulation.ViperBoogieFunctionInst
begin

ML \<open>

  fun post_framing_rel_init_tac ctxt (info : basic_stmt_rel_info) lookup_heap_var_thm lookup_mask_var_thm =
    (Rmsg' "Post Framing Init - Start" (resolve_tac ctxt [ @{thm post_framing_rel_aux} OF [#wf_ty_repr_thm info, #consistency_wf_thm info]]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Type Interp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Domain Type" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Program" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Lookup Heap"
            (simp_tac_with_thms [#ty_repr_def_thm info] ctxt THEN'
            resolve_tac ctxt [lookup_heap_var_thm]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Lookup Mask"
            (simp_tac_with_thms [#ty_repr_def_thm info] ctxt THEN'
             resolve_tac ctxt [lookup_mask_var_thm]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Zero Mask"
            (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Disjointntess" ((#aux_var_disj_tac info) ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Heap and Mask Disjoint" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Propagate 1"
         (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN'
         resolve_tac ctxt @{thms red_ast_bpl_rel_if_nondet_then} THEN'
         (* One_nat_def is applied as a hack to match 1 and Suc 0.
           It would be good to solve this problem more generally such that there cannot be such
           mismatches at this point *)
         progress_red_bpl_rel_tac_2 (fn ctxt => simp_only_tac @{thms One_nat_def} ctxt) ctxt THEN'
         simplify_continuation ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Propagate 2" (resolve_tac ctxt @{thms stmt_rel_propagate_same_rel}) ctxt) THEN'
    (Rmsg' "Post Framing Init - Assume Good State" (progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm info) (#tr_def_thm info)) ctxt)

\<close>

method fun_interp_wf_aux_tac for fid :: fun_enum_bpl uses fun_wf_thm ty_repr_def wf_ty_repr_thm fun_repr_inj_thm =
      ((rule exI, rule conjI),
      (rule fun_interp_vpr_bpl_concrete_lookup[where ?fid=fid, OF fun_repr_inj_thm]),
      simp,
      simp,
      (simp del: fun_interp_single_wf.simps fun_interp_single_wf_2.simps),
      (rule lift_fun_decl_fun_interp_single_wf_eq[OF _ fun_wf_thm[OF wf_ty_repr_thm], simplified]);
      (simp add: ty_repr_def ty_repr_basic_def))

lemmas axioms_sat_proof_del = vbpl_absval_ty.simps type_of_val.simps full_ext_env.simps

method simplify_bound_var_tac uses inversion_type_of_vbpl_val_equalities_concrete =
   (simp add: inversion_type_of_vbpl_val_equalities_concrete realv_inversion_type_of_vbpl_val del: axioms_sat_proof_del id_apply),
   (erule conjE, erule exE)+,
   (simp only: id_apply)

method axiom_proof_init uses inversion_type_of_vbpl_val_equalities_concrete =
   (simp only: expr_sat_def),
   ((rule RedForallT_True | rule RedForAllTrue)+ | succeed),
   (simplify_bound_var_tac inversion_type_of_vbpl_val_equalities_concrete: inversion_type_of_vbpl_val_equalities_concrete) ? \<comment>\<open>only makes sense if there is at least one universal value quantifier\<close>

ML \<open>

  \<comment>\<open>TODO: move to same location as add_simps\<close>
  fun del_simps [] ctxt = ctxt
   |  del_simps (thm::thms) ctxt = del_simps thms (Simplifier.del_simp thm ctxt)

  type axiom_tac_data = {
    lookup_const_tac : (int -> tactic),
    finterp_eval_tac : (Proof.context -> term -> int -> tactic),
    fun_interp_inst_def_thm: thm,
    lookup_field_tac: (int -> tactic),
    fun_repr_inj_thm: thm
  }

  fun extract_fun_name t =
    case Logic.strip_assums_concl t of
      @{term "Trueprop"} $ t' => extract_fun_name t'
    | Const (@{const_name HOL.eq}, _) $ _ $ fname => fname
    | t => raise TERM ("cannot extract Boogie function name", [t])

  fun extract_fun_enum_bpl t =
    case t of
      @{term "Trueprop"} $ t' => extract_fun_enum_bpl t'
    | Const (@{const_name HOL.eq}, _) $ lhs $ _ => extract_fun_enum_bpl lhs
    | Const (@{const_name "fun_interp_vpr_bpl"}, _)
           $ _ (* program *)
           $ _ (* type representation *)
           $ _ (* field translation *)
           $ fun_enum
           $ _ (* type parameters *)
           $ _ (* function arguments *) =>
             fun_enum
    | _ => raise TERM ("goal is not fun_interp_vpr_bpl", [t])

  fun axiom_aux_tac ctxt lookup_const_thms del_thms (axiom_tac_data : axiom_tac_data) =
    FIRST_AND_THEN' [
       resolve_tac ctxt @{thms RedVar},
       resolve_tac ctxt @{thms RedBVar},
       resolve_tac ctxt @{thms RedBinOp},
       resolve_tac ctxt @{thms RedFunOp},
       resolve_tac ctxt @{thms RedLit},
       resolve_tac ctxt @{thms RedUnOp},
       Rmsg' "Unexpected case" (K no_tac) ctxt
    ] [
      (* Var *)
      (Rmsg' "RedVar" ( (#lookup_const_tac axiom_tac_data |> SOLVED') ORELSE'
                        (#lookup_field_tac axiom_tac_data |> SOLVED')) ctxt),

      (* BVar *)
       Rmsg' "RedBVar simp" (assm_full_simp_solved_tac ctxt) ctxt,

      (* BinOp *)
       (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       Rmsg' "RedBinOp simp" (assm_full_simp_solved_tac ctxt) ctxt,

      (* FunOp *)
       (Rmsg' "RedFunOp init"
         (simp_only_tac [#fun_interp_inst_def_thm axiom_tac_data] ctxt THEN'
          resolve_tac ctxt [@{thm fun_interp_vpr_bpl_concrete_lookup} OF [#fun_repr_inj_thm axiom_tac_data]] THEN'
          (SUBGOAL (fn (t,i) => (let val fname = HOLogic.dest_string (extract_fun_name t) in
             writeln (if String.isSuffix "#sm" fname then "a" else "b");
             if not (String.isSuffix "#sm" fname)
               \<comment> \<open>\<^const>\<open>fun_repr_concrete\<close> of \<^const>\<open>FPredicateLoc\<close> and \<^const>\<open>FPredicateSMLoc\<close> is too general.
                   If we do not make the case distinction here, the resolution of a function name like "P#sm"
                   will default to \<^const>\<open>FPredicateLoc\<close>.
                   Possible alternative solution: change the order in the definition of \<^const>\<open>fun_repr_concrete\<close>.\<close>
               then fast_tac (ctxt addIs @{thms fun_repr_concrete.simps}) i
               else fast_tac (ctxt addIs [simp_thm ctxt (inst ctxt @{thm fun_repr_concrete.simps(14)} (HOLogic.mk_string (str_trimr fname 3))) @{thms append.simps}]) i
             end
          ))) THEN'
          assm_full_simp_solved_tac ctxt) ctxt) THEN'

       (* function arguments *)
       (fn i => fn st => axiom_aux_list_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       (* function interpretation evaluation *)
       (Rmsg' "RedFunOp finish"
          (SUBGOAL (fn (t,i) => (#finterp_eval_tac axiom_tac_data) ctxt (extract_fun_enum_bpl (Logic.strip_assums_concl t)) i) |> SOLVED') ctxt),

       (* Lit *)
       K all_tac,

       (* UnOp *)
       (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       Rmsg' "ReUnOp simp" (assm_full_simp_solved_tac ctxt) ctxt,

       (* unexpected case *)
       K no_tac
     ]

and axiom_aux_list_tac ctxt lookup_const_thms del_thms (axiom_tac_data : axiom_tac_data) =
    FIRST_AND_THEN'
      [ resolve_tac ctxt @{thms RedExpListCons},
        resolve_tac ctxt @{thms RedExpListNil},
        Rmsg' "Unexpected case: axiom_aux_list_tac" (K no_tac) ctxt
      ]
      [ (* cons *)
        ((fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) |> SOLVED') THEN'
        (fn i => fn st => axiom_aux_list_tac ctxt lookup_const_thms del_thms axiom_tac_data i st),

        (* nil *)
        K all_tac,

       (* unexpected case *)
        K no_tac
      ]

fun finterp_eval_concrete_tac del_thms ty_repr_def wf_ty_repr ctxt t =
  case t of
    Const (@{const_name FReadHeap}, _) =>
     asm_full_simp_tac (del_simps (@{thm fun_upd_apply}::del_thms) (add_simps [ty_repr_def, @{thm lift_fun_bpl_def}, @{thm heap_upd_ty_preserved_2_concrete} OF [wf_ty_repr]] ctxt)) THEN'
     asm_full_simp_tac (del_simps (@{thm fun_upd_apply}::del_thms) (add_simps @{thms ty_repr_basic_def} ctxt))
  | Const (@{const_name FReadMask}, _) =>
     asm_full_simp_tac (del_simps (@{thm fun_upd_apply}::del_thms) (add_simps [ty_repr_def, @{thm lift_fun_bpl_def}] ctxt)) THEN'
     asm_full_simp_tac (del_simps @{thms fun_upd_apply} (add_simps @{thms ty_repr_basic_def} ctxt))
  | Const (@{const_name FReadKnownFoldedMask}, _) =>
     asm_full_simp_tac (del_simps (@{thm fun_upd_apply}::del_thms) (add_simps [ty_repr_def, @{thm lift_fun_bpl_def}] ctxt)) THEN'
     asm_full_simp_tac (del_simps @{thms fun_upd_apply} (add_simps @{thms ty_repr_basic_def} ctxt))
  | Const (@{const_name FIsPredicateField}, _) =>
     (* (SUBGOAL (fn (t,_) => raise TERM ("breakpoint", [t]))) THEN' *)
     asm_full_simp_tac (add_simps (ty_repr_def::(@{thms lift_fun_bpl_def ty_repr_basic_def ty_bpl_normal_field})) ctxt)
  | Const (@{const_name FPredicateMaskField}, _) =>
     asm_full_simp_tac (add_simps (ty_repr_def::(@{thms lift_fun_bpl_def ty_repr_basic_def ty_bpl_normal_field})) ctxt)
  | Const (@{const_name FPredicateLoc}, _) $ _ $ _ =>
     asm_full_simp_tac (add_simps (ty_repr_def::(@{thms lift_fun_bpl_def ty_repr_basic_def ty_bpl_normal_field})) ctxt)
     (* For some unknown reason, we could not delete those lemmas to prove this case.
        Todo: Investigate this. *)
  | _ =>
     asm_full_simp_tac (del_simps del_thms (add_simps (ty_repr_def::(@{thms lift_fun_bpl_def ty_repr_basic_def ty_bpl_normal_field})) ctxt))

fun axiom_tac ctxt fun_interp_inst_def_thm lookup_const_thms lookup_fields_thms del_thms ty_repr_def wf_ty_repr fun_repr_inj_thm =
  let val axiom_tac_data : axiom_tac_data = {
     lookup_const_tac = asm_full_simp_tac (del_simps del_thms (add_simps (@{thm lookup_full_ext_env_same} :: lookup_const_thms) ctxt)),
     lookup_field_tac = asm_full_simp_tac (del_simps del_thms (add_simps (@{thm lookup_full_ext_env_same} :: lookup_fields_thms) ctxt)),
     finterp_eval_tac = finterp_eval_concrete_tac del_thms ty_repr_def wf_ty_repr,
     fun_interp_inst_def_thm = fun_interp_inst_def_thm,
     fun_repr_inj_thm = fun_repr_inj_thm
  }
  in (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st)
  end

\<close>

method axiom_prove_ploc_inject =
  (intro impI),
  (intro conjI)?;
  (insert val_inject_bpl_vpr');
  fastforce

end