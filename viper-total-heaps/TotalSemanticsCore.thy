section \<open>Core Semantics\<close>

theory TotalSemanticsCore
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState TotalViperState ViperCommon.Binop ViperCommon.DeBruijn ViperCommon.PredicatesUtil TotalStateUtil TotalResult
begin


subsection \<open>Type Definitions\<close>

type_synonym 'a heapfun_repr = "'a val list \<Rightarrow> 'a full_total_state \<rightharpoonup> 'a extended_val"
type_synonym 'a interp = "function_ident \<rightharpoonup> 'a heapfun_repr"

record 'a total_context =
  program_total :: program
  fun_interp_total :: "'a interp"
  absval_interp_total :: "'a \<Rightarrow> abs_type"


(* Some helper definitions. Not sure where to put these. *)

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {lh |lh. pgt (get_mh_total_full \<omega> lh) pnone}"

definition get_writeable_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_writeable_locs \<omega> = {lh |lh. (get_mh_total_full \<omega> lh) = pwrite}"


subsection \<open>Shift Operations\<close>

\<comment> \<open>Begin \<^term>\<open>shift_up\<close>\<close>
(* \<^term>\<open>shift_up\<close> only "unfolds" the specified predicate by one level.
   It does not check if the body of the predicate being unfolded is satisfied. *)

inductive shift_up :: "predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool" where
  ShiftAny:
  "\<lbrakk> mh = get_mh_nm nm;
     mp = get_mp_nm nm;
     Some pnm = get_nm_loc_nm nm (pred_id,vs);
     p = mp (pred_id,vs);
     q \<le> p;
     q \<noteq> 0;
     mp' = mp( (pred_id,vs) := p - q );
     fnm' = fnm( (pred_id,vs) := if q = p then None else Some (nested_mask_multiply pnm ((p - q) / p)) );
     nm' = NM mh np' fnm' \<rbrakk> \<Longrightarrow>
     shift_up pred_id vs q nm (nested_mask_merge nm' (nested_mask_multiply pnm (q / p)))"

\<comment> \<open>End \<^const>\<open>shift_up\<close>\<close>


subsection \<open>Internal Consistency\<close>

inductive total_heap_consistent_unfold_n :: "'a nested_mask \<Rightarrow> nat \<Rightarrow> bool"
  where
  Zero:
  "\<lbrakk> valid_heap_mask (get_mh_nm nm)
   \<rbrakk> \<Longrightarrow>
   total_heap_consistent_unfold_n nm 0"
| UnfoldStep:
  "\<lbrakk> \<And> pred_id vs q nm'. q \<le> get_mp_nm nm (pred_id,vs) \<Longrightarrow> q > 0 \<Longrightarrow>
         shift_up pred_id vs q nm nm' \<Longrightarrow>
         total_heap_consistent_unfold_n nm' n
   \<rbrakk> \<Longrightarrow>
   total_heap_consistent_unfold_n nm (Suc n)"

inductive_cases UnfoldStep_cases: "total_heap_consistent_unfold_n nm (Suc n)"

definition total_heap_consistent :: "'a total_state \<Rightarrow> bool" where
  "total_heap_consistent \<phi> \<equiv> \<forall> n. total_heap_consistent_unfold_n (get_nm_total \<phi>) n"


subsection \<open>Pure Expression Evaluation\<close>

fun sub_pure_exp_total :: "pure_exp \<Rightarrow> pure_exp list" where
  "sub_pure_exp_total (Unop _ e) = [e]"
\<comment>\<open>the second expression of a binary expression might not be evaluated due to lazy binary operators\<close>
| "sub_pure_exp_total (Binop e _ _) = [e]"
| "sub_pure_exp_total (FieldAcc e _) = [e]"
| "sub_pure_exp_total (Let e _) = [e]"
| "sub_pure_exp_total (Perm e _) = [e]"
| "sub_pure_exp_total (CondExp e _ _) = [e]"
| "sub_pure_exp_total (PermPred _ exps) = exps"
| "sub_pure_exp_total (FunApp _ exps) = exps"
| "sub_pure_exp_total (Unfolding _ exps e) = exps"
| "sub_pure_exp_total _ = []"

fun sub_expressions_exp_or_wildcard :: "pure_exp exp_or_wildcard \<Rightarrow> pure_exp list" where
  "sub_expressions_exp_or_wildcard (PureExp e) = [e]"
| "sub_expressions_exp_or_wildcard Wildcard = []"

fun sub_expressions_atomic :: "pure_exp atomic_assert \<Rightarrow> pure_exp list" where
  "sub_expressions_atomic (Pure e) = [e]"
| "sub_expressions_atomic (Acc x f p) = x # sub_expressions_exp_or_wildcard p"
| "sub_expressions_atomic (AccPredicate P exps p) = exps @ sub_expressions_exp_or_wildcard p"

fun direct_sub_expressions_assertion :: "assertion \<Rightarrow> pure_exp list" where
  "direct_sub_expressions_assertion (Atomic A) = sub_expressions_atomic A"
| "direct_sub_expressions_assertion (Imp e A) = [e]"
| "direct_sub_expressions_assertion (CondAssert e A B) = [e]"
| "direct_sub_expressions_assertion _ = []"

inductive red_pure_exp_total :: "'a total_context \<Rightarrow> 'a full_total_state option \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a extended_val \<Rightarrow> bool" ("_, _ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>]\<^sub>t _)" [51,51,0,51,51] 81) and
  red_pure_exps_total :: "'a total_context \<Rightarrow> 'a full_total_state option \<Rightarrow> pure_exp list \<Rightarrow> 'a full_total_state \<Rightarrow> (('a val) list) option \<Rightarrow> bool"
  for ctxt :: "'a total_context" where

\<comment>\<open>Pure expression evaluation and well-definedness of pure expressions\<close>

\<comment>\<open>Atomic expressions\<close>
  RedLit: "ctxt, \<omega>_def \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t Val (val_of_lit l)"
| RedVar: "\<lbrakk> (get_store_total \<omega>) n = Some v \<rbrakk> \<Longrightarrow> ctxt, \<omega>_def \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedResult: "\<lbrakk> get_store_total \<omega> 0 = Some v \<rbrakk> \<Longrightarrow> ctxt, \<omega>_def \<turnstile> \<langle>Result; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

\<comment>\<open>Binop and Unop\<close>
| RedBinopLazy:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; eval_binop_lazy v1 bop = Some v \<rbrakk>\<Longrightarrow>
     ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinop:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ;
     ctxt, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ;
     eval_binop_lazy v1 bop = None;
     eval_binop v1 bop v2 = BinopNormal v \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinopRightFailure:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1;
     ctxt, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure;
     eval_binop_lazy v1 bop = None;
     \<comment>\<open>The following premise makes sure in this case that the binary operation does not reduce if
       e1 evaluates to a value that renders the binary operation ill-typed\<close>
     (\<exists> v2. eval_binop v1 bop v2 \<noteq> BinopTypeFailure) \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedBinopOpFailure:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1;
     ctxt, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2;
     eval_binop v1 bop v2 = BinopOpFailure;
     eval_binop_lazy v1 bop = None \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" \<comment>\<open>happens for division by 0, modulo 0\<close>

| RedUnop:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v;
     eval_unop unop v = BinopNormal v' \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"

\<comment>\<open>Cond\<close>
| RedCondExpTrue:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) ;
     ctxt, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedCondExpFalse:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) ;
     ctxt, \<omega>_def \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"

\<comment>\<open>Old\<close>
| RedOld:
  "\<lbrakk> get_trace_total \<omega> l = Some \<phi> ;
     \<omega>_def' = map_option (\<lambda>\<omega>_def_val. \<omega>_def_val\<lparr> get_total_full := \<phi> \<rparr>) \<omega>_def;
     ctxt, \<omega>_def' \<turnstile> \<langle>e; \<omega>\<lparr> get_total_full := \<phi> \<rparr>\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Old l e; \<omega>\<rangle> [\<Down>]\<^sub>t v"
| RedOldFailure:
  "\<lbrakk> get_trace_total \<omega> l = None \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Old l e ; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

\<comment>\<open>Heap lookup\<close>
| RedField:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
     get_hh_total_full \<omega> (a, f) = v \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t (if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) \<omega>_def) then Val v else VFailure)"
| RedFieldNullFailure:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

\<comment>\<open>
\<comment>\<open>Function application\<close>
| RedFunApp: (* Should function application be expressed operationally? *)
  "\<lbrakk> (fun_interp_total ctxt) fname = Some f;
     red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs);
     \<comment>\<open>TODO: The precondition of a function needs to be checked w.r.t. the well-definedness state.
              One could define two interpretations of the function, one that checks the precondition
              and one that does not.\<close>
     f vs \<omega> = Some res \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>FunApp fname es; \<omega>\<rangle> [\<Down>] res"
\<close>

\<comment>\<open>Permission introspection\<close>
| RedPermNull:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
| RedPerm:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
     get_mh_total_full \<omega> (a, f) = v \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal v))"

\<comment>\<open>Unfolding\<close>
\<comment> \<open>Viper allows unfolding a fraction of a predicate. Not reflected in the semantics?
     e.g. unfolding acc(P(x), 1/2) in x.f == 1\<close>
| RedUnfolding:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow>
   ctxt, None \<turnstile> \<langle>Unfolding p es ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v"
| RedUnfoldingDefNoPred:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>_def) es \<omega> (Some vs);
     ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     get_mp_total_full \<omega>_def (pred_id,vs) < 1 \<rbrakk> \<Longrightarrow> \<comment>\<open>insufficient permission\<close>
   ctxt, (Some \<omega>_def) \<turnstile> \<langle>Unfolding p es ubody ; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedUnfoldingDef:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>_def) es \<omega> (Some vs);
     shift_up p vs 1 (get_nm_total_full \<omega>_def) nm';
     \<omega>'_def = \<omega>_def \<lparr> get_total_full := get_total_full \<omega>_def \<lparr> get_nm_total := nm' \<rparr> \<rparr>;
     ctxt, (Some \<omega>'_def) \<turnstile> \<langle>ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow>
   ctxt, (Some \<omega>_def) \<turnstile> \<langle>Unfolding p es ubody ; \<omega>\<rangle> [\<Down>]\<^sub>t v"

\<comment>\<open>Important: \<^const>\<open>sub_pure_exp_total\<close> should not include the body of an unfolding\<close>
| RedSubFailure:
  "\<lbrakk> (sub_pure_exp_total e') \<noteq> [];
     red_pure_exps_total ctxt \<omega>_def (sub_pure_exp_total e') \<omega> None \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>e'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

\<comment>\<open>List of expressions\<close>
| RedExpListCons:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v;
     red_pure_exps_total ctxt \<omega>_def es \<omega> res;
     res' = map_option (\<lambda>vs. (v#vs)) res \<rbrakk> \<Longrightarrow>
   red_pure_exps_total ctxt \<omega>_def (e#es) \<omega> res'"
| RedExpListFailure:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>
   red_pure_exps_total ctxt \<omega>_def (e#es) \<omega> None"
| RedExpListNil:
  "red_pure_exps_total ctxt \<omega>_def Nil \<omega> (Some Nil)"


subsection \<open>Exhale\<close>

fun exh_if_total :: "bool \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total"  where
  "exh_if_total False _ = RFailure"
| "exh_if_total True \<omega> = RNormal \<omega>"

inductive red_exhale :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total \<Rightarrow> bool"
  for ctxt :: "'a total_context" and \<omega>0 :: "'a full_total_state" where

\<comment>\<open>exhale acc(e.f, p)\<close>
  ExhAcc:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     a = the_address r
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) \<omega>
     (exh_if_total (p \<ge> 0 \<and> (if r = Null then p = 0 else mh (a,f) \<ge> Abs_preal p))
                    (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a,f) ((mh (a,f)) - (Abs_preal p))))"

\<comment>\<open>Exhaling wildcard removes some non-zero permission that is less than the current permission held.\<close>
| ExhAccWildcard:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     a = the_address r;
     \<comment>\<open>\<^term>\<open>q\<close> satisfies the right-hand side if \<^prop>\<open>mh (a,f) \<noteq> 0\<close> (thm prat_exists_stricly_smaller_nonzero).
     If \<^prop>\<open>mh (a,f) \<noteq> 0\<close> does not hold, then the exhale fails and the value of q is irrelevant. \<close>
     q = (SOME p. p \<noteq> 0 \<and> mh (a,f) > p)
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (Acc e_r f Wildcard)) \<omega>
     (exh_if_total (mh (a,f) \<noteq> 0 \<and> r \<noteq> Null)
                    (update_mh_loc_total_full \<omega> (a,f) q))"

\<comment>\<open>exhale acc(P(es), p)\<close>
\<comment> \<open>TODO: remove the corresponding fraction of the nested mask when exhaling a predicate\<close>
| ExhAccPred:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt (Some \<omega>0) e_args \<omega> (Some v_args);
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>
     (exh_if_total (p \<ge> 0 \<and> mp (pred_id, v_args) \<ge> Abs_preal p)
                   (update_mp_loc_total_full \<omega> (pred_id, v_args) (mp (pred_id, v_args) - (Abs_preal p))))"
| ExhAccPredWildcard:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt (Some \<omega>0) e_args \<omega> (Some v_args);
     \<comment>\<open>q satisfies the right-hand side if \<^prop>\<open>mp (pred_id, v_args) \<noteq> 0\<close> (thm prat_exists_strictly_smaller_nonzero).
     If \<^prop>\<open>mp (pred_id, v_args) \<noteq> 0\<close> does not hold, then the exhale fails and the value of q is irrelevant.\<close>
     q = (SOME p. p \<noteq> 0 \<and> mp (pred_id, v_args) > p)
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega>
     (exh_if_total (mp (pred_id, v_args) \<noteq> 0)
                   (update_mp_loc_total_full \<omega> (pred_id, v_args) q))"

| ExhPure:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (Pure e)) \<omega> (exh_if_total b \<omega>)"

\<comment>\<open>exhale A && B\<close>
| ExhStarNormal:
  "\<lbrakk> red_exhale ctxt \<omega>0 A \<omega> (RNormal \<omega>');
     red_exhale ctxt \<omega>0 B \<omega>' res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (A && B) \<omega> res"
| ExhStarFailure:
  "\<lbrakk> red_exhale ctxt \<omega>0 A \<omega> RFailure \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (A && B) \<omega> RFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
| ExhImpTrue:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     red_exhale ctxt \<omega>0 A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Imp e A) \<omega> res"
| ExhImpFalse:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Imp e A) \<omega> (RNormal \<omega>)"

\<comment>\<open>exhale e ? A : B\<close>
| ExhCondTrue:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     red_exhale ctxt \<omega>0 A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (CondAssert e A B) \<omega> res"
| ExhCondFalse:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
     red_exhale ctxt \<omega>0 B \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (CondAssert e A B) \<omega> res"

\<comment>\<open>If a \<^emph>\<open>direct\<close> subexpression is not well-defined, then this results in failure.\<close>
| ExhSubExpFailure:
  "\<lbrakk> direct_sub_expressions_assertion A \<noteq> [];
     red_pure_exps_total ctxt (Some \<omega>0) (direct_sub_expressions_assertion A) \<omega> None
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 A \<omega> RFailure"


subsection \<open>Satisfiability\<close>

fun zero_mh :: "field_mask" where
  "zero_mh _ = 0"

fun zero_mp :: "'a predicate_mask" where
  "zero_mp _ = 0"

fun singleton_mh :: "heap_loc \<Rightarrow> preal \<Rightarrow> field_mask" where
  "singleton_mh loc p l = (if l = loc then p else 0)"

fun singleton_mp :: "'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a predicate_mask" where
  "singleton_mp ploc p pl = (if pl = ploc then p else 0)"

fun is_singleton_mh :: "heap_loc \<Rightarrow> field_mask \<Rightarrow> bool" where
  "is_singleton_mh loc mh = (\<exists>p > 0. mh = singleton_mh loc p)"

fun is_singleton_mp :: "'a predicate_loc \<Rightarrow> 'a predicate_mask \<Rightarrow> bool" where
  "is_singleton_mp ploc mp = (\<exists>p > 0. mp = singleton_mp ploc p)"

inductive sat :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> bool"
  for ctxt :: "'a total_context" and \<omega> :: "'a full_total_state" where

\<comment>\<open>sat acc(e.f, p)
  The mask must have exactly p amount of permission.\<close>
  SatAcc:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     a = the_address r;
     p \<ge> 0;
     if r = Null then p = 0 else mh = singleton_mh (a,f) (Abs_preal p);
     get_mp_total_full \<omega> = zero_mp
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (Atomic (Acc e_r f (PureExp e_p)))"

\<comment>\<open>A wildcard permission accepts any positive amount of permission.\<close>
| SatAccWildcard:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     a = the_address r;
     \<comment>\<open>\<^term>\<open>q\<close> satisfies the right-hand side if \<^prop>\<open>mh (a,f) \<noteq> 0\<close> (thm prat_exists_stricly_smaller_nonzero).
     If \<^prop>\<open>mh (a,f) \<noteq> 0\<close> does not hold, then the exhale fails and the value of q is irrelevant. \<close>
     r \<noteq> Null;
     is_singleton_mh (a,f) mh
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (Atomic (Acc e_r f Wildcard))"

\<comment>\<open>sat acc(P(es), p)\<close>
\<comment> \<open>TODO: remove the corresponding fraction of the nested mask when exhaling a predicate\<close>
| SatAccPred:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     p \<ge> 0;
     mh = singleton_mp (pred_id,v_args) (Abs_preal p)
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"

| SatAccPredWildcard:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args);
     is_singleton_mp (pred_id,v_args) mp
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (Atomic (AccPredicate pred_id e_args Wildcard))"

| SatPure:
  "\<lbrakk> ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (Atomic (Pure e))"

\<comment>\<open>sat A && B\<close>
| SatStar:
  "\<lbrakk> sat ctxt \<omega> A;
     sat ctxt \<omega> B
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (A && B)" \<comment> \<open>TODO: split the state\<close>

\<comment>\<open>sat A \<longrightarrow> B\<close>
| SatImpTrue:
  "\<lbrakk> ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     sat ctxt \<omega> A
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (Imp e A)"
| SatImpFalse:
  "\<lbrakk> ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (Imp e A)"

\<comment>\<open>sat e ? A : B\<close>
| SatCondTrue:
  "\<lbrakk> ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     sat ctxt \<omega> A
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (CondAssert e A B)"
| SatCondFalse:
  "\<lbrakk> ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
     sat ctxt \<omega> B
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> (CondAssert e A B)"


subsection \<open>External Consistency\<close>

inductive consistent_external_n :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> nat \<Rightarrow> bool"
  for ctxt :: "'a total_context" where
  SatBase:
  "consistent_external_n ctxt \<omega> ploc p 0"
| SatStep:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     sat ctxt \<omega> (syntactic_mult (Rep_preal p) pred_body);
     \<And>pred_id vs q nm' \<omega>''. get_mp_total_full \<omega> (pred_id,vs) = q \<Longrightarrow> q > 0 \<Longrightarrow>
       Some nm' = get_nm_loc_total_full \<omega> (pred_id,vs) \<Longrightarrow>
       \<omega>'' = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = \<phi>'\<lparr> get_nm_total := nm' \<rparr> \<rparr> \<Longrightarrow>
       consistent_external_n ctxt \<omega>'' (pred_id,vs) q n
   \<rbrakk> \<Longrightarrow>
   consistent_external_n ctxt \<omega> ploc p (Suc n)"

definition consistent_external :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> bool"
  where "consistent_external ctxt \<omega> ploc p \<equiv> \<forall>n. consistent_external_n ctxt \<omega> ploc p n"


subsection \<open>Inhale\<close>

(* The general question is, if we put consistent checks inside inhale or inside statement reduction. *)

definition inhale_perm_single :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> preal option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single \<omega> lh p_opt =
    { \<omega>'| \<omega>' q.
            option_fold ((=) q) (q \<noteq> 0) p_opt \<and>
            get_mh_total_full \<omega> lh + q \<le> 1 \<and>  \<comment> \<open>There can be at most 1 field permission\<close>
               \<comment> \<open>Do we really need the check here? Or it is covered in consistency?\<close>
            \<omega>' = update_mh_loc_total_full \<omega> lh (get_mh_total_full \<omega> lh + q)
    }"

definition inhale_perm_single_pred :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single_pred ctxt \<omega> lp p_opt =
    { \<omega>'| \<omega>' \<omega>_inh q.
            option_fold ((=) q) (q \<noteq> 0) p_opt \<and>
            consistent_external ctxt \<omega>_inh lp q \<and> \<comment> \<open>Needs to decide the signature of \<^term>\<open>sat\<close>\<close>
            \<comment> \<open>TODO\<close>
            \<omega>' = add_to_nm_loc_total_full (update_mp_loc_total_full \<omega> lp (get_mp_total_full \<omega> lp + q)) lp (get_nm_total_full \<omega>_inh)
    }"

inductive red_inhale :: "'a total_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total \<Rightarrow> bool" where
\<comment>\<open>Atomic inhale\<close>
  InhAcc:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     ctxt, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     W' = (if r = Null then {\<omega>} else inhale_perm_single \<omega> (the_address r,f) (Some (Abs_preal p)));
     th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (Acc e_r f (PureExp e_p))) \<omega> res"
| InhAccPred:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     W' = inhale_perm_single_pred ctxt \<omega> (pred_id, v_args) (Some (Abs_preal p));
     th_result_rel (p \<ge> 0) (W' \<noteq> {}) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> res"
| InhAccWildcard:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     W' = inhale_perm_single \<omega> (the_address r,f) None;
     th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (Acc e_r f Wildcard)) \<omega> res"
| InhAccPredWildcard:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args);
     W' = inhale_perm_single_pred ctxt \<omega> (pred_id, v_args) None;
     th_result_rel True (W' \<noteq> {}) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega> res"
| InhPure:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic)"

\<comment>\<open>Connectives inhale\<close>
| InhStarNormal:
  "\<lbrakk> red_inhale ctxt A \<omega> (RNormal \<omega>'');
     red_inhale ctxt B \<omega>'' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (A && B) \<omega> res"
| InhStarFailureMagic:
  "\<lbrakk> red_inhale ctxt A \<omega> resA;
     resA = RFailure \<or> resA = RMagic
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (A && B) \<omega> resA"
| InhImpTrue:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True));
     red_inhale ctxt A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Imp e A) \<omega> res"
| InhImpFalse:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Imp e A) \<omega> (RNormal \<omega>)"
| InhCondAssertTrue:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True));
     red_inhale ctxt A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (CondAssert e A B) \<omega> res"
| InhCondAssertFalse:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
     red_inhale ctxt B \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (CondAssert e A B) \<omega> res"

\<comment>\<open>If a \<^emph>\<open>direct\<close> subexpression is not well-defined, then this results in failure.\<close>
| InhSubExpFailure:
  "\<lbrakk> (direct_sub_expressions_assertion A) \<noteq> [];
     red_pure_exps_total ctxt (Some \<omega>) (direct_sub_expressions_assertion A) \<omega> None
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt A \<omega> RFailure"


subsection \<open>Unfold\<close>

(* \<^term>\<open>unfold_rel\<close> unfolds a consistent predicate. *)

inductive unfold_rel :: "'a total_context \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state \<Rightarrow> bool" where
  UnfoldRel:
  "\<lbrakk> shift_up pred_id vs p nm nm';
     get_nm_total \<phi> = nm;
     get_nm_total \<phi>' = nm'
     \<comment> \<open>TODO\<close>
   \<rbrakk> \<Longrightarrow>
   unfold_rel ctxt pred_id vs p \<phi> \<phi>'"

subsection \<open>Fold\<close>

inductive fold_rel :: "'a total_context \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total \<Rightarrow> bool" where
  FoldRelNormal:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     q \<noteq> 0;
     \<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>;
     red_exhale ctxt \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 (RNormal \<omega>1);
     nm_exh = nested_mask_subtract (get_nm_total_full \<omega>0) (get_nm_total_full \<omega>1);
     \<omega>' = \<lparr> get_store_total = get_store_total \<omega>,
            get_trace_total = get_trace_total \<omega>,
            get_total_full = add_to_nm_loc_total
              (update_mp_loc_total (get_total_full \<omega>1) (pred_id,vs) (get_mp_total (get_total_full \<omega>1) (pred_id, vs) + q))
              (pred_id,vs) nm_exh
              \<comment> \<open>The code is a bit messy here. What we describe is first increasing the permission mask by q, and then merging the nested mask with the exhaled nested mask.\<close>
          \<rparr>
   \<rbrakk> \<Longrightarrow>
   fold_rel ctxt pred_id vs q \<omega> (RNormal \<omega>')"
| FoldRelFailure:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     q \<noteq> 0;
     \<omega>0 = \<lparr> get_store_total = nth_option vs,
            get_trace_total = Map.empty,
            get_total_full = get_total_full \<omega> \<rparr>;
     red_exhale ctxt \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 RFailure
   \<rbrakk> \<Longrightarrow>
   fold_rel ctxt pred_id vs q \<omega> RFailure"

end
