section \<open>Pure Expression Evaluation\<close>

theory TotalExpressions
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState ViperCommon.Binop ViperCommon.PredicatesUtil
          TotalContext TotalViperState TotalStateUtil TotalResult
begin


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
     eval_binop (Option.is_none \<omega>_def) v1 bop v2 = BinopNormal v \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinopRightFailure:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1;
     ctxt, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure;
     eval_binop_lazy v1 bop = None;
     \<comment>\<open>The following premise makes sure in this case that the binary operation does not reduce if
       e1 evaluates to a value that renders the binary operation ill-typed\<close>
     (\<exists> v2. eval_binop (Option.is_none \<omega>_def) v1 bop v2 \<noteq> BinopTypeFailure) \<rbrakk> \<Longrightarrow>
   ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedBinopOpFailure:
  "\<lbrakk> ctxt, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1;
     ctxt, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2;
     eval_binop (Option.is_none \<omega>_def) v1 bop v2 = BinopOpFailure;
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
     get_mp_total_full \<omega>_def (pred_id,vs) = 0 \<rbrakk> \<Longrightarrow> \<comment>\<open>insufficient permission\<close>
   ctxt, (Some \<omega>_def) \<turnstile> \<langle>Unfolding p es ubody ; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedUnfoldingDef:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>_def) es \<omega> (Some vs);
     perm = get_mp_total_full \<omega>_def (pred_id,vs);
     shift_up p vs (perm / Abs_preal 2) (get_nm_total_full \<omega>_def) nm';
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

inductive_cases RedBinop_case: "ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
inductive_cases RedOld_case: "ctxt, \<omega>_def \<turnstile> \<langle>RedOld \<omega> l \<phi> \<omega>_def' \<omega>_def e v; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

end
