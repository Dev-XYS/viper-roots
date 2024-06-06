section \<open>Core Semantics\<close>

theory TotalSemanticsCore
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState TotalViperState ViperCommon.Binop ViperCommon.DeBruijn ViperCommon.PredicatesUtil TotalStateUtil
begin


subsection \<open>Type Definitions\<close>

type_synonym 'a heapfun_repr = "'a val list \<Rightarrow> 'a full_total_state \<rightharpoonup> 'a extended_val"
type_synonym 'a interp = "function_ident \<rightharpoonup> 'a heapfun_repr"

record 'a total_context =
  program_total :: program
  fun_interp_total :: "'a interp"
  absval_interp_total :: "'a \<Rightarrow> abs_type"


subsection \<open>Shift Operations\<close>

(* TODO: Move these utility definitions elsewhere. *)
definition fun_comb :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" ("_ +\<lbrakk> _ \<rbrakk>+ _") where
  "(f +\<lbrakk>c\<rbrakk>+ g) x = c (f x) (g x)"

definition pfun_comb :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" ("_ +\<lparr> _ \<rparr>+ _") where
  "(f +\<lparr>c\<rparr>+ g) x = combine_options c (f x) (g x)"

(* The following \<^keyword>\<open>fun\<close> definition does not work (or only work if we prove termination). *)
(*
fun nested_mask_merge :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 nm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 nm\<^sub>2) = (NM (mh\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mh\<^sub>2) (mp\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mp\<^sub>2) (nm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ nm\<^sub>2))"
*)

abbreviation nested_mask_rel :: "('a nested_mask \<times> 'a nested_mask) set"
  where "nested_mask_rel \<equiv> {(nm, (NM mh mp fnm)) | nm mh mp fnm ploc. nm \<in> set_option (fnm ploc)}"

lemma wf_nested_mask_rel: "wf nested_mask_rel"
  unfolding wf_def
  apply (rule allI | rule impI)+
  apply (rule nested_mask.induct)
  by blast

function (sequential) nested_mask_merge :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2) =
                (NM (mh\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mh\<^sub>2) (mp\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mp\<^sub>2)
                (\<lambda>p. (case (fnm\<^sub>1 p) of None \<Rightarrow> (fnm\<^sub>2 p) | Some nm\<^sub>1 \<Rightarrow> (case (fnm\<^sub>2 p) of None \<Rightarrow> Some nm\<^sub>1 | Some nm\<^sub>2 \<Rightarrow> Some (nested_mask_merge nm\<^sub>1 nm\<^sub>2))))) "
  by (pat_completeness) auto
termination
   \<comment>\<open>"nested_mask_rel <*lex*> {}" would be sufficient here, since the first argument becomes smaller always\<close>
  apply (relation "nested_mask_rel <*lex*> nested_mask_rel")
  using wf_nested_mask_rel
   apply blast
  by auto

text \<open>Defining \<^const>\<open>nested_mask_merge\<close> directly using \<^term>\<open>(nm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ nm\<^sub>2)\<close> but not sure how to do the termination proof in that case.
      So, we instead show the equivalence separately in a lemma and replace the rewrite rule in the simpset with the lemma.\<close>

declare nested_mask_merge.simps [simp del]

lemma nested_mask_merge_combine_options[simp]:
  "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 nm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 nm\<^sub>2) = (NM (mh\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mh\<^sub>2) (mp\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mp\<^sub>2) (nm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ nm\<^sub>2))"
  unfolding pfun_comb_def combine_options_def
  by (simp add: nested_mask_merge.simps)

\<comment> \<open>Auxiliary definitions for multiplying the mask\<close>

function (sequential) nested_mask_multiply :: "'a nested_mask \<Rightarrow> preal \<Rightarrow> 'a nested_mask" where
  "nested_mask_multiply (NM mh mp fnm) p = NM ((\<lambda>x. x * p) \<circ> mh) ((\<lambda>x. x * p) \<circ> mp) ((map_option (\<lambda>nm. nested_mask_multiply nm p)) \<circ> fnm)"
  by (pat_completeness) auto
termination
  apply (relation "nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by fastforce

\<comment> \<open>Begin \<^term>\<open>shift_up\<close>\<close>
(* \<^term>\<open>shift_up\<close> only "unfolds" the specified predicate by one level.
   It does not check if the body of the predicate being unfolded is satisfied. *)

inductive shift_up :: "'a total_context \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool" where
ShiftPartial:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     mh = get_mh nm;
     mp = get_mp nm;
     Some pnm = get_nm nm (pred_id,vs);
     p = mp (pred_id,vs);
     p > q;
     q \<noteq> 0;
     mp' = mp( (pred_id,vs) := p - q );
     fnm' = fnm( (pred_id,vs) := Some (nested_mask_multiply pnm ((p - q) / p)) );
     nm' = NM mh np' fnm' \<rbrakk> \<Longrightarrow>
     shift_up ctxt pred_id vs q nm (nested_mask_merge nm' (nested_mask_multiply pnm (q / p)))"
| ShiftAll:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     mh = get_mh nm;
     mp = get_mp nm;
     Some pnm = get_nm nm (pred_id,vs);
     p = mp (pred_id,vs);
     p \<noteq> 0;
     mp' = mp( (pred_id,vs) := 0 );
     fnm' = fnm( (pred_id,vs) := None );
     nm' = NM mh np' fnm' \<rbrakk> \<Longrightarrow>
     shift_up ctxt pred_id vs p nm (nested_mask_merge nm' pnm)"

\<comment> \<open>End \<^term>\<open>shift_up\<close>\<close>


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
     (\<exists> v2. eval_binop v1 bop v2 \<noteq> BinopTypeFailure)\<rbrakk> \<Longrightarrow>
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
      red_pure_exps_total ctxt R \<omega>_def es \<omega> (Some vs);
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
| RedUnfolding:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow>
   ctxt, None \<turnstile> \<langle>Unfolding p es ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v"
| RedUnfoldingDefNoPred:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>_def) es \<omega> (Some vs);
     ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     \<not> (pgte (get_mp_total_full \<omega>_def (pred_id,vs)) pwrite) \<rbrakk> \<Longrightarrow> \<comment>\<open>insufficient permission\<close>
   ctxt, (Some \<omega>_def) \<turnstile> \<langle>Unfolding p es ubody ; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedUnfoldingDef:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>_def) es \<omega> (Some vs);
     shift_up ctxt p vs pwrite (get_nm_total_full \<omega>_def) nm';
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


subsection \<open>Unfold\<close>

\<comment> \<open>Begin \<^term>\<open>unfold_rel\<close>\<close>
(* \<^term>\<open>unfold_rel\<close> unfolds a consistent predicate. *)

\<comment> \<open>End \<^term>\<open>unfold_rel\<close>\<close>

end
