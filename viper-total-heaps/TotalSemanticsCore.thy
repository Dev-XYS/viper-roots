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
  where "nested_mask_rel \<equiv> {(nm, (NM mh mp fnm))  | nm mh mp fnm ploc. nm \<in> set_option (fnm ploc)}"

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

\<comment> \<open>Begin \<^term>\<open>unfold_rel\<close>\<close>
(* \<^term>\<open>unfold_rel\<close> unfolds a consistent predicate. *)


\<comment> \<open>End \<^term>\<open>unfold_rel\<close>\<close>

end
