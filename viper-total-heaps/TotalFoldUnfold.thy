section \<open>Core Semantics\<close>

theory TotalFoldUnfold
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState ViperCommon.Binop ViperCommon.DeBruijn ViperCommon.PredicatesUtil
          TotalViperState TotalStateUtil TotalResult TotalInhaleExhale
begin


subsection \<open>Unfold\<close>

text \<open>\<^term>\<open>unfold_rel\<close> unfolds a consistent predicate.\<close>

inductive unfold_rel :: "'a total_context \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state \<Rightarrow> bool" where
  UnfoldRel:
  "\<lbrakk> shift_up pred_id vs p nm nm';
     get_nm_total \<phi> = nm;
     get_nm_total \<phi>' = nm';
     get_hh_total \<phi>' = get_hh_total \<phi>
   \<rbrakk> \<Longrightarrow>
   unfold_rel ctxt pred_id vs p \<phi> \<phi>'"

lemma unfold_rel_perm_sufficient:
  assumes "unfold_rel ctxt pid vs p \<phi> \<phi>'"
  shows "p \<le> get_mp_total \<phi> (pid,vs)"
  by (metis assms get_mp_total.elims shift_up_perm_sufficient unfold_rel.simps)


subsection \<open>Fold\<close>

inductive fold_rel :: "'a total_context \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total \<Rightarrow> bool" where
  FoldRelNormal:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pid = Some pdecl;
     ViperLang.predicate_decl.body pdecl = Some pbody;
     vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pdecl); \<comment> \<open>Todo: reconsider this\<close>
     \<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>;
     red_exhale ctxt (\<lambda>_. True) \<omega>0 (syntactic_mult (Rep_preal q) pbody) \<omega>0 (RNormal \<omega>1');
     \<omega>1 = \<omega>\<lparr> get_total_full := get_total_full \<omega>1' \<rparr>;
     get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0;
     \<omega>' = add_to_lpm_total_full \<omega>1 (pid,vs) (if q = 0 then None else Some (p2pos q, nm_exh))
   \<rbrakk> \<Longrightarrow>
   fold_rel ctxt pid vs q \<omega> (RNormal \<omega>')"
| FoldRelFailure:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     \<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>;
     red_exhale ctxt (\<lambda>_. True) \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 RFailure
   \<rbrakk> \<Longrightarrow>
   fold_rel ctxt pred_id vs q \<omega> RFailure"

inductive_cases FoldRelNormal_case: "fold_rel ctxt pred_id vs q \<omega> (RNormal \<omega>')"
inductive_cases FoldRelFailure_case: "fold_rel ctxt pred_id vs q \<omega> RFailure"


end
