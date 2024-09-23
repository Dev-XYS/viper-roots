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


subsection \<open>Fold\<close>

inductive fold_rel :: "'a total_context \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total \<Rightarrow> bool" where
  FoldRelNormal:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     q \<noteq> 0;
     \<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>;
     red_exhale ctxt (\<lambda>_. True) \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 (RNormal \<omega>1);
     nm_exh = nested_mask_subtract (get_nm_total_full \<omega>0) (get_nm_total_full \<omega>1);
     \<omega>' = \<lparr> get_store_total = get_store_total \<omega>,
            get_trace_total = get_trace_total \<omega>,
            get_total_full = add_to_nm_loc_total
              (inc_mp_loc_total (get_total_full \<omega>1) (pred_id, vs) q)
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
     red_exhale ctxt (\<lambda>_. True) \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 RFailure
   \<rbrakk> \<Longrightarrow>
   fold_rel ctxt pred_id vs q \<omega> RFailure"

inductive_cases FoldRelNormal_case: "fold_rel ctxt pred_id vs q \<omega> (RNormal \<omega>')"
inductive_cases FoldRelFailure_case: "fold_rel ctxt pred_id vs q \<omega> RFailure"


end
