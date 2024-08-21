section \<open>Core Semantics\<close>

theory TotalFoldUnfold
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState ViperCommon.Binop ViperCommon.DeBruijn ViperCommon.PredicatesUtil
          TotalViperState TotalStateUtil TotalResult TotalExpressions TotalInhaleExhale
begin


subsection \<open>Shift Operations\<close>

text \<open>\<^term>\<open>shift_up\<close> only "unfolds" the specified predicate by one level.
      It does not check if the body of the predicate being unfolded is satisfied.\<close>

inductive shift_up :: "predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool" where
  ShiftAny:
  "\<lbrakk> nm = NM mh mp fnm;
     Some pnm = fnm (pred_id,vs);
     p = mp (pred_id,vs);
     q \<le> p;
     q \<noteq> 0;
     mp' = mp( (pred_id,vs) := p - q );
     fnm' = fnm( (pred_id,vs) := if q = p then None else Some (nested_mask_multiply pnm ((p - q) / p)) );
     nm'_sub = NM mh mp' fnm';
     nm' = nested_mask_merge nm'_sub (nested_mask_multiply pnm (q / p)) \<rbrakk> \<Longrightarrow>
     shift_up pred_id vs q nm nm'"

inductive_cases shift_up_case: "shift_up pred_id vs q nm nm'"
inductive_simps shift_up_simp: "shift_up pred_id vs q nm nm'"


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
     red_exhale ctxt \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 (RNormal \<omega>1);
     nm_exh = nested_mask_subtract (get_nm_total_full \<omega>0) (get_nm_total_full \<omega>1);
     \<omega>' = \<lparr> get_store_total = get_store_total \<omega>,
            get_trace_total = get_trace_total \<omega>,
            get_total_full = add_to_nm_loc_total
              (add_to_mp_loc_total (get_total_full \<omega>1) (pred_id, vs) q)
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

inductive_cases FoldRelNormal_case: "fold_rel ctxt pred_id vs q \<omega> (RNormal \<omega>')"
inductive_cases FoldRelFailure_case: "fold_rel ctxt pred_id vs q \<omega> RFailure"


end
