section \<open>Utilities for Total Masks (Heap Mask, Predicate Mask, Nested Mask)\<close>

theory TotalMaskUtil
  imports TotalViperUtil TotalViperState
begin


subsection \<open>Utilities for \<^typ>\<open>'a nested_mask\<close>\<close>

abbreviation nested_mask_rel :: "('a nested_mask \<times> 'a nested_mask) set"
  where "nested_mask_rel \<equiv> {(nm, (NM mh mp fnm)) | nm mh mp fnm ploc. nm \<in> set_option (fnm ploc)}"

lemma wf_nested_mask_rel: "wf nested_mask_rel"
  unfolding wf_def
  apply (rule allI | rule impI)+
  apply (rule nested_mask.induct)
  by blast

fun field_mask_merge :: "field_mask \<Rightarrow> field_mask \<Rightarrow> field_mask" where
  "field_mask_merge mh\<^sub>1 mh\<^sub>2 = (mh\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mh\<^sub>2)"

fun predicate_mask_merge :: "'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask" where
  "predicate_mask_merge mp\<^sub>1 mp\<^sub>2 = (mp\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mp\<^sub>2)"

function (sequential) nested_mask_merge :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2) =
                (NM (field_mask_merge mh\<^sub>1 mh\<^sub>2) (predicate_mask_merge mp\<^sub>1 mp\<^sub>2)
                (\<lambda>p. (case (fnm\<^sub>1 p) of None \<Rightarrow> (fnm\<^sub>2 p) | Some nm\<^sub>1 \<Rightarrow> (case (fnm\<^sub>2 p) of None \<Rightarrow> Some nm\<^sub>1 | Some nm\<^sub>2 \<Rightarrow> Some (nested_mask_merge nm\<^sub>1 nm\<^sub>2))))) "
  by (pat_completeness) auto
termination
   \<comment>\<open>"nested_mask_rel <*lex*> {}" would be sufficient here, since the first argument becomes smaller always\<close>
  apply (relation "nested_mask_rel <*lex*> nested_mask_rel")
  using wf_nested_mask_rel
   apply blast
  by auto

fun nested_mask_merge_option :: "'a nested_mask option \<Rightarrow> 'a nested_mask option \<Rightarrow> 'a nested_mask option" where
  "nested_mask_merge_option nm\<^sub>1 nm\<^sub>2 = combine_options nested_mask_merge nm\<^sub>1 nm\<^sub>2"

text \<open>Defining \<^const>\<open>nested_mask_merge\<close> directly using \<^term>\<open>(nm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ nm\<^sub>2)\<close> but not sure how to do the termination proof in that case.
      So, we instead show the equivalence separately in a lemma and replace the rewrite rule in the simpset with the lemma.\<close>

declare nested_mask_merge.simps [simp del]

lemma nested_mask_merge_combine_options[simp]:
  "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 nm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 nm\<^sub>2) = (NM (mh\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mh\<^sub>2) (mp\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mp\<^sub>2) (nm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ nm\<^sub>2))"
  unfolding pfun_comb_def combine_options_def
  by (simp add: nested_mask_merge.simps)


subsection \<open>Mask Multiplication\<close>

fun field_mask_multiply :: "field_mask \<Rightarrow> preal \<Rightarrow> field_mask" where
  "field_mask_multiply mh p = ((*) p) \<circ> mh"

fun predicate_mask_multiply :: "'a predicate_mask \<Rightarrow> preal \<Rightarrow> 'a predicate_mask" where
  "predicate_mask_multiply mp p = ((*) p) \<circ> mp"

function (sequential) nested_mask_multiply :: "'a nested_mask \<Rightarrow> preal \<Rightarrow> 'a nested_mask" where
  "nested_mask_multiply (NM mh mp fnm) p = NM (field_mask_multiply mh p) (predicate_mask_multiply mp p) ((map_option (\<lambda>nm. nested_mask_multiply nm p)) \<circ> fnm)"
  by (pat_completeness) auto
termination
  apply (relation "nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by fastforce

fun nested_mask_multiply_option :: "'a nested_mask option \<Rightarrow> preal \<Rightarrow> 'a nested_mask option" where
  "nested_mask_multiply_option None _ = None"
| "nested_mask_multiply_option (Some nm) p = (if p = 0 then None else Some (nested_mask_multiply nm p))"


subsection \<open>Constant Masks\<close>

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

definition empty_nm :: "'a nested_mask"
  where "empty_nm \<equiv> NM zero_mh zero_mp Map.empty"


subsection \<open>Mask Subtraction\<close>

fun field_mask_sub :: "field_mask \<Rightarrow> field_mask \<Rightarrow> field_mask" where
  "field_mask_sub nm\<^sub>1 nm\<^sub>2 l = nm\<^sub>1 l - nm\<^sub>2 l"

fun predicate_mask_sub :: "'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask" where
  "predicate_mask_sub nm\<^sub>1 nm\<^sub>2 l = nm\<^sub>1 l - nm\<^sub>2 l"

function (sequential) nested_mask_subtract :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_subtract (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2) = NM (field_mask_sub mh\<^sub>1 mh\<^sub>2) (predicate_mask_sub mp\<^sub>1 mp\<^sub>2) (fnm\<^sub>1 +\<lparr>nested_mask_subtract\<rparr>+ fnm\<^sub>2)"
  by (pat_completeness) auto
termination
  apply (relation "nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  using Option.is_none_def by fastforce


subsection \<open>Mask Split\<close>

fun mh_split :: "field_mask \<Rightarrow> field_mask \<Rightarrow> field_mask \<Rightarrow> bool" where
  "mh_split mh mh\<^sub>1 mh\<^sub>2 = (mh = (mh\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mh\<^sub>2))"

fun mp_split :: "'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> bool" where
  "mp_split mp mp\<^sub>1 mp\<^sub>2 = (mp = (mp\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mp\<^sub>2))"


end
