section \<open>Utilities for Total Masks (Heap Mask, Predicate Mask, Nested Mask)\<close>

theory TotalMaskUtil
  imports TotalViperUtil TotalViperState
begin


subsection \<open>Well-foundness Relation for \<^typ>\<open>'a nested_mask\<close>\<close>

abbreviation nested_mask_rel :: "('a nested_mask \<times> 'a nested_mask) set"
  where "nested_mask_rel \<equiv> {(nm, (NM mh mp fnm)) | nm mh mp fnm ploc. nm \<in> set_option (fnm ploc)}"

lemma wf_nested_mask_rel: "wf nested_mask_rel"
  unfolding wf_def
  apply (rule allI | rule impI)+
  apply (rule nested_mask.induct)
  by blast


subsection \<open>Mask Merge\<close>

fun field_mask_merge :: "field_mask \<Rightarrow> field_mask \<Rightarrow> field_mask" where
  "field_mask_merge mh\<^sub>1 mh\<^sub>2 = add_masks mh\<^sub>1 mh\<^sub>2"

fun predicate_mask_merge :: "'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask" where
  "predicate_mask_merge mp\<^sub>1 mp\<^sub>2 = add_masks mp\<^sub>1 mp\<^sub>2"

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


text \<open>Defining \<^const>\<open>nested_mask_merge\<close> directly using \<^term>\<open>(nm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ nm\<^sub>2)\<close> but not sure how to do the termination proof in that case.
      So, we instead show the equivalence separately in a lemma and replace the rewrite rule in the simpset with the lemma.\<close>

declare nested_mask_merge.simps [simp del]

lemma nested_mask_merge_combine_options [simp]:
  "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 nm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 nm\<^sub>2) = (NM (add_masks mh\<^sub>1 mh\<^sub>2) (add_masks mp\<^sub>1 mp\<^sub>2) (nm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ nm\<^sub>2))"
  unfolding pfun_comb_def combine_options_def
  by (simp add: nested_mask_merge.simps)


subsection \<open>Mask Multiplication\<close>

fun field_mask_multiply :: "preal \<Rightarrow> field_mask \<Rightarrow> field_mask" where
  "field_mask_multiply p mh = ((*) p) \<circ> mh"

fun predicate_mask_multiply :: "preal \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask" where
  "predicate_mask_multiply p mp = ((*) p) \<circ> mp"

function (sequential) nested_mask_multiply :: "preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_multiply p (NM mh mp fnm) = NM (field_mask_multiply p mh) (predicate_mask_multiply p mp) ((map_option (\<lambda>nm. nested_mask_multiply p nm)) \<circ> fnm)"
  by (pat_completeness) auto
termination
  apply (relation "{} <*lex*> nested_mask_rel")
  using wf_nested_mask_rel
   apply blast
  by fastforce


subsection \<open>Mask Subtraction\<close>

function (sequential) nested_mask_subtract :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_subtract (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2) = NM (mh\<^sub>1 - mh\<^sub>2) (mp\<^sub>1 - mp\<^sub>2) (fnm\<^sub>1 +\<lparr>nested_mask_subtract\<rparr>+ fnm\<^sub>2)"
  by (pat_completeness) auto
termination
  apply (relation "nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  using Option.is_none_def by fastforce


subsection \<open>Mask Split\<close>

fun mh_split :: "field_mask \<Rightarrow> field_mask \<Rightarrow> field_mask \<Rightarrow> bool" where
  "mh_split mh mh\<^sub>1 mh\<^sub>2 = (mh = add_masks mh\<^sub>1 mh\<^sub>2)"

fun mp_split :: "'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> bool" where
  "mp_split mp mp\<^sub>1 mp\<^sub>2 = (mp = add_masks mp\<^sub>1 mp\<^sub>2)"


subsection \<open>Mask Ordering\<close>

fun nested_mask_le :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool" where
  "nested_mask_le (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2) = (mh\<^sub>1 \<le> mh\<^sub>2 \<and> mp\<^sub>1 \<le> mp\<^sub>2)"


subsection \<open>Constant Masks\<close>

fun singleton_mh :: "heap_loc \<Rightarrow> preal \<Rightarrow> field_mask" where
  "singleton_mh loc p l = (if l = loc then p else 0)"

fun singleton_mp :: "'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a predicate_mask" where
  "singleton_mp ploc p pl = (if pl = ploc then p else 0)"

fun is_singleton_mh :: "heap_loc \<Rightarrow> field_mask \<Rightarrow> bool" where
  "is_singleton_mh loc mh = (\<exists>p > 0. mh = singleton_mh loc p)"

fun is_singleton_mp :: "'a predicate_loc \<Rightarrow> 'a predicate_mask \<Rightarrow> bool" where
  "is_singleton_mp ploc mp = (\<exists>p > 0. mp = singleton_mp ploc p)"


end
