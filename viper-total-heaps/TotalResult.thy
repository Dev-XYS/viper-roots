theory TotalResult
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState TotalViperState ViperCommon.Binop ViperCommon.DeBruijn ViperCommon.PredicatesUtil TotalStateUtil
begin

datatype 'a result_total = RMagic | RFailure | RNormal "'a full_total_state"

fun map_result_total :: "('a full_total_state \<Rightarrow> 'b full_total_state) \<Rightarrow> 'a result_total \<Rightarrow> 'b result_total"
  where
    "map_result_total f (RNormal \<omega>) = (RNormal (f \<omega>))"
  | "map_result_total f RMagic = RMagic"
  | "map_result_total f RFailure = RFailure"

inductive th_result_rel :: "bool \<Rightarrow> bool \<Rightarrow> ('a full_total_state) set \<Rightarrow> 'a result_total \<Rightarrow> bool"  where
  THResultNormal: "\<lbrakk> \<omega> \<in> W \<rbrakk> \<Longrightarrow> th_result_rel True True W (RNormal \<omega>)"
| THResultMagic: "th_result_rel True False W RMagic"
| THResultFailure: "th_result_rel False b W RFailure"

text \<open>\<^const>\<open>th_result_rel\<close> is an auxiliary relation that is useful to express a state in terms of
conditions. \<^term>\<open>th_result_rel bSuccess bFeasible W res\<close> is used in the following way:

  \<^item> \<^term>\<open>bSuccess\<close> expresses when \<^term>\<open>res\<close> is not a failing state
  \<^item> If \<^term>\<open>bSuccess\<close> holds (i.e., \<^term>\<open>res\<close> not a failing state), then
    \<^term>\<open>bFeasible\<close> expresses when res is a normal state.
  \<^item> W expresses the set of possible normal states for \<^term>\<open>res\<close> if both \<^term>\<open>bSuccess\<close> and
    \<^term>\<open>bFeasible\<close> hold.
\<close>

inductive_cases THResultNormal_case: "th_result_rel True True W (RNormal \<omega>)"
thm THResultNormal_case

lemma THResultNormal_alt: "\<lbrakk> \<omega> \<in> W; A; B\<rbrakk> \<Longrightarrow> th_result_rel A B W (RNormal \<omega>)"
  by (cases A; cases B) (auto intro: THResultNormal)

lemma th_result_rel_normal:
  assumes "th_result_rel a b W (RNormal \<omega>)"
  shows "a \<and> b \<and> \<omega> \<in> W"
  using assms
  by (cases) auto

text \<open>\<^typ>\<open>'a result_total\<close> expresses the possible states for statements. \<close>


lemma th_result_rel_failure:
  assumes "th_result_rel False b W res"
  shows "res = RFailure"
  using assms
  by (cases) auto

lemma th_result_rel_failure_2:
  assumes "th_result_rel a b W RFailure"
  shows "\<not>a"
  using assms
  by (cases) auto

lemma th_result_rel_magic:
  assumes "th_result_rel True False W res"
  shows "res = RMagic"
  using assms
  by (cases) auto

lemma th_result_rel_magic_2:
  assumes "th_result_rel a b W RMagic"
  shows "a \<and> \<not>b"
  using assms
  by (cases) auto

end
