subsection \<open>Total Context\<close>

theory TotalContext
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState TotalViperState
begin


subsection \<open>Type Definitions\<close>

type_synonym 'a heapfun_repr = "'a val list \<Rightarrow> 'a full_total_state \<rightharpoonup> 'a extended_val"
type_synonym 'a interp = "function_ident \<rightharpoonup> 'a heapfun_repr"

record 'a total_context =
  program_total :: program
  fun_interp_total :: "'a interp"
  absval_interp_total :: "'a \<Rightarrow> abs_type"


end
