theory Misc
  imports Main

begin

definition map2set:: "('n \<rightharpoonup> 'm) \<Rightarrow> ('n \<times>'m) set" where 
  "map2set m = {(x, the (m x)) | x. x\<in>dom m}"

lemma map2set_union:
  assumes "dom m \<inter> dom n = {}"
  shows "map2set (m++n) = map2set m \<union> map2set n"
  apply (simp add: set_eq_iff)
  by (smt (z3) assms Un_iff dom_map_add map2set_def map_add_comm map_le_def 
               map_le_iff_map_add_commute mem_Collect_eq)

end