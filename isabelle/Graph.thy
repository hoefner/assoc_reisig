theory Graph
  imports Main

begin

subsection \<open>Transitions\<close>

type_synonym 'a transition = "'a \<times> 'a"

type_synonym 'a tss = "'a transition set"

definition tss_sources :: "'a tss \<Rightarrow> 'a set" where
  "tss_sources T \<equiv> {fst t | t. t\<in>T}"

definition tss_targets :: "'a tss \<Rightarrow> 'a set" where
  "tss_targets T \<equiv> {snd t | t. t\<in>T}"

abbreviation (import) tss_nodes :: "'a tss \<Rightarrow> 'a set" where
  "tss_nodes T \<equiv> tss_sources T \<union> tss_targets T"


subsection \<open>Graph with labelled nodes\<close>

type_synonym ('n,'l) node_set = "('n \<rightharpoonup> 'l)"
type_synonym ('n,'l) graph = "('n,'l) node_set \<times> 'n tss"

definition graph_nodes :: "('n,'l) graph \<Rightarrow> 'n set" where
  "graph_nodes G \<equiv> dom(fst G)"

abbreviation graph_labels :: "('n,'l) graph \<Rightarrow> 'l set" where
  "graph_labels G \<equiv> ran(fst G) "

definition graph_transitions :: "('n,'l) graph \<Rightarrow> 'n tss" where
  "graph_transitions G \<equiv> snd G"

(* maybe get rid of it *)
definition is_graph :: "('n,'l) graph \<Rightarrow> bool" where
  "is_graph G \<equiv> tss_nodes(snd G) \<subseteq> dom(fst G)"

lemma is_graph_var:
  "is_graph G \<equiv> tss_nodes(graph_transitions G) \<subseteq> graph_nodes G"
  by (simp add: is_graph_def graph_nodes_def graph_transitions_def)

lemma nodes_is_graph:
  assumes "is_graph G"
  shows "tss_sources(graph_transitions G) \<subseteq> graph_nodes G"
  and "tss_targets(graph_transitions G) \<subseteq> graph_nodes G"
  by (metis assms is_graph_var sup.bounded_iff)+

abbreviation empty :: "('n,'l) graph" where
  "empty \<equiv> (Map.empty,{})"

lemma empty_isgraph:
  "is_graph empty"
  by (simp add: is_graph_def graph_transitions_def tss_sources_def tss_targets_def)

end