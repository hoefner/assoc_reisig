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

abbreviation tss_nodes :: "'a tss \<Rightarrow> 'a set" where
  "tss_nodes T \<equiv> tss_sources T \<union> tss_targets T"


subsection \<open>Graph\<close>

type_synonym 'a graph = "'a set \<times> 'a tss"

definition graph_nodes :: "'a graph \<Rightarrow> 'a  set" where
  "graph_nodes g \<equiv> fst g"

definition graph_transitions :: "'a graph \<Rightarrow> 'a tss" where
  "graph_transitions g \<equiv> snd g"

definition is_graph :: "'a graph \<Rightarrow> bool" where
  "is_graph g \<equiv> tss_nodes(graph_transitions g) \<subseteq> graph_nodes g"

lemma nodes_is_graph:
  shows "is_graph g \<Longrightarrow> tss_sources(graph_transitions g) \<subseteq> graph_nodes g"
  and "is_graph g \<Longrightarrow> tss_targets(graph_transitions g) \<subseteq> graph_nodes g"
  unfolding is_graph_def tss_sources_def tss_targets_def
  by blast+

abbreviation empty :: "'a set \<times> 'a tss" where
  "empty \<equiv> ({},{})"

lemma empty_isgraph:
  "is_graph empty"
  unfolding is_graph_def graph_transitions_def tss_sources_def tss_targets_def
  by simp

subsection \<open>Labelled Nodes\<close>
type_synonym ('n,'l) node = "'n \<times> 'l" 
definition node_id :: "('n,'l) node \<Rightarrow> 'n" where 
  "node_id n \<equiv> fst n"
definition label :: "('n,'l) node \<Rightarrow> 'l" where 
  "label n \<equiv> snd n"

subsection \<open>Graphs with Labelled Nodes\<close>
(* labels are of course not unique *)
type_synonym ('n,'l) labelledGraph = "('n,'l) node graph"
abbreviation graph_nodeIds :: "('n,'l) labelledGraph \<Rightarrow> 'n set" where
  "graph_nodeIds g \<equiv> {node_id n |n. n\<in>fst g}"
abbreviation graph_nodeLabels :: "('n,'l) labelledGraph \<Rightarrow> 'l set" where
  "graph_nodeLabels g \<equiv> {label n |n. n\<in>fst g}"

end