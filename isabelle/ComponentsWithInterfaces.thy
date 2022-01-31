theory ComponentsWithInterfaces
  imports Interface

begin
type_synonym ('n,'l) component_model = "('n,'l) interface \<times> ('n,'l) labelledGraph \<times> ('n,'l) interface"

abbreviation graph :: "('n,'l) component_model \<Rightarrow> ('n,'l) labelledGraph" where
  "graph c \<equiv> fst (snd c)"
abbreviation nodes :: "('n,'l) component_model \<Rightarrow> ('n,'l) node set" where
  "nodes c \<equiv> graph_nodes (graph c)"
abbreviation nodeIds :: "('n,'l) component_model \<Rightarrow> 'n set" where
  "nodeIds c \<equiv> graph_nodeIds (graph c)"
abbreviation transitions :: "('n,'l) component_model \<Rightarrow> ('n,'l) node tss" where
  "transitions c \<equiv> graph_transitions (graph c)"
abbreviation left_interface :: "('n,'l) component_model \<Rightarrow>  ('n,'l) interface" ("\<^sup>\<star>_"[101] 100) where
  "left_interface c \<equiv> fst c"
abbreviation right_interface :: "('n,'l) component_model \<Rightarrow>  ('n,'l) interface" ("_\<^sup>\<star>"[101] 100) where
  "right_interface c \<equiv> snd (snd c)"
definition inner ::  "('n,'l) component_model \<Rightarrow> ('n,'l) node set" where
  "inner c = (nodes c) - (inter_nodes(\<^sup>\<star>c) \<union> inter_nodes(c\<^sup>\<star>))"

abbreviation empty :: "('n,'l) component_model" ("\<langle>\<rangle>") where
  "empty \<equiv> (\<lparr>\<rparr>, Graph.empty, \<lparr>\<rparr>)"

lemma empty_interfaces[simp]:
  shows "\<^sup>\<star>\<langle>\<rangle> = \<lparr>\<rparr>"
  and "\<langle>\<rangle>\<^sup>\<star> = \<lparr>\<rparr>"
  by simp+

(*some side condition for is_component *)
abbreviation is_component :: "('n,'l) component_model \<Rightarrow> bool" where
  "is_component c \<equiv> is_graph(graph c) \<and> 
                    inter_nodes(\<^sup>\<star>c) \<subseteq>  nodes c \<and> 
                    inter_nodes(c\<^sup>\<star>) \<subseteq>  nodes c"
lemma is_component_alt:
  "is_component c \<equiv> tss_nodes (transitions c) \<union> inter_nodes(\<^sup>\<star>c) \<union> inter_nodes(c\<^sup>\<star>) \<subseteq>  graph_nodes(graph c)"
  by (simp add: is_graph_def)

lemma empty_iscomponent:
  "is_component empty"
  using empty_isgraph by simp

section \<open>Composition\<close>
(* to be sorted *)
(* more general types *)
definition rename :: "'n \<Rightarrow> ('n \<rightharpoonup> 'n) \<Rightarrow> 'n" where
  "rename s m = (if s\<in>dom m then the(m s) else s)"

definition nodes_rename :: "('n,'l) node set \<Rightarrow> ('l \<Rightarrow> 'n \<rightharpoonup> 'n) \<Rightarrow> ('n,'l) node set" where
  "nodes_rename S M = {(rename n (M l),l) | n l. (n,l)\<in>S}"

lemma nodes_rename_empty[simp]:
  "nodes_rename S (\<lambda>l. Map.empty) = S"
  unfolding nodes_rename_def rename_def
  by clarsimp

lemma node_rename_dist:
  "nodes_rename (S\<union>T) M = nodes_rename S M \<union> nodes_rename T M"
  unfolding nodes_rename_def rename_def
  by fastforce

definition tss_rename :: "('n,'l) node tss \<Rightarrow> ('l \<Rightarrow> 'n \<rightharpoonup> 'n) \<Rightarrow> ('n,'l) node tss" where
  "tss_rename T M = {((rename a (M l),l),n) | a l n. ((a,l),n)\<in>T}" 

lemma tss_rename_empty[simp]:
  "tss_rename T (\<lambda>l. Map.empty) = T"
  unfolding tss_rename_def rename_def
  by fastforce

lemma tss_rename_dist:
  "tss_rename (S\<union>T) M = tss_rename S M \<union> tss_rename T M"
  unfolding tss_rename_def rename_def
  by fast

primrec list_rename :: "'n list \<Rightarrow> ('n \<rightharpoonup> 'n) \<Rightarrow> 'n list" where
  "list_rename [] m = []" | 
  "list_rename (l#ls) m = (rename l m) # (list_rename ls m)"

lemma list_rename_dist:
  "list_rename (xs @ ys) m = (list_rename xs m) @ (list_rename ys m)"
  by(induct xs arbitrary: ys, simp_all)

definition inter_rename :: "('n,'l) interface \<Rightarrow> ('l \<Rightarrow> 'n \<rightharpoonup> 'n) \<Rightarrow> ('n,'l) interface" where
  "inter_rename i M = (\<lambda>l. list_rename (i l) (M l))"

lemma inter_rename_dist:
   "inter_rename (i @@ j) M =(inter_rename i M) @@ (inter_rename j M)"
  unfolding inter_rename_def inter_comp_def
  by (simp add: list_rename_dist)


(* can probably be made more beautiful *)
definition comp_merge :: "('n,'l) component_model \<Rightarrow> ('n,'l) component_model 
                          \<Rightarrow> ('n,'l) component_model" (infixl "\<cdot>" 70) where
  "comp_merge c d = (
      (\<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d) (c\<^sup>\<star>)),
      (nodes_rename (nodes c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union> nodes d, 
       tss_rename (transitions c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union> transitions d),
      (inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d) @@ d\<^sup>\<star>))"

lemma comp_merge_neutral:
  shows "empty \<cdot> c = c"
  and   "empty \<cdot> c = c"
  unfolding comp_merge_def
  by (simp add: graph_nodes_def graph_transitions_def)+



lemma comp_merge_left:
  "\<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>)) (c\<^sup>\<star>) =
    \<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d) (c\<^sup>\<star>) @@ inter_prune (\<^sup>\<star>e) (inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d) @@ d\<^sup>\<star>)"
  unfolding inter_prune_def inter_comp_def
  by (simp)

(*
lemma 
  "match_lists (l @ m) n = (match_lists l n) ++ (match_lists m (drop (length m) n))"
  apply(induct l arbitrary: m)
  sledgehammer
.

lemma 
  "match_inter (i @@ j) k = (match_inter i k) @@ match_inter j (drop (length )"
*)

(* may need preconditions *)
lemma comp_merge_graph_nodes:
  "nodes_rename (nodes c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>))) \<union>
    graph_nodes
     (nodes_rename (nodes d) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) \<union> nodes e, tss_rename (transitions d) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) \<union> transitions e) =
    nodes_rename
     (graph_nodes
       (nodes_rename (nodes c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union> nodes d, tss_rename (transitions c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union> transitions d))
     (match_inter (inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d) @@ d\<^sup>\<star>) (\<^sup>\<star>e)) \<union>
    nodes e"
  unfolding nodes_rename_def match_inter_def rename_def 
  apply simp
  sorry

lemma comp_merge_graph_tss:
  "tss_rename (transitions c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>))) \<union>
    graph_transitions
     (nodes_rename (nodes d) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) \<union> nodes e, tss_rename (transitions d) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) \<union> transitions e) =
    tss_rename
     (graph_transitions
       (nodes_rename (nodes c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union> nodes d, tss_rename (transitions c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union> transitions d))
     (match_inter (inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d) @@ d\<^sup>\<star>) (\<^sup>\<star>e)) \<union>
    transitions e"
  sorry

lemma comp_merge_right:
  "inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>)) @@ (inter_prune (d\<^sup>\<star>) (\<^sup>\<star>e) @@ e\<^sup>\<star>) =
    inter_prune (inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d) @@ d\<^sup>\<star>) (\<^sup>\<star>e) @@ e\<^sup>\<star>"
  unfolding inter_prune_def inter_comp_def
  apply(standard)
  sorry

lemma comp_merge_assoc:
  "c \<cdot> (d \<cdot> e) = (c \<cdot> d) \<cdot> e"
  unfolding comp_merge_def
  apply(simp)
  apply(rule conjI, rule comp_merge_left)
  apply(rule conjI, rule comp_merge_graph_nodes)
  apply(rule conjI, rule comp_merge_graph_tss)
  by(rule comp_merge_right)

end





