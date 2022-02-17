theory ComponentsWithInterfacesAlt
  imports Interface

begin
type_synonym ('n,'l) component_model = "('n,'l) interface \<times> ('n,'l) graph \<times> 'n tss \<times> ('n,'l) interface"

abbreviation graph :: "('n,'l) component_model \<Rightarrow> ('n,'l) graph" where
  "graph c \<equiv> fst (snd c)"
abbreviation (import) nodes :: "('n,'l) component_model \<Rightarrow> 'n set" where
  "nodes c \<equiv> graph_nodes (graph c)"

abbreviation (import) transitions :: "('n,'l) component_model \<Rightarrow> 'n tss" where
  "transitions c \<equiv> graph_transitions (graph c)"

abbreviation  silent_transitions :: "('n,'l) component_model \<Rightarrow> 'n tss" where
  "silent_transitions c \<equiv>  fst (snd (snd c))"

abbreviation left_interface :: "('n,'l) component_model \<Rightarrow>  ('n,'l) interface" ("\<^sup>\<star>_" [81] 80) where
  "left_interface c \<equiv> fst c"
abbreviation right_interface :: "('n,'l) component_model \<Rightarrow>  ('n,'l) interface" ("_\<^sup>\<star>" [81] 80) where
  "right_interface c \<equiv> snd (snd (snd c))"
definition inner ::  "('n,'l) component_model \<Rightarrow> 'n set" where
  "inner c = (nodes c) - (inter_nodes(\<^sup>\<star>c) \<union> inter_nodes(c\<^sup>\<star>))"

abbreviation empty :: "('n,'l) component_model" ("\<langle>\<rangle>") where
  "empty \<equiv> (\<lparr>\<rparr>, Graph.empty, {}, \<lparr>\<rparr>)"

lemma empty_interfaces[simp]:
  shows "\<^sup>\<star>\<langle>\<rangle> = \<lparr>\<rparr>"
  and "\<langle>\<rangle>\<^sup>\<star>= \<lparr>\<rparr>"
  by simp+

abbreviation is_component :: "('n,'l) component_model \<Rightarrow> bool" where
  "is_component c \<equiv> is_graph(graph c) \<and>
                    (\<forall>l. \<forall>n\<in>set((\<^sup>\<star>c) l). fst(graph c) n = Some l) \<and>
                    (\<forall>l. \<forall>n\<in>set((c\<^sup>\<star>) l). fst(graph c) n = Some l)"

lemma is_component_props:
  assumes "is_component c"
  shows "is_graph(graph c)"
  and "n\<in>set((\<^sup>\<star>c) l) \<Longrightarrow> fst(graph c) n = Some l"
  and "inter_nodes(\<^sup>\<star>c) \<subseteq>  nodes c"
  and "inter_nodes(c\<^sup>\<star>) \<subseteq>  nodes c"
  and "tss_nodes (transitions c) \<subseteq>  graph_nodes(graph c)"
  and "inter_nodes(\<^sup>\<star>c) \<subseteq>  graph_nodes(graph c)"
  and "inter_nodes(c\<^sup>\<star>) \<subseteq>  graph_nodes(graph c)"
        unfolding inter_nodes_def graph_nodes_def
        using assms apply blast
       using assms apply blast
      using assms apply blast
     using assms apply blast
    using assms apply (simp add: graph_nodes_def graph_transitions_def is_graph_var tss_sources_def)
   using assms apply blast     
  using assms by blast

lemma is_component_lists_distinct:
  assumes "is_component c"
  shows "k\<noteq>l \<Longrightarrow> set((c\<^sup>\<star>) k) \<inter> set((c\<^sup>\<star>) l) = {}"
  and "k\<noteq>l \<Longrightarrow> set((\<^sup>\<star>c) k) \<inter> set((\<^sup>\<star>c) l) = {}"
  by (metis assms Int_emptyI option.inject)+

lemma empty_iscomponent:
  "is_component empty"
  using empty_isgraph by simp

section \<open>Composition\<close>



definition match_inter :: "('n,'l) interface \<Rightarrow> ('n,'l) interface \<Rightarrow> 'l \<Rightarrow> ('n tss)" where
  "match_inter i j = (\<lambda>l. set (zip (i l) (j l)))"

term match_inter
(* can probably be made more beautiful *)
(* what if 2 graphs have the same node id, but different labels? *)
definition comp_merge :: "('n,'l) component_model \<Rightarrow> ('n,'l) component_model 
                          \<Rightarrow> ('n,'l) component_model" (infixl "\<cdot>" 70) where
  "comp_merge c d = (
      (\<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d) (c\<^sup>\<star>)), 
      (fst (graph c) ++ fst (graph d), transitions c \<union> transitions d),
       silent_transitions c \<union> silent_transitions d \<union> (Sup (range (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)))),
      (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)))"


lemma comp_merge_left:
  "\<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>)) (c\<^sup>\<star>) =
    \<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d) (c\<^sup>\<star>) @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d))"
  unfolding inter_prune_def inter_comp_def
  apply(standard)
  by (simp add: add.commute)

lemma comp_merge_right:
  "e\<^sup>\<star>@@ inter_prune (d\<^sup>\<star>) (\<^sup>\<star>e) @@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>)) =
    e\<^sup>\<star>@@ inter_prune (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)) (\<^sup>\<star>e)"
  unfolding inter_prune_def inter_comp_def
  apply(standard)
  by (simp add: add.commute)


lemma un_cong: "y = z \<Longrightarrow> x \<union> y = x \<union> z"
  by blast

lemma rewrite: " (\<Union>x. f x \<union> g x)  = (Sup (range f) \<union> Sup (range g))"
  apply (clarsimp)
  apply (standard; clarsimp)
   apply auto[1]
  apply (standard; clarsimp)
   apply (auto)
  done

lemma name_later: " set (zip dr el) \<union> 
        set (zip cr (dl @ drop (length dr) (el))) =
        set (zip cr dl) \<union> 
        set (zip (dr @ drop (length dl) cr) el)" 
  apply (intro set_eqI iffI; clarsimp, elim disjE)
     apply (metis Un_iff append_Nil2 set_append zip_Nil zip_append1)
    apply (metis Un_iff append_Nil2 set_append zip_append1 zip_append2)
   apply (metis Un_iff append_Nil2 set_append zip.simps(1) zip_append2)
  by (metis Un_iff append_Nil2 set_append zip_append1 zip_append2)

lemma match_inter_assoc: "match_inter (d\<^sup>\<star>) (\<^sup>\<star>e) x \<union> match_inter (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>)) x =
       match_inter (c\<^sup>\<star>) (\<^sup>\<star>d) x \<union> match_inter (d\<^sup>\<star> @@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)) (\<^sup>\<star>e) x "
  apply (clarsimp simp: match_inter_def inter_comp_def inter_prune_def)
  by (rule name_later)

lemma comp_merge_assoc:
  "c \<cdot> (d \<cdot> e) = (c \<cdot> d) \<cdot> e"
  unfolding comp_merge_def
  apply(simp)
  apply (intro conjI)
     apply (rule comp_merge_left)
    apply (simp add: graph_transitions_def sup_assoc)
   apply (clarsimp simp add: Un_Union_image[symmetric] match_inter_assoc sup_assoc sup.left_commute intro!: un_cong)
  by (rule comp_merge_right)


abbreviation symcl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(_\<^sup>-)" [1000] 999)
  where "r\<^sup>- \<equiv> r \<union> converse r"

definition "new_nodes c = (nodes c) // (symcl (silent_transitions c))^*"

definition "new_transitions c = {(x,y). x \<in> new_nodes c \<and> y \<in> new_nodes c \<and> (\<exists>a\<in>x.\<exists>b\<in>y. (a,b) \<in> transitions c)} "

definition "resig_sig c = (c\<^sup>\<star>, (nodes c,  new_transitions c), c\<^sup>\<star>)" 


end






