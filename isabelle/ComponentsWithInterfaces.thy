theory ComponentsWithInterfaces
  imports Interface

begin
type_synonym ('n,'l) component_model = "('n,'l) interface \<times> ('n,'l)graph \<times> ('n,'l) interface"

abbreviation graph :: "('n,'l) component_model \<Rightarrow> ('n,'l) graph" where
  "graph c \<equiv> fst (snd c)"
abbreviation (import) nodes :: "('n,'l) component_model \<Rightarrow> 'n set" where
  "nodes c \<equiv> graph_nodes (graph c)"
abbreviation (import) transitions :: "('n,'l) component_model \<Rightarrow> 'n tss" where
  "transitions c \<equiv> graph_transitions (graph c)"
abbreviation left_interface :: "('n,'l) component_model \<Rightarrow>  ('n,'l) interface" ("\<^sup>\<star>_" [81] 80) where
  "left_interface c \<equiv> fst c"
abbreviation right_interface :: "('n,'l) component_model \<Rightarrow>  ('n,'l) interface" ("_\<^sup>\<star>" [81] 80) where
  "right_interface c \<equiv> snd (snd c)"
definition inner ::  "('n,'l) component_model \<Rightarrow> 'n set" where
  "inner c = (nodes c) - (inter_nodes(\<^sup>\<star>c) \<union> inter_nodes(c\<^sup>\<star>))"

abbreviation empty :: "('n,'l) component_model" ("\<langle>\<rangle>") where
  "empty \<equiv> (\<lparr>\<rparr>, Graph.empty, \<lparr>\<rparr>)"

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
(* to be sorted *)
(* more general types *)
definition rename :: "'n \<Rightarrow> ('n \<rightharpoonup> 'n) \<Rightarrow> 'n" where
  "rename s m = (if s\<in>dom m then the(m s) else s)"

definition rename_tss :: "'n tss \<Rightarrow> ('n \<rightharpoonup> 'n) \<Rightarrow> 'n tss" where
  "rename_tss T m = {(rename n\<^sub>1 m, rename n\<^sub>2 m) | n\<^sub>1 n\<^sub>2. (n\<^sub>1,n\<^sub>2)\<in>T}" 

definition lrename_tss :: "'n tss \<Rightarrow> ('l \<Rightarrow> 'n \<rightharpoonup> 'n) \<Rightarrow> 'n tss" where
  "lrename_tss T M = \<Union>{rename_tss T (M l) | l. True}" 

lemma lrename_tss_var:
  "lrename_tss T M = \<Union>{{(rename n\<^sub>1 (M l), rename n\<^sub>2 (M l)) | n\<^sub>1 n\<^sub>2. (n\<^sub>1,n\<^sub>2)\<in>T} | l. True}" 
  unfolding rename_tss_def lrename_tss_def..

lemma rename_tss_empty[simp]:
  "rename_tss T Map.empty = T"
  "lrename_tss T (\<lambda>l. Map.empty) = T"
  unfolding rename_def rename_tss_def lrename_tss_def
  by simp_all

lemma rename_tss_dist:
  "rename_tss (S\<union>T) m = rename_tss S m \<union> rename_tss T m"
  unfolding rename_def rename_tss_def
  by fast

lemma lrename_tss_dist:
  "lrename_tss (S\<union>T) M = lrename_tss S M \<union> lrename_tss T M"
proof-
  have "lrename_tss (S\<union>T) M = \<Union>{rename_tss S (M l) \<union> rename_tss T (M l) | l. True}"
    unfolding lrename_tss_def 
    by (simp add: rename_tss_dist)
  also have "... = \<Union>{rename_tss S (M l) | l. True} \<union> \<Union>{rename_tss T (M l) | l. True}"
    by blast
  also have "... = lrename_tss S M \<union> lrename_tss T M"
    unfolding lrename_tss_def ..
  ultimately show ?thesis 
    by simp
qed

primrec rename_list :: "'n list \<Rightarrow> ('n \<rightharpoonup> 'n) \<Rightarrow> 'n list" where
  "rename_list [] m = []" | 
  "rename_list (l#ls) m = (rename l m) # (rename_list ls m)"

lemma rename_list_dist:
  "rename_list (xs @ ys) m = (rename_list xs m) @ (rename_list ys m)"
  by(induct xs arbitrary: ys, simp_all)

definition rename_inter :: "('n,'l) interface \<Rightarrow> ('l \<Rightarrow> 'n \<rightharpoonup> 'n) \<Rightarrow> ('n,'l) interface" where
  "rename_inter i M = (\<lambda>l. rename_list (i l) (M l))"

lemma rename_inter_dist:
   "rename_inter (i @@ j) M =(rename_inter i M) @@ (rename_inter j M)"
  unfolding rename_inter_def inter_comp_def
  by (simp add: rename_list_dist)

definition rename_nodes :: "('n \<rightharpoonup> 'l) => ('n \<rightharpoonup> 'n) => ('n \<rightharpoonup> 'l)" where
  "rename_nodes N m = N |`(- dom m)"

lemma  rename_nodes_alt:
  "rename_nodes N m = (\<lambda>n. if n \<in> (dom m) then None else N n)"
  unfolding rename_nodes_def restrict_map_def
  by (metis Compl_iff)

definition lrename_nodes :: "('n \<rightharpoonup> 'l) => ('l \<Rightarrow> 'n \<rightharpoonup> 'n) => ('n \<rightharpoonup> 'l)" where
  "lrename_nodes N M = N |` (-\<Union>{dom (M l) |l. True})"

lemma lrename_nodes:
  "lrename_nodes N M = N|`(\<Inter>{-dom (M l)|l. True})"
  unfolding lrename_nodes_def restrict_map_def
  by (simp add: full_SetCompr_eq)

lemma lrename_nodes_var: 
  "lrename_nodes N M  = (\<lambda>n. if n \<in> \<Union>{dom (M l) |l. True} then None else N n)"
  unfolding lrename_nodes_def restrict_map_def
  by (meson Compl_iff)


lemma dom_lrename:
  "dom(lrename_nodes N M) = dom N \<inter> (\<Inter>{-dom (M l)|l. True})"
  by (simp add: lrename_nodes)


(* can probably be made more beautiful *)
(* what if 2 graphs have the same node id, but different labels? *)
definition comp_merge :: "('n,'l) component_model \<Rightarrow> ('n,'l) component_model 
                          \<Rightarrow> ('n,'l) component_model" (infixl "\<cdot>" 70) where
  "comp_merge c d = (
      (\<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d) (c\<^sup>\<star>)),
      (lrename_nodes (fst(graph c)) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) ++ (fst(graph d)),
       lrename_tss (transitions c) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union> transitions d),
      (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)))"


lemma comp_merge_left:
  "\<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>)) (c\<^sup>\<star>) =
    \<^sup>\<star>c @@ inter_prune (\<^sup>\<star>d) (c\<^sup>\<star>) @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d))"
  unfolding inter_prune_def inter_comp_def
  apply(standard)
  by (simp add: add.commute)

(*
lemma a1:
 "dom(M |` (A\<inter>-(dom (N))\<union>(A\<inter>-B))) \<inter> dom(N|`B) = {}"
  unfolding dom_def restrict_map_def
  apply clarsimp
  by fastforce

lemma a2:
 "M |`A ++ N|`B = ((M++(N|`B)) |` (A\<inter>-(dom (N))\<union> (A\<inter>-B)) ++ N|`B)"
  unfolding restrict_map_def map_add_def dom_def
  by fastforce

lemma a3:
  "length ((\<^sup>\<star>d @@ (\<lambda>l. drop (length ((d\<^sup>\<star>) l)) ((\<^sup>\<star>e) l))) l)
    =
   length ((\<^sup>\<star>d) l) + (max ((length((\<^sup>\<star>e) l))-(length ((d\<^sup>\<star>) l))) 0)"
  by (simp add: inter_comp_def)

lemma a4:
  "((d\<^sup>\<star>@@ (\<lambda>l. drop (length ((\<^sup>\<star>d) l)) ((c\<^sup>\<star>) l))) l)
   =
   ((d\<^sup>\<star>) l) @ drop (length ((\<^sup>\<star>d) l)) ((c\<^sup>\<star>) l)"
  by (simp add: inter_comp_def)   

lemma a:
  "M|`A ++ N|`B = M|`(A-dom(N|`B)) ++ N|`B"
  unfolding restrict_map_def map_add_def dom_def
  by fastforce
*)
lemma restrict_add_map_distribute: 
  "(M|`A ++ N)|`B = (M|`A)|`B ++ N|`B"
  unfolding restrict_map_def map_add_def
  by fastforce

lemma not_dom_none: "x\<notin>dom M \<Longrightarrow> M x = None"
  unfolding dom_def by blast

lemma doms_comp:
  "dom(lrename_nodes (fst (graph c)) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>))) ++
    lrename_nodes (fst (graph d)) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) ++
    fst (graph e)) = 
dom(lrename_nodes (lrename_nodes (fst (graph c)) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) ++ fst (graph d))
     (match_inter (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)) (\<^sup>\<star>e)) ++
    fst (graph e))"
  apply(simp add:sup_commute dom_lrename match_inter_def  match_lists_dom inter_prune_def  inter_comp_def)
  unfolding dom_def
  sledgehammer 
  sledgehammer
  apply standard
  sledgehammer
  sorry


lemma comp_merge_graph_nodes_aux:
  "(fst (graph c) |` \<Inter> {u. \<exists>l. u = - set (take (length ((\<^sup>\<star>d) l) + (length ((\<^sup>\<star>e) l) - length ((d\<^sup>\<star>) l))) ((c\<^sup>\<star>) l))} ++
          fst (graph d) |` \<Inter> {u. \<exists>l. u = - set (take (length ((\<^sup>\<star>e) l)) ((d\<^sup>\<star>) l))} ++
          fst (graph e))
          x =
         (fst (graph c) |`
          (\<Inter> {u. \<exists>l. u = - set (take (length ((\<^sup>\<star>d) l)) ((c\<^sup>\<star>) l))} \<inter>
           \<Inter> {u. \<exists>l. u = - set (take (length ((\<^sup>\<star>e) l)) ((d\<^sup>\<star>) l)) \<inter>
                          - set (take (length ((\<^sup>\<star>e) l) - length ((d\<^sup>\<star>) l)) (drop (length ((\<^sup>\<star>d) l)) ((c\<^sup>\<star>) l)))}) ++
          fst (graph d) |`
          \<Inter> {u. \<exists>l. u = - set (take (length ((\<^sup>\<star>e) l)) ((d\<^sup>\<star>) l)) \<inter>
                         - set (take (length ((\<^sup>\<star>e) l) - length ((d\<^sup>\<star>) l)) (drop (length ((\<^sup>\<star>d) l)) ((c\<^sup>\<star>) l)))} ++
          fst (graph e))
          x"
  (is "(?l1 ++ ?l2 ++ ?l3) x = (?r1 ++ ?r2 ++ ?r3) x")
proof -
  have dom_iff: "dom(?l1 ++ ?l2 ++ ?l3) = dom(?r1 ++ ?r2 ++ ?r3)"
    using doms_comp 
    by (simp add: lrename_nodes match_inter_def inter_prune_def match_lists_dom 
          inter_comp_def restrict_add_map_distribute)

  have  "x\<notin>dom(?l1 ++ ?l2 ++ ?l3) \<or>
         x\<in>dom(?l3) \<or>
        (x\<in>dom ?l2 - dom ?l3 \<and> x\<in>dom ?r3) \<or>
        (x\<in>dom ?l2 - dom ?l3 \<and> x\<in>dom ?r2) \<or>
        (x\<in>dom ?l2 - dom ?l3 \<and> x\<in>dom ?r1 - dom ?r2) \<or>
        (x\<in>dom ?l1 - dom ?l2 -dom ?l3 \<and> x\<in>dom ?r3) \<or>
        (x\<in>dom ?l1 - dom ?l2 -dom ?l3 \<and> x\<in>dom ?r1) \<or>
        (x\<in>dom ?l1 - dom ?l2 -dom ?l3 \<and> x\<in>dom ?r2 - dom ?r1)"
    by (metis (no_types, lifting) DiffI domIff map_add_None dom_iff)
  moreover
  { (* shorten *)
    assume a: "x\<notin>dom(?l1 ++ ?l2 ++ ?l3)"
    hence lhs: "(?l1 ++ ?l2 ++ ?l3) x = None"
      apply(rule not_dom_none) done

    have "x\<notin>dom(?l1 ++ ?l2 ++ ?l3) \<longleftrightarrow> x\<notin>dom(?r1 ++ ?r2 ++ ?r3)"
      using dom_iff by auto
    hence ?thesis 
      by (metis (no_types, lifting) domIff lhs)
  }
  moreover
  { assume "x\<in>dom(?l3)"
    hence ?thesis
      by force
  }
  moreover
  { assume "x\<in>dom ?l2 - dom ?l3 \<and> x\<in>dom ?r3"
    hence ?thesis
      by force
  }
  moreover
  { assume "x\<in>dom ?l2 - dom ?l3 \<and> x\<in>dom ?r2"
    hence ?thesis
      by (simp add: map_add_dom_app_simps(1) map_add_dom_app_simps(3))
  }
  moreover
  { assume "x\<in>dom ?l2 - dom ?l3 \<and> x\<in>dom ?r1 - dom ?r2"
    hence ?thesis
      by auto
  }
  moreover
  { assume "x\<in>dom (?l1)-dom (?l2)-dom ?l3 \<and> x\<in>dom ?r3"
    hence ?thesis
      by force
  }
  moreover 
  { assume "x\<in>dom ?l1 - dom ?l2 - dom ?l3 \<and> x\<in>dom ?r1"
    hence ?thesis
    by (smt (z3) DiffD2 IntD1 diff_eq domIff map_add_dom_app_simps(3) mem_Collect_eq mem_simps(11) restrict_map_def)
  }
  moreover
  { assume "x\<in>dom (?l1)-dom (?l2)-dom ?l3 \<and> x\<in>dom(?r2)-dom(?r1)"
    hence ?thesis
      apply clarsimp by blast
  }
  ultimately show ?thesis 
    by fastforce
qed

lemma comp_merge_graph_nodes:
shows "lrename_nodes (fst (graph c)) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>))) ++
    lrename_nodes (fst (graph d)) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) ++
    fst (graph e) =
    lrename_nodes (lrename_nodes (fst (graph c)) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) ++ fst (graph d))
     (match_inter (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)) (\<^sup>\<star>e)) ++
    fst (graph e)"
  apply(standard)
  by (simp add: lrename_nodes match_inter_def inter_prune_def match_lists_dom 
                inter_comp_def restrict_add_map_distribute comp_merge_graph_nodes_aux)

lemma comp_merge_graph_tss:
  "lrename_tss (graph_transitions (graph c))
     (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>))) \<union>
    graph_transitions
     (lrename_nodes (fst (graph d)) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) ++ fst (graph e),
      lrename_tss (graph_transitions (graph d)) (match_inter (d\<^sup>\<star>) (\<^sup>\<star>e)) \<union>
      graph_transitions (graph e)) =
    lrename_tss
     (graph_transitions
       (lrename_nodes (fst (graph c)) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) ++ fst (graph d),
        lrename_tss (graph_transitions (graph c)) (match_inter (c\<^sup>\<star>) (\<^sup>\<star>d)) \<union>
        graph_transitions (graph d)))
     (match_inter (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)) (\<^sup>\<star>e)) \<union>
    graph_transitions (graph e)"
  unfolding lrename_tss_def rename_tss_def inter_prune_def lrename_nodes_def
  apply standard
  sorry


lemma comp_merge_right:
  "e\<^sup>\<star>@@ inter_prune (d\<^sup>\<star>) (\<^sup>\<star>e) @@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d @@ inter_prune (\<^sup>\<star>e) (d\<^sup>\<star>)) =
    e\<^sup>\<star>@@ inter_prune (d\<^sup>\<star>@@ inter_prune (c\<^sup>\<star>) (\<^sup>\<star>d)) (\<^sup>\<star>e)"
  unfolding inter_prune_def inter_comp_def
  apply(standard)
  by (simp add: add.commute)


lemma comp_merge_assoc:
  "c \<cdot> (d \<cdot> e) = (c \<cdot> d) \<cdot> e"
  unfolding comp_merge_def
  apply(simp)
  apply(rule conjI, rule comp_merge_left)
  apply(rule conjI, rule comp_merge_graph_nodes)
  apply(rule conjI, rule comp_merge_graph_tss)
  by(rule comp_merge_right)

end





