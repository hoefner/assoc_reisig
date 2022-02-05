theory Interface
  imports Graph Misc

begin

(* thought about partial function, but then I would have needed non-empty lists; 
this one seems easier; empty list means no label of this kind in interface *)
(* lists make re-indexing easier *)

type_synonym ('n,'l) interface = "'l \<Rightarrow> 'n list"
definition inter_nodes :: "('n,'l) interface \<Rightarrow> 'n set" where
  "inter_nodes i \<equiv> \<Union>{set (i l)| l. True}"


(* index calculation is only for fun to make it compatible to the paper, 
but is of no relevance for this development *)
primrec list_index_aux:: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat option" where
  "list_index_aux a [] n = None" |
  "list_index_aux a (x#xs) n = (if a=x then (Some n) else list_index_aux a xs (Suc n))" 

abbreviation list_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "list_index a l \<equiv> list_index_aux a l 0"

definition index :: "('n,'l) interface \<Rightarrow> 'n \<Rightarrow> 'l \<Rightarrow> nat option" where 
  "index i n l = list_index n (i l)"
(* end index calculation *)

abbreviation empty:: "'l \<Rightarrow> 'n list" ("\<lparr>\<rparr>") where
  "empty \<equiv> \<lambda>l. []"

lemma empty_inter_nodes:
  "inter_nodes \<lparr>\<rparr> = {}"
  by (simp add: inter_nodes_def)

subsection \<open>Matching Lists\<close>
(* could we allow the same node occur in the list multiple times? I guess not;
this will be ruled out by the definition of is_ComponentInterface *)
fun match_lists :: "'n list \<Rightarrow> 'n list \<Rightarrow> 'n \<rightharpoonup> 'n" where
  "match_lists [] ys = Map.empty" | 
  "match_lists xs [] = Map.empty" |
  "match_lists (x#xs) (y#ys) = (match_lists xs ys)(x\<mapsto>y)"
 

lemma match_lists_empty[simp]:
  shows "match_lists [] ys = Map.empty"
  and "match_lists xs [] = Map.empty"
  using match_lists.elims by blast+

lemma match_lists_dom:
  "dom (match_lists xs ys) = set (take (length ys) xs)"
  apply(induct xs arbitrary: ys,simp)
  by (smt (verit) dom_fun_upd length_0_conv length_tl list.discI list.sel(3) list.simps(15) 
                  match_lists.elims option.distinct(1) take_Cons' take_eq_Nil)

lemma match_lists_dom':
  "dom (match_lists xs ys) \<subseteq> set xs"
  by (simp add: match_lists_dom set_take_subset)

lemma distinct_dom:
  "distinct(x#xs) \<Longrightarrow> (x \<notin> dom (match_lists xs ys))"
  by (meson distinct.simps(2) match_lists_dom' subsetD)

lemma match_lists_restrict: 
  "distinct xs \<Longrightarrow> match_lists xs ys |` set xs = match_lists xs ys"
proof(induct xs arbitrary: ys, simp)
  case (Cons x xs)
  thus ?case 
  proof(cases "ys=[]", simp)
    case False
    then obtain y ys' where y: "ys=y#ys'"
      by (meson list.exhaust)
    thus "match_lists (x # xs) ys |` set (x # xs) = match_lists (x # xs) ys"
      using Cons by simp
  qed
qed

lemma match_list_added:
  assumes "(a, b) \<notin> map2set (match_lists xs ys)"
  and "(a, b) \<in> map2set (match_lists (x # xs) (y#ys))"
  shows "(a,b) = (x,y)"
  using assms
  by (smt (z3) dom_fun_upd fun_upd_other insertCI insertE map2set_def map_upd_Some_unfold 
               match_lists.simps(3) mem_Collect_eq option.distinct(1) option.sel)

lemma distinct_match_lists_restrict:
  "distinct (x#xs) \<Longrightarrow> (match_lists (x#xs) (y#ys)) |` set xs = match_lists xs ys"
  by (simp add: match_lists_restrict)

lemma match_lists_minimum:
  "let n = min(length xs) (length ys) 
   in match_lists xs ys = match_lists (take n xs) (take n ys)"
proof(induct xs arbitrary: ys, fastforce)
  case (Cons x xs)
  thus ?case 
  proof(cases "ys = []", fastforce)
    case False
    then obtain y ys' where y: "ys=y#ys'"
      by (meson list.exhaust)
    thus ?thesis
      by (metis Cons.hyps length_Cons match_lists.simps(3) min_Suc_Suc take_Suc_Cons)
  qed
qed

lemma match_list_iso:
  "distinct (x#xs) \<Longrightarrow> map2set (match_lists xs ys) \<subseteq> map2set (match_lists (x#xs) (y#ys))"
  unfolding map2set_def
  using Suc_leI match_lists_dom' by fastforce

lemma match_lists_point1:
  "(a,b) \<in> map2set (match_lists xs ys) 
     \<Longrightarrow> (\<exists>(n::nat) < min (length xs) (length ys). a = xs!n \<and> b = ys!n)"
unfolding map2set_def  
proof(induct xs arbitrary: ys,fastforce)
  case (Cons x xs)
  thus ?case 
  proof(cases "ys=[]", simp add: Cons.prems)
    case False
    then obtain y ys' 
      where x1: "(a, b) \<in> map2set (match_lists (x # xs) (y#ys'))" and x2: "ys = y#ys'"
      unfolding map2set_def
      by (metis list.exhaust Cons.prems)
    thus ?thesis
      apply(cases "(a, b) \<in> map2set (match_lists xs ys')")
       apply (metis map2set_def Cons.hyps Suc_leI x2 length_Cons less_Suc_eq_le min_less_iff_conj 
                    nth_Cons_Suc)
      using x1 x2 match_list_added by fastforce 
  qed
qed

lemma match_lists_point2:
  "\<lbrakk>distinct xs; (\<exists>n < min (length xs) (length ys). a = xs!n \<and> b = ys!n)\<rbrakk>
      \<Longrightarrow> (a,b) \<in> map2set (match_lists xs ys)"
proof(induct xs arbitrary: ys, fastforce)
  case (Cons x xs)
  thus ?case 
  proof-
    from Cons.prems(2)
    obtain n where a1: "n<min (length (x # xs)) (length ys)\<and> a = (x # xs) ! n \<and> b = ys ! n"
      by blast
    thus ?thesis
    proof(cases "ys=[]",simp add: Cons.prems)
      case False
      then obtain y ys' where a2: "ys = y#ys'"
        using list.exhaust by blast
      thus ?thesis
      proof(cases "n=0",(auto simp:  map2set_def a1 a2)[1])
        case False
        hence "(a, b) \<in> map2set (match_lists xs ys')"
          using a1 a2 gr0_conv_Suc Cons.hyps Cons.prems(1) by fastforce
        thus ?thesis
          by (metis Cons.prems(1) a2 match_list_iso subset_eq)
      qed
    qed
  qed
qed

lemma match_lists_point:
  assumes "distinct xs"
  shows "(a,b) \<in> map2set (match_lists xs ys) 
         \<longleftrightarrow> (\<exists>(n::nat) < min (length xs) (length ys). a = xs!n \<and> b = ys!n)"
  by (metis assms match_lists_point1 match_lists_point2)

lemma match_lists_point':  
  assumes "distinct xs"
  shows "a\<in>dom(match_lists xs ys) 
         \<longleftrightarrow> (\<exists>(n::nat) < min(length xs)(length ys). a = xs!n \<and> the((match_lists xs ys) a) = ys!n)"
  using match_lists_point assms unfolding map2set_def
  by fastforce

(*
lemma test:
  "distinct (x # xs) \<Longrightarrow> x\<notin>dom (match_lists xs ys)"
  by (meson distinct.simps(2) match_lists_dom' subsetD) 
*)

lemma match_lists_assoc:
  "distinct (xs@ys) \<Longrightarrow> match_lists (xs@ys) zs = (match_lists xs zs) ++ (match_lists ys (drop (length xs) zs))"
proof(induct xs arbitrary:zs, simp)
  case (Cons x xs)
  show "match_lists ((x # xs) @ ys) zs = match_lists (x # xs) zs ++ match_lists ys (drop (length (x # xs)) zs)"
  proof(cases "zs=[]", simp)
    case False
    then obtain z zs' where z: "zs=z#zs'"
      by (meson list.exhaust)
    have "x\<notin>dom (match_lists ys (drop (length xs) zs'))"
      using Cons.prems
      by (metis Un_iff append_Cons distinct.simps(2) match_lists_dom' set_append subsetD)
    thus "match_lists ((x # xs) @ ys) zs = match_lists (x # xs) zs ++ match_lists ys (drop (length (x # xs)) zs)"
      by (metis z Cons.hyps Cons.prems append_Cons distinct.simps(2) drop_Suc_Cons length_Cons map_add_upd_left match_lists.simps(3))
  qed
qed

subsection \<open>Matching Interfaces\<close>
(* function makes it easier to have disjointness, as nodes are defined as pairs n,l *)
definition match_inter :: "('n,'l) interface \<Rightarrow> ('n,'l) interface \<Rightarrow> 'l \<Rightarrow> 'n \<rightharpoonup> 'n" where
  "match_inter i j = (\<lambda>l. match_lists (i l) (j l))"

(* 
(\<lambda>l. set (zip (i l) (j l))) 
*)


lemma match_inter_point: 
  assumes "distinct (i l)"
  shows "(a, b) \<in> map2set ((match_inter i j) l) 
         \<longleftrightarrow> (\<exists>n < min (length (i l)) (length (j l)). a = (i l)!n \<and> b = (j l)!n)"
  unfolding match_inter_def
    using assms by (rule match_lists_point)

lemma match_inter_point': 
  assumes "distinct (i l)"
  shows "a \<in> dom((match_inter i j) l) 
         \<longleftrightarrow> (\<exists>n<min(length(i l)) (length(j l)). a=(i l)!n \<and> the(((match_inter i j) l) a)=(j l)!n)"
  using match_inter_point assms unfolding map2set_def
  by fastforce

lemma match_inter_empty[simp]:
  shows "match_inter \<lparr>\<rparr> i = (\<lambda>l. Map.empty)"
  and "match_inter i \<lparr>\<rparr> = (\<lambda>l. Map.empty)"
  unfolding match_inter_def
   apply simp
  by (metis list.discI match_lists.elims)


subsection \<open>Matching -- in preparation\<close>

definition inter_prune :: "('n,'l) interface \<Rightarrow> ('n,'l) interface \<Rightarrow> ('n,'l) interface" where
  "inter_prune i j = (\<lambda>l. drop (length (j l)) (i l))"

definition inter_comp :: "('n,'l) interface \<Rightarrow> ('n,'l) interface \<Rightarrow> ('n,'l) interface" (infixl "@@" 60) where
  "inter_comp  i j = (\<lambda>l. (i l)@(j l))"

lemma inter_comp_empty[simp]:
  shows "\<lparr>\<rparr> @@ i = i"
  and   "i @@ \<lparr>\<rparr> = i"
  unfolding inter_comp_def
  by force+

lemma inter_comp_assoc:
  "(i @@ j) @@ k = i @@ (j @@ k)"
  unfolding inter_comp_def
  by simp 

lemma inter_prune_empty[simp]:
  "inter_prune i \<lparr>\<rparr> = i"
  "inter_prune \<lparr>\<rparr> i = \<lparr>\<rparr>"
  unfolding inter_prune_def
  by fastforce+


lemma map2set_extend:
  assumes "distinct (x#xs)"
  shows" map2set (match_lists (x # xs) (y#ys)) = {(x,y)} \<union> map2set (match_lists xs ys)"
proof-
  have "map2set (match_lists (x # xs) (y#ys)) = map2set (Map.empty(x\<mapsto>y) ++ (match_lists xs ys))"
    by (metis assms distinct_dom empty_map_add map_add_upd_left match_lists.simps(3))
  also have "... = map2set (Map.empty(x\<mapsto>y)) \<union> map2set ((match_lists xs ys))"
    apply(rule map2set_union)
    by (metis assms distinct_dom Int_empty_left Int_insert_left_if0 dom_eq_singleton_conv)
  ultimately show ?thesis 
    by (simp add: map2set_single)
qed

lemma match_lists_set_zip:
  "distinct xs \<Longrightarrow> map2set(match_lists xs ys) = set (zip xs ys)"
proof(induct xs arbitrary:ys, simp add: map2set_def)
  case (Cons x xs)
  then show ?case
  proof(cases "ys = []", simp add: map2set_def)
  assume "distinct (x#xs)"
  case False
   then obtain y ys' where y: "ys=y#ys'"
      by (meson list.exhaust)
    thus " map2set (match_lists (x # xs) ys) = set (zip (x # xs) ys)"
      using Cons 
      by (smt (z3) Collect_cong map2set_def match_lists_point mem_Collect_eq set_zip)
  qed
qed



end