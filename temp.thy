theory temp
imports Main
begin

(* Further proofs will go here *)


(* Definition 2. An argumentation framework is a pair
AF = (AR, attacks)
where AR is a set of arguments, and attacks is a binary relation on AR, i.e.
attacks \<subseteq> AR x AR.
For two arguments A and B, the meaning of attacks(A, B) is that A represents
an attack against B.

 *)

typedef ('v) argumentation_framework = "{(V :: 'v set, E :: ('v \<times> 'v) set). E \<subseteq> V \<times> V}" by auto

(*
Definition 2. An argumentation framework is a pair
AF = (AR, attacks)
where AR is a set of arguments, and attacks is a binary relation on AR, i.e.
attacks \<subseteq> AR x AR.
For two arguments A and B, the meaning of attacks(A, B) is that A represents
an attack against B.
*)

definition arguments :: "('v set \<times> ('v \<times> 'v) set) \<Rightarrow> 'v set" where
  "arguments G = fst G"

definition attack_relations :: "('v set \<times> ('v \<times> 'v) set) \<Rightarrow> ('v \<times> 'v) set" where
  "attack_relations G = snd G"

definition attacks :: "('v set \<times> ('v \<times> 'v) set) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "attacks G a b \<longleftrightarrow> (a, b) \<in> attack_relations G"

(* Definition 5. A set S of arguments is said to be conflict-free if there are no
arguments A and B in S such that A attacks B. *)

definition conflict_free :: "('v set \<times> ('v \<times> 'v) set) \<Rightarrow> 'v set \<Rightarrow> bool" where
  "conflict_free G S \<longleftrightarrow> (\<forall>a b. a \<in> S \<and> b \<in> S \<longrightarrow> \<not>attacks G a b)"

(* Definition 6.
(1) An argument A \<in> AR is acceptable with respect to a set S of arguments iff
for each argument B \<in> AR: if B attacks A then B is attacked by S.
(2) A conflict-free set of arguments S is admissible iff each argument in S is
acceptable with respect to S. *)

definition acceptable :: "('v set \<times> ('v \<times> 'v) set) \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool" where
  "acceptable G A S \<longleftrightarrow> (\<forall>B. B \<in> arguments G \<and> attacks G B A \<longrightarrow> (\<exists>C. C \<in> S \<and> attacks G C B))"

definition admissible :: "('v set \<times> ('v \<times> 'v) set) \<Rightarrow> 'v set \<Rightarrow> bool" where
  "admissible G S \<longleftrightarrow> conflict_free G S \<and> (\<forall>A. A \<in> S \<longrightarrow> acceptable G A S)"

(* Definition 7. A preferred extension of an argumentation framework AF is a
maximal (with respect to set inclusion) admissible set of AF. *)

definition preferred_extension :: "('v set \<times> ('v \<times> 'v) set) \<Rightarrow> 'v set \<Rightarrow> bool" where
  "preferred_extension G S \<longleftrightarrow> admissible G S \<and> (\<forall>T. admissible G T \<and> S \<subseteq> T \<longrightarrow> S = T)"

(* Example 8. Consider the argumentation framework AR = {i_1, i_2, a} and 
attacks = {(i_1, a), (a, i_1), (i_2, a)}. It is not difficult to see that AF has
exactly one preferred extension E = {i_1, i_2}. *)

definition example_af :: "string argumentation_framework" where
  "example_af = Abs_argumentation_framework ({''i1'', ''i2'', ''a''}, 
                                             {(''i1'', ''a''), (''a'', ''i1''), (''i2'', ''a'')})"


definition example_preferred_extension :: "string set" where
  "example_preferred_extension = {''i1'', ''i2''}"


lemma example_preferred_extension_correct:
  "preferred_extension example_af example_preferred_extension"
proof -
  have "argumentation_framework example_af" 
  have "conflict_free example_af example_preferred_extension" 

end
