theory temp
imports Main

begin

(* Definition 2. An argumentation framework is a pair
AF = (AR, attacks)
where AR is a set of arguments, and attacks is a binary relation on AR, i.e.
attacks \<subseteq> AR x AR.
For two arguments A and B, the meaning of attacks(A, B) is that A represents
an attack against B.
*)

typedef ('v) argumentation_framework = "{(V :: 'v set, E :: ('v \<times> 'v) set). E \<subseteq> V \<times> V}" by auto

definition arguments :: "('v) argumentation_framework \<Rightarrow> 'v set" where
  "arguments G = fst (Rep_argumentation_framework G)"

definition attack_relations :: "('v) argumentation_framework \<Rightarrow> ('v \<times> 'v) set" where
  "attack_relations G = snd (Rep_argumentation_framework G)"

definition attacks :: "('v) argumentation_framework \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "attacks G a b \<longleftrightarrow> (a, b) \<in> attack_relations G"

(* Example 3 (Continuation of Example 1). The exchange between I and A can be
represented by an argumentation framework (AR, attacks) as follows: AR =
{i_1, i_2, a} and attacks = {(i_1, a), (a, i_1), (i_2, a)} with i_1 and i_2 denoting the first and
the second argument of I, respectively, and a denoting the argument of A. 
*)

definition example_af :: "string argumentation_framework" where
  "example_af = Abs_argumentation_framework ({''i1'', ''i2'', ''a''}, 
                                             {(''i1'', ''a''), (''a'', ''i1''), (''i2'', ''a'')})"

(* Definition 5. A set S of arguments is said to be conflict-free if there are no
arguments A and B in S such that A attacks B. *)

definition conflict_free :: "('v) argumentation_framework \<Rightarrow> 'v set \<Rightarrow> bool" where
  "conflict_free G S \<longleftrightarrow> (\<forall>a b. a \<in> S \<and> b \<in> S \<longrightarrow> \<not>attacks G a b)"

(* Definition 6.
(1) An argument A \<in> AR is acceptable with respect to a set S of arguments iff
for each argument B \<in> AR: if B attacks A then B is attacked by S.
(2) A conflict-free set of arguments S is admissible iff each argument in S is
acceptable with respect to S. *)

definition acceptable :: "('v) argumentation_framework \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool" where
  "acceptable G A S \<longleftrightarrow> (\<forall>B. B \<in> arguments G \<and> attacks G B A \<longrightarrow> (\<exists>C. C \<in> S \<and> attacks G C B))"

definition admissible :: "('v) argumentation_framework \<Rightarrow> 'v set \<Rightarrow> bool" where
  "admissible G S \<longleftrightarrow> conflict_free G S \<and> (\<forall>A. A \<in> S \<longrightarrow> acceptable G A S)"

(* Definition 7. A preferred extension of an argumentation framework AF is a
maximal (with respect to set inclusion) admissible set of AF. *)

definition preferred_extension :: "('v) argumentation_framework \<Rightarrow> 'v set \<Rightarrow> bool" where
  "preferred_extension G S \<longleftrightarrow> admissible G S \<and> (\<forall>T. admissible G T \<and> S \<subseteq> T \<longrightarrow> S = T)"

(* Example 8 (Continuation of Example 3). It is not difficult to see that AF has
exactly one preferred extension E = {i_1, i_2}.
*)
definition example_af :: "(string) argumentation_framework" where
  "example_af = \<lparr>arguments = {''i1'', ''i2'', ''i3''}, attacks = {(''i3'', ''i1''), (''i3'', ''i2'')} \<rparr>"

definition example_preferred_extension :: "string set" where
  "example_preferred_extension = {''i1'', ''i2''}"

lemma example_preferred_extension_correct:
  "preferred_extension example_af example_preferred_extension"
proof -
  have "admissible example_af example_preferred_extension"
  proof
    show "conflict_free example_af example_preferred_extension"
      unfolding conflict_free_def example_af_def example_preferred_extension_def
      by auto
  next
    show "\<forall>A. A \<in> example_preferred_extension \<longrightarrow> acceptable example_af A example_preferred_extension"
      unfolding acceptable_def example_af_def example_preferred_extension_def
      by auto
  qed
  moreover have "\<forall>T. admissible example_af T \<and> example_preferred_extension \<subseteq> T \<longrightarrow> example_preferred_extension = T"
  proof (intro allI impI)
    fix T
    assume "admissible example_af T" and "example_preferred_extension \<subseteq> T"
    then show "example_preferred_extension = T"
      unfolding admissible_def conflict_free_def acceptable_def example_af_def example_preferred_extension_def
      by auto
  qed
  ultimately show ?thesis
    unfolding preferred_extension_def
    by auto
qed

end
