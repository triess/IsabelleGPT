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
  "conflict_free G S \<longleftrightarrow> S \<subseteq> arguments G \<and> (\<forall>a b. a \<in> S \<and> b \<in> S \<longrightarrow> \<not>attacks G a b)"

(* Definition 6.
(1) An argument A \<in> AR is acceptable with respect to a set S of arguments iff
for each argument B \<in> AR: if B attacks A then B is attacked by S.
(2) A conflict-free set of arguments S is admissible iff each argument in S is
acceptable with respect to S. *)

definition acceptable :: "('v) argumentation_framework \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool" where
  "acceptable G A S \<longleftrightarrow> S \<subseteq> arguments G \<and> A \<in> arguments G \<and> (\<forall>B. B \<in> arguments G \<and> attacks G B A \<longrightarrow> (\<exists>C. C \<in> S \<and> attacks G C B))"

definition admissible :: "('v) argumentation_framework \<Rightarrow> 'v set \<Rightarrow> bool" where
  "admissible G S \<longleftrightarrow> S \<subseteq> arguments G \<and> conflict_free G S \<and> (\<forall>A. A \<in> S \<longrightarrow> acceptable G A S)"

(* Definition 7. A preferred extension of an argumentation framework AF is a
maximal (with respect to set inclusion) admissible set of AF. *)

definition preferred_extension :: "('v) argumentation_framework \<Rightarrow> 'v set \<Rightarrow> bool" where
  "preferred_extension G S \<longleftrightarrow> admissible G S \<and> (\<forall>T. admissible G T \<and> S \<subseteq> T \<longrightarrow> S = T)"


(* 
Lemma 10 (Fundamental Lemma). Let S be an admissible set of arguments, and A
and A’ be arguments which are acceptable with respect to S. Then
(1) S’ = S \<union> {A} is admissible, and
(2) A’ is acceptable with respect to S’.
Proof. (1) We need only to show that S’ is conflict-free. Assume the contrary.
Therefore, there exists an argument B \<in> S such that either A attacks B or B
attacks A. From the admissibility of S and the acceptability of A, there is an
argument B’ in S such that B’ attacks B or B’ attacks A. Since S is conflict-free,
it follows that B’ attacks A. But then there is an argument B” in S such that B”
attacks B’. Contradiction!
(2) Obvious. \<box>
 *)
lemma fundamental_lemma:
  assumes "admissible G S" 
    and "acceptable G A S" 
    and "acceptable G A' S"
  shows "admissible G (S \<union> {A})" 
    and "acceptable G A' (S \<union> {A})"
proof -
  have conflict_free_SA: "conflict_free G (S \<union> {A})"
  proof (rule ccontr)
    assume "\<not> conflict_free G (S \<union> {A})"
    then obtain B where "B \<in> S \<union> {A}" and "attacks G B A \<or> attacks G A B"
      by (smt (verit, del_insts) Un_insert_right acceptable_def admissible_def assms(1) assms(2) conflict_free_def insert_iff insert_subset sup_bot_right)  
    then consider (1) "B \<in> S" "attacks G B A" | (2) "B \<in> S" "attacks G A B" 
      | (3) "B = A" "attacks G A B" 
      by auto
    then show False
    proof cases
      case 1
      then obtain B' where "B' \<in> S" and "attacks G B' B" using acceptable_def assms(2)
        by (metis admissible_def assms(1))
      moreover have "\<not> attacks G B' A" 
        using assms(1) `B' \<in> S` conflict_free_def
        by (metis "1"(1) admissible_def calculation(2)) 
      ultimately show False 
        using 1
        by (meson admissible_def assms(1) conflict_free_def) 
    next
      case 2
      then obtain B' where "B' \<in> S" and "attacks G B' A" using assms(2) acceptable_def
        by (metis admissible_def assms(1)) 
      then obtain B'' where "B'' \<in> S" and "attacks G B'' B'" 
        using assms(1) admissible_def acceptable_def
        by (metis assms(2)) 
      moreover have "\<not> attacks G B'' B'" 
        using assms(1) `B'' \<in> S` conflict_free_def
        by (metis \<open>B' \<in> S\<close> admissible_def) 
      ultimately show False 
        by blast
    next
      case 3
      then show False 
        using assms(2) acceptable_def
        by (smt (verit) admissible_def assms(1) conflict_free_def) 
    qed
  qed
  moreover have "\<forall>x\<in>S \<union> {A}. acceptable G x (S \<union> {A})"
  proof
    fix x
    assume "x \<in> S \<union> {A}"
    then show "acceptable G x (S \<union> {A})"
    proof
      assume "x \<in> S"
      then have "acceptable G x S"
        by (metis admissible_def assms(1)) 
      then have "\<forall>y\<in> arguments G.(attacks G y x \<longrightarrow> (\<exists>z\<in> S \<union> {A}.attacks G z y))"
        by (metis Un_insert_right acceptable_def insert_iff sup_bot_right)
      then show "acceptable G x (S \<union> {A})"
        by (meson \<open>acceptable G x S\<close> acceptable_def conflict_free_SA conflict_free_def) 
    next
      assume "x \<in> {A}"
      then have "acceptable G x S"
        by (simp add: assms(2)) 
      then have "\<forall>y\<in> arguments G.(attacks G y x \<longrightarrow> (\<exists>z\<in> S \<union> {A}.attacks G z y))"
        by (metis Un_insert_right acceptable_def insert_iff sup_bot_right) 
      then show "acceptable G x (S \<union> {A})"
        by (meson \<open>acceptable G x S\<close> acceptable_def conflict_free_SA conflict_free_def)
    qed
  qed
  ultimately show "admissible G (S \<union> {A})"
    by (simp add: admissible_def conflict_free_def)
  then have "\<forall>y\<in> arguments G.(attacks G y A' \<longrightarrow> (\<exists>z\<in> S \<union> {A}.attacks G z y))"
    by (metis Un_insert_right acceptable_def assms(3) insert_iff sup_bot_right) 
  moreover show "acceptable G A' (S \<union> {A})"
    by (meson \<open>admissible G (S \<union> {A})\<close> acceptable_def admissible_def assms(3) calculation) 
qed

definition complete_partial_order :: "'a set set \<Rightarrow> bool" where
  "complete_partial_order P \<longleftrightarrow> 
    (\<forall>C. C \<subseteq> P \<and> (\<forall>A B. A \<in> C \<and> B \<in> C \<longrightarrow> (A \<subseteq> B \<or> B \<subseteq> A)) \<longrightarrow> (\<Union>C \<in> P))"

(* 
###
Theorem 11. Let AF be an argumentation framework.
(1) The set of all admissible sets of AF form a complete partial order with
respect to set inclusion.
(2) For each admissible set S of AF, there exists a preferred extension E of AF
such that S \<subseteq> E.

Corollary 12. Every argumentation framework possesses at least one preferred
extension.
###
 *)


theorem admissible_cpo:
  shows "complete_partial_order (admissible G) (\<subseteq>)"
proof -
  have "partial_order (admissible G) (\<subseteq>)"
    by (simp add: partial_order_def admissible_def)
  moreover have "\<forall>c. chain c \<longrightarrow> (\<exists>u. upper_bound c u \<and> admissible G u)"
  proof (rule allI, rule impI)
    fix c
    assume "chain c"
    then have "\<forall>S T. S \<in> c \<and> T \<in> c \<longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
      by (simp add: chain_def)
    then have "\<exists>u. upper_bound c u \<and> admissible G u"
      by (metis (mono_tags, lifting) Union_upper admissible_def upper_bound_def)
    then show "\<exists>u. upper_bound c u \<and> admissible G u"
      by blast
  qed
  ultimately show ?thesis
    by (simp add: complete_partial_order_def)
qed

theorem exists_preferred_extension:
  assumes "admissible G S"
  shows "\<exists>E. preferred_extension G E \<and> S \<subseteq> E"
proof -
  have "\<exists>E. maximal (admissible G) E \<and> S \<subseteq> E"
    using admissible_cpo assms complete_partial_order_def maximal_def
    by blast
  then show ?thesis
    by (simp add: preferred_extension_def)
qed

corollary exists_preferred_extension_for_all:
  shows "\<exists>E. preferred_extension G E"
proof -
  have "\<exists>S. admissible G S"
    by (simp add: admissible_def)
  then obtain S where "admissible G S"
    by blast
  then show ?thesis
    using exists_preferred_extension by blast
qed

end
