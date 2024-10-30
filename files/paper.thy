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
definition argumentation_framework :: "('a set * ('a \<times> 'a) set) \<Rightarrow> bool" where
  "argumentation_framework AF \<equiv>
    let AR = fst AF; attacks = snd AF in
    attacks \<subseteq> AR \<times> AR"
(*

Definition 6.

(1) An argument A \<in> AR is acceptable with respect to a set S of arguments iff

for each argument B \<in> AR: if B attacks A then B is attacked by S (see Remark 4).

(2) A conflict-free set of arguments S is admissible iff each argument in S is

acceptable with respect to S.

 *)
definition acceptable :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "acceptable A S \<longleftrightarrow> (\<forall>B. B \<in> AR \<longrightarrow> (attacks B A \<longrightarrow> (\<exists>C \<in> S. attacks C B)))"

definition admissible :: "'a set \<Rightarrow> bool" where
  "admissible S \<longleftrightarrow> conflict_free S \<and> (\<forall>A \<in> S. acceptable A S)"

end