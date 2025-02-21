
(* Definition 2. An argumentation framework is a pair

AF = (AR, attacks)

where AR is a set of arguments, and attacks is a binary relation on AR, i.e.

attacks \<subseteq> AR x AR.

For two arguments A and B, the meaning of attacks(A, B) is that A represents

an attack against B.

 *)
locale argumentation_framework =
  fixes AR :: "'a set" and attacks :: "('a \<times> 'a) set"
  assumes attacks_subset: "attacks \<subseteq> AR \<times> AR"
begin

definition attacks_meaning :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "attacks_meaning A B \<equiv> (A, B) \<in> attacks"

end
