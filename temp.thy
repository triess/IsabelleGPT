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
definition argumentation_framework :: "'a set \<times> ('a \<times> 'a) set \<Rightarrow> bool" where
"argumentation_framework AF \<equiv> let (AR, attacks) = AF in attacks \<subseteq> AR \<times> AR"
end