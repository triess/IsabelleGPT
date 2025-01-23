theory temp
imports Main
begin

(* Further proofs will go here *)


(* Definition 2. An argumentation framework is a pair
AF = (AR, attacks)
where AR is a set of arguments, and attacks is a binary relation on AR, i.e.
attacks ⊆ AR x AR.
For two arguments A and B, the meaning of attacks(A, B) is that A represents
an attack against B.

 *)

typedef ('v) argumentation_framework = "{(V :: 'v set, E :: ('v × 'v) set). E ⊆ V × V}" by auto

(*
Definition 2. An argumentation framework is a pair
AF = (AR, attacks)
where AR is a set of arguments, and attacks is a binary relation on AR, i.e.
attacks ⊆ AR x AR.
For two arguments A and B, the meaning of attacks(A, B) is that A represents
an attack against B.
*)

definition arguments :: "('v) argumentation_framework ⇒ 'v set" where
  "arguments G = fst (Rep_argumentation_framework G)"

definition attack_relations :: "('v) argumentation_framework ⇒ ('v × 'v) set" where
  "attack_relations G = snd (Rep_argumentation_framework G)"

definition attacks :: "('v) argumentation_framework ⇒ 'v ⇒ 'v ⇒ bool" where
  "attacks G a b ⟷ (a, b) ∈ attack_relations G"


(* Definition 5. A set S of arguments is said to be conflict-free if there are no
arguments A and B in S such that A attacks B. *)

definition conflict_free :: "('v set × ('v × 'v) set) ⇒ 'v set ⇒ bool" where
  "conflict_free G S ⟷ (∀a b. a ∈ S ∧ b ∈ S ⟶ ¬attacks G a b)"

(* Definition 6.
(1) An argument A ∈ AR is acceptable with respect to a set S of arguments iff
for each argument B ∈ AR: if B attacks A then B is attacked by S.
(2) A conflict-free set of arguments S is admissible iff each argument in S is
acceptable with respect to S. *)

definition acceptable :: "('v set × ('v × 'v) set) ⇒ 'v ⇒ 'v set ⇒ bool" where
  "acceptable G A S ⟷ (∀B. B ∈ arguments G ∧ attacks G B A ⟶ (∃C. C ∈ S ∧ attacks G C B))"

definition admissible :: "('v set × ('v × 'v) set) ⇒ 'v set ⇒ bool" where
  "admissible G S ⟷ conflict_free G S ∧ (∀A. A ∈ S ⟶ acceptable G A S)"

(* Definition 7. A preferred extension of an argumentation framework AF is a
maximal (with respect to set inclusion) admissible set of AF. *)

definition preferred_extension :: "('v set × ('v × 'v) set) ⇒ 'v set ⇒ bool" where
  "preferred_extension G S ⟷ admissible G S ∧ (∀T. admissible G T ∧ S ⊆ T ⟶ S = T)"

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
