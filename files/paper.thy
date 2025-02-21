	theory paper
	imports Main

	begin

	(* Definition 2. An argumentation framework is a pair
	AF = (AR, attacks)
	where AR is a set of arguments, and attacks is a binary relation on AR, i.e.
	attacks \<subseteq> AR x AR.
	For two arguments A and B, the meaning of attacks(A, B) is that A represents
	an attack against B.

	*)

definition argumentation_framework :: "string set \<times> (string \<times> string) set \<Rightarrow> bool" where
  "argumentation_framework G \<longleftrightarrow> snd G \<subseteq> (fst G \<times> fst G)"


	definition arguments :: "string set \<times> (string \<times> string) set \<Rightarrow> string set" where
	  "arguments G = fst G"

	definition attack_relation :: "string set \<times> (string \<times> string) set \<Rightarrow> (string \<times> string) set" where
	  "attack_relation G = snd G"

	definition attacks :: "string set \<times> (string \<times> string) set \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where
	  "attacks G a b \<longleftrightarrow> argumentation_framework G \<and> (a, b) \<in> attack_relation G"

	(* Example 3 (Continuation of Example 1). The exchange between I and A can be
	represented by an argumentation framework (AR, attacks) as follows: AR =
	{i_1, i_2, a} and attacks = {(i_1, a), (a, i_1), (i_2, a)} with i_1 and i_2 denoting the first and
	the second argument of I, respectively, and a denoting the argument of A.
	*)

	definition example_af :: "string set \<times> (string \<times> string) set" where
	  "example_af = ({''i1'', ''i2'', ''a''},
												 {(''i1'', ''a''), (''a'', ''i1''), (''i2'', ''a'')})"

lemma example_correct: "argumentation_framework example_af"
proof-
  have "snd example_af \<subseteq>fst example_af \<times> fst example_af"
    by (simp add: example_af_def)
  then show ?thesis
    by (simp add: argumentation_framework_def)
qed

	(* Definition 5. A set S of arguments is said to be conflict-free if there are no
	arguments A and B in S such that A attacks B. *)

	definition conflict_free :: "string set \<times> (string \<times> string) set \<Rightarrow> string set \<Rightarrow> bool" where
	  "conflict_free G S \<longleftrightarrow> argumentation_framework G \<and> S \<subseteq> arguments G \<and> (\<forall>a b. a \<in> S \<and> b \<in> S \<longrightarrow> \<not>attacks G a b)"

	(* Definition 6.
	(1) An argument A \<in> AR is acceptable with respect to a set S of arguments iff
	for each argument B \<in> AR: if B attacks A then B is attacked by S.
	(2) A conflict-free set of arguments S is admissible iff each argument in S is
	acceptable with respect to S. *)

	definition acceptable :: "string set \<times> (string \<times> string) set \<Rightarrow> string \<Rightarrow> string set \<Rightarrow> bool" where
	  "acceptable G A S \<longleftrightarrow> argumentation_framework G \<and> S \<subseteq> arguments G \<and> A \<in> arguments G \<and> (\<forall>B. B \<in> arguments G \<and> attacks G B A \<longrightarrow> (\<exists>C. C \<in> S \<and> attacks G C B))"

	definition admissible :: "string set \<times> (string \<times> string) set \<Rightarrow> string set \<Rightarrow> bool" where
	  "admissible G S \<longleftrightarrow> argumentation_framework G \<and> S \<subseteq> arguments G \<and> conflict_free G S \<and> (\<forall>A. A \<in> S \<longrightarrow> acceptable G A S)"

	(* Definition 7. A preferred extension of an argumentation framework AF is a
	maximal (with respect to set inclusion) admissible set of AF. *)

	definition preferred_extension :: "string set \<times> (string \<times> string) set \<Rightarrow> string set \<Rightarrow> bool" where
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

definition complete_partial_order :: "string set set \<Rightarrow> bool" where
	  "complete_partial_order P \<longleftrightarrow>
		(\<forall>C. C \<subseteq> P \<and> C\<noteq>{} \<and> (\<forall>A B. A \<in> C \<and> B \<in> C \<longrightarrow> (A \<subseteq> B \<or> B \<subseteq> A)) \<longrightarrow> (\<Union>C \<in> P))"

lemma helper_lemma:"\<forall>P A.(complete_partial_order P \<and> A \<in> P \<longrightarrow> complete_partial_order {B\<in>P. A\<subseteq>B})"
proof-
  {
  fix P
  assume "complete_partial_order P"
  fix A
  assume "A \<in> P"
  have "complete_partial_order {B\<in>P. A\<subseteq>B}"
  proof-
    {
    fix C
    assume "C\<subseteq>{B\<in>P. A\<subseteq>B}" and "C\<noteq>{}" and "(\<forall>A B. A \<in> C \<and> B \<in> C \<longrightarrow> (A \<subseteq> B \<or> B \<subseteq> A))"
    have "C\<subseteq>P"
      using \<open>C \<subseteq> {B \<in> P. A \<subseteq> B}\<close> by blast
    have "\<Union>C \<in> P"
      by (meson \<open>C \<noteq> {}\<close> \<open>C \<subseteq> P\<close> \<open>\<forall>A B. A \<in> C \<and> B \<in> C \<longrightarrow> A \<subseteq> B \<or> B \<subseteq> A\<close> \<open>complete_partial_order P\<close> complete_partial_order_def)
    obtain D where "D\<in>C"
      using \<open>C \<noteq> {}\<close> by blast
    have "A\<subseteq>D"
      using \<open>C \<subseteq> {B \<in> P. A \<subseteq> B}\<close> \<open>D \<in> C\<close> by blast
    have "D\<subseteq>\<Union>C"
      by (simp add: Union_upper \<open>D \<in> C\<close>)
    then have "A\<subseteq>\<Union>C"
      using \<open>A \<subseteq> D\<close> by order
    then have "\<Union>C\<in>{B\<in>P. A\<subseteq>B}"
      by (simp add: \<open>\<Union> C \<in> P\<close>)
    }
  show "complete_partial_order {B\<in>P. A\<subseteq>B}"
    by (metis (no_types, lifting) \<open>\<And>C. \<lbrakk>C \<subseteq> {B \<in> P. A \<subseteq> B}; C \<noteq> {}; \<forall>A B. A \<in> C \<and> B \<in> C \<longrightarrow> A \<subseteq> B \<or> B \<subseteq> A\<rbrakk> \<Longrightarrow> \<Union> C \<in> {B \<in> P. A \<subseteq> B}\<close> complete_partial_order_def)
  qed
  }
  show ?thesis
    using \<open>\<And>P A. \<lbrakk>complete_partial_order P; A \<in> P\<rbrakk> \<Longrightarrow> complete_partial_order {B \<in> P. A \<subseteq> B}\<close> by blast
qed

	(*
	Theorem 11. Let AF be an argumentation framework.
	(1) The set of all admissible sets of AF form a complete partial order with
	respect to set inclusion.
	 *)
theorem admissible_sets_cpo:
  assumes "argumentation_framework G"
	  shows "complete_partial_order {S. admissible G S}"
	proof -
    {
		fix C
		assume "C \<subseteq> {S. admissible G S}" and "\<forall>A B. A \<in> C \<and> B \<in> C \<longrightarrow> (A \<subseteq> B \<or> B \<subseteq> A)"
		then have "\<Union>C \<subseteq> arguments G"
		  by (metis Sup_le_iff admissible_def mem_Collect_eq subsetD)
		moreover have "conflict_free G (\<Union>C)"
		proof (rule ccontr)
		  assume "\<not> conflict_free G (\<Union>C)"
		  then obtain a b where "a \<in> \<Union>C" and "b \<in> \<Union>C" and "attacks G a b"
		    using assms calculation conflict_free_def by blast
		  then obtain A B where "A \<in> C" and "B \<in> C" and "a \<in> A" and "b \<in> B"
			by blast
		  then have "A \<subseteq> B \<or> B \<subseteq> A"
			using \<open>\<forall>A B. A \<in> C \<and> B \<in> C \<longrightarrow> (A \<subseteq> B \<or> B \<subseteq> A)\<close> by blast
		  then have "a \<in> B \<and> b \<in> B \<or> a \<in> A \<and> b \<in> A"
			using \<open>a \<in> A\<close> \<open>b \<in> B\<close> by blast
		  then show False
			using \<open>B \<in> C\<close> \<open>attacks G a b\<close> admissible_def conflict_free_def
			by (metis \<open>A \<in> C\<close> \<open>C \<subseteq> {S. admissible G S}\<close> mem_Collect_eq subsetD)
		qed
		moreover
		{
		  fix a :: string
		  assume "a \<in> \<Union>C"
		  then obtain A where "A \<in> C" and "a \<in> A"
			by blast
		  then have "acceptable G a A"
			using \<open>C \<subseteq> {S. admissible G S}\<close> admissible_def
			by (metis mem_Collect_eq subsetD)
		  then have "acceptable G a (\<Union>C)"
		    by (meson UnionI \<open>A \<in> C\<close> acceptable_def calculation(1))
		}
		ultimately have "admissible G (\<Union>C)"
		  using admissible_def conflict_free_def by blast
	  }
	  then show ?thesis
		by (simp add: complete_partial_order_def)
	qed


(*
	(2) For each admissible set S of AF, there exists a preferred extension E of AF
	such that S \<subseteq> E.
*)

theorem Our_Zorn_Lemma:
  assumes r: "complete_partial_order S"
    and aS: "a \<in> S"
  shows "\<exists>y \<in> S. \<forall>z \<in> S. y \<subseteq> z \<longrightarrow> z = y"
proof (rule Zorn_Lemma2)
  show "\<forall>c \<in> chains S. \<exists>y \<in> S. \<forall>z \<in> c. z \<subseteq> y"
  proof
    fix c assume "c \<in> chains S"
    show "\<exists>y \<in> S. \<forall>z \<in> c. z \<subseteq> y"
    proof cases
      assume "c = {}"
      with aS show ?thesis by fast
    next
      assume "c \<noteq> {}"
      show ?thesis
      proof
        show "\<forall>z \<in> c. z \<subseteq> \<Union>c" by fast
        show "\<Union>c \<in> S"
          by (metis (full_types) \<open>c \<in> chains S\<close> \<open>c \<noteq> {}\<close> chains_alt_def complete_partial_order_def mem_Collect_eq r subset_chain_def)
      qed
    qed
  qed
qed


theorem exists_preferred_extension:
  assumes "admissible G S"
  and "argumentation_framework G"
  shows "\<exists>E. preferred_extension G E \<and> S \<subseteq> E"
proof -
  let ?P = "{T. admissible G T \<and> S \<subseteq> T}"
  have "complete_partial_order ?P"
    using admissible_sets_cpo assms helper_lemma by fastforce
  have "\<exists>M. M \<in> ?P \<and> (\<forall>T. T \<in> ?P \<and> M \<subseteq> T \<longrightarrow> M = T)" using Our_Zorn_Lemma
    by (metis (no_types, lifting) \<open>complete_partial_order {T. admissible G T \<and> S \<subseteq> T}\<close> assms(1) dual_order.refl mem_Collect_eq)
  then obtain E where "E \<in> ?P" and "\<forall>T. T \<in> ?P \<longrightarrow> E \<subseteq> T \<longrightarrow> E = T"
    by force
  then have "admissible G E" and "S \<subseteq> E"
  by auto
  moreover have "\<forall>T. admissible G T \<and> E \<subseteq> T \<longrightarrow> E = T"
  using \<open>\<forall>T. T \<in> ?P \<longrightarrow> E \<subseteq> T \<longrightarrow> E = T\<close>
  by (metis CollectI calculation(2) order_trans)
  ultimately show ?thesis
  by (metis preferred_extension_def)
qed


(*
Corollary 12. Every argumentation framework possesses at least one preferred
extension.
 *)
corollary always_exists_preferred_extension:
  assumes "argumentation_framework G"
  shows "\<exists>E. preferred_extension G E"
proof -
  have "admissible G {}"
    by (simp add: admissible_def assms conflict_free_def)
  then show ?thesis
    using exists_preferred_extension
    using assms by blast
qed


(*
Definition 13. A conflict-free set of arguments S is called a stable extension iff S
attacks each argument which does not belong to S.
 *)

definition stable_extension :: "string set \<times> (string \<times> string) set \<Rightarrow> string set \<Rightarrow> bool" where
  "stable_extension G S \<longleftrightarrow> argumentation_framework G \<and> conflict_free G S \<and> (\<forall>a\<in>arguments G. a \<notin> S \<longrightarrow> (\<exists>b \<in> S. attacks G b a))"


(*
Lemma 14. S is a stable extension iff S = {A|A is not attacked by S}.
 *)
lemma stable_extension_characterization:
  assumes "argumentation_framework G"
  shows "stable_extension G S \<longleftrightarrow> S = {a\<in>arguments G. \<not> (\<exists>b \<in> S. attacks G b a)}"
proof
  assume "stable_extension G S"
  then have "conflict_free G S"
    using stable_extension_def by blast
  then have "\<forall>a\<in>arguments G. a \<notin> S \<longrightarrow> (\<exists>b \<in> S. attacks G b a)"
    by (meson \<open>stable_extension G S\<close> stable_extension_def)
  show "S = {a\<in>arguments G. \<not> (\<exists>b \<in> S. attacks G b a)}"
  proof
    show "S \<subseteq> {a\<in>arguments G. \<not> (\<exists>b \<in> S. attacks G b a)}"
      using \<open>conflict_free G S\<close> conflict_free_def
      by (smt (verit) Ball_Collect subsetD)
    show "{a\<in>arguments G. \<not> (\<exists>b \<in> S. attacks G b a)} \<subseteq> S"
    proof
      fix a
      assume "a \<in> {a\<in>arguments G. \<not> (\<exists>b \<in> S. attacks G b a)}"
      then have "\<not> (\<exists>b \<in> S. attacks G b a)"
        by simp
      then show "a \<in> S"
        using \<open>\<forall>a\<in>arguments G. a \<notin> S \<longrightarrow> (\<exists>b \<in> S. attacks G b a)\<close>
        using \<open>a \<in> {a \<in> arguments G. \<not> (\<exists>b\<in>S. attacks G b a)}\<close> by fastforce
    qed
  qed
next
  assume "S = {a\<in>arguments G. \<not> (\<exists>b \<in> S. attacks G b a)}"
  then have "conflict_free G S"
    using conflict_free_def
    using assms by auto
  moreover have "\<forall>a\<in>arguments G. a \<notin> S \<longrightarrow> (\<exists>b \<in> S. attacks G b a)"
    using \<open>S = {a\<in>arguments G. \<not> (\<exists>b\<in>S. attacks G b a)}\<close>
    by blast
  ultimately show "stable_extension G S"
    using stable_extension_def assms
    by blast
qed

(*
Lemma 15. Every stable extension is a preferred extension, but not vice versa.
Proof. It is clear that each stable extension is a preferred extension. To show that
the reverse does not hold, we construct the following argumentation framework:
Let AF = (AR, attacks) with AR = {A} and attacks = {(A, A)}. It is clear that the
empty set is a preferred extension of AF which is clearly not stable. \<box>
 *)
lemma stable_implies_preferred:
  assumes "stable_extension G S"
  shows "preferred_extension G S"
proof -
  have "admissible G S"
    using assms stable_extension_def admissible_def
    by (smt (verit, ccfv_SIG) acceptable_def conflict_free_def subsetD)
  moreover have "\<forall>T. admissible G T \<and> S \<subseteq> T \<longrightarrow> S = T"
    by (meson admissible_def assms conflict_free_def stable_extension_def subset_antisym subset_eq)
  ultimately show ?thesis
    using preferred_extension_def by blast
qed

lemma not_preferred_implies_not_stable:
  assumes "argumentation_framework G"
  shows "\<exists>G S. preferred_extension G S \<and> \<not> stable_extension G S"
proof -
  let ?atom = "''A''"
  let ?G = "({?atom}, {(?atom, ?atom)})"
  let ?S = "{}"
  let ?A = "{?atom}"
  have "argumentation_framework ?G"
    by (simp add: argumentation_framework_def)
  have "admissible ?G ?S"
    by (simp add: admissible_def argumentation_framework_def conflict_free_def)
  have "(?atom,?atom) \<in> attack_relation ?G"
    by (simp add: attack_relation_def)
  have "attacks ?G ?atom ?atom"
    by (simp add: \<open>(''A'', ''A'') \<in> attack_relation ({''A''}, {(''A'', ''A'')})\<close> \<open>argumentation_framework ({''A''}, {(''A'', ''A'')})\<close> attacks_def)
  then have "\<not>conflict_free ?G ?A"
    by (simp add: conflict_free_def)
  have "\<forall>T. admissible ?G T \<and> ?S \<subseteq> T \<longrightarrow> ?S = T"
    by (metis \<open>\<not> conflict_free ({''A''}, {(''A'', ''A'')}) {''A''}\<close> admissible_def arguments_def prod.sel(1) subset_singletonD)
  have "preferred_extension ?G ?S"
    using \<open>\<forall>T. admissible ({''A''}, {(''A'', ''A'')}) T \<and> {} \<subseteq> T \<longrightarrow> {} = T\<close> \<open>admissible ({''A''}, {(''A'', ''A'')}) {}\<close> preferred_extension_def by blast
  moreover have "\<not>stable_extension ?G ?S"
    by (simp add: arguments_def stable_extension_def)
  then have "preferred_extension ?G ?S \<and> \<not> stable_extension ?G ?S"
    using calculation by blast
  ultimately show ?thesis
    by blast
qed


(* 
Definition 16. The characteristic function, denoted by FAF, of an argumentation
framework AF = (AR. attacks) is defined as follows:
F_AF:2^AR \<rightarrow> 2^AR,
F_AF(S) = {A | A is acceptable with respect to S}.
 *)
definition characteristic_function :: "(string set \<times> (string \<times> string) set) \<Rightarrow> string set \<Rightarrow> string set" where
  "characteristic_function G S = {a \<in> arguments G. acceptable G a S}"



(* 
Remark 17. As we always refer to an arbitrary but fixed argumentation framework AF, we often write F instead of FAF for short.
 *)
(* No formalization needed for remarks as they are explanatory in nature. *)
end