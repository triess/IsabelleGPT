theory temp

(* imports HOL.Set HOL.Metis HOL.Meson HOL.SMT HOL.Sledgehammer *)

imports Main

(*
TODOs:
- split up equations
 *)

begin

typedecl Natnums

axiomatization  I :: Natnums
  and succ :: "Natnums \<Rightarrow> Natnums"
  where
    Axiom_3 : "succ x \<noteq> I" and
    Axiom_4 : "succ x  = succ y \<longrightarrow> x = y" and
    Axiom_5 : "I \<in> M \<and> (\<forall>x. (x \<in> M \<longrightarrow> succ x \<in> M)) \<longrightarrow> (\<forall>x. x \<in> M)"

(* "Theorem 1: If
$$x \neq y$$
then
$$x' \neq y'.$$" *)
theorem Theorem_1: "\<forall>x y. (x \<noteq> y \<longrightarrow> succ x \<noteq> succ y)"
(*" Proof: Otherwise, we would have
$$x' = y'$$" *)
proof -
  {
    fix x y assume "succ x = succ y"
(* "and hence, by Axiom 4,
$$x = y.$$" *)
    from this Axiom_4 have "x = y" by auto
  }
(* Finish proof by deducing theorem statement. *)
  from this show "\<forall>x y. (x \<noteq> y \<longrightarrow> succ x \<noteq> succ y)" by auto
qed

(* "Theorem 2: $x' \neq x.$" *)
theorem Theorem_2: "\<forall>x. succ x \<noteq> x"
(* "Proof: Let $\mathfrak{M}$ be the set of all $x$ for which this holds true." *)
proof -
  define M where "M \<equiv> {x. succ x \<noteq> x}"
(* "I) By Axiom 1 and Axiom 3,
$$1' \neq 1;$$" *)
  {
    from Axiom_3 have "succ I \<noteq> I" by auto
(* "therefore $1$ belongs to $\mathfrak{M}$." *)
    from this have "I \<in> M" (* sledgehammer *) by (simp add: M_def)
  }
(* "II) If $x$ belongs to $\mathfrak{M}$," *)
  {
    fix x assume "x \<in> M"
    (* "then
$$x' \neq x,$$*)
    from this have "succ x \<noteq> x" (* sledgehammer *) using M_def by auto
(* "and hence by Theorem 1,
$$(x')' \neq x',$$" *)
    from this Theorem_1 have "succ (succ x) \<noteq> succ x" by auto
(* "so that $x'$ belongs to $\mathfrak{M}$." *)
    from this have "succ x \<in> M" (* sledgehammer *) using M_def by blast
  }
(* "By Axiom 5, $\mathfrak{M}$ therefore contains all the natural numbers," *)
  from Axiom_5 have "\<forall>x. x \<in> M" (* sledgehammer *)
    using \<open>I \<in> M\<close> \<open>\<And>x. x \<in> M \<Longrightarrow> succ x \<in> M\<close> by blast
(* "i.e.\ we have for each $x$ that
$$x' \neq x.$$"
This is identical to the theorem statement, so it finishes the proof.  *)
  from this show "\<forall>x. succ x \<noteq> x" (* sledgehammer *)
    using M_def by blast
qed

(* "Theorem 3: If
$$x \neq 1,$$
then there exists one (hence, by Axiom 4, exactly one) $u$ such that
$$x = u'.$$" *)
theorem Theorem_3: "\<forall>x. (x \<noteq> I \<longrightarrow> (\<exists>!u. x = succ u))"
(* "Proof: Let $\mathfrak{M}$ be the set consisting of the number $1$ and of all those $x$ for which there exists such a $u$." *)
proof -
define M where "M \<equiv> {I} \<union> {x. \<exists>u. x = succ u}"
(* "(For any such $x$, we have of necessity that
$$x \neq 1$$
by Axiom 3.)" *)
{
fix x::Natnums assume "x \<in> {x. \<exists>u. x = succ u}"
from this Axiom_3 have "x \<noteq> I" by auto
}
have "I \<in> M" by (simp add: M_def)
{
fix x::Natnums assume "x \<in> M"
define u where "u \<equiv> x"
have "succ x = succ u" by (simp add: u_def)
from this have "succ x \<in> M" using M_def by blast
}
(* "By Axiom 5, $\mathfrak{M}$ therefore contains all the natural numbers;" *)
from Axiom_5 have "\<forall>x. x \<in> M" (* sledgehammer *)
    using \<open>I \<in> M\<close> \<open>\<And>x. x \<in> M \<Longrightarrow> succ x \<in> M\<close> by blast
(* "thus for each
$$x \neq 1$$
there exists a $u$ such that
$$x = u'.$$" *)
(* This is identical to the theorem statement, so it finishes the proof. *)
{
  fix x::Natnums assume "x \<noteq> I"
  from \<open>\<forall>x. x \<in> M\<close> have "x \<in> M" by simp
  from this M_def have "\<exists>u. x = succ u"  (* sledgehammer *)
    using \<open>x \<noteq> I\<close> by blast
}
{
    fix x::Natnums assume "x \<noteq> I"
    from \<open>\<forall>x. x \<in> M\<close> have "x \<in> M" by simp
    from this M_def have "\<exists>u. x = succ u" (* sledgehammer *)
      using \<open>x \<noteq> I\<close> by blast
    then obtain u where "x = succ u" by auto
    moreover have "\<forall>v. x = succ v \<longrightarrow> v = u" (* sledgehammer *)
      using Axiom_4 calculation by blast
    ultimately have "\<exists>!u. x = succ u" by auto
  }
  thus "\<forall>x. x \<noteq> I \<longrightarrow> (\<exists>!u. x = succ u)" by auto
qed


(* "Theorem 4, and at the same time Definition 1: To every pair of numbers $x$, $y$, we may assign in exactly one way a natural number, called $x + y$ ($+$ to be read "plus"), such that

1) $x + 1 = x'$ for every $x$,

2) $x + y' = (x + y)'$ for every $x$ and every $y$."

In the statement of the theorem, we represent the assignment through a curried binary function $f$. The notation $x + y$ will be introduced in a separate formalization of Definition 1. *)
theorem Theorem_4: "\<exists>!f :: Natnums \<Rightarrow> Natnums \<Rightarrow> Natnums. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))"
(* The following statement only defines terminology that does not need to be formalized: "$x + y$ is called the sum of $x$ and $y$, or the number obtained by addition of $y$ to $x$." *)
(* "Proof: A) First we will show that for each fixed $x$ there is at most one possibility of defining $x + y$ for all $y$ in such a way that
$$x + 1 = x'$$
and
$$x + y' = (x + y)' \textnormal{for every $y$.}$$"
We formalize this statement by saying that for each fixed $x$, any two functions $a$, $b$ that assign $y$ to $x + y$ in the specified way are actually identical.*)
proof -
  have "\<forall>x. \<forall>a b :: Natnums \<Rightarrow> Natnums. (a I = succ x \<and> (\<forall>y. a(succ y) = succ(a y)) \<and> b I = succ x \<and> (\<forall>y. b(succ y) = succ(b y)) \<longrightarrow> a = b)"
  proof -
    {
(* The fact that $x$ was called "fixed" means that we need to fix $x$ at the beginning of the formalization of the subproof. *)
      fix x::Natnums
(* "Let $a_y$ and $b_y$ be defined for all $y$ and be such that
$$a_1 = x', b_1 = x',$$
$$a_{y'} = (a_y)', b_{y'} = (by)' \textnormal{for every y}.$$" *)
      fix a b :: "Natnums \<Rightarrow> Natnums" assume "a I = succ x \<and> (\<forall>y. a(succ y) = succ(a y)) \<and> b I = succ x \<and> (\<forall>y. b(succ y) = succ(b y))"
(* "Let $\mathfrak{M}$ be the set of all $y$ for which
$$a_y = b_y.$$" *)
      define M where "M \<equiv> {y. a y = b y}"
(* "I) $a_1 = x' = b_1$;"
We need to split the chained equation into its parts: *)
      {
        have eq4_1 : "a I = succ x" (* sledgehammer *)
          by (simp add: \<open>a I = succ x \<and> (\<forall>y. a (succ y) = succ (a y)) \<and> b I = succ x \<and> (\<forall>y. b (succ y) = succ (b y))\<close>)
        have eq4_2 : "succ x = b I" (* sledgehammer *)
          by (simp add: \<open>a I = succ x \<and> (\<forall>y. a (succ y) = succ (a y)) \<and> b I = succ x \<and> (\<forall>y. b (succ y) = succ (b y))\<close>)
(* We need to derive the relationship between the first and the last term in the chained equation: *)
        from eq4_1 eq4_2 have "a I =  b I" by auto
(* "hence $1$ belongs to $\mathfrak{M}$." *)
        have "I \<in> M" (* sledgehammer *)
          by (simp add: M_def \<open>a I = succ x \<and> (\<forall>y. a (succ y) = succ (a y)) \<and> b I = succ x \<and> (\<forall>y. b (succ y) = succ (b y))\<close>)
      }
(* "II) If $y$ belongs to $\mathfrak{M}$," *)
      {
        fix y::Natnums assume "y \<in> M"
(* "then
$$a_y = b_y,$$" *)
        from this have "a y = b y" (* sledgehammer *) using M_def by blast
(* "hence by Axiom 2,
$$(a_y)' = (b_y)',$$" *)
        from this have "succ (a y) = succ (b y)" by auto
(* "therefore
$$a_{y'} = (a_y)' = (b_y)' = b_{y'},$$"
We need to split the chained equation into its parts: *)
        have eq4_3 : "a (succ y) = succ (a y)" (* sledgehammer *)
          by (simp add: \<open>a I = succ x \<and> (\<forall>y. a (succ y) = succ (a y)) \<and> b I = succ x \<and> (\<forall>y. b (succ y) = succ (b y))\<close>)
        have eq4_4 : "succ (a y) = succ (b y)" (* sledgehammer *)
          by (simp add: \<open>succ (a y) = succ (b y)\<close>)
        have eq4_5 : "succ (b y) = b (succ y)" (* sledgehammer *)
          by (simp add: \<open>a I = succ x \<and> (\<forall>y. a (succ y) = succ (a y)) \<and> b I = succ x \<and> (\<forall>y. b (succ y) = succ (b y))\<close>)
(* We need to derive the relationship between the first and the last term in the chained equation: *)
        from eq4_3 eq4_4 eq4_5 have"a (succ y) = b (succ y)" by auto
(* "so that $y'$ belongs to $\mathfrak{M}$." *)
        from this have "succ y \<in> M" (* sledgehammer *) by (simp add: M_def)
      }
(* "Hence $\mathfrak{M}$ is the set of all natural numbers;" *)
      have "\<forall>x. x \<in> M" (* sledgehammer *)
        using Axiom_5 \<open>I \<in> M\<close> \<open>\<And>y. y \<in> M \<Longrightarrow> succ y \<in> M\<close> by blast
(* "i.e. for every $y$ we have
$$a_y = b_y.$$" *)
      from this have "\<forall>y. a y = b y" (* sledgehammer *) using M_def by blast
    }
(* Finish subproof by deducing statement announced to be proven. *)
    from this show "\<forall>x. \<forall>a b :: Natnums \<Rightarrow> Natnums. (a I = succ x \<and> (\<forall>y. a(succ y) = succ(a y)) \<and> b I = succ x \<and> (\<forall>y. b(succ y) = succ(b y)) \<longrightarrow> a = b)" by auto
  qed
(* For the overall statement of Theorem 4, we need to move the quantifier "\<forall>x" inside: *)
  have "\<forall>a b :: Natnums \<Rightarrow> Natnums \<Rightarrow> Natnums. ((\<forall>x. a x I = succ x) \<and> (\<forall>x y. a x (succ y) = succ(a x y)) \<and> (\<forall>x. b x I = succ x) \<and> (\<forall>x y. b x (succ y) = succ(a x y)) \<longrightarrow> a = b)" (* sledgehammer *)
  (* begin details not in source *)
  proof -
  {
    fix a b assume "(\<forall>x. a x I = succ x) \<and> (\<forall>x y. a x (succ y) = succ(a x y)) \<and> (\<forall>x. b x I = succ x) \<and> (\<forall>x y. b x (succ y) = succ(a x y))"
    {
      fix x::Natnums
      have "a x I = succ x \<and> (\<forall>y. a x (succ y) = succ(a x y)) \<and> b x I = succ x \<and> (\<forall>y. b x (succ y) = succ(a x y))" (* sledgehammer *)
        by (simp add: \<open>(\<forall>x. a x I = succ x) \<and> (\<forall>x y. a x (succ y) = succ (a x y)) \<and> (\<forall>x. b x I = succ x) \<and> (\<forall>x y. b x (succ y) = succ (a x y))\<close>)
      have "\<forall>a b :: Natnums \<Rightarrow> Natnums. (a I = succ x \<and> (\<forall>y. a(succ y) = succ(a y)) \<and> b I = succ x \<and> (\<forall>y. b(succ y) = succ(b y)) \<longrightarrow> a = b)" (* sledgehammer *)
        by (simp add: \<open>\<forall>x a b. a I = succ x \<and> (\<forall>y. a (succ y) = succ (a y)) \<and> b I = succ x \<and> (\<forall>y. b (succ y) = succ (b y)) \<longrightarrow> a = b\<close>)
      from this have "a x I = succ x \<and> (\<forall>y. a x (succ y) = succ(a x y)) \<and> b x I = succ x \<and> (\<forall>y. b x (succ y) = succ(a x y)) \<longrightarrow> a x = b x" (* sledgehammer *)
        by (metis Theorem_3)
      from this have "a x = b x" (* sledgehammer *)
        using \<open>a x I = succ x \<and> (\<forall>y. a x (succ y) = succ (a x y)) \<and> b x I = succ x \<and> (\<forall>y. b x (succ y) = succ (a x y))\<close> by blast
    }
    from this have "a = b" by auto
  }
  from this show "\<forall>a b :: Natnums \<Rightarrow> Natnums \<Rightarrow> Natnums. ((\<forall>x. a x I = succ x) \<and> (\<forall>x y. a x (succ y) = succ(a x y)) \<and> (\<forall>x. b x I = succ x) \<and> (\<forall>x y. b x (succ y) = succ(a x y)) \<longrightarrow> a = b)" by auto
  qed
  (* end details not in source *)
  have "\<forall>x. \<exists>f :: Natnums \<Rightarrow> Natnums. (f I = succ x  \<and> (\<forall>y. f(succ y) = succ(f y)))"
  proof -
    define M where "M \<equiv> {x. \<exists>f :: Natnums \<Rightarrow> Natnums. (f I = succ x  \<and> (\<forall>y. f(succ y) = succ(f y)))}"
    {
      define x where "x \<equiv> I"
      define f where "f \<equiv> \<lambda>y. succ y"
      have "f I = succ x  \<and> (\<forall>y. f(succ y) = succ(f y))"
      proof -
        have "f I = succ I \<and> succ I = succ x" (* sledgehammer *)
          by (simp add: f_def x_def)
        have "\<forall>y. (f(succ y) = succ(succ y) \<and> succ(succ y) = succ(f y))" (* sledgehammer *)
          by (simp add: f_def)
        show "f(I) = succ x  \<and> (\<forall>y. f(succ y) = succ(f y))" (* sledgehammer *)
          by (simp add: \<open>\<forall>y. f (succ y) = succ (succ y) \<and> succ (succ y) = succ (f y)\<close> \<open>f I = succ I \<and> succ I = succ x\<close>)
      qed
      have "I \<in> M" (* sledgehammer *) using M_def by blast
    }
    {
      fix x::Natnums assume  "x \<in> M"
      from this obtain f where "(f I = succ x  \<and> (\<forall>y. f(succ y) = succ(f y)))" (* sledgehammer *)
        using M_def by blast
      define f' where "f' \<equiv> \<lambda>y. succ (f y)"
      have "f' I = succ (succ x)  \<and> (\<forall>y. f'(succ y) = succ(f' y))"
      proof -
        have "f' I = succ (f I) \<and> succ (f I) = succ (succ x)" (* sledgehammer *)
          by (simp add: \<open>f I = succ x \<and> (\<forall>y. f (succ y) = succ (f y))\<close> f'_def)
        have "f' (succ y) = succ (f (succ y)) \<and> succ (f (succ y)) = succ (succ (f y)) \<and> succ (succ (f y)) = succ(f' y)" (* sledgehammer *)
          by (simp add: \<open>f I = succ x \<and> (\<forall>y. f (succ y) = succ (f y))\<close> f'_def)
        show "f' I = succ (succ x)  \<and> (\<forall>y. f'(succ y) = succ(f' y))" (* sledgehammer *)
          by (simp add: \<open>f I = succ x \<and> (\<forall>y. f (succ y) = succ (f y))\<close> f'_def)
      qed
      have "succ x \<in> M" (* sledgehammer *)
        using M_def \<open>f' I = succ (succ x) \<and> (\<forall>y. f' (succ y) = succ (f' y))\<close> by blast
    }
    have "\<forall>x. x \<in> M" (* sledgehammer *)
      using Axiom_5 \<open>I \<in> M\<close> \<open>\<And>x. x \<in> M \<Longrightarrow> succ x \<in> M\<close> by blast
    from this show "\<forall>x. \<exists>f :: Natnums \<Rightarrow> Natnums. (f I = succ x  \<and> (\<forall>y. f(succ y) = succ(f y)))" (* sledgehammer *)
      using M_def by blast
  qed
  have "\<exists>f :: Natnums \<Rightarrow> Natnums \<Rightarrow> Natnums. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))" (* sledgehammer *)
    by (meson \<open>\<forall>x. \<exists>f. f I = succ x \<and> (\<forall>y. f (succ y) = succ (f y))\<close>)
  from this show "\<exists>!f :: Natnums \<Rightarrow> Natnums \<Rightarrow> Natnums. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))" (* sledgehammer *)
    using \<open>\<forall>x a b. a I = succ x \<and> (\<forall>y. a (succ y) = succ (a y)) \<and> b I = succ x \<and> (\<forall>y. b (succ y) = succ (b y)) \<longrightarrow> a = b\<close> by auto
qed

(* The following definition formalizes the words "and at the same time Definition 1" before the statement of Theorem 4. *)
definition plus (infixl "\<^bold>+" 65) where "plus \<equiv> THE f. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))"

(* begin details not in source *)

lemma L1: "(\<forall>x. plus x I = succ x)  \<and> (\<forall>x y. plus x (succ y) = succ(plus x y))"
proof -
  from Theorem_4 obtain f where "((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))" by auto
  define P where "P \<equiv> (\<lambda>f. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y))))"
  from this P_def have theI_assumption_1 : "P f"
    using \<open>(\<forall>x. f x I = succ x) \<and> (\<forall>x y. f x (succ y) = succ (f x y))\<close> by fastforce
  from this Theorem_4 have "\<And>g. P g \<Longrightarrow> g = f"
    using P_def by blast
  from theI theI_assumption_1 this have "P (THE f. P f)"
    by metis
  from this P_def have "(\<lambda>f. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))) (THE f. (\<lambda>f. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))) f)" by auto
  from this plus_def have "(\<lambda>f. ((\<forall>x. f x I = succ x)  \<and> (\<forall>x y. f x (succ y) = succ(f x y)))) plus" by auto
  from this show "(\<forall>x. plus x I = succ x)  \<and> (\<forall>x y. plus x (succ y) = succ(plus x y))" by auto
qed

(* end details not in source *)

(* "Theorem 5 (Associative Law of Addition):
$$(x + y) + z = x + (y + z).$$" *)
theorem Theorem_5: "\<forall>x y z. (x\<^bold>+y)\<^bold>+z = x\<^bold>+(y\<^bold>+z)"
(* "Proof: Fix $x$ and $y$, and denote by $\mathfrak{M}$ the set of all $z$ for which the assertion of the theorem holds." *)
proof -
{
fix x y::Natnums
define M where "M \<equiv> {z. (x \<^bold>+ y) \<^bold>+ z = x \<^bold>+ (y \<^bold>+ z)}"
(* "I) $$(x + y) + 1 = (x + y)' = x + y' = x + (y + 1);$$
thus $1$ belongs to $\mathfrak{M}$." *)
    {
      have eq5_1 : "(x\<^bold>+y)\<^bold>+I = succ (x\<^bold>+y)" (* sledgehammer *) using L1 by auto
      have eq5_2 : "succ (x\<^bold>+y) = x \<^bold>+ (succ y)" (* sledgehammer *) using L1 by auto
      have eq5_3 :"x \<^bold>+ (succ y) = x\<^bold>+(y\<^bold>+I)" (* sledgehammer *) by (simp add: L1)
      from eq5_1 eq5_2 eq5_3 have "(x\<^bold>+y)\<^bold>+I = x\<^bold>+(y\<^bold>+I)" by auto
      from this have "I \<in> M" by (simp add: M_def)
      from this have "I \<in> M" (* sledgehammer *) using M_def by auto
    }
(* "II) Let $z$ belong to $\mathfrak{M}$." *)
{
fix z::Natnums assume "z \<in> M"
(* "Then
$$(x + y) + z = x + (y + z),$$
hence
$$(x + y) + z' = ((x + y) + z)' = (x + (y + z))' = x + (y + z)' = x + (y + z'),$$
so that $z'$ belongs to $\mathfrak{M}$." *)
have eq5_4: "(x\<^bold>+y)\<^bold>+z = x\<^bold>+(y\<^bold>+z)" (* sledgehammer *)
  using M_def \<open>z \<in> M\<close> by auto
have eq5_5: "(x\<^bold>+y)\<^bold>+(succ z) = succ ((x\<^bold>+y)\<^bold>+z)" (* sledgehammer *) using L1 by auto
have eq5_6: "succ ((x\<^bold>+y)\<^bold>+z) = succ (x\<^bold>+(y\<^bold>+z))" using eq5_4 by simp
have eq5_7 :"succ (x\<^bold>+(y\<^bold>+z)) = x\<^bold>+(succ (y\<^bold>+z))" (* sledgehammer *) using L1 by auto
have eq5_8 :"x\<^bold>+(succ (y\<^bold>+z)) = x\<^bold>+(y\<^bold>+(succ z))" (* sledgehammer *) by (simp add: L1)
from eq5_5 eq5_6 eq5_7 eq5_8 have "(x\<^bold>+y)\<^bold>+(succ z) = x\<^bold>+(y\<^bold>+(succ z))" by auto
from this have "succ z \<in> M" by (simp add: M_def)
}
from this have "\<forall>z. z \<in> M"  (* sledgehammer *)
  using Axiom_5 \<open>I \<in> M\<close> by blast
  {
    fix z have "z \<in> M" using \<open>\<forall>z. z \<in> M\<close> by auto
    then have "(x\<^bold>+y)\<^bold>+z = x\<^bold>+(y\<^bold>+z)" using M_def by auto
  }
  from \<open>\<forall>z. z \<in> M\<close> M_def have "\<forall>z. (x \<^bold>+ y) \<^bold>+ z = x \<^bold>+ (y \<^bold>+ z)" by auto
}
thus "\<forall>x y z. (x \<^bold>+ y) \<^bold>+ z = x \<^bold>+ (y \<^bold>+ z)" by auto
qed

(* "Theorem 6 (Commutative Law of Addition) :
$$x + y = y + x.$$" *)
theorem Theorem_6: "\<forall>x y. x \<^bold>+ y = y \<^bold>+ x"
proof -
(*Proof: Fix y, and let M be the set of all x for which the assertion holds. *)
{
  fix y::Natnums
  define M where "M \<equiv> {x. x \<^bold>+ y = y \<^bold>+ x}"
(*I) We have \n y+1=y' \n and furthermore by the construction in the proof of Theorem 4, \n 1+y=y' \n so that \n 1+y=y+1 \n and 1 belongs to M. *)
{
    have eq6_1: "y \<^bold>+ I = succ y" by (simp add: L1)
     define N where "N \<equiv> {y. I\<^bold>+y =y\<^bold>+I}"

    have "I \<in> N"
      by (simp add: N_def)

    {
      fix z::Natnums assume "z \<in> N"

      have "succ z \<in> N"
        using L1 N_def \<open>z \<in> N\<close> by force
    }

    from this have "\<forall>z. z \<in> N"
      using Axiom_5 \<open>I \<in> N\<close> by blast

    have eq6_2: "I\<^bold>+y = succ y"
      using N_def \<open>\<forall>z. z \<in> N\<close> eq6_1 by auto

    have eq6_3: "I \<^bold>+ y = y\<^bold>+I"
      by (simp add: eq6_1 eq6_2)

    from eq6_1 eq6_2 eq6_3 have "I \<in> M"
      using M_def by blast
  }
(*II) If x belongs to M, then \n x+y=y+x \n therefore \n (x+y)'=(y+x)'=y+x'. *)
{
    fix x::Natnums assume "x \<in> M"
    from this M_def have "x \<^bold>+ y = y \<^bold>+ x" by auto
    then have "succ (x \<^bold>+ y) = succ (y \<^bold>+ x)" by auto
    moreover have "succ (y \<^bold>+ x) = y \<^bold>+ succ x" by (simp add: L1)
  }
(*By the construction in the proof of Theorem 4, we have \n x'+y=(x+y)', \n hence \n x'+y=y+x' \n so that x' belongs to M *)
{
    have eq6_4: "succ x \<^bold>+ y = succ (x \<^bold>+ y)"
    by (metis (mono_tags, lifting) L1 M_def Theorem_5 \<open>I \<in> M\<close> mem_Collect_eq)
    from this have "succ x \<^bold>+ y = y \<^bold>+ succ x"
      by (smt (z3) Axiom_5 L1 M_def Theorem_5 \<open>I \<in> M\<close> mem_Collect_eq)
    from this have "succ x \<in> M" by (simp add: M_def)
  }
from Axiom_5 have "\<forall>x. x \<in> M" using \<open>I \<in> M\<close>
  by (smt (verit) L1 M_def Theorem_5 mem_Collect_eq)
  from this M_def have "\<forall>x. x \<^bold>+ y = y \<^bold>+ x" by auto
}
  thus "\<forall>x y. x \<^bold>+y=y \<^bold>+x"
    by simp
qed
(* Theorem 7: y \<noteq> x + y.
Proof: Fix x, and let \<MM> be the set of all y for which the assertion holds.
I) 1 \<noteq> x',
1 \<noteq> x + 1;
1 belongs to \<MM>.
II) If y belongs to \<MM>, then
y \<noteq> x + y,
hence
y' \<noteq> (x + y)',
y' \<noteq> x + y'.
so that y' belongs to \<MM>.
Therefore the assertion holds for all y. *)
theorem Theorem_7: "\<forall>x y. y \<noteq> x \<^bold>+ y"
proof -
  {
    fix x::Natnums
    define M where "M \<equiv> {y. y \<noteq> x \<^bold>+ y}"
    {
      have "I \<noteq> succ x"
        by (metis Axiom_3)
      moreover have "I \<noteq> x \<^bold>+ I"
      using L1 calculation by presburger
      ultimately have "I \<in> M" by (simp add: M_def)
    }
    {
      fix y::Natnums assume "y \<in> M"
      from this have "y \<noteq> x \<^bold>+ y" by (simp add: M_def)
      hence "succ y \<noteq> succ (x \<^bold>+ y)"
        using Theorem_1 by presburger
      moreover have "succ (x \<^bold>+ y) = x \<^bold>+ succ y" by (simp add: L1)
      ultimately have "succ y \<noteq> x \<^bold>+ succ y" by auto
      hence "succ y \<in> M" by (simp add: M_def)
    }
    from Axiom_5 have "\<forall>y. y \<in> M" using \<open>I \<in> M\<close> \<open>\<And>y. y \<in> M \<Longrightarrow> succ y \<in> M\<close> by blast
    from this M_def have "\<forall>y. y \<noteq> x \<^bold>+ y" by auto
  }
  thus "\<forall>x y. y \<noteq> x \<^bold>+ y" by auto
qed
(* Theorem 8: Ify \<noteq> z
then
x + y \<noteq> x + z.
Proof: Consider a fixed y and a fixed z such that
y \<noteq> z,
and let \<MM> be the set of all x for which
x + y \<noteq> x + z.
I) y' \<noteq> z',
1 + y \<noteq> 1 + z;
hence 1 belongs to \<MM>.
II) If x belongs to \<MM>, then
x + y \<noteq> x + z,
hence
(x + y)' \<noteq> (x + z)',
x' + y \<noteq> x' + z,
so that x' belongs to \<MM>.
Therefore the assertion holds always.

 *)
(* Theorem 8: If
y \<noteq> z
then
x + y \<noteq> x + z.
Proof: Consider a fixed y and a fixed z such that
y \<noteq> z,
and let \<MM> be the set of all x for which
x + y \<noteq> x + z.
I) y' \<noteq> z',
1 + y \<noteq> 1 + z;
hence 1 belongs to \<MM>.
II) If x belongs to \<MM>, then
x + y \<noteq> x + z,
hence
(x + y)' \<noteq> (x + z)',
x' + y \<noteq> x' + z,
so that x' belongs to \<MM>.
Therefore the assertion holds always.

 *)
theorem Theorem_8: "\<forall>x y z. y \<noteq> z \<longrightarrow> x \<^bold>+ y \<noteq> x \<^bold>+ z"
proof -
  {
    fix y z::Natnums assume "y \<noteq> z"
    define M where "M \<equiv> {x. x \<^bold>+ y \<noteq> x \<^bold>+ z}"
    {
      have "succ y \<noteq> succ z" (*manual sledge*)
        using Axiom_4 \<open>y \<noteq> z\<close> by blast
      moreover have "I \<^bold>+ y \<noteq> I \<^bold>+ z"
        by (metis L1 Theorem_6 calculation)
      ultimately have "I \<in> M" by (simp add: M_def)
    }
    {
      fix x::Natnums assume "x \<in> M"
      from this have "x \<^bold>+ y \<noteq> x \<^bold>+ z" by (simp add: M_def)
      hence "succ (x \<^bold>+ y) \<noteq> succ (x \<^bold>+ z)"
        using Axiom_4 by blast
      moreover have "succ (x \<^bold>+ y) = x \<^bold>+ succ y" by (simp add: L1)
      moreover have "succ (x \<^bold>+ z) = x \<^bold>+ succ z" by (simp add: L1)
      ultimately have "x \<^bold>+ succ y \<noteq> x \<^bold>+ succ z" by auto
      hence "succ x \<^bold>+ y \<noteq> succ x \<^bold>+ z"
        by (simp add: L1 Theorem_6)
      hence "succ x \<in> M" by (simp add: M_def)
    }
    from Axiom_5 have "\<forall>x. x \<in> M" using \<open>I \<in> M\<close> \<open>\<And>x. x \<in> M \<Longrightarrow> succ x \<in> M\<close> by blast
    from this M_def have "\<forall>x. x \<^bold>+ y \<noteq> x \<^bold>+ z" by auto
  }
  thus "\<forall>x y z. y \<noteq> z \<longrightarrow> x \<^bold>+ y \<noteq> x \<^bold>+ z" by auto
qed
(* Theorem 9: For given x and y, exactly one of the following
must be the case:
1) x = y.
2) There exists a u (exactly one, by Theorem 8) such that
x = y + u.
3) There exists a v (exactly one, by Theorem 8) such that
y = x + v.
Proof: A) By Theorem 7, cases 1) and 2) are incompatible.
Similarly, 1) and 3) are incompatible. The incompatibility of 2)
and 3) also follows from Theorem 7; for otherwise, we would have
x = y + u = (x + v) + u = x + (v + u) = (v + u) + x.
Therefore we can have at most one of the cases 1), 2) and 3).
B) Let x be fixed, and let \<MM> be the set of all y for which one
(hence by A), exactly one) of the cases 1), 2) and 3) obtains.
I) For y = 1, we have by Theorem 3 that either
x = 1 = y (case 1))
or
x = u' = 1 + u = y + u (case 2)).
Hence 1 belongs to \<MM>.
II) Let y belong to \<MM>. Then
either (case 1) for y)
x = y
hence
y' = y + 1 = x + 1 (case 3) for y');
or (case 2) for y)
x = y + u,
hence if
u = 1,
then
x = y + 1 = y' (case 1) for y');
but if
u \<noteq> 1,
then, by Theorem 3,
u = w' = 1 + w,
x = y + (1 + w) = (y + 1) + w = y' + w (case 2) for y');
or (case 3) for y)
y= x + v,
hence
y' = (x + v)' = x + v' (case 3) for y').
In any case, y' belongs to \<MM>.
Therefore we always have one of the cases 1),2) and 3).

 *)
theorem Theorem_9: "\<forall>x y. (x = y) \<or> (\<exists>!u. x = y \<^bold>+ u) \<or> (\<exists>!v. y = x \<^bold>+ v)"
proof -
  {
    fix x::Natnums
    define M where "M \<equiv> {y. (x = y) \<or> (\<exists>!u. x = y \<^bold>+ u) \<or> (\<exists>!v. y = x \<^bold>+ v)}"
    {
      from Theorem_3 have "x = I \<or> (\<exists>!u. x = I \<^bold>+ u)"
        by (metis L1 Theorem_6)
      hence "I \<in> M"
        using M_def by blast
    }
    {
      fix y::Natnums assume "y \<in> M"
      from this M_def have "(x = y) \<or> (\<exists>!u. x = y \<^bold>+ u) \<or> (\<exists>!v. y = x \<^bold>+ v)" by auto
      {
        assume "x = y"
        hence "succ x = succ y" by simp
        hence "succ y = x \<^bold>+ I" by (simp add: L1)
        hence "succ y = y \<^bold>+ I" by (simp add: \<open>x = y\<close>)
        hence "succ y \<in> M"
          using M_def Theorem_8 \<open>x = y\<close> by auto
      }
      moreover
      {
        assume "\<exists>!u. x = y \<^bold>+ u"
        then obtain u where "x = y \<^bold>+ u" and "\<forall>v. x = y \<^bold>+ v \<longrightarrow> v = u" by auto
        hence "succ x = succ (y \<^bold>+ u)" by simp
        hence "succ x = y \<^bold>+ succ u" by (simp add: L1)
        hence "succ y = y \<^bold>+ succ u" sorry
        hence "succ y \<in> M"
          using Axiom_4 \<open>succ x = y \<^bold>+ succ u\<close> calculation by presburger
      }
      moreover
      {
        assume "\<exists>!v. y = x \<^bold>+ v"
        then obtain v where "y = x \<^bold>+ v" and "\<forall>w. y = x \<^bold>+ w \<longrightarrow> w = v" by auto
        hence "succ y = succ (x \<^bold>+ v)" by simp
        hence "succ y = x \<^bold>+ succ v" by (simp add: L1)
        hence "succ y \<in> M"
          using M_def Theorem_8 by auto
      }
      ultimately have "succ y \<in> M"
        using \<open>x = y \<or> (\<exists>!u. x = y \<^bold>+ u) \<or> (\<exists>!v. y = x \<^bold>+ v)\<close> by fastforce
    }
    from Axiom_5 have "\<forall>y. y \<in> M" using \<open>I \<in> M\<close> \<open>\<And>y. y \<in> M \<Longrightarrow> succ y \<in> M\<close> by blast
    from this M_def have "\<forall>y. (x = y) \<or> (\<exists>!u. x = y \<^bold>+ u) \<or> (\<exists>!v. y = x \<^bold>+ v)" by auto
  }
  thus "\<forall>x y. (x = y) \<or> (\<exists>!u. x = y \<^bold>+ u) \<or> (\<exists>!v. y = x \<^bold>+ v)" by auto
qed
(* Definition 2: If
x = y + u
then
x > y.
(> to be read "is greater than.")

 *)
definition greater_than (infix "\<^bold>>" 50) where
"x \<^bold>> y \<equiv> (\<exists>u. x = y \<^bold>+ u \<and> u \<noteq> I)"
(* Definition 3: If
y = x + v
then
x < y.
(< to be read "is less than.")

 *)
definition less_than (infix "\<^bold><" 50) where
"x \<^bold>< y \<equiv> (\<exists>v. y = x \<^bold>+ v \<and> v \<noteq> I)"
(* Theorem 10: For any given x, y, we have exactly one of the cases
x = y, x > y, x < y.
Proof: Theorem 9, Definition 2 and Definition 3.

 *)
theorem Theorem_10: "\<forall>x y. (x = y) \<or> (x \<^bold>> y) \<or> (x \<^bold>< y)"
proof -
  from Theorem_9 have "\<forall>x y. (x = y) \<or> (\<exists>!u. x = y \<^bold>+ u) \<or> (\<exists>!v. y = x \<^bold>+ v)" by simp
  thus "\<forall>x y. (x = y) \<or> (x \<^bold>> y) \<or> (x \<^bold>< y)"
    unfolding greater_than_def less_than_def sorry
qed
(* Theorem 11: If
x > y
then
y < x.
Proof: Each of these means that
x = y + u
for some suitable u.

 *)
theorem Theorem_11: "\<forall>x y. (x \<^bold>> y) \<longrightarrow> (y \<^bold>< x)"
proof -
  {
    fix x y assume "x \<^bold>> y"
    then have "\<exists>u. x = y \<^bold>+ u \<and> u \<noteq> I"
      unfolding greater_than_def by simp
    then obtain u where "x = y \<^bold>+ u" and "u \<noteq> I" by auto
    hence "y = x \<^bold>+ u"
      by (metis L1 less_than_def Theorem_10 Theorem_7 Theorem_8 greater_than_def)
    hence "y \<^bold>< x"
      unfolding less_than_def using \<open>u \<noteq> I\<close>
      using \<open>\<exists>u. x = y \<^bold>+ u \<and> u \<noteq> I\<close> by blast
  }
  thus "\<forall>x y. (x \<^bold>> y) \<longrightarrow> (y \<^bold>< x)" by auto
qed
(* Theorem 12: If
x < y
then
y > x.
Proof: Each of these means that
y = x + v
for some suitable v.

 *)
theorem Theorem_12: "\<forall>x y. (x \<^bold>< y) \<longrightarrow> (y \<^bold>> x)"
proof -
  {
    fix x y assume "x \<^bold>< y"
    then have "\<exists>v. y = x \<^bold>+ v \<and> v \<noteq> I"
      unfolding less_than_def by simp
    then obtain v where "y = x \<^bold>+ v" and "v \<noteq> I" by auto
    hence "y \<^bold>> x"
      unfolding greater_than_def using \<open>v \<noteq> I\<close> by auto
  }
  thus "\<forall>x y. (x \<^bold>< y) \<longrightarrow> (y \<^bold>> x)" by auto
qed
(* Definition 4: x \<ge> y
means
x > y or x = y.
(\<ge> to be read "is greater than or equal to.")

 *)
definition geq (infix "\<^bold>\<ge>" 50) where
"x \<^bold>\<ge> y \<equiv> (x \<^bold>> y) \<or> (x = y)"
(* Definition 5: x \<le> y
means
x < y or x = y.
(\<le> to be read "is less than or equal to.")

 *)
definition leq (infix "\<^bold>\<le>" 50) where
"x \<^bold>\<le> y \<equiv> (x \<^bold>< y) \<or> (x = y)"
(* Theorem 13: If
x \<ge> y
then
y \<le> x.
Proof: Theorem 11.

 *)
theorem Theorem_13: "\<forall>x y. (x \<^bold>\<ge> y) \<longrightarrow> (y \<^bold>\<le> x)"
proof -
  {
    fix x y assume "x \<^bold>\<ge> y"
    then have "(x \<^bold>> y) \<or> (x = y)"
      unfolding geq_def by simp
    then have "y \<^bold>\<le> x"
    proof
      assume "x \<^bold>> y"
      then have "y \<^bold>< x"
        using Theorem_11 by simp
      then show "y \<^bold>\<le> x"
        unfolding leq_def by simp
    next
      assume "x = y"
      then show "y \<^bold>\<le> x"
        unfolding leq_def by simp
    qed
  }
  thus "\<forall>x y. (x \<^bold>\<ge> y) \<longrightarrow> (y \<^bold>\<le> x)" by auto
qed
(* Theorem 14: If
x \<le> y
then
y \<ge> x.
Proof: Theorem 12.

 *)
theorem Theorem_14: "\<forall>x y. (x \<^bold>\<le> y) \<longrightarrow> (y \<^bold>\<ge> x)"
proof -
  {
    fix x y assume "x \<^bold>\<le> y"
    then have "(x \<^bold>< y) \<or> (x = y)"
      unfolding leq_def by simp
    then have "y \<^bold>\<ge> x"
    proof
      assume "x \<^bold>< y"
      then have "y \<^bold>> x"
        using Theorem_12 by simp
      then show "y \<^bold>\<ge> x"
        unfolding geq_def by simp
    next
      assume "x = y"
      then show "y \<^bold>\<ge> x"
        unfolding geq_def by simp
    qed
  }
  thus "\<forall>x y. (x \<^bold>\<le> y) \<longrightarrow> (y \<^bold>\<ge> x)" by auto
qed
(* Theorem 15 (Transitivity of Ordering): If
x < y, y < z,
then
x < z.
Preliminary Remark: Thus if
x > y, y > z,
then
x > z,
since
z < y, y < x,
z < x;
but in what follows I will not even bother to write down such
statements, which are obtained trivially by simply reading the
formulas backwards.
Proof: With suitable v, w, we have
y = x + v, z = y + w,
hence
z = (x + v) + w = x + (v + w),
x < z.

 *)
theorem Theorem_15: "\<forall>x y z. (x \<^bold>< y) \<and> (y \<^bold>< z) \<longrightarrow> (x \<^bold>< z)"
proof -
  {
    fix x y z assume "(x \<^bold>< y) \<and> (y \<^bold>< z)"
    then have "x \<^bold>< y" and "y \<^bold>< z" by simp+
    from `x \<^bold>< y` obtain v where "y = x \<^bold>+ v" and "v \<noteq> I"
      unfolding less_than_def by auto
    from `y \<^bold>< z` obtain w where "z = y \<^bold>+ w" and "w \<noteq> I"
      unfolding less_than_def by auto
    have "z = (x \<^bold>+ v) \<^bold>+ w"
      using `z = y \<^bold>+ w` `y = x \<^bold>+ v` by simp
    also have "... = x \<^bold>+ (v \<^bold>+ w)"
      using Theorem_5 by simp
    finally have "z = x \<^bold>+ (v \<^bold>+ w)" .
    then have "x \<^bold>< z"
      using `v \<noteq> I` `w \<noteq> I` Theorem_1
      unfolding less_than_def
      by (metis L1 Theorem_3 Theorem_7)
  }
  thus "\<forall>x y z. (x \<^bold>< y) \<and> (y \<^bold>< z) \<longrightarrow> (x \<^bold>< z)" by fastforce
qed
end