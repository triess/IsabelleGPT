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
theorem Theorem_9:
  "\<forall>x y. \<exists>!c::nat. (c = 1 \<and> x = y) \<or> (c = 2 \<and> (\<exists>!u. x = y \<^bold>+ u)) \<or> (c = 3 \<and> (\<exists>!v. y = x \<^bold>+ v))"
proof -
  {
    fix x y::Natnums
    have "\<not>((x = y) \<and> (\<exists>!u. x = y \<^bold>+ u))"
    proof
      assume "x = y" and "\<exists>!u. x = y \<^bold>+ u"
      then obtain u where "x = y \<^bold>+ u" by auto
      hence "y = y \<^bold>+ u" using \<open>x = y\<close> by auto
      hence "u = I" using Theorem_7
        using Theorem_6 by fastforce
      hence "x = y \<^bold>+ I" using \<open>x = y \<^bold>+ u\<close> by auto
      hence "x = succ y" using L1 by auto
      hence "x \<noteq> y"
        by (simp add: Theorem_2)
      thus False using \<open>x = y\<close> by auto
    qed
    moreover have "\<not>((x = y) \<and> (\<exists>!v. y = x \<^bold>+ v))"
    proof
      assume "x = y" and "\<exists>!v. y = x \<^bold>+ v"
      then obtain v where "y = x \<^bold>+ v" by auto
      hence "x = x \<^bold>+ v" using \<open>x = y\<close> by auto
      hence "v = I" using Theorem_7 by auto
      hence "y = x \<^bold>+ I" using \<open>y = x \<^bold>+ v\<close> by auto
      hence "y = succ x" using L1 by auto
      hence "y \<noteq> x" by (metis Axiom_3)
      thus False using \<open>x = y\<close> by auto
    qed
    moreover have "\<not>((\<exists>!u. x = y \<^bold>+ u) \<and> (\<exists>!v. y = x \<^bold>+ v))"
    proof
      assume "\<exists>!u. x = y \<^bold>+ u" and "\<exists>!v. y = x \<^bold>+ v"
      then obtain u v where "x = y \<^bold>+ u" and "y = x \<^bold>+ v" by auto
      hence "x = (x \<^bold>+ v) \<^bold>+ u" by auto
      hence "x = x \<^bold>+ (v \<^bold>+ u)" using Theorem_5 by auto
      hence "v \<^bold>+ u = I" using Theorem_7 by auto
      hence "x = (v \<^bold>+ u) \<^bold>+ x" by auto
      hence "x = I \<^bold>+ x" using Theorem_6 by auto
      hence "x = succ x" using L1 by auto
      thus False by (metis Theorem_2)
    qed
    ultimately have "\<not>((x = y) \<and> (\<exists>!u. x = y \<^bold>+ u) \<and> (\<exists>!v. y = x \<^bold>+ v))" by auto
  }
  {
    fix x::Natnums
    define M where "M \<equiv> {y. \<exists>!c::nat. (c = 1 \<and> x = y) \<or> (c = 2 \<and> (\<exists>!u. x = y \<^bold>+ u)) \<or> (c = 3 \<and> (\<exists>!v. y = x \<^bold>+ v))}"
    {
      have "x = I \<or> (\<exists>!u. x = I \<^bold>+ u)"
      proof (cases "x = I")
        case True
        then show ?thesis by auto
      next
        case False
        then obtain u where "x = succ u" using Theorem_3 by auto
        then have "x = I \<^bold>+ u" using L1 by auto
        moreover have "\<forall>v. x = I \<^bold>+ v \<longrightarrow> v = u" using Axiom_4 by auto
        ultimately show ?thesis by auto
      qed
      hence "I \<in> M" by (simp add: M_def)
    }
    {
      fix y::Natnums assume "y \<in> M"
      then have "\<exists>!c::nat. (c = 1 \<and> x = y) \<or> (c = 2 \<and> (\<exists>!u. x = y \<^bold>+ u)) \<or> (c = 3 \<and> (\<exists>!v. y = x \<^bold>+ v))" by (simp add: M_def)
      then show "succ y \<in> M"
      proof
        assume "x = y"
        then have "succ y = y \<^bold>+ I" using L1 by auto
        then have "succ y = x \<^bold>+ I" using \<open>x = y\<close> by auto
        then have "\<exists>!v. succ y = x \<^bold>+ v" by (metis Axiom_4)
        thus "succ y \<in> M" by (simp add: M_def)
      next
        assume "\<exists>!u. x = y \<^bold>+ u"
        then obtain u where "x = y \<^bold>+ u" by auto
        show "succ y \<in> M"
        proof (cases "u = I")
          case True
          then have "x = succ y" using L1 \<open>x = y \<^bold>+ u\<close> by auto
          then have "succ y = x" by auto
          thus "succ y \<in> M" by (simp add: M_def)
        next
          case False
          then obtain w where "u = succ w" using Theorem_3 by auto
          then have "x = y \<^bold>+ succ w" using \<open>x = y \<^bold>+ u\<close> by auto
          then have "x = succ (y \<^bold>+ w)" using L1 by auto
          then have "x = succ y \<^bold>+ w" using Theorem_6 by auto
          then have "\<exists>!u. x = succ y \<^bold>+ u" by (metis Axiom_4)
          thus "succ y \<in> M" by (simp add: M_def)
        qed
      next
        assume "\<exists>!v. y = x \<^bold>+ v"
        then obtain v where "y = x \<^bold>+ v" by auto
        then have "succ y = succ (x \<^bold>+ v)" by auto
        then have "succ y = x \<^bold>+ succ v" using L1 by auto
        then have "\<exists>!v. succ y = x \<^bold>+ v" by (metis Axiom_4)
        thus "succ y \<in> M" by (simp add: M_def)
      qed
    }
    from Axiom_5 have "\<forall>y. y \<in> M" using \<open>I \<in> M\<close> \<open>\<And>y. y \<in> M \<Longrightarrow> succ y \<in> M\<close> by blast
    from this M_def have "\<forall>y. \<exists>!c::nat. (c = 1 \<and> x = y) \<or> (c = 2 \<and> (\<exists>!u. x = y \<^bold>+ u)) \<or> (c = 3 \<and> (\<exists>!v. y = x \<^bold>+ v))" by auto
  }
  thus "\<forall>x y. \<exists>!c::nat. (c = 1 \<and> x = y) \<or> (c = 2 \<and> (\<exists>!u. x = y \<^bold>+ u)) \<or> (c = 3 \<and> (\<exists>!v. y = x \<^bold>+ v))" by auto
qed