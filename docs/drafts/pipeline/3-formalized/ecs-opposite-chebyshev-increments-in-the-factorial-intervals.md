# Opposite Chebyshev increments in the factorial intervals

If RH fails, arbitrarily late original §2.16 tests force two disjoint ordinary-prime intervals of opposite sign. One lies inside the selected factorial interval and one lies on its compensating side. For some $e>0$ independent of the aperture, at scale $X=e^T$ both intervals $(u,v]$ satisfy, with $h=v-u>0$,
$$
 h\le 1+v/X^e,\qquad |\theta(v)-\theta(u)-h|>X^e\sqrt h.
$$
Every integer on either interval has one fixed odd quotient throughout the selected consecutive block of numerators. Each interval can have its own quotient. The sign on the interior interval is opposite to the state orientation $m\Phi$ at the original displacement. [Original test theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/OppositeShortChebyshevIncrementsAtTheOriginalTest.lean#L330).

**Quotient intervals.** Use the [compensating discrepancies](../3-formalized/ecs-compensating-factorial-intervals-at-consecutive-numerators.md) for the entire block $[M,H]$. On either side $(x,y]$, all surviving denominators with odd quotient $q$ form one interval
$$
 (U,V]=\big(\max(x,\lfloor H/(q+1)\rfloor),\ \min(y,\lfloor M/q\rfloor)\big].
$$
On this interval the contribution is exactly $D=\theta(V)-\theta(U)-(V-U)$. When $U<V$, one has $qV\le H<(q+1)(U+1)$, so $q(V-U-1)\le U+1$, and $V-U\le U+1$. Also $V>\sqrt H$ gives $q^2\le H$. Thus $(V-U)q^2\le 2H$. Summing the square-root costs over the nonempty quotient intervals costs at most $2\sqrt H(1+\log H)$.

**Short intervals.** Cut each nonempty quotient interval into at most $P$ pieces of length at most $1+\lfloor (V-U)/P\rfloor$. A piece $(u,v]$ then has $P(v-u-1)\le V-U\le v$. If the signed discrepancy on every piece were at most $B\sqrt{v-u}$, the total signed discrepancy would be at most $2BP\sqrt H(1+\log H)$. This estimate works separately for either sign and any admissible block $[M,H]$. [Harmonic bound and short interval](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/OppositeShortChebyshevIncrementsAtTheOriginalTest.lean#L92).

On the original test sequence the two signed totals exceed $cX^g\sqrt H$ and $H^{g/6}\le X^g$. Taking $B=X^{g/4}$ and $P=\lceil B\rceil$ gives $2BP(1+\log H)=o(X^g)$. Both signs therefore occur among ordinary unweighted prime counts on the same tests and the interval widths satisfy the displayed bound with $e=g/4$.

**Consecutive starting locations.** Write $R=X^{g/8}$, so $B=R^2$. Eventually $2R(1+\log H)\le B$ because $\log H\le6\log X$. On a selected interval of length $h$, the absolute contribution of any $D$ removed terms is at most $D(1+\log H)$. Its signed discrepancy $>B\sqrt h$ therefore gives $2R\sqrt h<h$. Put $D=\lfloor R\sqrt h\rfloor$. For every integer $0\le r\le D$, the interval $(u+r,v-D+r]$ loses exactly $D$ terms and retains signed discrepancy $>R\sqrt h$. All these intervals have the same length $h-D>h/2$ and remain in the same quotient interval. Thus for each sign more than $R\sqrt h$ consecutive starting locations give an exceptional ordinary Chebyshev increment at the same length. [Consecutive starts](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/OppositeShortChebyshevIncrementsAtTheOriginalTest.lean#L211).

The arithmetic obstruction is a pair of such runs, of opposite signs, on the state-selected tests.
