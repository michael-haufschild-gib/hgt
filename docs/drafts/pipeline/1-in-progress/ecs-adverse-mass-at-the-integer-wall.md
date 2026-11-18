# Adverse integer mass next to the wall

**Target.** On the critical state of [§2.16](../../../reports/review-1811/obstacles-summary.md#216-exclusion-of-the-critical-state-programme-ecs), put $m=\int\Phi$, $X=e^t$ and $J_t=(X,X+\sqrt X]\cap\mathbb N$. Bound the negative mass of the literal coefficients $m(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)$ on $J_t$, before averaging in $t$.

The state’s terminal sign agrees with its total charge. Its inverse-square-root logarithmic wall law gives $0\le m\Phi(t-\log n)\ll_\Phi t^{-1/2}$ throughout $J_t$. The negative part of each coefficient costs at most the unit reference times this oriented profile. Summing gives $O_\Phi(t^{-1/2})$, uniformly over subsets of $J_t$.

**Early mass.** Write $P$ and $S$ as in §2.16. On $t\le U$, $U\ge0$, confinement bounds $|P(t)|+|S(t)|\ll_\Phi e^{2U}$, including both subtractions. Since $K(T-t)\le e^{(t-T)/2}$, the absolute early integral is $O_\Phi(e^{(5U-T)/2})$. Taking $U=T/8$ makes this decay while the sign-transfer bound applies on $t>U$ with $V=U-1$.

**Remaining arithmetic.** Keep every coefficient outside the selected set and the subtraction $-m^2/2$. The admissible moving-divisor choice $\alpha=1/4,\ b=1/8$ gives an exponentially weighted square bound for the discarded small divisors. The sign of the remaining ordered logarithmic Möbius sum on late windows is open. The wall interval indexes integers $n$; the cutoff $d\le e^{t/4}$ indexes divisors. Removing both requires accounting for their intersection.

**Critical width conjecture.** More generally let $A_-(t,H)$ be the adverse coefficient mass on $(X,X+H]$. For $X^{1/4}\le H\le X^{3/4}$ the state law predicts
\[
 A_-(t,H)\asymp_\Phi H/\sqrt{X\log X}.
\]
For the lower bound, retain the multiples of six in $(X+H/2,X+H]$. Their Mangoldt coefficient vanishes and $H/(4X)\le\log(n/X)\le H/X$. There are at least $H/12-1$ of them. At width $H=\sqrt{X\log X}$ their adverse contribution has positive order even before averaging. The positive prime contribution on the same interval still enters the signed row.
