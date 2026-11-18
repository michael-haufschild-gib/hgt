# Adverse integer mass next to the wall

**Target.** On the critical state of [§2.16](../../../reports/review-1811/obstacles-summary.md#216-exclusion-of-the-critical-state-programme-ecs), put $m=\int\Phi$, $X=e^t$ and $J_t=(X,X+\sqrt X]\cap\mathbb N$. Bound the negative mass of the literal coefficients $m(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)$ on $J_t$, before averaging in $t$.

The state’s terminal sign agrees with its total charge. Its inverse-square-root logarithmic wall law gives $0\le m\Phi(t-\log n)\ll_\Phi t^{-1/2}$ throughout $J_t$. The negative part of each coefficient costs at most the unit reference times this oriented profile. Summing gives $O_\Phi(t^{-1/2})$, uniformly over subsets of $J_t$.

**Early mass.** Write $P$ and $S$ as in §2.16. On $t\le U$, $U\ge0$, confinement bounds $|P(t)|+|S(t)|\ll_\Phi e^{2U}$, including both subtractions. Since $K(T-t)\le e^{(t-T)/2}$, the absolute early integral is $O_\Phi(e^{(5U-T)/2})$. Taking $U=T/8$ makes this decay while the sign-transfer bound applies on $t>U$ with $V=U-1$.

**Remaining arithmetic.** Let $L(t)$ be the natural-order logarithmic Möbius sum over $d>e^{t/4}$ and $D(t)$ the integer quadrature error. The [large-divisor estimate](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheLargeDivisorMomentsOfThePrimeWave.lean) with tilt $1/8$ bounds the omitted centered multiples in weighted $L^2$. Subtract $D(t)$ to recover the literal $-1$ reference. Cauchy–Schwarz then gives $\int_{t>U}|S(t)-(L(t)-m/2)|\,dt\ll_\Phi e^{-U/16}$. The sign of $m(L-m/2)$ on late windows is open. The wall interval indexes integers $n$ and the cutoff indexes divisors $d$. Removing both requires accounting for their intersection.

**Critical width.** Let $A_-(t,H)$ be the adverse coefficient mass on $(X,X+H]$. The paper bound, uniform for $24\le H\le X^{3/4}$, is
\[
 A_-(t,H)\asymp_\Phi H/\sqrt{X\log X}.
\]
For the lower bound, retain the multiples of six in $(X+H/2,X+H]$. Their Mangoldt coefficient vanishes and $H/(4X)\le\log(n/X)\le H/X$. There are at least $H/12-1$ of them. For the upper bound $\log(n/X)\le X^{-1/4}$ throughout the window, so each adverse coefficient costs at most $C_\Phi/\sqrt{X\log X}$. At width $H=\sqrt{X\log X}$ the adverse contribution has positive order before averaging. The positive prime contribution on the same interval still enters the signed row.

**Signed contribution at the critical width.** Set $h=\sqrt{X\log X}$ and $\ell=\lim_{k\downarrow0}\Phi(-k)\sqrt{\log(1/k)}$. The next target is
\[
 m\!\!\sum_{X<n\le X+h}(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)
 =\sqrt2\,m\ell\left(\frac{\psi(X+h)-\psi(X)}h-1\right)+o_\Phi(1).
\]
For fixed $0<\eta<1$, the rescaled state weight tends uniformly to $\sqrt2\,m\ell$ on $\eta h<n-X\le h$. The [interval sieve](../../../../formal/GaloisForLFunctions/PNTPlus/BrunTitchmarsh.lean) and [local proper-power bound](../../../../formal/GaloisForLFunctions/RHTower/Sieve/MaynardLocalPrimePowerLeakage.lean) bound the discarded Mangoldt mass by $O(\eta h)$ with an absolute constant once $X$ is large enough for that $\eta$. This leaves the actual prime excess on this interval and the separately retained complementary row.

The prime number theorem forces the normalized excess to be at least $-\varepsilon$ arbitrarily late for each $\varepsilon>0$. Otherwise telescope along $x_{j+1}=x_j+h(x_j)$ to obtain $\psi(x_j)\le(1-\varepsilon)x_j+O(1)$. The corresponding upper reading follows by applying the same argument to $2x-\psi(x)$. Synchronizing a favorable window with the signed complementary row remains open.
