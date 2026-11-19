# Compensating factorial intervals at consecutive numerators

If RH fails, the §2.16 test scales $X=e^T$ and their [factorial interval](../3-formalized/ecs-odd-quotients-in-the-ordinary-prime-deficit.md) admit two fixed, disjoint intervals of denominators. One is the selected interval $[a,b]$. The other is either $(\lfloor\sqrt H\rfloor,a-1]$ or $(b,H]$, with $H\ge X$ the numerator extracted at this test time. Write $Q_j=j!/\lfloor j/2\rfloor!^2$. For some $c,g,d>0$ independent of the aperture, the following holds for every nonempty set $E$ of integer numerators in $[H-H^{1/2+d},H]\cap[1,H]$.

On each interval $S$, subtract the number of $n\in S$ with odd $\lfloor j/n\rfloor$ for every $j\in E$ from the log mass of prime divisors of $\gcd_{j\in E}Q_j$ in $S$. The two discrepancies have opposite signs and each exceeds $cX^g\sqrt H$ in magnitude. The sign inside $[a,b]$ is opposite to $m\Phi(v)$ at the displacement picked by the original test. The same intervals and signs work for singletons, the entire block and all intermediate selections. [Consecutive numerators](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/CompensatingFactorialPrimeIntervalsAtConsecutiveNumerators.lean#L60).

**Completing the row.** Put $q_n=\mathbf 1_{n\ {\rm prime}}\log n-1$ and $D_S(H)=\sum_{n\in S}q_n\mathbf1_{\lfloor H/n\rfloor\ {\rm odd}}$. The complete parity sum for $\Lambda(n)-1$ is $O(\sqrt H)$ by the [alternating divisor count](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheAlternatingDivisorCountHasSquareRootError.lean). Removing proper prime powers costs at most $\psi(H)-\theta(H)\ll\sqrt H$. Removing all $n\le\sqrt H$ costs at most $(1+\log4)\sqrt H$. Thus the full ordinary-prime row above $\sqrt H$ has square-root error for every $H$. Its two sides outside the selected interval must jointly compensate the selected discrepancy. One side alone supplies at least a fixed fraction of its magnitude with the opposite sign. [Complete row](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/VariationOfTheFactorialPrimeDiscrepancy.lean#L72).

**Changing numerators.** Let $D(N)=\sum_{n\le N}\lfloor N/n\rfloor$ and $V(N)=\log(N!)+D(N)$. For $1\le M\le H$, any changed parity column costs at most
\[
 (\Lambda(n)+1)\big(\lfloor H/n\rfloor-\lfloor M/n\rfloor\big).
\]
Summing this majorant gives exactly $V(H)-V(M)$ by the factorial identity. It bounds total variation along consecutive numerators. It also bounds the cost of intersecting the parity tests over any nonempty selection in $[M,H]$, since every constant column survives with its original value. [Intersection bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/VariationOfTheFactorialPrimeDiscrepancy.lean#L199). The Dirichlet hyperbola estimate gives
\[
 V(H)-V(M)\le(H-M)(2\log H+2+2|\gamma|)+40\sqrt H .
\]
Here $H\log H-M\log M\le(H-M)(1+\log H)$ and $\log(H!/M!)\le(H-M)\log H$. These estimates are uniform in the set of denominators. [Total variation](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/VariationOfTheFactorialPrimeDiscrepancy.lean#L184).

**Common prime divisors.** The extracted numerator satisfies $H^{g/6}\le X^g$. Take $d=\min(g/12,1/4)$. For $H-M\le H^{1/2+d}$ the variation bound is $o(X^g\sqrt H)$, since $\log H=o(H^d)$. Above $\sqrt H$, the prime valuation of each $Q_j$ for $j\le H$ is exactly $\lfloor j/p\rfloor\bmod 2$. Intersection of the prime supports thus gives the gcd. [Gcd identity](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/CompensatingFactorialPrimeIntervalsAtConsecutiveNumerators.lean#L28). On a whole consecutive block, an odd column survives exactly when its endpoint quotients agree and are odd. Its denominator exceeds $H-M$. [Surviving quotients](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/VariationOfTheFactorialPrimeDiscrepancy.lean#L219).

The remaining arithmetic estimate must exclude these simultaneous signed discrepancies on the selected intervals.
