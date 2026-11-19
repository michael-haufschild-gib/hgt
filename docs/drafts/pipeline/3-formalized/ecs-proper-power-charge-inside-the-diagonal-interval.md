# The proper-power charge inside the diagonal interval

Let $m=\int\Phi$ for the forced critical state. Write $B$ for the signed Mangoldt band beyond the moving edge on $T/6<t\le6T$, and $B_{\rm ord}$ for the same band with coefficient $\mathbf1_{n\text{ prime}}\log n-1$. Both include the original kernel $K(T-t)$ and the orientation $m$. Whenever $T\to\infty$, $T-\log N\to\infty$, and $\log L-T\to\infty$,
\[
 B(T,N,L)-B_{\rm ord}(T,N,L)\longrightarrow-\operatorname{Re}\zeta(1/2)m^2 .
\]
If RH fails, the [positive exterior tests](../3-formalized/ecs-diagonal-localization-of-the-signed-test.md) give $c,g>0$ such that for every fixed $0<\eta\le1$ there is a sequence $X=e^T\to\infty$, $X^{1/(1+\eta)}\le N\le X$, $L=\lceil X^{1+\eta}\rceil$, with $S_{\rm int}-B\ge cX^g$. Their construction gives $T\ge(1+\delta)\log N$ for a fixed $0<\delta<\eta$ and $N\to\infty$. Thus $T-\log N\ge\delta\log N$ and $\log L-T\ge\eta T$ both diverge. The uncharged complete middle integral $S_{\rm int}(T)$ tends to zero. Subtracting the proper-power correction gives
\[
 B_{\rm ord}+(S_{\rm int}-B)\longrightarrow\operatorname{Re}\zeta(1/2)m^2,\qquad
 B_{\rm ord}\le -cX^g+\operatorname{Re}\zeta(1/2)m^2+o(1).
\]
This deficit concerns the original weighted ordinary-prime band. Summation by parts on it must retain the prefix at its lower endpoint. Exclusion requires an independent arithmetic estimate incompatible with that deficit. [Ordinary-prime deficit](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSquareChargeInsideTheDiagonalInterval.lean#L409).

**Complete middle integral.** The charged middle complement differs in tested absolute integral from the ordinary-prime polar response by $o(1)$. Their signed integrals therefore have the same limit $\operatorname{Re}\zeta(1/2)m^2$. Translation by $T$ and dominated convergence give $\int_{T/6}^{6T} K(T-t)\,dt\to-2\operatorname{Re}\zeta(1/2)$. Removing the charge $-m^2/2$ leaves zero. Uniqueness up to sign transfers this identity to the state selected by the exterior gain, since the oriented integral is quadratic in the state. [Uncharged middle integral](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUnchargedMiddleIntegralOfTheOriginalTest.lean#L129).

**Distribution within the band.** For every continuous $b$ with $|b|\le1$, multiplying each proper-power term by $b(\log n-T)$ gives the limiting oriented reading
\[
 \frac m2\int_{\mathbb R}K(r)\int_{\mathbb R}\Phi(v)b(-r-v)\,dv\,dr .
\]
Put $t=T-r$, $v=t-\log n$. For any $z>0$, the set $|\Phi(v)|>z$ lies in a compact interval strictly inside $(-\infty,0)$. Confinement bounds its left endpoint and continuity at the wall bounds its right endpoint. For fixed $r$ all atoms there eventually satisfy $N<n\le L$ and $n>e^t+e^{t/2}\sqrt t$, since the relative width $e^{-t/2}\sqrt t$ tends to zero. Missing terms are bounded in absolute sum by the full proper-power reading of $\min(|\Phi|,z)$. The [proper-power sampling theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ThePrimeNumberTheoremOnTheState.lean#L322) sends this bound to $\tfrac12\int\min(|\Phi|,z)$, which tends to zero with $z$. The same theorem applied to $\Phi(v)b(-r-v)$ gives the inner integral. The full absolute proper-power row is bounded on the whole real line, so dominated convergence against $K(r)$ restores the original middle test. Taking $b=1$ and using $\int K=-2\operatorname{Re}\zeta(1/2)$ gives the stated correction. [Displacement law](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSquareChargeInsideTheDiagonalInterval.lean#L211) · [Charge limit](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSquareChargeInsideTheDiagonalInterval.lean#L372).
