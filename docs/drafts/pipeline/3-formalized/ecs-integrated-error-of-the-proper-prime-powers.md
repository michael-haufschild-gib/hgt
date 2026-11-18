# The integrated error of the proper prime powers

Let $\Phi$ be the continuous critical-state profile. For any real $1$-Lipschitz map $L$ fixing zero put $g=L\circ\Phi$. The proper-power wave satisfies
\[
  \int_T^\infty\left|
  \sum_{p,\ k\ge2}\frac{\log p}{p^{k/2}}g(t-k\log p)-\frac12\int_{\mathbb R}g
  \right|dt\ll_{\Phi,L} e^{-T/40}.
\]
Let $P$ be the polar-subtracted ordinary-prime wave and $M$ the polar-subtracted Mangoldt wave minus $\frac12\int\Phi$. Taking $L(x)=x$ gives
\[
 \int_T^\infty\bigl(|P_+-M_+|+|P_--M_-|\bigr)\,dt\ll_\Phi e^{-T/40},
\]
since the integrand equals $|P-M|$ pointwise. Thus both sign masses transfer on arbitrary measurable subsets of the late ray with the same absolute error. Taking $L(x)=(\pm x)_+$ controls the two extremal proper-power sign masses separately.

Give each prime $p$ a bin $[\theta(p-1),\theta(p))$ of length $\log p$, and let $p(y)$ denote the prime at mass $y$. Since $\theta(x)=x+O(x^{9/10})$, the two bin endpoints give $|p(y)-y|\ll y^{9/10}$. Thus $\ell(v)=2\log p(e^{v/2})$ and $w(v)=e^{v/2}/p(e^{v/2})$ satisfy $|\ell(v)-v|+|w(v)-1|\ll e^{-v/20}$. Changing variables $y=e^{v/2}$ writes twice the square wave as $\int w(v)g(t-\ell(v))\,dv$.

Subtract $\int g(t-v)\,dv$. For $t>T$ each integrand vanishes below $v=T-1$ for large $T$, by monotonicity of $\ell$ and negative support. For each remaining $v$ integrate first in $t$. The absolute cost is at most $|w(v)-1|\|\Phi\|_1+\|\Phi(\cdot+\ell(v)-v)-\Phi\|_1$. The [first absolute increment bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheFirstAbsoluteMomentOfStateIncrements.lean) bounds the latter by $\sqrt{|\ell(v)-v|}$ for all sufficiently small displacements of either sign. Integrating $O(e^{-v/40})$ proves the assertion for squares, uniformly in $L$.

For $k\ge3$, negative support restricts the sum at $t$ to $k\log p>t$. Its entire absolute contribution is at most $e^{-t/40}\|\Phi\|_\infty\sum_{p,k\ge3}(\log p)p^{-k(1/2-1/40)}$. The sum converges since $3(1/2-1/40)>1$. Integration gives the same tail estimate. The ordinary-prime sign bound beyond this transfer remains open.

The same sign comparison holds for the literal integer coefficients $\Lambda(n)-1$, after subtracting the square charge $\tfrac12\int\Phi$. Their wave differs from the polar-centered Mangoldt wave by the integer quadrature error $D$. Put $r=1/40$. The [weighted square estimate](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/SubcriticalMeanSquareOfTheIntegerQuadrature.lean) gives $e^{2rt}D\in L^2$. Since $e^{-rt}\in L^2(0,\infty)$, Cauchy–Schwarz gives $e^{rt}D\in L^1(0,\infty)$. Consequently the cost of this replacement on any measurable subset of $(T,\infty)$ is $O(e^{-rT})$.

**Lean.** The proper-power bound is `riemannHypothesis_or_integrated_properPower_error`. The two transfers are `riemannHypothesis_or_ordinary_sign_transfer` and `riemannHypothesis_or_integer_mangoldt_sign_transfer`. [Formal proof](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheIntegratedErrorInThePrimeSquareLayer.lean).
