# The heat threshold of completed conductor energies

For fixed overlap $c>0$, let $E_m(c)$ be the completed conductor energy of a
profile $\phi$, including the pole and shell correction. The exact heat domain is
\[
\sum_{m\ge1}e^{-\beta E_m(c)}<\infty\quad\Longleftrightarrow\quad\beta>1.
\]

Put $A=\operatorname{completeWeilSelfFinitePart}(\phi,c)$ and
\[
K=\frac2{|\int\phi^2|}\sum_{1\le h<\lceil c\rceil}
\left|\int_{h/c}^1\frac{G(u)}u\,du\right|.
\]
The literal shell bound gives $|\kappa_m(c)|\le K$. The exact source identity is
\[
E_m=A+\log m+\operatorname{tameDifferent}(m)
+\mathbf1_{m=1}\operatorname{completeWeilPoleShift}(\phi,c)-\kappa_m(c).
\]
Nonnegative tame different and pole shift imply $E_m\ge\log m+A-K$.
For prime $p$, $\operatorname{tameDifferent}(p)=\log p/(p-1)\le1$, hence
$E_p\le\log p+A+K+1$.

The upper heat estimate is a constant multiple of the convergent $\beta$-series.
For $0<\beta\le1$, the prime ceiling and $\beta\log p\le\log p$ give a constant
multiple of $1/p$ below the prime heat weights. Divergence of the prime reciprocal
series gives the sharp boundary, including $\beta=1$. For $\beta\le0$, properness
$E_m\to\infty$ prevents the heat weights from tending to zero. The threshold
is independent of the profile and the positive overlap.

For the actual tilted spline, $E_m>0$. The inequality
$E_m^k/k!\le e^{E_m}$ and divergence of the heat series at $\beta=1$ imply
$\sum_m E_m^{-k}=\infty$ for every integer $k\ge0$.

This concerns the infinite conductor model identified by fixed arithmetic
packets. Convergence of finite complete-Weil heat traces additionally requires
control of their growing high-energy multiplicities.

Lean target: `CompletedArithmeticForms/ConductorHeatThreshold.lean`.
