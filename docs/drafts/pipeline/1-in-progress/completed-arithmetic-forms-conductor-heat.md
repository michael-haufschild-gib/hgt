# The heat threshold of completed conductor energies

For fixed overlap $c>0$, let $E_m(c)$ be the completed tilted-spline conductor
energy, including the pole and shell correction. The target is the exact domain
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
For $\beta\le1$, positivity of the tilted-spline energies and the prime ceiling
give a constant multiple of $1/p$ below the prime heat weights. Divergence of
the prime reciprocal series gives the sharp boundary, including $\beta=1$.

This concerns the infinite conductor model identified by fixed arithmetic
packets. Convergence of finite complete-Weil heat traces additionally requires
control of their growing high-energy multiplicities.

Lean target: `CompletedArithmeticForms/ConductorHeatThreshold.lean`.
