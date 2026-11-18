# Critical width of adverse integer mass

On the forced critical state, put $m=\int\Phi$, $X=e^t$, $J=(X,X+H]\cap\mathbb N$, and
\[
 v_n=(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n),\qquad A_-(J)=\sum_{n\in J}[-m v_n]_+ .
\]
For all sufficiently large $t$, uniformly for $24\le H\le X^{3/4}$,
\[
 A_-(J)\asymp_\Phi\frac{H}{\sqrt{X\log X}}.
\]
Consequently the adverse cost vanishes for $H=\sqrt X$ and stays bounded above and below by positive constants for $H=\sqrt{X\log X}$.

**Orientation.** The real state transform is continuous and nonzero from $0$ to $1/2$, so $m$ has the sign of the half charge. The half charge times the terminal mass is positive for all sufficiently small terminal intervals. Since the continuous representative has one sign there, $m\Phi(-k)>0$ for small $k>0$. The state equation gives $m\Phi(-k)\sqrt{\log(1/k)}\to |m|\sqrt{8aM}>0$, where $a$ is the critical alias coefficient and $M=\int F(u)^2 e^{-8u}\,du$.

**Upper bound.** For $n\in J$ put $k=\log(n/X)$. Then $0<k\le H/X\le X^{-1/4}$, so $m\Phi(-k)\ll_\Phi 1/\sqrt t$. Since $\Lambda(n)\ge0$, the adverse part costs at most $m\Phi(-k)/\sqrt n$. There are at most $H+1$ indices. The same upper bound holds for every subset of $J$.

**Lower bound.** At least $H/12-1\ge H/24$ multiples of six lie in $(X+H/2,X+H]$. They have $\Lambda(n)=0$. The inequality $\log(n/X)\ge(n-X)/n$ and $n\le2X$ give $k\ge1/X$. Thus $\log(1/k)\le t$ and every selected index contributes at least $c_\Phi/\sqrt{Xt}$.

**Complement.** For every $A\subseteq J$, absolute convergence gives
\[
 m\left(\sum_n v_n-m/2\right)\ge
 m\left(\sum_{n\notin A}v_n-m/2\right)-C_\Phi H/\sqrt{X\log X}.
\]
The sign of the full complementary row is open.

**Lean.** [`criticalState_oriented_wall_limit`, `criticalState_adverse_mass_by_width` and `riemannHypothesis_or_critical_width_adverse_mass`](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheCriticalWidthOfAdverseIntegerMass.lean). The unconditional capstone uses `propext`, `Classical.choice` and `Quot.sound`.
