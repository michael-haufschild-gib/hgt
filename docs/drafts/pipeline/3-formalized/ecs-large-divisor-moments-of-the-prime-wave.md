# Large-divisor moments of the prime wave

Let $\Phi$ be the continuous representative of the critical state, $A=\int e^{-u/2}\Phi(u)\,du$, and $D=N-Ae^{t/2}$ the integer quadrature error. The centered row of multiples of $d$ is $B_d(t)=d^{-1/2}D(t-\log d)$. Write $E_\Lambda(t)=\sum_{n\ge1}\Lambda(n)n^{-1/2}\Phi(t-\log n)-Ae^{t/2}$.

For $b\ge0$, $0<\alpha<1/2-b$ and integer $k\ge0$,
\[
 e^{bt}\sum_{1\le d\le e^{\alpha t}}(\log d)^k|B_d(t)|\in L^2(\mathbb R).
\]
On $t\ge0$, let $Z,L$ be the increasing-order sums over $d>e^{\alpha t}$ with weights $\mu(d)$ and $-\mu(d)\log d$, respectively. Both exist pointwise, and $e^{bt}Z,e^{bt}(E_\Lambda-L)\in L^2(0,\infty)$.

Choose $\beta<1/2$ with $b<\beta-\alpha(\beta+1/2)$. Translation and $t\ge(\log d)/\alpha$ bound the weighted $L^2$ cost of each small divisor by $\|e^{\beta t}D\|_2(\log d)^k d^{-1/2+\beta-(\beta-b)/\alpha}$. The exponent is strictly below $-1$. Summing the norms proves the absolute estimate. The [full ordered moments](ecs-ordered-moebius-inversion-of-the-integer-quadrature.md) are $0$ and $E_\Lambda$ on $t\ge0$. Subtract the finite small-divisor sums and apply the absolute estimate with $k=0,1$.

**Lean.** [criticalState_smallDivisorEnvelope](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/MovingDivisorsBelowTheSquareRoot.lean) and [riemannHypothesis_or_large_divisor_moments](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheLargeDivisorMomentsOfThePrimeWave.lean).
