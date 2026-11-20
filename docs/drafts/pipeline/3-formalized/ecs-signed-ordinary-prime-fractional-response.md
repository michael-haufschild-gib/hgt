# The signed fractional-part response of the ordinary-prime wave

On the critical state forced by failure of RH, let $P(t)$ denote the ordinary-prime wave after pole subtraction, $K(v)=e^{-v/2}\{e^v\}$ and $m=\int\Phi$. Then
\[
 I(T)=\int_{\mathbb R}P(t)K(T-t)\,dt\longrightarrow \zeta(1/2)m,
 \qquad m I(T)<0\quad\text{for all sufficiently large }T .
\]
Each integral converges absolutely for $T\ge0$.

The [Mangoldt integral](../3-formalized/ecs-fractional-part-test-of-the-prime-wave.md) tends to zero. Subtract the wave $Q$ of all proper powers. It tends to $m/2$ at $+\infty$, and confinement bounds its absolute sum by $Ce^{2t}\sum_{p,k\ge2}(\log p)p^{-5k/2}$ on the other ray. Thus $Q$ is bounded globally. In mass coordinates $v=T-t$, dominated convergence gives $\int Q(T-v)K(v)\,dv\to(m/2)\int K$. The fractional-part Mellin integral gives $\int K=-2\zeta(1/2)$. The state transform at zero is nonzero, and $\zeta(1/2)<0$ gives the strict sign. The unaveraged sign masses remain open.

**Lean.** [fractionalPrimeTest_mass, riemannHypothesis_or_ordinary_fractional_response](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSignedOrdinaryPrimeResponseAtEveryLateTime.lean).
