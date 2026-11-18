# Ordered Möbius inversion of the centered integer wave

For $|\Phi(u)|\le C e^{2u}$, let $N(t)=\sum_{n\ge1}n^{-1/2}\Phi(t-\log n)$, $D(t)=N(t)-Ae^{t/2}$ and $B_d(t)=d^{-1/2}D(t-\log d)$. For every real $t,A$,
\[
 \lim_{H\to\infty}\sum_{d\le H}\mu(d)B_d(t)=\Phi(t),\qquad
 \lim_{H\to\infty}\sum_{d\le H}-\mu(d)\log d\,B_d(t)
 =\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}\Phi(t-\log n)-Ae^{t/2}.
\]
The zeroth moment vanishes on the positive ray for the critical state.

The uncentered double series converges absolutely by confinement. Grouping the pair $(d,m)$ by $dm=n$ leaves the divisor sum of the weight. Möbius inversion gives $1_{n=1}$ and $\Lambda(n)$ for the two weights. The subtracted density contributes $Ae^{t/2}\sum_{d\le H}w(d)/d$, whose ordered limits are zero and one, respectively. [Harmonic normalization](../../../../formal/GaloisForLFunctions/RHTower/Sieve/MoebiusLogarithmicNormalization.lean).

**Lean.** `tendsto_moebius_centredMultipleRow` and `tendsto_moebius_log_centredMultipleRow`. [Ordered inversion](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/MoebiusInversionOfTheIntegerQuadrature.lean).
