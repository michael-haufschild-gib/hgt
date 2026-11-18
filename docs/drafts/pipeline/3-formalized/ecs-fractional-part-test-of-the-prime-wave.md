# The fractional-part test of the Mangoldt wave

Let $\Phi$ be measurable, vanish on $[0,\infty)$ and satisfy $|\Phi(u)|\le Ce^{2u}$. Put $W(t)=\sum_n\Lambda(n)n^{-1/2}\Phi(t-\log n)$, $A=\int \Phi(u)e^{-u/2}\,du$ and $K(v)=e^{-v/2}\{e^v\}$. For every $T\ge0$,
\[
 \lim_{M\to\infty}\int_{-\infty}^{M}(W(t)-Ae^{t/2})K(T-t)\,dt
 =\int_{-\infty}^0 \Phi(u)e^{(u-T)/2}
   [x(\log x-1)-\log(\lfloor x\rfloor!)]\,du,\quad x=e^{T-u}.
\]
The absolute value is at most $C(1+T)e^{-T/2}$.

At $M\ge T$, translating each atom in the integral gives the arithmetic cutoff $Y=e^{M-u}\ge x$. The integral of the polar density is $e^{T/2}(M-T+1-\gamma)$. The [finite fractional-part identity](ecs-fractional-part-average-of-the-mangoldt-measure.md) leaves the displayed factorial term and an error bounded by $e^{T/2}\int|\Phi(u)|e^{-u/2}du$ times $\sup_{Y\ge e^M}|\sum_{n\le Y}\Lambda(n)/n-\log Y+\gamma|$. This supremum tends to zero. The logarithmic bound for the factorial error gives the estimate.

[Lean](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheFractionalPartTestOfThePrimeWave.lean) proves `integral_mangoldt_fractional_cut`, `tendsto_mangoldt_fractional_response` and `abs_stirlingTestResponse_le`.
