# Exterior mass of the original fractional test

On the forced state put $m=\int\Phi$, let $P$ be its ordinary-prime polar error and $S=\sum_n(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)-m/2$. With $K(v)=e^{-v/2}\{e^v\}$, every $T\ge0$ satisfies
\[
 \int_{t\le T/6} (|S(t)|+|P(t)|)K(T-t)\,dt\ll_\Phi e^{-T/12},\qquad
 \int_{D\cap(6T,\infty)} |mP(t)|K(T-t)\,dt\ll_\Phi e^{-T/10}
\]
for every measurable $D$, with both integrals absolutely convergent. The constants depend only on the state. Nonnegativity also permits any restriction of the early integral. [Lean theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheEarlyMassOfTheSignedFractionalTest.lean#L237).

**Proof.** For $t\le U$, $U\ge0$, confinement bounds each integer atom by $C_\Phi e^{2U}/n^2$ for $n\ge1$. Both arithmetic rows, the polar term and the square charge are $O_\Phi(e^{2U})$. Integrating $K(T-t)\le e^{(t-T)/2}$ gives $O_\Phi(e^{(5U-T)/2})$. Take $U=T/6$.

The project zero-free strip gives $\Theta-1/2<31/80$. The damped ordinary-prime theorem puts $e^{-31t/80}P(t)$ in $L^2(0,\infty)$. Cauchy–Schwarz with $e^{-t/80}$ gives $e^{-2t/5}|P(t)|\in L^1(0,\infty)$. On $t>6T$ the kernel satisfies $K(T-t)\le e^{(T-t)/2}\le e^{-T/10}e^{-2t/5}$. Integrating this majorant over any subset proves the second estimate. [Damped prime error](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ExponentiallyIntegrableChangeOfPrimeVariance.lean#L32).
