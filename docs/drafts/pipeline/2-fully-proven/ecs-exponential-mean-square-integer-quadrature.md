# Sharp exponential mean-square boundary for integer quadrature

For the critical state, write $D(t)=N(t)-Ae^{t/2}$. Then $e^{\lambda t}D\in L^2(\mathbb R)$ for $0\le\lambda<1/2$, and $e^{\lambda t}D\notin L^2(0,\infty)$ for every $\lambda\ge1/2$. The endpoint obstruction is the wall of the state itself.

**Endpoint transform.** Write $\Psi(u)=e^{u/2}\Phi(u)$ and $H(\tau)=\widehat\Psi(\tau)$ in angular frequency. Suppose the positive-ray endpoint integral is finite. The [subcritical Parseval formula](ecs-subcritical-exponential-mean-square-integer-quadrature.md), dominated convergence on the time side and Fatou on the frequency side give $\int|\zeta(i\tau)H(\tau)|^2d\tau<\infty$. Exponential confinement makes the negative ray integrable uniformly as $\lambda\uparrow1/2$. In the functional equation $\zeta(i\tau)=\chi(i\tau)\zeta(1-i\tau)$ the reflection formula gives
\[
 |\chi(i\tau)|^2=\frac{|\tau|}{2\pi}\tanh\frac{\pi|\tau|}{2}.
\]
Thus $\int_{|\tau|\ge1}|\tau|\,|\eta(1-i\tau)H(\tau)|^2d\tau<\infty$, where $\eta(s)=(1-2^{1-s})\zeta(s)$. The product is bounded on the remaining compact interval.

**The wall survives reflection.** Take
\[
 U_\varepsilon(u)=\sum_{n\ge1}(-1)^{n+1}n^{-1-\varepsilon}\Psi(u+\log n).
\]
For $\varepsilon>0$ this series converges in $L^1\cap L^2$ and $\widehat U_\varepsilon=\eta(1+\varepsilon-i\tau)H(\tau)$. For $0\le\varepsilon\le1$ the alternating prefix through $N=\lceil1+|\tau|\rceil$ costs $O(1+\log N)$ in absolute value; pairing consecutive tail terms costs $O((1+|\tau|)/N)$ by integrating the derivative of $x^{-1-\varepsilon+i\tau}$. This gives a common $O(1+\log(2+|\tau|))$ majorant for the multiplier. The tilted-state increment estimate, valid also for the tilt $1/2$, gives $\int(1+|\tau|)^{1/2}|H(\tau)|^2d\tau<\infty$. Plancherel and dominated convergence therefore give $U_\varepsilon\to U$ in $L^2$, with $\widehat U=\eta(1-i\tau)H(\tau)$.

Every translate with $n\ge2$ vanishes on $(-\log2,\infty)$ because $\Psi$ vanishes on the positive ray. Hence $U=\Psi$ almost everywhere on that interval. The endpoint transform bound puts $U$ in $H^{1/2}$. For any $0<b<\log2$, its Gagliardo seminorm dominates
\[
 \int_{-b/2}^0|\Psi(u)|^2\int_0^b\frac{dv}{(v-u)^2}\,du
 \ \gg\ \int_0^{b/2}\frac{|\Psi(-x)|^2}{x}\,dx .
\]
The wall law gives $|\Psi(-x)|^2\log(1/x)\to 8a\int F^2e^{-8u}>0$. The last integral diverges as $\int_0 dx/(x\log(1/x))$. This contradicts endpoint square integrability. Any larger positive-ray exponent would imply the endpoint by monotonicity. [Wall law](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw.lean) · [Difference symbol](../../../../formal/GaloisForLFunctions/HTGeometry/GagliardoFourierConstant.lean) · [Alternating divisor symbol](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheAlternatingPrimeSymbolsAtARightZero.lean).
