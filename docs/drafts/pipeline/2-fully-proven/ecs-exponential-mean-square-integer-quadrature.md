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
For $\varepsilon>0$ this series converges in $L^1\cap L^2$ and $\widehat U_\varepsilon=\eta(1+\varepsilon-i\tau)H(\tau)$. The entire continuation of $\eta$ satisfies $|\eta(s)|\ll (1+|\Im s|)^{5/16}$ uniformly for $\Re s\ge1/2$, by zeta convexity and pole cancellation. The tilted-state Fourier energy is finite against $1+|\tau|^{5/8}$. For each fixed $h$, Plancherel and dominated convergence therefore give
\[
 \int_{-h}^0 |\Psi(u)|^2du\ \le\ 
 \int_{\mathbb R}|1-e^{ih\tau}|^2|\eta(1-i\tau)H(\tau)|^2\,\frac{d\tau}{2\pi}
 \quad(0<h<\log2).
\]
Indeed, every term with $n\ge2$ vanishes in $U_\varepsilon(u)$ for $u\ge-\log2$, and every term vanishes in $U_\varepsilon(u+h)$ when $u\ge-h$.

Take $h_j=2^{-j}$ and put $a=|\tau|$, $q(y)=y/(1+y)$. Since $|1-e^{ih\tau}|^2\le\min(4,h^2a^2)$,
\[
 \frac{|1-e^{ih\tau}|^2}{h}\le24a\,[q(ha)-q(ha/2)] .
\]
For $y=ha\le1$, $(1+y)(2+y)\le6$; for $y\ge1$, the product is at most $6y^2$. Summing in $j$ telescopes. The endpoint transform bound would consequently give a uniform bound on $\sum_{j=1}^J h_j^{-1}\int_{-h_j}^0|\Psi|^2$. But the established terminal mass law gives $h_j^{-1}\int_{-h_j}^0|\Psi|^2\sim 8a_0 M/(j\log2)$, with $a_0$ the confinement coefficient and $M=\int F^2 e^{-8u}>0$. The half tilt has squared weight between $e^{-h_j}$ and 1 on the integration interval. The harmonic sum diverges. Larger positive-ray exponents imply the endpoint by monotonicity. [Terminal mass law](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheModulusOfContinuityOfTheStateIsCarriedByTheWall.lean) · [Uniform eta bound](../../../../formal/GaloisForLFunctions/RHTower/TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa.lean) · [Readout of the alternating divisor symbol](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheAlternatingPrimeSymbolsAtARightZero.lean).
