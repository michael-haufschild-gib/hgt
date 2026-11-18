# Signed Chebyshev excess at the critical width

Let $X=e^t$, $h=\sqrt{X\log X}$, $m=\int\Phi$ and $\gamma=\sqrt2\,|m|\sqrt{8aM}>0$ on the critical state. For the initial window's literal signed row,
\[
 W(t)=m\sum_{X<n\le X+h}(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n),
 \qquad W(t)-\gamma\left(\frac{\psi(X+h)-\psi(X)}h-1\right)\to0 .
\]
Consequently for each $\varepsilon>0$ there are arbitrarily late $t$ with $W(t)>-\varepsilon$.

**State weight.** Fix $0<\eta<1$. Put $v=h/X$, $n=X(1+dv)$, and $k=\log(1+dv)$. For $\eta\le d\le1$, eventually $\eta v/2\le k\le v$. Thus $\log(1/k)/t\to1/2$ and $\sqrt{X/n}\to1$, uniformly in $d$. The [oriented wall law](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheCriticalWidthOfAdverseIntegerMass.lean) gives $hm n^{-1/2}\Phi(-k)\to\gamma$ uniformly on the outer fraction. The same weight is bounded on the entire interval since $k\le v\le X^{-1/4}$ eventually.

**Prime and reference costs.** For $X^{1/4}\le H\le X$ the [interval sieve](../../../../formal/GaloisForLFunctions/PNTPlus/BrunTitchmarsh.lean) at $z=X^{1/64}$ gives $\theta(X+H)-\theta(X)\ll H$. The [proper powers](../../../../formal/GaloisForLFunctions/RHTower/Sieve/MaynardLocalPrimePowerLeakage.lean) cost $O((\sqrt H+1)\log^2(2X))=O(H)$. The [resulting linear Mangoldt bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheMangoldtMassInPowerWidthIntervals.lean) gives $\sum_{X<n\le X+H}|\Lambda(n)-1|\ll H$, with an absolute constant. Apply this at both $H=h$ and $H=\eta h$. The inner fraction costs $O_\Phi(\eta)$ after division by $h$; the outer weight replacement costs $o_{\Phi,\eta}(1)$. Let $\eta\downarrow0$. The number of integer reference terms differs from $h$ by at most one.

**Favorable windows.** For each $b>0$, $\psi(x+h(x))-\psi(x)\ge(1-b)h(x)$ arbitrarily late. Otherwise telescoping along $x_{j+1}=x_j+h(x_j)$ contradicts $\psi(x_j)/x_j\to1$. Taking $b<\varepsilon/(2\gamma)$ gives the asserted reading. All coefficients outside this window and the square charge $-m^2/2$ remain in the complementary signed row.
