# Moving divisors in the centered prime wave

Let $D=N-Ae^{t/2}$ be the [integer quadrature error](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/SubcriticalMeanSquareOfTheIntegerQuadrature.lean). The discrepancy of the row of multiples of $d$, after subtracting its own density $Ae^{t/2}/d$, is exactly $d^{-1/2}D(t-\log d)$. For $\alpha>0$, $b\ge0$, $\alpha+b<1/2$ and each fixed $k$, the positive envelope
\[
 e^{bt}\sum_{d\le e^{\alpha t}}(1+\log d)^k d^{-1/2}|D(t-\log d)|
\]
lies in $L^2(0,\infty)$. Choose $b<\beta-\alpha(\beta+1/2)$ with $\beta<1/2$. On the support of each summand, $e^{-(\beta-b)t}\le d^{-(\beta-b)/\alpha}$. The $L^2$ cost of that summand is at most $\|e^{\beta t}D\|_2(1+\log d)^k d^{-1/2+\beta-(\beta-b)/\alpha}$, summable over $d$. This controls all small-divisor coefficients in absolute value, including coefficients selected separately at each time.

For $w_d=-\mu(d)\log d$, $\sum_{d\mid n}w_d=\Lambda(n)$ and $\sum_{d\ge1}w_d/d=1$ in increasing order. Interchanging the original confined integer atoms is absolutely justified by the divisor bound. Subtraction of the polar densities then gives
\[
 P_\Lambda(t)-Ae^{t/2}
 =\lim_{H\to\infty}\sum_{d\le H}w_d d^{-1/2}D(t-\log d).
\]
The centered series requires its indicated order. Consequently all divisors $d\le e^{(1/2-\epsilon)t}$ can be removed from the actual Mangoldt wave after individual centering with exponentially square-integrable error. The remaining large-divisor sum contains the Möbius cancellation needed for a one-sided bound. Lean targets are the simultaneous envelope, the ordered identity, and their application to this actual large-divisor remainder.

The same inversion without the logarithm gives a stronger cancellation law. Since $\sum_{d\mid n}\mu(d)=1_{n=1}$ and $\sum_{d\le H}\mu(d)/d\to0$,
\[
 \lim_{H\to\infty}\sum_{d\le H}\frac{\mu(d)}{\sqrt d}D(t-\log d)=\Phi(t)=0\qquad(t\ge0).
\]
Thus the **entire signed large-divisor tail** $d>e^{\alpha t}$ without the logarithm is exactly the negative of the small-divisor row and is exponentially square integrable whenever $b+\alpha<1/2$. The logarithmic prime response can be written with weight $t-\log d$ against that same signed row. Zeroth-moment cancellation is exact; controlling the first logarithmic moment on the remaining divisors is open. [Ordered logarithmic normalization](../../../../formal/GaloisForLFunctions/RHTower/Sieve/MoebiusLogarithmicNormalization.lean).

**All divisor scales.** Put $a_d(t)=d^{-1/2}(\log d)^kD(t-\log d)$, $d\ge1$. For $0\le b<1/6$, translation and Tonelli give the exact finite cubic integral
\[
 \int_{\mathbb R}\sum_d |e^{bt}a_d(t)|^3\,dt
 =\left(\sum_d (\log d)^{3k}d^{3b-3/2}\right)\int_{\mathbb R}e^{3bu}|D(u)|^3\,du.
\]
Indeed $|D(u)|\ll_\sigma e^{u/2}+e^{\sigma u}$ for $1/2<\sigma\le2$ by confinement, negative support and summability of $n^{-1/2-\sigma}$. Choose $3b+\sigma<1$ and apply the two subcritical squared norms with tilts $(3b+1/2)/2$ and $(3b+\sigma)/2$. The Dirichlet factor converges for $3b<1/2$ and diverges at equality. For any sets $S(t)$ of at most $e^{\kappa t}$ divisors, Hölder bounds $(\sum_{d\in S}|a_d|)^3\le |S|^2\sum_d |a_d|^3$. Thus a single integrable majorant controls the cubed absolute contribution with weight $e^{rt}$ whenever $r+2\kappa<1/2$, with no restriction on the sizes of the selected divisors. This applies to the true logarithmic Möbius row, including selections made after observing its coefficients. An exponentially large prime fluctuation cannot be supplied by those selected terms. The signed interaction among the remaining divisors is open.

**Upper truncation.** At a real cutoff $Y\ge e^t$ use the equivalent logarithmic weight $\log(Y/d)$, since the complete zeroth moment vanishes for $t\ge0$. Put $H(v)=\sum_{d\le v}\mu(d)/d$. The signed polar tail $\sum_{d>Y}\mu(d)\log(Y/d)/d$ equals $\int_Y^\infty H(v)\,dv/v$ by partial summation and $H(v)\log v\to0$. The [Mertens harmonic bound](../../../../formal/GaloisForLFunctions/RHTower/MertensPowerBoundsControlMobiusHarmonicSums.lean) and [seven-eighths estimate](../../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAbscissaAvoidsAnIntervalBelowSevenEighths.lean) give $H(v)=O(v^{-1/8})$. On $d>Y$ the uncentered integer row has absolute cost $O(e^{2t}d^{-5/2})$ by confinement. Consequently all divisors above $Y$ together cost $O(e^{t/2}Y^{-1/8}+e^{2t}Y^{-3/2})$ in the centered logarithmic representation. Taking $Y=e^{ct}$ with $c>4$ leaves exponential decay and reduces the infinite ordered first moment to a moving finite band. Sizes above the band have been controlled only in their forced natural order.
