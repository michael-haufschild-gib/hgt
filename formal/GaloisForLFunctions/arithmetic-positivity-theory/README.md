# Arithmetic Positivity Theory

Arithmetic Positivity Theory asks which independently checkable features of an
exact arithmetic source control the sign, the mixed couplings, and the stability
of its complete spectral energy. The spectral energy is the Weil form of the
Riemann zeta function; the sources are literal functions built from prime-power
weights, divisor identities, and Bernoulli sawtooth remainders, with every
endpoint jump, collar shift, Gamma factor and pole kept. The theory is built
*below* the Riemann Hypothesis: every theorem is unconditional, every positivity
statement is proved on a stated family at a stated scale, and the two universal
receivers that would deliver RH are treated as destinations and circularity
checks, never as premises.

This document is the foundational introduction: why the theory exists, which
objects it speaks about, which mechanisms carry its proofs, where its sharp
boundaries lie, and how to work inside it. Mathematics only; no ledger.

---

## 1. Why

### 1.1 Exact identities do not supply a sign

The explicit formula writes a complete spectral energy
$\mathcal W(f,f)$ as archimedean minus prime plus polar contributions. Every
piece is exact, and the corpus owns many such identities, self-adjoint
realisations and Krein-space involutions. None of them determines the sign of
the whole:

- a self-adjoint operator or an involution $J$ with $J^2=I$ has eigenvalues of
  both signs; a ground state may be negative;
- positivity of one piece, such as the archimedean jump integral or the
  Markovian part $\mathcal M_N(g)$ of the Weil–Markov–pole split, says nothing
  about $\mathcal W(g,g)=\mathcal M_N(g)+\tfrac12C(g)^2-\tfrac12S(g)^2$;
- Cauchy–Schwarz in the form $\lvert\mathcal W(f,g)\rvert^2\le
  \mathcal W(f,f)\mathcal W(g,g)$ is available only after $\mathcal W$ is known
  to be positive semidefinite on the span of $f$ and $g$.

The arithmetic has to pay for the sign. The programme's first discovery is that
it can pay, on an explicit family, through quantities that are measurable
without any knowledge of zero locations: physical square mass, translation
energy at the arithmetic scale, an independent absolute zero-sampling form,
harmonic separation of collar frequencies, and oscillatory cancellation under
prime dilation.

### 1.2 The two receivers

Two universal statements are RH-equivalent in the corpus and fix the horizon.

**Critical-scale cancellation.** With $\psi$ the Chebyshev function and
$D(T)=\int_0^T(e^t-\psi(e^t))\,dt$, either one-sided bound
$\exists B\,\forall T\ge0:\ D(T)\le B(1+T)e^{T/2}$ or
$\exists B\,\forall T\ge0:\ D(T)\ge-B(1+T)e^{T/2}$, with a single side and a
single constant for every scale, implies RH, and conversely.

**Sign of the complete arithmetic energy.** For real compact $C^2$ tests $g$
and prime apertures $N$ beyond the autocorrelation support,
$$
\mathcal W(g,g)=\mathcal M_N(g)+\tfrac12C(g)^2-\tfrac12S(g)^2,\qquad
\mathcal M_N(g)=V_N\|g\|_2^2+J_{\mathrm{L\acute evy}}(g)+J_{\mathrm{prime},N}(g),
$$
with creation potential $V_N=\Omega(0)-2\sum_{2\le m\le N}\Lambda(m)/\sqrt m$,
$C(g)=\int 2\cosh(u/2)g$, $S(g)=\int 2\sinh(u/2)g$. The capacity inequality
$S(g)^2\le 2\mathcal M_N(g)+C(g)^2$ for every admitted test and every aperture
is equivalent to RH. Proving it on a preferred finite-dimensional family is not
the same statement.

Neither receiver manufactures the arithmetic input it needs. The theory exists
to build that input from the bottom, keeping every result at its exact scope.

### 1.3 Why one exact family

Abstract principles are calibrated against a concrete laboratory: the
*factorial correction tail*. It is the difference between a canonically
pole-corrected arithmetic source and a compact ramp. It is noncompact, has an
endpoint jump at the origin, carries a shrinking irrational collar, and its
zero readouts are not entire. Every mechanism of the theory was forced into
existence by one of these features, and every mechanism is required to
reproduce an understood positive case and to fail honestly on an understood
obstruction. "Arithmetic" means the source keeps its literal $\Lambda$-weights
and divisor relations; "positivity" means a signed statement about the complete
form, never about a convenient piece of it.

---

## 2. What

### 2.1 Zero-side objects

Let $\rho$ run over the distinct nontrivial zeros of $\zeta$ with multiplicity
$m_\rho$; no location beyond the open strip $0<\Re\rho<1$ is assumed. For a
source $f:\mathbb R\to\mathbb C$ the **Mellin readout** is
$$
F_f(s)=\int_{\mathbb R}f(x)\,e^{(s-1/2)x}\,dx .
$$
In the corpus convention this is `paperFT f (gammaOf s)` with `paperFT f z = ∫ f(u) e^{izu} du`
and `gammaOf s = (s-1/2)/i` from the `Zeta23` dependency; on a vertical line
$s=\sigma+it$ it is the unitary Fourier transform of $x\mapsto e^{(\sigma-1/2)x}f(x)$
at the frequency $-t/(2\pi)$. Compact tests have entire readouts; the factorial
tails have readouts holomorphic exactly on $\Re s>-1$.

The **absolute square-sampling mass** and the **zero-side Weil pairing** are
$$
\mathcal Z(f)=\sum_\rho m_\rho\lvert F_f(\rho)\rvert^2,\qquad
\mathcal W(f,g)=\sum_\rho m_\rho F_f(\rho)\,\overline{F_g(1-\overline\rho)} .
$$
Reflection $\rho\mapsto1-\overline\rho$ preserves the zero divisor with
multiplicities, so $\mathcal W$ is the inner product twisted by a unitary
involution and
$\lvert\mathcal W(f,g)\rvert\le\sqrt{\mathcal Z(f)\mathcal Z(g)}$ holds for
all square-summable sources. Summability is always proved before a totalised
sum is used; $\mathcal Z\ge0$ is trivial, $\mathcal W(f,f)\ge0$ is never
assumed. On smooth compact tests $\mathcal W(f,f)$ equals the complete
physical Weil energy; on the factorial tails the same identity is a theorem
with an explicit limiting argument.

### 2.2 Physical-side objects

The **complete physical energy** of a real source $g$ is
$$
Q(g)=\frac1{2\pi}\int\lvert\hat g(r)\rvert^2\,\Omega(r)\,dr
+2\,\Re\bigl(\hat g(i/2)\,\overline{\hat g(-i/2)}\bigr)
-T_\Lambda(g\star\tilde g),
$$
with $\Omega$ the Gamma bracket, the two polar readouts at $\pm i/2$, and the
von Mangoldt atom pairing $T_\Lambda$ of the autocorrelation. The Weil form
*subtracts* the prime channel. The Weil–Markov–pole split of §1.2 is the same
quantity reorganised around the Markovian creation-and-jump energy and the
rank-two hyperbolic pole plane $\tfrac12C^2-\tfrac12S^2$.

### 2.3 The factorial source family

Four pieces generate everything.

**Clamped Bernoulli kernel.** $C(u)=\{u\}(1-\{u\})/2$, the negative of the
periodic second Bernoulli function: $1$-periodic, with values in $[0,1/8]$,
unit-cell mean $1/12$, global Lipschitz constant $1/2$ including the integer
joins, and cosine series
$C(u)=\tfrac1{12}-\tfrac1{2\pi^2}\sum_{k\ge1}\cos(2\pi ku)/k^2$.

**Dyadic Bernoulli filter.** $P(u)=\tfrac14C(4u)-2C(2u)+4C(u)$, whose
centred form is
$$
P(u)-\tfrac3{16}=-\frac2{\pi^2}\sum_{k\ge1}\frac{\chi(k)}{k^2}\cos(2\pi ku),
\qquad
\chi(k)=\begin{cases}1&k\text{ odd}\\-1&k\equiv2\ (4)\\0&4\mid k.\end{cases}
$$
The stencil $(4,-2,\tfrac14)$ on the divisor set $\{1,2,4\}$ is the unique one
with harmonic multipliers $M(1)=4$, $M(2)=-4$, $M(4)=0$. Its quadratic drift
$\sum d^2\alpha(d)$ vanishes; its linear drift $\sum d\alpha(d)$ equals one and
is the secular ramp carried by the compact ramp below. The higher harmonics
satisfy $\sum_{k\ge2}\lvert\chi(k)\rvert/k^2\le3/4$, so the first harmonic
dominates with margin $1/4$.

**Collar and shifted frequency.** For $N\ge1$ the collar is
$\varepsilon_N=e^{w_N}-1$ with $w_N=\tfrac13\log(1+\tfrac1{4N})$, so that
$(1+\varepsilon_N)^3=1+\tfrac1{4N}$. The shifted frequency
$\lambda_N=N(1+\varepsilon_N)$ satisfies the exact cubic
$4\lambda_N^3=N^2(4N+1)$ and the collar bounds
$1/15\le\delta_N:=\lambda_N-N\le1/12$. The **affine clock** is $12N+1$ and the
**affine defect** $e_N=N+\tfrac1{12}-\lambda_N$ obeys
$Ne_N=\delta_N^2+\delta_N^3/(3N)$, hence $1/(225N)\le e_N\le1/(140N)$.

**Phase profile and correction tail.** $\Phi_N(v)=P(\lambda_Nv)-P(Nv)$ is the
$1$-periodic-minus-almost-periodic phase. With $N=n+1$ and amplitude
$a_n=1/(N\varepsilon_N\sqrt N)\in[12/\sqrt N,\,15/\sqrt N]$,
$$
T_n(x)=a_n\,e^{3x/2}\,\Phi_N(e^{-x})\,\mathbf 1_{x\le0},
\qquad \lvert\Phi_N\rvert\le\tfrac{25}{32},\qquad
\lvert T_n(x)\rvert\le\frac{12\,e^{3x/2}}{\sqrt N}.
$$
The **compact ramp** $r_n$ is a continuous bi-null combination of three dilated
factorial lifts with coefficients $(1,-4,4)$ and normalisation $1/\sqrt N$; the
**boundary-corrected source** is $H_n=r_n+T_n$, and its zero readout is a
single reciprocal mode
$$
F_{H_n}(\rho)=\frac{c_n}{\rho},\qquad c_n=\frac1{2\sqrt N}.
$$
Normalised nonnegative mollifiers $\eta_k$ of radius $1/(4(k+1))$ give
$H_{n,k}=\eta_k*H_n$, $U_{n,k}=\eta_k*T_n$, $r_{n,k}=\eta_k*r_n$, with
$\lvert F_{\eta_k}\rvert\le e$ on the closed strip and $F_{\eta_k}\to1$.

**Spans and envelopes.** For a finite complex family $b$ put
$B_b(v)=\sum_Nb_N\Phi_N(v)$. The **span test** is
$f_b(x)=e^{3x/2}B_b(e^{-x})\mathbf 1_{x\le0}$, and every finite combination
$\sum c_nT_n$ is the span test with $b_{n+1}=c_na_n$. Replacing $3/2$ by an
**envelope exponent** $\beta$ gives $f_\beta(x)=e^{\beta x}B(e^{-x})\mathbf 1_{x\le0}$;
the clock substitution $v=e^{-x}$ turns physical $L^2$ mass into
$\int_1^\infty v^{-(2\beta+1)}\lvert B(v)\rvert^2dv$. The canonical tail is
$\beta=3/2$ (weight $v^{-4}$); the **critical source** is $\beta=1/2$
(weight $v^{-2}$), namely $g(x)=\mathbf 1_{x\le0}e^{x/2}F(e^{-x})=\sum_n(b_n/a_n)e^{-x}T_n(x)$.

### 2.4 Harmonic language

Expanding each profile in its Bernoulli series,
$$
-\frac{\pi^2}2B_b=\sum_{k\ge1}w_kH_k,\qquad w_k=\frac{\chi(k)}{k^2},\qquad
H_k(v)=\sum_Nb_N\bigl(\cos(2\pi k\lambda_Nv)-\cos(2\pi kNv)\bigr).
$$
Each layer $H_k(rv)$, $r\ge1$, is an exponential sum over the four signed
branches $\pm krN$, $\pm kr\lambda_N$ with coefficients $\mp b_N/2$; the collar
bounds separate the branches by at least $k/15$. The weights satisfy
$w_1=1$, $\sum_{k\ge2}\lvert w_k\rvert\le3/4$, $\sum_k\lvert w_k\rvert\le7/4$.

### 2.5 Critical-scale objects

At $\beta=1/2$ the slow collar phase survives the limit $N\to\infty$ and new
arithmetic objects appear.

| Object | Definition |
|---|---|
| Harmonic defect | $J_m=\int_1^\infty v^{-2}\bigl(1-\cos(2\pi mv/12)\bigr)dv\in[0,2]$, positive for $m>0$, $J_m\to1$ |
| Pattern density | $Q_b(t)=\bigl\lvert\sum_{j\in S}b_je^{2\pi ijt}\bigr\rvert^2$ for a finite real pattern $b$, period one, even |
| Pattern mass | $J_m(b)=\int_1^\infty v^{-2}\bigl(1-\cos(2\pi mv/12)\bigr)Q_b(mv)\,dv$ |
| Divisor charge | $A(m)=\chi(m)\sum_{d\mid m}d\,\Lambda(d)\,\chi(m/d)$ |
| Cumulative charge | $H_N=\sum_{1\le m\le N}A(m)/m^3$ |
| Kernel weight | $\gamma(u)=u^{-2}\bigl(1-\cos(2\pi u/12)\bigr)=2\sin^2(\pi u/12)/u^2$, a scaled sinc square with Fourier support in $[-1/12,1/12]$ |
| Kernel density | $D(u)=\gamma(u)\,H_{\lfloor u\rfloor}$, vanishing for $u<2$ |
| Real cell kernel | $R(t)=\tfrac12\bigl(K(t)+K(1-t)\bigr)$, $K(t)=\sum_{j\ge1}H_j\,\gamma(j+t)$ on $[0,1]$ |

### 2.6 Scales and weights

| Envelope $\beta$ | Physical weight | Prime majorant $\Lambda(r)/r^{\beta+1/2}$ | Polar $s=1$ weight $j^{-\beta}$ |
|---|---|---|---|
| $3/2$ (canonical tail) | $v^{-4}$ | summable | summable |
| $(1,2]$ | $v^{-(2\beta+1)}$ | summable | summable |
| $(1/2,1]$ | $v^{-(2\beta+1)}$ | summable | divergent, needs rank-one pole cancellation |
| $1/2$ (critical) | $v^{-2}$ | divergent as an absolute bound | divergent |

The logarithmic majorant $\log r/r^{\beta+1/2}$ is summable iff $\beta>1/2$.
The oscillatory majorant $\Lambda(r)/(r^{\beta+1/2}(r-1))$, obtained after one
integration by parts, is summable for all $\beta>-1/2$, so the critical line
$\beta=1/2$ is a failure of the absolute bound, not of the prime channel.

### 2.7 Glossary

| Object | Lean name |
|---|---|
| clamped kernel $C$, periodic extension | `clampedLatticeRemainder`, `periodicClampedKernel` |
| dyadic filter $P$, $P_0=P-3/16$, sign $\chi$, weight $w_k$ | `dyadicBernoulliFilter`, `dyadicCenteredBernoulliFilter`, `dyadicHarmonicChi`, `dyadicHarmonicWeight` |
| divisor stencil filter, multipliers, drifts | `divisorBernoulliFilter`, `divisorHarmonicMultiplier`, `divisorLinearDrift`, `divisorQuadraticDrift` |
| collar $\varepsilon_N$, width $w_N$ | `sourceFactorialCollar`, `sourceFactorialWidth` |
| $\lambda_N$, $\delta_N$, $e_N$ | `factorialShiftedFreq`, `factorialCollarShift`, `factorialAffineDefect` |
| phase profile $\Phi_N$, phase along the clock, amplitude $a_n$ | `factorialPhaseProfile`, `factorialTailPhase`, `factorialTailAmplitude` |
| correction tail $T_n$, smoothed tail $U_{n,k}$ | `factorialMuntzCorrectedTail`, `factorialMuntzSmoothedTail` |
| compact ramp $r_n$, corrected source $H_n$, $H_{n,k}$, $r_{n,k}$ | `sourceFactorialRamp`, `factorialMuntzBoundaryCorrected`, `factorialMuntzSmoothed`, `factorialMuntzSmoothedRamp` |
| coefficient $c_n$, pole functional $\Lambda_{\mathrm{pole}}$ | `factorialMuntzBoundaryCoefficient`, `factorialPoleFunctional` |
| readout $F_f(s)$, tail readout, Fourier readout | `paperFT`/`gammaOf`, `factorialTailReadout`, `factorialTailFourier` |
| $\mathcal Z$, $\mathcal W$ | `zetaZeroSquareMass`, `zetaZeroConfig.W` |
| weighted tail, translation energy, log energy, Lévy energy | `factorialWeightedTail`, `factorialTailTranslationEnergy`, `factorialTailLogTranslationEnergy`, `factorialTailLevyEnergy` |
| zero-disk overlap, strip density | `zeroDiskOverlap`, `factorialTailStripDensity` |
| harmonic layer $H_k$, combination $B_b$ | `factorialHarmonicLayer`, `factorialPhaseCombination` |
| window constants $K,L,A,J,B$ | `factorialWindowGapConstant`, `factorialWindowLength`, `factorialWeightedPhaseLower`, `factorialUnitIntervalUpper`, `factorialWeightedPhaseUpper` |
| span test $f_b$, correlation $C_b(r)$, prime atom, polar readouts | `factorialSpanTest`, `factorialSpanCorrelation`, `factorialSpanPrimeAtom`, `factorialSpanPolarZero`/`One` |
| envelope majorants | `envelopeLogMajorant`, `envelopePrimeMajorant`, `oscillatoryEnvelopePrimeMajorant`, `canonicalPrimeMajorantConstant` |
| two-parameter span energy $Q_n(c,d)$ | `factorialSpanWeil` |
| Markov form, creation potential, pairings | `markovForm`, `creationPotential`, `coshPairing`, `sinhPairing`, `hyperbolicPoleForm` |
| critical source, prime constant, polar endpoint | `criticalFactorialSource`, `criticalFactorialPrimeConstant`, `criticalFactorialPolarEndpoint` |
| $J_m$, $C_\infty(r)$, prime limit | `factorialCriticalHarmonicDefect`, `factorialCriticalCorrelationLimit`, `factorialCriticalPrimeLimit` |
| $A(m)$, $H_N$ | `factorialCriticalPrimeHarmonicCharge`, `factorialCriticalPrimeCumulativeCharge` |
| $Q_b$, $J_m(b)$, translated prime limit | `factorialCriticalPatternDensity`, `factorialCriticalPatternHarmonicMass`, `factorialCriticalTranslatedPrimeLimit` |
| $\gamma$, $D$, periodised, real and continuous kernels | `factorialCriticalPrimeKernelWeight`, `factorialCriticalPrimeKernelDensity`, `factorialCriticalPrimePeriodizedKernel`, `factorialCriticalPrimeRealKernel`, `factorialCriticalPrimeContinuousRealKernel` |
| affine model $\Psi_N$, affine error layers | `factorialAffinePhaseCombination`, `factorialAffineHarmonicError` |
| compact full energy, approximation cost, tent patterns, detector | `compactFullWeilEnergy`, `compactFullWeilApproximationCost`, `factorialTentPattern`, `factorialTentDetector` |

---

## 3. How

### 3.1 Exact arithmetic compression

Identities are used to expose structure before anything is estimated. The
divisor identity $\sum_{d\mid k}\Lambda(d)=\log k$ collapses a finite weighted
prime rectangle to a logarithmic sum whenever the support conditions hold; it
removes a distribution-of-primes question from one calculation and leaves the
sign question intact. The Bernoulli stencils compress differently: in any collar
difference $P_{D,\alpha}(\lambda v)-P_{D,\alpha}(\mu v)$ the constant mode
cancels identically, and the un-periodised polynomial part of a stencil is
$\tfrac12(\sum d\alpha(d))u-\tfrac12(\sum d^2\alpha(d))u^2$. Drift-free
stencils are classified: on $\{1,d\}$ only the zero stencil cancels both
drifts; on $\{1,q,q^2\}$ the sign-flip stencil is $(c,-2c/q^2,c/q^4)$ with
linear residual $c(1-1/q)^2$, and the drift-free stencil is
$(c,-(q+1)c/q^2,c/q^3)$. The dyadic choice is the sign-flip stencil at
$(q,c)=(2,4)$; its surviving linear slope is exactly what the compact ramp
carries.

### 3.2 Regularity through the clock, not through derivatives

The tail is not differentiable across the integer joins of $C$. Its regularity
is read through the clock: the phase $\Phi_N(Ne^{-x})$ is bounded by $25/32$
and $14$-Lipschitz in the clock variable, so a displacement $h$ of $x$ costs
$\lvert\Phi(x+h)-\Phi(x)\rvert^2\le 28N e^{-x}h$. Combined with the weight
$e^{(\sigma+1)x}$ on the enlarged strip $\sigma\in[-1/4,5/4]$ and the endpoint
jump at $x=0$, the weighted translation energy
$D_{n,\sigma}(h)=\int\lvert f(x+h)-f(x)\rvert^2dx$ obeys
$$
D_{n,\sigma}(h)\le C\min\{N^{-1},h\}\quad(0<h\le1),\qquad
\int_0^1D_{n,\sigma}(h)\frac{dh}h\le C\,\frac{1+\log N}N,
$$
with the split exactly at the arithmetic scale $h=1/N$ and the square mass
bounded by $96/N$. The logarithm is the price of the jump; an $H^1$ bound
uniform in smoothing is false.

### 3.3 Gamma–Lévy transport

The positive archimedean form is a Lévy jump integral: for every admitted
$L^1\cap L^2$ source the Gamma excess $\int2(\gamma_H(2\pi\xi)-\gamma_H(0))\lvert\hat f(\xi)\rvert^2d\xi$
equals $\int_0^\infty\omega(h)D(h)\,dh$ with a positive density $\omega(h)\le1/h$
near zero and finite mass beyond unit displacement. The logarithmic translation
budget therefore bounds the complete Gamma energy by $(C+384A)(1+\log N)/N$,
and the global comparison of the archimedean weight with $1+\log^+\lvert\xi\rvert$
converts this into a logarithmic Fourier budget uniform over the whole
enlarged strip.

### 3.4 Zero-divisor sampling

Three steps turn Fourier energy into a bound on $\mathcal Z$ without any zero
location.

1. **Local holomorphy.** The tail readout is holomorphic on $\Re s>-1$, so the
   subharmonic mean-value inequality on the disk of radius $1/4$ around any
   point of the closed strip $0\le\Re s\le1$ gives
   $\tfrac\pi{16}\lvert F(\rho)\rvert^2\le\int_{B(\rho,1/4)}\lvert F\rvert^2$.
   Entire-function versions of this inequality are not applicable and are not
   used.
2. **Multiplicity-exact overlap.** The number of divisor copies whose disks
   contain a point $s$ is at most the unit-height packet count at height
   $\Im s$, which is $O(\log(2+\lvert\Im s\rvert))$ unconditionally; outside
   the strip $-1/4\le\Re s\le5/4$ the overlap is zero.
3. **Strip energy.** On every vertical line the logarithmically weighted
   readout energy is $O((1+\log N)/N)$ by §3.3, the strip has width $3/2$,
   and Fubini is justified before the area integral is used.

The result is the **logarithmic sampling theorem**: one constant $C$ with
$\mathcal Z(T_n)+\mathcal Z(U_{n,k})\le C(1+\log N)/N$ for all $n,k$, both sums
proved summable. The corrected source is one logarithm cheaper,
$\mathcal Z(H_{n,k})\le C_H/N$, because its readout is the single mode $c_n/\rho$
and $\sum m_\rho/\lvert\rho\rvert^2$ converges. The logarithm is sharp: the
eventual tail diagonal $\Re\mathcal W(U_{n,k},U_{n,k})\ge\log N/(2048N)$ forces
$\mathcal Z(U_{n,k})\gtrsim\log N/N$, so physical mass $O(1/N)$ underestimates
spectral sampling by exactly a logarithm, and an absolute $\delta>0$ with
$\Re\mathcal W(U,U)\ge\delta\mathcal Z(U)$ holds eventually in $n$, then in $k$.

### 3.5 Independent control of mixed terms

Positivity transfers across an exact decomposition $r=h-u$ through the
independent comparison form, never through $\mathcal W$ itself:
$$
\Re\mathcal W(u,u)\ge\delta\mathcal Z(u),\quad \mathcal Z(h)\le\varepsilon\mathcal Z(u)
\ \Longrightarrow\
\Re\mathcal W(r,r)\ge(\delta-\varepsilon-2\sqrt\varepsilon)\,\mathcal Z(u),
$$
using only $\Re\mathcal W(h,h)\ge-\mathcal Z(h)$. The factor is positive iff
$\varepsilon<(\sqrt{1+\delta}-1)^2$, and a two-mode involution pair attains
equality, so the Krein stability radius is sharp. On the factorial family the
scales separate: $\mathcal Z(H)=O(1/N)$ against $\log N/N$ for the tail gives
$\Re\mathcal W(r_{n,k},r_{n,k})\ge\log N/(4096N)$ for the smoothed compact
ramp, eventually in $n$ then $k$, together with a uniform upper bound
$O((1+\log N)/N)$. The mollifier is removed by **complete energy continuity**:
normalised averaging contracts every squared translation increment, so the
singular Lévy integrand is dominated; a common compact support fixes the finite
prime set and the polar windows; hence $Q(\eta_k*r_n)\to Q(r_n)$ with all
channels included. Finally the two-dimensional ramp–tent Gram form
$Q_n(c,d)=A_nc^2+M_ncd+D_nd^2$ with $D_n\ge N$ and $M_n\to0$ has
$$
Q_n(c,d)\ \ge\ \frac{\log N}{8192N}c^2+\frac N2d^2
\qquad\text{eventually in }n,\ \text{for all real }c,d,
$$
and the binary Schur law $Q\ge0\iff M^2\le4AD$ (with the explicit negative
direction $(2D,-M)$ otherwise) is the exact criterion behind it.

### 3.6 Rank-one pole readout and the pole-free hyperplane

For any finite family, $F_{\sum a_nH_{n,k}}(\rho)=F_{\eta_k}(\rho)\,\Lambda_{\mathrm{pole}}(S,a)/\rho$
with $\Lambda_{\mathrm{pole}}(S,a)=\sum a_nc_n$. Consequences: the corrected
sources span at most one dimension in the zero-side evaluation space at fixed
smoothing; the unsmoothed combination vanishes at a zero iff
$\Lambda_{\mathrm{pole}}=0$; on that hyperplane the ramp combination and the
negated tail combination have identical readouts, identical $\mathcal Z$ and
identical zero-side Weil energy; and
$\mathcal Z(H_{S,a,k})=4\lvert\Lambda_{\mathrm{pole}}\rvert^2\mathcal Z(H_{0,k})$,
so one smoothing threshold, independent of $S$ and $a$, makes every corrected
combination zero-side nonnegative, strictly positive iff off the hyperplane.
Two distinct scales always give a nonzero pole-free vector. This is where
cross-scale positivity must be won: the pole correction costs nothing there and
the whole question is the tail Gram matrix.

### 3.7 Harmonic layers and separated frequencies

Within a fixed harmonic $k$, the four branches are separated by $k/15$, so
Montgomery–Vaughan interval estimates give, for every dilation $r\ge1$ and
window $[a,a+\ell]$,
$(\ell-K/k)\sum\lvert b_N\rvert^2\le\int_a^{a+\ell}\lvert H_k(rv)\rvert^2\le(\ell+K/k)\sum\lvert b_N\rvert^2$
with $K=390/\pi$. First-harmonic dominance then yields three coercivity laws,
all uniform in the number, size and spacing of the source indices:

- **Bohr coercivity.** The Bohr square mean of $B_b$ exists and is at least
  $\sum\lvert b_N\rvert^2/(8\pi^4)$; shifted and integer harmonics are
  Bohr-orthogonal because every $k\lambda_N$ is irrational; the tails $T_n$ are
  linearly independent.
- **Window coercivity.** On every window of length $L=16K$,
  $\int_a^{a+L}\lvert B_b\rvert^2\ge(L/16\pi^4)\sum\lvert b_N\rvert^2$, and for
  every $r\ge1$, $\int_a^{a+\ell}\lvert B_b(rv)\rvert^2\le(49/4\pi^4)(\ell+K)\sum\lvert b_N\rvert^2$.
- **Physical Riesz bounds.** With $A=L/(16\pi^4(1+L)^4)$ and
  $B=49(1+K)/(3\pi^4)$,
  $144A\sum\lvert c_n\rvert^2/(n+1)\le\bigl\|\sum c_nT_n\bigr\|_2^2\le225B\sum\lvert c_n\rvert^2/(n+1)$.

Physical coercivity is not spectral coercivity: it is the raw material that the
next mechanism converts.

### 3.8 Nonstationary Mellin exclusion and high-scale span coercivity

The readout of a span test is $F_b(t)=\int_1^\infty v^{-5/2}B_b(v)e^{-it\log v}dv$.
For $\lvert t\rvert\le\lvert\omega\rvert/2$ the phase $\omega v-t\log v$ has no
stationary point on $v\ge1$, and two integrations by parts give
$\bigl\lvert\int_1^\infty v^{-5/2}e^{i(\omega v-t\log v)}dv\bigr\rvert\le5/\lvert\omega\rvert$.
Summing the harmonics with $\sum k^{-3}\le3/2$ gives
$\lvert F_b(t)\rvert\le D\sum\lvert b_N\rvert/N$, $D=15/\pi^3$, in the band
$\lvert t\rvert\le\pi M$ when all indices are at least $M$; Cauchy–Schwarz with
$\sum_{N\ge M}N^{-2}\le2/M$ makes the band carry less than half of the
Plancherel mass guaranteed by §3.7. Outside the band the Gamma bracket is at
least $\log(\eta M)-G_0$, so the archimedean energy grows like $\log M$. The
prime channel is paid through the exact correlation
$C_b(r)=r^{-3/2}\int_1^\infty v^{-4}B_b(v)\overline{B_b(rv)}dv$,
$\lvert C_b(r)\rvert\le Br^{-3/2}\sum\lvert b_N\rvert^2$, hence
$\lvert T_\Lambda\rvert\le2B\sum_{r\ge2}\Lambda(r)/r^2\cdot\sum\lvert b_N\rvert^2$; the
polar channel through unit-interval bounds on $\int_1^\infty v^{-2}B_b$ and
$\int_1^\infty v^{-3}B_b$, giving $6J\sum\lvert b_N\rvert^2$. With the exact
explicit formula for raw tail combinations, proved by passing every channel
through the smoothing limit and splitting complex coefficients into real and
imaginary parts, the **high-scale span coercivity** follows:
$$
\Re\mathcal W(f_b,f_b)\ \ge\ \Bigl(\frac A2\log M-C\Bigr)\sum_N\lvert b_N\rvert^2
\qquad\text{for every finite }b\text{ supported on }N\ge M\ge2,
$$
with absolute $A>0$, $C\ge0$ and an absolutely convergent zero sum. The span
is positive without RH once $M>e^{2C/A}$; it is a restricted span, not a dense
one.

### 3.9 Hyperbolic pole parity decoupling

$C(g)$ vanishes on odd tests and $S(g)$ on even tests, so on $cg_e+dg_o$ the
pole plane splits without cross term into $c^2C(g_e)^2/2-d^2S(g_o)^2/2$. Even
tests are stabilised, $\mathcal W(g)\ge\mathcal M_N(g)$; odd tests carry the
whole anti-Markovian risk, $\mathcal W(g)=\mathcal M_N(g)-S(g)^2/2$, with
$\mathcal W(g)\ge0\iff S(g)^2\le2\mathcal M_N(g)$. The creation potential is
antitone in the aperture, $V_{N_1}-V_{N_2}=2\sum_{N_1<n\le N_2}\Lambda(n)/\sqrt n$,
so the Markovian floor drifts down as the prime cutoff opens.

### 3.10 Arithmetic of the collar

The cubic $4\lambda_N^3=N^2(4N+1)$ is the arithmetic skeleton. Consecutive
integer cubes never differ by one and $4N$ is coprime to $4N+1$, so
$1+\varepsilon_N$ and every $k\lambda_N$ are irrational; two shifted harmonics
resonate iff $k^3N^2(4N+1)=\ell^3M^2(4M+1)$. Finer structure is affine: for
$a\le N$, $b\le M$,
$$
\lvert a\lambda_N-b\lambda_M\rvert<\tfrac1{15}\iff a(12N+1)=b(12M+1),
$$
with a residual gap in $[r/(400M),r/(140M)]$ on the resonant branch, and exact
equality forces $N=M$, $a=b$ through the factorisation
$(N-M)[144NM(N+M)+4N^2+40NM+4M^2+N+M]$. The prime-thirteen family
$N=13M+1$ has gaps tending to zero: its critical physical correlation
$\int_1^\infty v^{-2}e^{2\pi ig_Mv}dv$ tends to one although every fixed-scale
Bohr mean is zero. A uniform cross-scale oscillatory gain is therefore false,
and what survives is the classification. Mixed aliases are excluded by the
stencil: $\lvert\chi(k)\rvert/12\le\lvert k\lambda_N-J\rvert+k/(140N)$ for
every integer $J$. The **affine comparison** replaces $\lambda_N$ by $N+1/12$:
for each harmonic the native frequency intervals $[k\lambda_N,k(N+1/12)]$ are
disjoint across $N$, the whole-line energy of the error layer is exactly
$2\pi^2k\sum e_N\lvert b_N\rvert^2$, and
$\int_1^\infty v^{-2}\lvert\sum b_N(\Phi_N-\Psi_N)\rvert^2\le(4Z^2/\pi^2)\sum e_N\lvert b_N\rvert^2\le(Z^2/35\pi^2)\sum\lvert b_N\rvert^2/N$
with $Z=\sum\lvert\chi(k)\rvert/k^{3/2}$ and no loss in the support
cardinality. Baker's theorem separates the collar spectrum from the prime
spectrum absolutely: $\lambda_N$ is algebraic of degree three, every
$\overline{\mathbb Q}$-combination of prime logarithms is transcendental, the
logarithmic width $w_N$ is transcendental, and the two spectra never meet.

### 3.11 The critical scale

At $\beta=1/2$ the absolute prime majorant diverges, so admission must come
from oscillation. The bounded lattice primitive $G$ of $F=\sum b_n\Phi_{n+1}$
($G'=F$ on $v>0$, $\lvert G\rvert\le P:=12\sum\lvert b_n\rvert/(n+1)$), together
with right-derivative bounds $\lvert F\rvert\le A:=2\sum\lvert b_n\rvert$,
$\lvert F'_+\rvert\le L:=14\sum(n+1)\lvert b_n\rvert$, gives one dilation power:
$\bigl\lvert\int_1^\infty v^{-2}F(v)F(rv)dv\bigr\rvert\le P(4A+L)/r$. Since the
physical correlation at $\log r$ is $r^{-1/2}$ times this integral, every prime
atom is bounded by $K\Lambda(r)/r^2$ and the complete prime channel of the
critical source converges absolutely. Translating a fixed pattern $b_j$ to
scales $N+j$ keeps the constant $K=12B_1(8B_1+14B_w)$ independent of $N$.

**Correlation and prime limits.** Cosine decay separates the fast carriers
$kN$, $rlN$ from the slow collar detuning; the surviving pairs are the dilation
resonances $k=rl$, and
$$
C_\infty(r)=\frac4{\pi^4}\sum_{l\ge1}w_{rl}w_l\,J_{rl},\qquad
\lim_{N\to\infty}\sum_{r\ge2}\frac{\Lambda(r)}{\sqrt r}\,\mathrm{autocorr}(g_N)(\log r)
=\sum_{r\ge2}\frac{\Lambda(r)}rC_\infty(r)
=\frac4{\pi^4}\sum_{m\ge1}\frac{A(m)J_m}{m^4}.
$$
$C_\infty(r)$ is positive for odd $r$, negative for $r\equiv2\pmod4$, zero for
$4\mid r$: every odd prime power pushes one way, the prime two the other, and
higher powers of two vanish. Regrouping by $m=rl$ is absolutely convergent
(the summand is at most $2\Lambda(r)/(r^3l^4)$), and the divisor charge is
rigid: $A(2)=-2\log2$ is the unique negative charge, $A(m)=0$ iff $m=1$ or
$4\mid m$, $A(m)>0$ otherwise, with $A(2n)=\sum_{d\mid n}d\Lambda(d)-2\log2$
for odd $n$ and $\lvert A(m)\rvert\le m\log m$.

**Translated patterns.** For a finite real pattern the same limit holds with
$J_m$ replaced by $J_m(b)$, and the masses are uniformly comparable to the
coefficient energy $E_b=\sum b_j^2$:
$$
\frac{E_b}{48}\le J_m(b)\le4E_b\quad(m\ge1),\qquad
P_\infty(b)=\frac4{\pi^4}\sum_m\frac{A(m)J_m(b)}{m^4},\qquad
\lvert P_\infty(b)\rvert\le\frac{16}{\pi^4}\Bigl(\sum_{r\ge2}\frac{\Lambda(r)}{r^2}\Bigr)\Bigl(\sum_l\lvert w_l\rvert\Bigr)E_b .
$$
The upper bound uses exact unit-cell Parseval, $\int_j^{j+1}Q_b(mv)dv=E_b$;
the lower bound uses the twelve-unit collar $[12,24]$, on which the mixed
frequencies $m(i-j\pm1/12)$ make integer numbers of periods and
$\int_{12}^{24}(1-\cos(2\pi mv/12))Q_b(mv)dv=12E_b$. Hence the limiting prime
form is bounded in coefficient $\ell^2$ independently of the number and
positions of offsets, and every harmonic sign is rigid; the sign of the total is
not determined by this.

**Kernel representations.** Changing variables, $J_m(b)=m\int_{u>m}\gamma(u)Q_b(u)du$,
so after a justified Fubini (the cubic series $\sum\lvert A(m)\rvert/m^3$
converges)
$$
P_\infty(b)=\frac4{\pi^4}\int_{\mathbb R}D(u)Q_b(u)\,du=\frac4{\pi^4}\int_0^1R(t)Q_b(t)\,dt,
$$
where $R$ is the reflected unit-cell periodisation of $D$; a continuous
representative with matching endpoint values agrees with it on the open cell.
The cumulative charge changes sign exactly once: $H_N=0$ for $N\le1$, $H_N<0$
for $2\le N\le4$ with minimum $H_2=-\log2/4$, and $H_N>\log2/150$ for $N\ge5$
(from $3^2>2^3$ and $5^4>2^9$). Hence $D=0$ on $(-\infty,2)$,
$D\ge-(\log2/4)\gamma$ everywhere, and $D\ge(\log2/150)\gamma$ on $[5,\infty)$:
the negative support of the physical kernel is confined to the three cells
$[2,5)$. The weight has exact total mass $\int_0^\infty\gamma Q_b=(\pi^2/12)E_b$,
because the band-limited $\gamma$ kills every nonzero integer frequency of $Q_b$.

**Sign results.** Exact harmonic bounds, $J_m=m[\pi^2/12-\int_0^m\gamma]$,
$\lvert J_m-1\rvert\le2/\theta$ and
$J_m\le1+\sin\theta/\theta+2(1-\cos\theta)/\theta^2$ at $\theta=\pi m/6$, give
$J_2\ge10/9$, $J_3,J_5\le4/3$, $J_6\le7/6$, explicit rational bounds through
harmonic nineteen and a uniform budget beyond, while $\lvert A(m)\rvert\le m\log m$
and $\int_{19}^\infty\log x/x^3dx$ control the tail. The outcome is
$\sum_mA(m)J_m/m^4\le-\log2/390$: the complete limiting prime form of every
unit singleton is strictly negative, with every prime power and harmonic
retained. Because the Weil form subtracts the prime channel, this is a negative
*prime* direction, not a negative Weil direction. In the other direction, any
finite harmonic truncation containing $m=2$ is a lower bound for $P_\infty(b)$,
and the $\{2,3,5\}$ truncation gives the sufficient positivity criterion
$(\log2/8)J_2(b)\le(\log3/27)J_3(b)+(\log5/125)J_5(b)$.

### 3.12 Quantitative full-form stability and native detection

For compact real sources with value bounds $M_f,M_g$, Lipschitz bounds
$K_f,K_g$ and $L^1$ distance $\Delta$, the identity
$R_f(t)-R_g(t)=\int(f-g)(x)[f(x+t)+g(x-t)]dx$ controls every channel at once:
$$
\lvert Q(f)-Q(g)\rvert\le\Delta\bigl[(M_f+M_g)(\lvert\Omega(0)\rvert+2\,\mathrm{mass}(N))+(K_f+K_g)\mathcal J\bigr],
\qquad \mathcal J=\int_0^\infty\frac{t\,e^{t/2}}{\sinh t}dt,
$$
where $\mathrm{mass}(N)$ is the literal prime-plus-polar budget on the common
support and the prime tail vanishes by support rather than being dropped. For a
finite translated pattern of factorial tents the mollifier error is
$\le C(R,M,K)/(k+1)$ with explicit dependence on radius, value and slope
moments, so one accuracy index pays for arbitrary simultaneous growth of
support, scales, translations and coefficients. The same smoothed family
detects a complete model configuration: the period difference
$\tau_n(x)-\tau_n(x-L)$ annihilates the entire on-line lattice $1/2+2\pi ik/L$
and sees a reflected pair $1/2\pm\delta+2\pi i/L$ with
$\Re\mathcal W_{\mathrm{model}}\le-(e^{\delta L}-1)(1-e^{-\delta L})e^{-6\delta/(n+1)}$
once $n\ge\lceil32\pi/L\rceil$, with the full square diagonal $Z$ and reflection
defect $\lvert U-V\rvert^2=Z-\Re\mathcal W_{\mathrm{model}}$ retained. The
model does not carry the Euler product; detection there is a calibration of the
test family, not a statement about $\zeta$.

### 3.13 Bridges

Three connections place the theory inside the wider corpus. Unconditional
zero-density inputs replace the abscissa-blind $O(\log T)$ count of §3.4 by
Ingham–Huxley and density-hypothesis exponents on abscissa slabs, Route-T
zero-free annihilation above $1-\mathrm{width}$, Selberg's exponential near-line
counts at distance $a/\log T$ from the line, and the Nyquist law that a
$C^2$ test of support radius $a$ detects an off-line vertical lattice of period
$L$ iff $a>L/2$. Baker's theorem supplies the spectral disjointness of §3.10.
The square-root-threshold bridge records that RH is equivalent to the localized
prime-tail inequality $\Re\Pi_f(\xi)\le\Re A_f(\xi)$ for all apertures, profiles
and heights, equivalently to a $2\times2$ pole compression, while every compact
$C^2$ profile is unconditionally positive at all sufficiently large heights and
the archimedean–pole budget cannot be frozen at height zero.

---

## 4. Traps and sharp boundaries

| Trap | Why it fails |
|---|---|
| Cauchy–Schwarz on $\mathcal W$ itself | Needs $\mathcal W\ge0$ on the span. Use $\lvert\mathcal W(f,g)\rvert\le\sqrt{\mathcal Z(f)\mathcal Z(g)}$. |
| Sign from self-adjointness, a ground state, or finite negative index | None excludes a negative ground energy. |
| Replace $g$ by $\lvert g\rvert$ and keep the Markov gain | Normal contraction lowers $\mathcal M_N$ but changes the pole plane $\tfrac12C^2-\tfrac12S^2$. |
| Absorb the polar loss into the Gram error | Polar loss is $\asymp\log N/N$; the ramp–tent correction $M_n^2/(4D_n)$ is $O(\log^2N/N^2)$. |
| $H^1$ bound uniform in smoothing | The endpoint jump forbids it; only $\int_0^1D(h)\,dh/h$ is uniform. |
| $O(1/N)$ spectral budget for the tail | False: the logarithm is necessary, $\mathcal Z(U_{n,k})\asymp\log N/N$ for fine smoothing. |
| Diagonal sampling bounds control cross-scale Gram matrices | After normalisation the off-diagonal entries are $O(1)$; cancellation needs oscillation or decay $\beta>1/2$. |
| Physical Riesz bounds are spectral coercivity | Physical $L^2$ mass misses the factor $\log N$ and the low-frequency exclusion. |
| A bound at each fixed zero bounds the divisor sum | Uniformity in height and summability must be proved separately. |
| Entire-function disk inequalities on the tail readout | The readout is holomorphic only on $\Re s>-1$; use the localized half-plane version. |
| Bohr orthogonality gives uniform physical decoupling | The prime-thirteen family has gaps $\to0$ and physical correlation $\to1$ while every fixed-scale Bohr mean is zero. |
| Divergence of $\sum\Lambda(r)/r^{\beta+1/2}$ at $\beta=1/2$ means negative energy | It is failure of an absolute majorant; the oscillatory majorant converges for all $\beta>-1/2$. |
| Fixed-pattern limit justifies a growing pattern | Constants retain $B_1,B_w$ and the limit is taken at fixed $(S,b)$. |
| Harmonic signs decide the total sign | $A(2)<0$ and all other $A(m)\ge0$, but the masses $J_m(b)$ are not independent variables. |
| Negative prime channel means negative Weil form | The Weil form subtracts the prime channel; the singleton result is a negative *prime* direction. |
| Model detection is a zeta sign | The lattice-plus-pair model lacks the Euler product; it calibrates the test family only. |
| Period or Bohr averaging at fixed scale is the physical limit | It erases the slow collar phase; the correct limit keeps $1-\cos(2\pi mv/12)$. |
| Replace the conditionally convergent polar readout by a Lebesgue integral | At $\beta=1/2$ the endpoint is defined through the bounded primitive, $-G(1)+\int_1^\infty G(v)v^{-2}dv$, with cutoff error $\le(24/T)\sum\lvert b_n\rvert/(n+1)$. |
| An endpoint value of the $L^1$ periodisation is a sign witness | The $L^1$ kernel and its continuous representative differ at integers; only pattern integrals matter. |
| Zero-density bounds exclude a zero | They are upper counts; a single fixed off-line zero survives all of them. |
| The corrected-source smoothing limit is the ramp limit | Different theorems: $H_{n,k}\to H_n$ concerns the noncompact source, the ramp limit needs the common compact support. |
| The dyadic stencil is drift-free | It kills the quadratic drift and $4\mid k$; its linear drift is one, the secular ramp. |
| Rename an RH-equivalent cone, metric or contraction as a hypothesis | The arithmetic work is unchanged; only universal statements proved from source data count. |
| Functional-equation symmetry alone | Without Euler product and completion data it permits off-line zeros and negative compact directions at large aperture. |

**Lean conventions.** Everything lives in
`GaloisForLFunctions.ArithmeticPositivityTheory`; sources are imported from the
`SignedPrimePolar` namespace of the bi-scale theory and the zero divisor from
`zetaZeroConfig.carrier` with multiplicities `zetaZeroConfig.mult`. The literal
zeros are never assumed to lie on the line; only the strip is used. Readouts are
`paperFT f (gammaOf s)`. Every `tsum` is preceded by a summability theorem, and
"eventually in $n$, then in $k$" is stated with nested eventual quantifiers,
not with a hidden threshold premise. Positive-integer ranges are encoded by
natural offsets such as `n+1`; public capstones carry data parameters only and
no analytic, positivity or zero-location hypotheses. Constants are named
definitions (`factorialTailTranslationConstant`, `factorialLowFreqConstant`,
…) rather than inline numerals. No heartbeat settings are raised. RH appears
only as the conclusion of an implication or inside an equivalence.

---

## 5. The frontier

**The critical kernel sign.** The complete translated prime form is
$\frac4{\pi^4}\int_0^1R(t)Q_b(t)dt$ with $R$ explicit. A positive lower bound
on $R$ would give coefficient $\ell^2$ coercivity by Fourier orthogonality; a
uniform negative bound would give negative coercivity of the limiting prime
channel on every nonzero finite pattern. The singleton is negative with margin
$4\log2/(390\pi^4)$; the general sign is open. A candidate route proves
$\lvert H_j\rvert\le3/8$, a curvature budget $T<1/50$ for the reflected cell
series, and a mean bound $\int_0^1R\le-\log2/300$, none of which is yet a
theorem.

**The complete critical form.** The prime channel converges; the critical
polar endpoint is defined; the archimedean term at $\beta=1/2$ and a
finite-scale error strong enough for growing patterns remain to be assembled
into a sign statement for the complete form.

**All apertures.** The pole-free hyperplane makes the pole correction free;
the remaining question is the tail Gram matrix across scales, the density of
the factorial spans in the form topology, and the odd-sector capacity ratio
$S(g)^2/(2\mathcal M_N(g))$ as the support aperture grows.

**The affine model.** In period-twelve coordinates the shifted branch has
frequencies $k(12N+1)$, never multiples of four when $\chi(k)\ne0$, and the
integer branch has frequencies $12kN$; the two branches have disjoint Fourier
supports on a full period. Its coefficient maps are divisor convolutions over
$12N+1\mid m$ and $N\mid m$. The sharp error constant
$N\int_1^\infty v^{-2}\lvert\Phi_N-\Psi_N\rvert^2\to7\zeta(3)/(256\pi^2)$ is
conjectural.

---

## 6. Working in the theory

Start from the source dictionary of §2.3 and keep the clock substitution
$v=e^{-x}$ explicit: every estimate is proved on $v\ge1$ with the physical
weight $v^{-(2\beta+1)}$ and transported back. Prove integrability and
summability before integrating or summing, and prove limits in every channel
rather than in a convenient one. Reuse the corpus: Montgomery–Vaughan interval
mean squares, the scalar $\int(1-\cos tv)/v^2=\pi\lvert t\rvert$ kernel, scalar
integer-cosine orthogonality, the real $L^1$ periodisation and its zero Fourier
mode, the band-limited sinc-square identities, the Gamma–Lévy identity and the
logarithmic weight comparison, and the unit-height packet count. Search the
corpus before proving anything new, and verify each name in a scratch file in
this toolchain. State every new result at its exact scope: family, scale range,
smoothing quantifiers, and which channels are included. When a mechanism fails,
extract its strongest positive survivor as a sharp boundary or classification
before retiring it. Comments in Lean are mathematics; status, dates and logs
belong on the pipeline cards.
