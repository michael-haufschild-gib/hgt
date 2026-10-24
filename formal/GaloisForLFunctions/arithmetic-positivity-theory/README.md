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

---

## Place in the research

APT is the **source theory of the complete Weil form**. Its central distinction is between
constructing a rich family of positive sources and controlling every compact test. The former
is available on high arithmetic scales; the latter is an RH-equivalent destination. A long
support, a dense approximation scheme, and a favourable prime-channel sign do not by themselves
bridge that distinction.

The shared research has three coordinates: pairwise incidence, lag, and aperture. They describe
the same critical arithmetic form, but expose different missing estimates. APT supplies literal
sources and complete-form approximation; it does not supply a theorem that their positive
subfamilies exhaust the receiver.

| Programme | Mathematical interface with APT |
|---|---|
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Factorial Müntz sources, signed prime–polar domain, logarithmic increment energy, and countermodels for source selectivity. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Zero configurations, reflection pairing, visibility lags, and the relation between support and zero depth. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Ground-energy path and ground-state coordinates for the same complete compact form. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Prime-power pair conductances, crossing debt, and local allocation of the pole charge. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md), [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Finite arithmetic and sign-sensitive receiver estimates beyond what size-only dilation bounds can prove. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Transport in damping, aperture, and cutoff, retaining the complete signed derivative and a common horizon bound. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Tests whether the data a proposed proof reads can distinguish its target from countermodels. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Signed compensation against the whole energy; explains why an adapted norm or a positive-part bound may merely restate the destination. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Searches for arithmetic effectivity producing the definite form that APT's source estimates alone do not construct. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Converts a signed arithmetic source into energy and cross terms; asks which source estimates survive a growing aperture. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Signed close-pair cancellation of prime Dirichlet polynomials beyond the Montgomery–Vaughan threshold, averaged over height: the mean-square counterpart of the single-height prime saving that the aperture face needs (§7.3). |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | The width dictionary and the selectivity battery. The temperedness gate of §3.13 is the battery's one proved shifted-pair test, and the factorial family is one of its calibration libraries. |

`RHTower` supplies the explicit formula, zero divisor, zero-counting inputs and operator
realisations. APT's spectral-realisation question is which source space carries a positive
realisation of the complete arithmetic form. An existing self-adjoint or indefinite
realisation is not already such a construction.

Three proof routes of the RH frontier consume APT directly (§3.15): the signed prime scheduling
route FU uses the negativity of the isolated critical prime channel on linear windows; the even
pole-weight route EWU uses high-scale window positivity and the grid-tent receiver transfer;
and the Suzuki route SZ obtains a strict source-level deficit on the compact critical family.
In each case APT supplies the family and its estimate, and the route supplies the receiver.

**The shared target and its criteria.** The programmes listed above work on one object: RH as
the nonnegativity of the complete critical arithmetic form, the same form in every face. Three
criteria recur throughout this document.

- *Selectivity.* A statement that holds verbatim for the shifted pair $\zeta(s-a)\zeta(s+a)$,
  for a Beurling system with an off-line zero, or for the Liouville-twisted weight is
  infrastructure, not information about RH.
- *No archimedean subsidy.* A gain of size $\log M$ (or $\log(1/w)$) at the archimedean place
  against a bounded prime cost is nonselective by construction. What matters is growth: a subsidy
  growing with the frequency of the test is satisfied by the all-ones weight and removes the
  criterion, while a loss constant or linear in the aperture is harmless.
- *Grading.* The destination has partial values. A floor losing $C_\sigma e^{2\sigma r}$ at
  aperture $r$ gives the zero-free strip $\Re s\le\tfrac12+\sigma$; a loss bounded uniformly in
  the aperture gives RH. A partial result states which member of this family it reaches. The
  grading is two-sided: for every $\beta$ above the zero width $\Delta=\sup_\rho\lvert\Re\rho-\tfrac12\rvert$
  the complete form obeys $\hat Z(F)\ge-C_\beta(1+A)e^{2\beta A}(\int F^2+D)$ on $C^2_c$ tests
  supported in $[-A,A]$, where $D$ bounds the gauge derivative of the autocorrelation
  (`exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt`, Square-Root Threshold). In this energy
  normalisation the floor exponent and the width are one number. Every receiver of the corpus
  reads that number in its own unit (`widthDictionary_tfae`), so a result that changes only the
  unit is not progress.

A useful contribution must state its quantifiers: which sources, how many scales, which
support lengths, and which constants are uniform. Restricted positivity paid for by
archimedean growth is useful infrastructure. To reach the shared target, a bound must survive
on the complete receiver without that source-specific gain. Partial results should report a
quantitative floor or a zero-free strip, rather than describe every positive identity as
progress towards RH.

**Reading route.** Start with the two receivers in §1.2, the one-form dictionary in §2.2,
and the source/clock definitions in §2.3. Then read logarithmic sampling and relative
stability (§§3.4–3.6), the critical kernel (§3.11), the many-scale and compact mechanisms
(§§3.12–3.13), and the receiver transfer with its ledger of rate-$1/2$ floors (§3.14). §4
collects the pillar theorems. The distinction between a positive subspace and a complete test
family governs the questions of §6 and the open problems of §7.

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

**The two receivers are one functional.** Abel summation against Chebyshev's
function, compared with the density $e^s+1$ of the two poles of the completed zeta
function, gives for every $C^1$ lag weight $h$ vanishing beyond its horizon
$$
\sum_n\Lambda(n)h(\log n)-\int_0^\infty(e^s+1)h(s)\,ds
=-\int_0^\infty\Bigl(D(s)+\frac{s^2}2-s\Bigr)h''(s)\,ds .
$$
On a compact test $F$ of aperture $r$ the prime channel minus the pole plane
$\tfrac12C(F)^2-\tfrac12S(F)^2$ is exactly $\int_0^{2r}E(s)\,w_F(s)\,ds$, with the
**two-pole Chebyshev defect** $E(s)=e^s+s-1-\psi(e^s)$ and the lag weight
$w_F(s)=2e^{-s/2}\bigl(\int F(x)F'(x+s)\,dx-\tfrac12a_F(s)\bigr)$
(`sum_vonMangoldt_sub_polar_eq_criticalScalePrefix`, `testBalance_poleplane`, Arithmetic
Incidence Positivity). With the Gamma–Lévy form of §2.2 the complete form is the archimedean
energy minus this pairing. The prime channel and the pole plane cancel identically to PNT
accuracy. The capacity inequality is a family of one-sided weighted bounds on $E$, indexed by
the lag weights realisable at aperture $r$, and the critical-scale receiver reads the same
datum through $h''$. The reflected pole at $s=0$ makes the Weil-natural defect
$\psi(x)-x-\log x+1$ rather than $\psi(x)-x$, and it is the source of the factor $(1+T)$ in
receiver 1. Read as a count, $E(s)$ is the number of degrees of freedom of the two-pole plane on
the logarithmic box $[0,s]$, $\int_0^s(e^u+1)\,du$, minus the weighted prime-power node count
$\psi(e^s)$ (`polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect`, Arithmetic
Castelnuovo–Severi): the sign question is whether the primes ever outnumber the poles by more
than the critical amount.

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

The **absolute square-sampling mass**, the **zero-side Weil pairing** and the
**reflection defect** are
$$
\mathcal Z(f)=\sum_\rho m_\rho\lvert F_f(\rho)\rvert^2,\qquad
\mathcal W(f,g)=\sum_\rho m_\rho F_f(\rho)\,\overline{F_g(1-\overline\rho)},\qquad
\mathcal R(f)=\sum_\rho\frac{m_\rho}2\bigl\lvert F_f(\rho)-F_f(1-\overline\rho)\bigr\rvert^2 .
$$
Reflection $\rho\mapsto1-\overline\rho$ preserves the zero divisor with
multiplicities, so $\mathcal W$ is the inner product twisted by a unitary
involution,
$\lvert\mathcal W(f,g)\rvert\le\sqrt{\mathcal Z(f)\mathcal Z(g)}$ holds for
all square-summable sources, and the **universal reflection identity**
$$
\mathcal Z(f)-\Re\mathcal W(f,f)=\mathcal R(f)
$$
holds for every zero configuration and every square-summable source: the gap
between the trivially nonnegative mass and the Weil energy is exactly the
square distance between the readout at a zero and at its mirror image, which
vanishes on the line and only there. Summability is always proved before a
totalised sum is used; $\mathcal Z\ge0$ is trivial, $\mathcal W(f,f)\ge0$ is
never assumed. On smooth compact tests $\mathcal W(f,f)$ equals the complete
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

**Gamma–Lévy form.** With the autocorrelation $a_g(x)=\int g(y)g(y-x)\,dy$ and
the Lévy weight $\omega(x)=e^{x/2}/\sinh x$ on $x>0$, the archimedean channel is
$\Omega(0)a_g(0)+\int_0^\infty(a_g(0)-a_g(x))\,\omega(x)\,dx$, the polar channel is
twice the product of the two half-exponential moments $\int g\,e^{\pm x/2}$, and
the prime channel is $2\sum_{r\ge2}\Lambda(r)r^{-1/2}a_g(\log r)$. In this form
the energy makes sense for noncompact sources: the Lévy integral is taken in
the extended reals, so a divergent archimedean channel is $+\infty$, never
undefined, and the arithmetic channels are proved finite separately.

**One form, five names.** On continuous compact real sources the complete
physical energy coincides identically with the full zero form of Arithmetic
Criticality Theory (Markov energy minus twice the odd pole moment squared plus
twice the even one) and with the real part of the literal $\Lambda$-weighted
explicit-formula functional of the RH tower; on $C^2_c$ sources all three equal
$\Re\mathcal W(F,F)$ of the Square-Root Threshold configuration and hence
$\mathcal Z(F)-\mathcal R(F)$. Any statement proved about one of these is a
statement about all of them.

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
dominates with margin $1/4$. The centred filter $P_0=P-3/16$ is
$9/2$-Lipschitz, and $\sum_k\chi(k)^2/k^3=\tfrac{63}{64}\zeta(3)$.

**Collar and shifted frequency.** For $N\ge1$ the collar is
$\varepsilon_N=e^{w_N}-1$ with $w_N=\tfrac13\log(1+\tfrac1{4N})$, so that
$(1+\varepsilon_N)^3=1+\tfrac1{4N}$. The shifted frequency
$\lambda_N=N(1+\varepsilon_N)$ satisfies the exact cubic
$4\lambda_N^3=N^2(4N+1)$ and the collar bounds
$1/15\le\delta_N:=\lambda_N-N\le1/12$. The **affine clock** is $12N+1$ and the
**affine defect** $e_N=N+\tfrac1{12}-\lambda_N$ obeys
$Ne_N=\delta_N^2+\delta_N^3/(3N)$, hence $1/(225N)\le e_N\le1/(140N)$ and
$Ne_N\to1/144$.

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

**Spans, envelopes, critical sources.** For a finite complex family $b$ put
$B_b(v)=\sum_Nb_N\Phi_N(v)$. The **span test** is
$f_b(x)=e^{3x/2}B_b(e^{-x})\mathbf 1_{x\le0}$, and every finite combination
$\sum c_nT_n$ is the span test with $b_{n+1}=c_na_n$. Replacing $3/2$ by an
**envelope exponent** $\beta$ gives $f_\beta(x)=e^{\beta x}B(e^{-x})\mathbf 1_{x\le0}$;
the clock substitution $v=e^{-x}$ turns physical $L^2$ mass into
$\int_1^\infty v^{-(2\beta+1)}\lvert B(v)\rvert^2dv$. The canonical tail is
$\beta=3/2$ (weight $v^{-4}$); the **critical source** of a finite real pattern
$(S,b)$ is $\beta=1/2$ (weight $v^{-2}$), namely
$g_b(x)=\mathbf 1_{x\le0}e^{x/2}F_b(e^{-x})$ with $F_b=\sum_{n\in S}b_n\Phi_{n+1}$.
A pattern $b$ on an offset set $S$ **translated to scale $n$** is the pattern
$j\mapsto b_j$ on $n+S$; the **single-scale sources** $g_q$ (pattern $\{q\}$,
coefficient one) span every critical source, $g_b=\sum_{q\in S}b_qg_q$.

**Collared sources.** With $\sigma$ the smooth transition function ($0$ on
$(-\infty,0]$, $1$ on $[1,\infty)$), the **collar weight** is
$\psi(v)=\sigma(v-1)/v^2$ and the **collared critical source** is
$g^c_b(x)=\sigma(e^{-x}-1)\,g_b(x)$. It agrees with $g_b$ for $x\le-\log2$ and
vanishes for $x\ge0$; the **endpoint layer** $(-\log2,0]$ is the only place
where the two differ. The collar weight is $C^\infty$, flat at $v=1$ and equal to
$v^{-2}$ for $v\ge2$, so its cosine transform decays like $1/f^2$, while the
complementary **endpoint weight** $\varphi_e(v)=(1-\sigma(v-1))/v^2$, supported on
$[1,2]$ with a unit jump at $v=1$, has cosine transform $j(f)+e(f)$ with the
**jump kernel** $j(f)=-\sin(2\pi f)/(2\pi f)=-\tfrac12\int_{-1}^1\cos(2\pi fu)\,du$
and a remainder $\lvert e(f)\rvert\le\kappa_e/f^2$; the raw weight
$v^{-2}\mathbf 1_{v>1}=\psi+\varphi_e$ decays only like $1/f$. The collar
amplitude $\sigma(v-1)v^{-3/2}$ and the endpoint weight $\sigma(v-1)/v$ play
the same role for the readout and for the polar channel.

**Dyadic blocks.** A finite offset set $S$ is a **dyadic block at $M$** when
$M\le n+1\le2M$ for every $n\in S$; its cardinality is at most $M+1$. Dyadic
blocks are the unit on which $\ell^2$-uniform statements are made: on a block
every scale is comparable to $M$, so one logarithm $\log M$ is the common
archimedean gain and one admission constant is the common prime budget.

### 2.4 Harmonic language

Expanding each profile in its Bernoulli series,
$$
-\frac{\pi^2}2B_b=\sum_{k\ge1}w_kH_k,\qquad w_k=\frac{\chi(k)}{k^2},\qquad
H_k(v)=\sum_Nb_N\bigl(\cos(2\pi k\lambda_Nv)-\cos(2\pi kNv)\bigr).
$$
Each layer $H_k(rv)$, $r\ge1$, is an exponential sum over the four signed
branches $\pm krN$, $\pm kr\lambda_N$ with coefficients $\mp b_N/2$; the collar
bounds separate the branches by at least $k/15$, and on a dyadic block the
branches of distinct scales are separated by at least $11/12$. The weights
satisfy $w_1=1$, $\sum_{k\ge2}\lvert w_k\rvert\le3/4$, $\sum_k\lvert w_k\rvert\le7/4$.

### 2.5 Critical-scale objects

At $\beta=1/2$ the slow collar phase survives the limit $N\to\infty$ and new
arithmetic objects appear.

| Object | Definition |
|---|---|
| Harmonic defect | $J_m=\int_1^\infty v^{-2}\bigl(1-\cos(2\pi mv/12)\bigr)dv\in[0,2]$, positive for $m>0$, $J_m\to1$; exactly $J_m=m\bigl(\pi^2/12-\int_0^m\gamma\bigr)$ |
| Pattern density | $Q_b(t)=\bigl\lvert\sum_{j\in S}b_je^{2\pi ijt}\bigr\rvert^2$ for a finite real pattern $b$, period one, even |
| Pattern mass | $J_m(b)=\int_1^\infty v^{-2}\bigl(1-\cos(2\pi mv/12)\bigr)Q_b(mv)\,dv$ |
| Divisor charge | $A(m)=\chi(m)\sum_{d\mid m}d\,\Lambda(d)\,\chi(m/d)$ |
| Cumulative charge | $H_N=\sum_{1\le m\le N}A(m)/m^3$ |
| Kernel weight | $\gamma(u)=u^{-2}\bigl(1-\cos(2\pi u/12)\bigr)=2\sin^2(\pi u/12)/u^2$, a scaled sinc square with Fourier support in $[-1/12,1/12]$ |
| Poisson window | $W_m(t)=\sum_{z=-m}^{m-1}\gamma(t+z)$ and its deviation $W_m(t)-2\int_0^m\gamma$ |
| Kernel density | $D(u)=\gamma(u)\,H_{\lfloor u\rfloor}$, vanishing for $u<2$ |
| Real cell kernel | $R(t)=\tfrac12\bigl(K(t)+K(1-t)\bigr)$, $K(t)=\sum_{j\ge1}H_j\,\gamma(j+t)$ on $[0,1]$; symmetric, $R(1-t)=R(t)$ |
| Scale coupling | $\kappa(k)=\int_0^1R(t)\cos(2\pi kt)\,dt$, the cosine coefficients of the cell kernel; $\kappa(0)=\sum_mA(m)J_m/m^4$ |
| Limiting prime form | $P_\infty(b)=\lim_n\sum_{r\ge2}\Lambda(r)r^{-1/2}a_{g_b^{(n)}}(\log r)$ over translates to scale $n$ |
| Rayleigh set | $\{P_\infty(b)/\sum b_j^2\}$ over all nonzero finite real patterns |
| Dilation limit | $\mathrm{Lim}_b(\rho)=\lim_n\int_1^\infty v^{-2}F^{(n)}_b(v)F^{(n)}_b(\rho v)\,dv$ for real $\rho>0$ |
| Finite-scale prime matrix | $M_n(i,j)$, the symmetric matrix of the actual prime channel on the single-scale sources at scales $n+i$, $n+j$ |
| Complete critical energy | $E_{\mathrm{crit}}(b)=\int_0^\infty(a(0)-a(x))\omega+\Omega(0)a(0)+2\,(\text{polar readout})(\text{polar endpoint})-2\sum_r\Lambda(r)r^{-1/2}a(\log r)$, valued in $[-\infty,+\infty]$ |
| Collared channels | the same four channels for $g^c_b$, with $\psi$ in place of $v^{-2}$ in the correlation law and $\sigma(v-1)/v$ in the polar endpoint |

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

### 2.7 The tent family

The **factorial tent** $\tau_n$ is the compact source
$e^{x/2}\cdot e^{x}\,\mathrm{hat}_{d_n}(x)/d_n$, a causal hat of width
$d_n=w_{n+1}$ (the collar width of the scale) carried by the common
exponential $e^{3x/2}$. A **tent pattern** is a finite combination
$\sum_ib_i\,\tau_{n_i}(\cdot+t_i)$ of translated tents at arbitrary scales and
sites; a **grid tent pattern** uses one scale $n$ and the uniform grid
$a+jd_n$, with coefficients read from a nodal profile $G$. Because every tent
carries the same $e^{3x/2}$ and a hat is the difference of two unit ramps, a
grid pattern is exactly $e^{3x/2}$ times the piecewise-linear interpolant of
the nodal data: it is a complete test family inside the laboratory. The
**period difference** $\tau_n(x)-\tau_n(x-L)$ and its mollification, the
**tent detector**, are the tests used for lattice and cluster detection.

### 2.8 Glossary

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
| $\mathcal Z$, $\mathcal W$, $\mathcal R$ | `zetaZeroSquareMass`, `zetaZeroConfig.W`, `configurationReflectionDefect` |
| weighted tail, translation energy, log energy, Lévy energy | `factorialWeightedTail`, `factorialTailTranslationEnergy`, `factorialTailLogTranslationEnergy`, `factorialTailLevyEnergy` |
| zero-disk overlap, strip density | `zeroDiskOverlap`, `factorialTailStripDensity` |
| harmonic layer $H_k$, combination $B_b$, real combination | `factorialHarmonicLayer`, `factorialPhaseCombination`, `realPhaseCombination` |
| window constants $K,L,A,J,B$ | `factorialWindowGapConstant`, `factorialWindowLength`, `factorialWeightedPhaseLower`, `factorialUnitIntervalUpper`, `factorialWeightedPhaseUpper` |
| span test $f_b$, correlation $C_b(r)$, prime atom, polar readouts | `factorialSpanTest`, `factorialSpanCorrelation`, `factorialSpanPrimeAtom`, `factorialSpanPolarZero`/`One` |
| envelope majorants | `envelopeLogMajorant`, `envelopePrimeMajorant`, `oscillatoryEnvelopePrimeMajorant`, `canonicalPrimeMajorantConstant` |
| two-parameter span energy $Q_n(c,d)$ | `factorialSpanWeil` |
| Markov form, creation potential, pairings | `markovForm`, `creationPotential`, `coshPairing`, `sinhPairing`, `hyperbolicPoleForm` |
| critical source, single-scale source, prime constant, polar readout and endpoint | `criticalFactorialSource`, `criticalScaleSource`, `criticalFactorialPrimeConstant`, `criticalFactorialPolarReadout`, `criticalFactorialPolarEndpoint` |
| $J_m$, $C_\infty(r)$, prime limit | `factorialCriticalHarmonicDefect`, `factorialCriticalCorrelationLimit`, `factorialCriticalPrimeLimit` |
| $A(m)$, $H_N$ | `factorialCriticalPrimeHarmonicCharge`, `factorialCriticalPrimeCumulativeCharge` |
| $Q_b$, $J_m(b)$, translated prime limit $P_\infty$ | `factorialCriticalPatternDensity`, `factorialCriticalPatternHarmonicMass`, `factorialCriticalTranslatedPrimeLimit` |
| $\gamma$, $D$, periodised, real and continuous kernels | `factorialCriticalPrimeKernelWeight`, `factorialCriticalPrimeKernelDensity`, `factorialCriticalPrimePeriodizedKernel`, `factorialCriticalPrimeRealKernel`, `factorialCriticalPrimeContinuousRealKernel` |
| band weight $\gamma$ as a sinc square, window $W_m$, deviation, harmonic tail | `criticalBandWeight`, `criticalBandWindow`, `criticalBandWindowDeviation`, `factorialCriticalPrimeHarmonicTail` |
| coupling $\kappa(k)$, Rayleigh set | `factorialCriticalPrimeCoupling`, `factorialCriticalPrimeRayleighSet` |
| dilation limit $\mathrm{Lim}_b(\rho)$, polarisation | `factorialCriticalDilationLimit`, `factorialCriticalDilationPolarization` |
| finite-scale prime matrix, symmetric correlation matrix, decorrelation defect, Lévy floor | `criticalTranslatedPrimeMatrix`, `criticalTranslatedSymmetricCorrelation`, `criticalTranslatedDecorrelationDefect`, `criticalTranslatedLevyFloor` |
| autocorrelation, Lévy energy, Lévy weight $\omega$, spectral density | `criticalAutocorrelation`/`sourceAutocorrelation`, `criticalLevyEnergy`/`sourceLevyEnergy`, `archLevySinhWeight`, `criticalSpectralDensity` |
| complete critical energy (translated, general support), arithmetic channels | `criticalTranslatedCompleteEnergy`, `criticalCompleteEnergy`, `criticalArithmeticChannels` |
| logarithmic slope and offset, channel constant, relative cutoff $\eta$ | `criticalArchLogSlope`, `criticalArchLogOffset`, `criticalChannelConstant`, `lowFreqRelativeCutoff` |
| dyadic block, dilation constant $K(A,B)$, cross kernel | `DyadicScaleBlock`, `dyadicDilationConstant`, `dyadicCrossKernel` |
| collar weight, amplitude, endpoint weight, collared source | `criticalCollarWeight`, `criticalCollarAmplitude`, `criticalCollarEndpointWeight`, `criticalCollaredSource` |
| endpoint weight $\varphi_e$, jump kernel $j$, uncollared prime constant | `criticalEndpointWeight`, `dyadicJumpKernel`, `criticalPrimeChannelConstant` |
| collared prime energy and constant, polar readout and endpoint, complete energy | `criticalCollaredPrimeEnergy`, `criticalCollaredPrimeConstant`, `criticalCollaredPolarReadout`, `criticalCollaredPolarEndpoint`, `criticalCollaredCompleteEnergy` |
| general source interface | `AdmissibleSource` |
| affine model $\Psi_N$, affine error layers, collar head | `factorialAffinePhaseCombination`, `factorialAffineHarmonicError`, `factorialAffineCollarHead` |
| compact full energy, approximation cost | `compactFullWeilEnergy`, `compactFullWeilApproximationCost` |
| tent $\tau_n$, tent pattern, grid pattern, interpolant, period difference, detector | `factorialSourceRight`, `factorialTentPattern`, `gridTentPattern`, `gridInterpolant`, `factorialTentPeriodDifference`, `factorialTentDetector` |

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
equals $\int_0^\infty\omega(h)D(h)\,dh$ with the positive density
$\omega(h)=e^{h/2}/\sinh h$, which satisfies $e^{-1/2}/h\le\omega(h)\le1/h$
near zero and has finite mass beyond unit displacement. The logarithmic
translation budget therefore bounds the complete Gamma energy by
$(C+384A)(1+\log N)/N$, and the global comparison of the archimedean weight
with $1+\log^+\lvert\xi\rvert$ converts this into a logarithmic Fourier budget
uniform over the whole enlarged strip. The same identity runs in the other
direction: the Lévy symbol $\int_0^\infty(1-\cos tx)\,\omega(x)\,dx$ is at least
$e^{-1/2}(\log\lvert t\rvert-3)$, so any source whose spectral density is small
on a low band and whose mass is not has Lévy energy growing like the logarithm
of the band edge.

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
$\bigl\lvert\int_1^\infty v^{-p}e^{i(\omega v-t\log v)}dv\bigr\rvert\le5/\lvert\omega\rvert$
for every exponent $p>1$; when the amplitude vanishes at $v=1$ there is no
boundary term and the bound is $(2/\lvert\omega\rvert)(\|a'\|_1+\|a/v^2\|_1)$.
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
every integer $J$.

**The affine comparison.** Replacing $\lambda_N$ by $N+1/12$ gives the affine
model $\Psi_N$. For each harmonic the native frequency intervals
$[k\lambda_N,k(N+1/12)]$ are disjoint across $N$, the whole-line energy of the
error layer is exactly $2\pi^2k\sum e_N\lvert b_N\rvert^2$, and
$\int_1^\infty v^{-2}\lvert\sum b_N(\Phi_N-\Psi_N)\rvert^2\le(4Z^2/\pi^2)\sum e_N\lvert b_N\rvert^2\le(Z^2/35\pi^2)\sum\lvert b_N\rvert^2/N$
with $Z=\sum\lvert\chi(k)\rvert/k^{3/2}$ and no loss in the support
cardinality. This Minkowski bound is not sharp. For a single scale the error
layers of the harmonics $k\le N+1$ are exactly orthogonal in $L^2(v^{-2}dv)$ on
$v>0$: the cosine-shell Gram $\int v^{-2}L_kL_l=(\pi/2)\lvert I_k\cap I_l\rvert$
is diagonal because the frequency intervals are separated, the head energy of
the first $K$ harmonics is $\pi^2e_N\sum_{k<K}kw_k^2$ exactly, the tail beyond
$K$ is at most $4/K$, and the head on $(0,1]$ costs at most $2\pi e_N(1+\log N)$.
With $Ne_N\to1/144$ and $\sum k w_k^2=\tfrac{63}{64}\zeta(3)$ the sharp constant
is
$$
N\int_1^\infty v^{-2}\lvert\Phi_N-\Psi_N\rvert^2\,dv\ \longrightarrow\ \frac{7\,\zeta(3)}{256\,\pi^2}.
$$
Baker's theorem separates the collar spectrum from the prime spectrum
absolutely: $\lambda_N$ is algebraic of degree three, every
$\overline{\mathbb Q}$-combination of prime logarithms is transcendental, the
logarithmic width $w_N$ is transcendental, and the two spectra never meet.

### 3.11 The critical scale: admission, limits and the kernel sign

At $\beta=1/2$ the absolute prime majorant diverges, so admission must come
from oscillation. The bounded lattice primitive $G$ of $F=\sum b_n\Phi_{n+1}$
($G'=F$ on $v>0$, $\lvert G\rvert\le P:=12\sum\lvert b_n\rvert/(n+1)$), together
with right-derivative bounds $\lvert F\rvert\le A:=2\sum\lvert b_n\rvert$,
$\lvert F'_+\rvert\le L:=14\sum(n+1)\lvert b_n\rvert$, gives one dilation power:
$\bigl\lvert\int_1^\infty v^{-2}F(v)F(rv)dv\bigr\rvert\le P(4A+L)/r$. Since the
physical correlation at $\log r$ is $r^{-1/2}$ times this integral, every prime
atom is bounded by $K\Lambda(r)/r^2$ and the complete prime channel of the
critical source converges absolutely. Translating a fixed pattern $b_j$ to
scales $N+j$ keeps the constant $K=12B_1(8B_1+14B_w)$ independent of $N$; on a
dyadic block the constant is at most $384B_1^2$ with $B_1=\sum\lvert b_j\rvert$.
The same integration by parts bounds both polar readouts of the critical
source by $24\sum\lvert b_n\rvert/(n+1)$, so the polar channel is $O(1/N)$ on
translates and vanishes in the limit.

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

**The rational dilation law.** The same cosine-decay argument runs at every
real dilation $\rho>0$: the complete critical correlation
$\int_1^\infty v^{-2}F^{(n)}_b(v)F^{(n)}_b(\rho v)\,dv$ of a translated pattern
converges to the resonance sum over harmonic pairs $k=\rho l$,
$$
\mathrm{Lim}_b(\rho)=\frac4{\pi^4}\sum_{k=\rho l}w_kw_l\,J_k(b),
$$
which vanishes at every irrational $\rho$ and equals
$(4/\pi^4)\sum_tw_{pt}w_{qt}J_{pt}(b)$ at a reduced fraction $p/q$. Hence the
limiting autocorrelation of a translated critical source at shift $x$ is
$e^{-x/2}\mathrm{Lim}_b(e^x)$: the critical limit has a **rational spectrum**,
with atoms exactly at $\log(p/q)$. The prime channel sees only the integer atoms
$\log r$; the atoms at $\log(3/2)$ and every other non-integer rational feed
the archimedean channel alone. At $\rho=1$ the limit is the mass
$\mu_\infty(b)=\mathrm{Lim}_b(1)\ge\sum b_j^2/(12\pi^4)$.

**Translated patterns.** For a finite real pattern the prime limit holds with
$J_m$ replaced by $J_m(b)$, and the masses are uniformly comparable to the
coefficient energy $E_b=\sum b_j^2$:
$$
\frac{E_b}{48}\le J_m(b)\le4E_b\quad(m\ge1),\qquad
P_\infty(b)=\frac4{\pi^4}\sum_m\frac{A(m)J_m(b)}{m^4},\qquad
\lvert P_\infty(b)\rvert\le\frac{16}{\pi^4}\Bigl(\sum_{r\ge2}\frac{\Lambda(r)}{r^2}\Bigr)\Bigl(\sum_l\lvert w_l\rvert\Bigr)E_b .
$$
The upper bound uses exact unit-cell Parseval, $\int_j^{j+1}Q_b(mv)dv=E_b$;
the lower bound uses the twelve-unit collar $[12,24]$, on which the mixed
frequencies $m(i-j\pm1/12)$ make integer numbers of periods. Hence the limiting
prime form is bounded in coefficient $\ell^2$ independently of the number and
positions of offsets, and every harmonic sign is rigid; the sign of the total
is decided by the kernel below.

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

**The singleton mean.** Exact harmonic bounds, $J_m=m[\pi^2/12-\int_0^m\gamma]$,
$\lvert J_m-1\rvert\le2/\theta$ and
$J_m\le1+\sin\theta/\theta+2(1-\cos\theta)/\theta^2$ at $\theta=\pi m/6$, give
$J_2\ge10/9$, $J_3,J_5\le4/3$, $J_6\le7/6$, explicit rational bounds through
harmonic nineteen and a uniform budget beyond, while $\lvert A(m)\rvert\le m\log m$
and $\int_{19}^\infty\log x/x^3dx$ control the tail. The outcome is
$\kappa(0)=\sum_mA(m)J_m/m^4\le-\log2/390$: the complete limiting prime form of
every unit singleton is strictly negative, with every prime power and harmonic
retained. Any finite harmonic truncation containing $m=2$ is a lower bound for
$P_\infty(b)$, and the $\{2,3,5\}$ truncation gives the sufficient positivity
criterion $(\log2/8)J_2(b)\le(\log3/27)J_3(b)+(\log5/125)J_5(b)$.

**The kernel is a near-constant: Poisson closes the cell.** The band-limited
weight obeys the exact Poisson identity $\sum_{z\in\mathbb Z}\gamma(t+z)=\pi^2/6$
for every real $t$, because the triangle spectrum of $\gamma$ vanishes at every
nonzero integer. Therefore the reflected harmonic tails
$T_m(t)=\sum_{j\ge0}\gamma(j+m+t)$ close on a finite window,
$T_m(t)+T_m(1-t)=\pi^2/6-W_m(t)$, and summation by parts against the
cumulative charge gives the exact cell formula
$$
R(t)=\sum_m\frac{A(m)J_m}{m^4}-\frac12\sum_m\frac{A(m)}{m^3}\Bigl(W_m(t)-2\int_0^m\gamma\Bigr).
$$
The window deviation is uniformly small: through the triangle representation
$\gamma(u)=\int_0^{\pi/6}(\pi/6-\xi)\cos(\xi u)\,d\xi$ and Dirichlet
telescoping, $\lvert W_m(t)-2\int_0^m\gamma\rvert\le\min\{(\pi/6)^3/35,\ m(\pi/6)^4/70\}$
for all $m$ and $t$. The mean dominates the curvature correction, and
$$
R(t)\le-\frac1{7000}\quad(0\le t\le1),\qquad
P_\infty(b)\le-\frac4{7000\,\pi^4}\sum_jb_j^2\ \text{ for every finite real pattern},
$$
strictly for nonzero patterns. Because the Weil form subtracts the prime
channel, the limiting critical prime channel contributes a uniformly
positive-definite amount to the complete critical form. The masses $J_m(b)$ are
not independent variables, but they do not need to be: the sign of the whole is
decided by the singleton mean because the kernel barely moves across the cell.

**Toeplitz symbol and spectral range.** The cell kernel is symmetric, its sine
moments vanish, and its Fourier coefficients on the cell are exactly the
couplings $\kappa(\lvert n\rvert)$, so
$$
P_\infty(b)=\frac4{\pi^4}\sum_{i,j\in S}b_ib_j\,\kappa(\lvert i-j\rvert),\qquad
R(t)=\sum_{n\in\mathbb Z}\kappa(\lvert n\rvert)\cos(2\pi nt),
$$
with $\kappa(k)=\sum_m(A(m)/m^3)\int_0^{\pi/6}(\pi/6-\xi)\,\xi\sin(m\xi)/(4\pi^2k^2-\xi^2)\,d\xi$
for $k\ge1$ and $\lvert\kappa(k)\rvert=O(1/k^2)$ (window cosine moments
telescope to $\int_{-m}^m\gamma(u)\cos(2\pi ku)\,du$). Translated scales
interact in the limiting prime channel only through this single
$1/k^2$-decaying coupling; the singleton value is the exact isotropic part and
$\lvert P_\infty(b)-(4/\pi^4)\kappa(0)E_b\rvert\le(4/\pi^4)\bigl(\sum_{k\ge1}2\lvert\kappa(k)\rvert\bigr)E_b$
uniformly in the pattern. Evaluating the band sine moments
$\mu_m=\int_0^{\pi/6}(\pi/6-\xi)\xi\sin(m\xi)\,d\xi=(2(1-\cos\frac{m\pi}6)-\frac{m\pi}6\sin\frac{m\pi}6)/m^3$
in closed form (`criticalBandSineMoment_eq`) shows that the spectral curvature constant
$I_0=\sum_m(A(m)/m^3)\mu_m$ satisfies $11/10000\le I_0\le 52/10000$
(`criticalKernelCurvatureConstant_bounds`), while the absolute sine moment series is bounded by
$M_{\mathrm{abs}}\le 19/1000$ (`criticalKernelAbsMoment_le`). A unified spectral perturbation bound
(`abs_tsum_charge_band_integral_sub_le`) then gives both the two-sided $1/k^2$ law for the scale
couplings,
$\lvert\kappa(k)-I_0/(4\pi^2k^2)\rvert\le(14/100000)/(4\pi^2k^4)$ (`abs_factorialCriticalPrimeCoupling_sub_le`,
hence $\kappa(k)>0$ for all $k\ge1$, $1/50000\le\kappa(1)\le1/6000$, and
$1/200000\le\kappa(2)\le1/24000$), and the quadratic difference bounds on $[0,1/2]$,
$$
\frac7{20000}\Bigl(\bigl(\tfrac12-t_1\bigr)^2-\bigl(\tfrac12-t_2\bigr)^2\Bigr)\ \le\ R(t_1)-R(t_2)\ \le\
\frac{56}{20000}\Bigl(\bigl(\tfrac12-t_1\bigr)^2-\bigl(\tfrac12-t_2\bigr)^2\Bigr)
\qquad\bigl(0\le t_1\le t_2\le\tfrac12\bigr)
$$
(`factorialCriticalPrimeContinuousRealKernel_sub_bounds`). In particular, $R$ is strictly decreasing
on $[0,1/2]$ and strictly increasing on $[1/2,1]$, with unique global minimum $\min_{[0,1]}R=R(1/2)$
attained only at $t=1/2$ and global maximum $\max_{[0,1]}R=R(0)=R(1)$ attained only at $t\in\{0,1\}$,
and explicit distances $7/120000\le R(0)-\kappa(0)\le 56/120000$ and
$7/240000\le\kappa(0)-R(1/2)\le 56/240000$ from the singleton mean
([ExplicitCollarThresholdsAndKernelShape](ExplicitCollarThresholdsAndKernelShape.lean)). The Cesàro
means of the long modulated patterns $b_j=\cos(2\pi jt)$, $\sin(2\pi jt)$ on $j<L$ give
$(P_\infty(\cos_L)+P_\infty(\sin_L))/L\to(4/\pi^4)R(t)$, so the Rayleigh set has exact supremum
$(4/\pi^4)R(0)$ and exact infimum $(4/\pi^4)R(1/2)$ (`isLUB_factorialCriticalPrimeRayleighSet_exact`,
`isGLB_factorialCriticalPrimeRayleighSet_exact`): the exact $\ell^2$ spectral range of the limiting
prime form over all finite patterns is $[(4/\pi^4)R(1/2),(4/\pi^4)R(0)]$, the optimal negativity
constant is $-(4/\pi^4)R(0)$, and the extremal patterns are long frequency-modulated patterns
concentrating at $t\in\{0,1\}$ and $t=1/2$. Sign and size questions about the limiting critical
prime channel are pointwise questions about $R$.

**Finite-scale negativity and the linear window.** The actual prime energy of a
pattern translated to scale $n$ is the quadratic form of the finite-scale prime
matrix $M_n(i,j)$, obtained by expanding the translated autocorrelation
bilinearly in the single-scale sources; polarisation of the translated prime
limit gives $M_n(i,j)\to(4/\pi^4)\kappa(\lvert i-j\rvert)$ entrywise. Hence for
every finite support $S$, eventually in $n$ and for all coefficient vectors at
once, the von Mangoldt channel on the span of the critical sources at scales
$n+S$ is at most $-(2/(7000\pi^4))\sum b_j^2$. Moreover, this negativity persists on
supports whose dimension grows linearly with the scale: comparing the actual form
$P(T,b)$ with its limit $P_\infty(T,b)$ uniformly via the prime-tail bound beyond
$R$, the support-uniform harmonic-tail bound beyond $K$, the cardinality-free
disjoint-interval affine clock comparison $O(R\sum b_m^2/N)$, and the affine
resonance-head bound $O((\delta+1/N)\sum b_m^2)$ yields, for every $\eta>0$,
explicit constants $\delta\in(0,1]$ and $N_0\ge2$ such that
$\lvert P(T,b)-P_\infty(T,b)\rvert\le\eta\sum_{m\in T}b_m^2$ on every linear window
$N\le m+1\le(1+\delta)N$ (`exists_linearWindow_criticalPrimeEnergy_sub_limit_le`).
At $\eta=2/(7000\pi^4)$ this gives strict negative definiteness
$P(T,b)\le-(2/(7000\pi^4))\sum b_m^2$ across the full linear window of dimension
$\lfloor\delta N\rfloor+1>\delta N$ (`exists_linearWindow_criticalPrimeEnergy_le`,
`exists_fullLinearWindowSupport_criticalPrimeEnergy_neg_definite`), turning the prime
contribution $-2P(T,b)$ in `criticalCompleteEnergy` from a channel cost into a strictly
positive subsidy $+(4/(7000\pi^4))\sum b_m^2$ while the polar cost decays as $2304/N$
(`exists_linearWindow_criticalCompleteEnergy_prime_subsidized`;
[TheLinearWindowOfTheCriticalPrimeChannel](TheLinearWindowOfTheCriticalPrimeChannel.lean)).

### 3.12 The complete critical form

**Assembly.** The complete critical energy of a pattern is written in the
Gamma–Lévy form of §2.2 with values in the extended reals; the Lévy integral is
the only channel allowed to be infinite. The polar channel of a translated
pattern vanishes in the limit, the prime channel converges to $P_\infty$, and
the Gamma constant term converges to $\Omega(0)\mu_\infty$; the arithmetic
channels together tend to $\Omega(0)\mu_\infty-2P_\infty$ with
$-2P_\infty\ge(8/(7000\pi^4))E_b$.

**Archimedean domination.** By the rational dilation law the translated
autocorrelation at shift $x$ tends to $e^{-x/2}\mathrm{Lim}_b(e^x)$, which is
zero for almost every $x$ because $e^x$ is irrational almost everywhere. The
Lévy integrand $(a(0)-a(x))\omega(x)$ therefore tends to $\mu_\infty\,\omega(x)$
almost everywhere, and $\omega(x)\ge e^{-1/2}/x$ is not integrable at the
origin, so Fatou's lemma gives Lévy energy $\to+\infty$: for every nonzero
finite pattern the complete critical energy of its translates tends to
$+\infty$. The critical complete form is archimedean-dominated: every
non-archimedean channel stays bounded while the source decorrelates at almost
every shift.

**Uniform coercivity on a fixed support.** The divergence is uniform over the
coefficient vector. The symmetric correlation matrix of the single-scale
sources converges entrywise to $e^{-t/2}$ times the polarised dilation limit at
$e^t$, the mass matrix represents $\mu_\infty$, and a decorrelation defect
$d_n(x)\to0$ almost everywhere controls the error at once for all $b$:
$a(0)-a(x)\ge(1/(12\pi^4)-d_n(x))E_b$. The common Lévy floor
$\int_0^\infty(1/(12\pi^4)-d_n(x))\omega(x)\,dx$ tends to $+\infty$, so for
every finite $S$ and every bound $M$, eventually in $n$, every pattern on $n+S$
has complete critical energy at least $M\sum_{j\in S}b_j^2$. The smallest
eigenvalue of the complete critical form on the span of single-scale critical
sources at scales $n+S$ tends to $+\infty$; the threshold scale depends on $S$.

**Logarithmic coercivity uniform in the support.** The threshold can be freed
from $S$ at the price of a logarithm. The critical readout is
$\hat g(t)=\int_1^\infty v^{-3/2}B_b(v)e^{-it\log v}dv$, and the nonstationary
Mellin bound with exponent $3/2$ gives the low-frequency exclusion
$\lvert\hat g(t)\rvert^2\le(2D^2/M)E_b$ on $\lvert t\rvert\le\pi M$ whenever all
scales are at least $M$. The autocorrelation is the cosine transform of the
spectral density (polarised Plancherel), so the Lévy energy is at least the
high-band part of $\int\lvert\hat g\rvert^2W(t)\,dt/2\pi$ with the Lévy symbol
$W(t)\ge e^{-1/2}(\log\lvert t\rvert-3)$; together with the window mass floor
$\int g^2\ge A\,E_b$ this yields
$$
\int_0^\infty(a(0)-a(x))\,\omega(x)\,dx\ \ge\ e^{-1/2}\frac A2\bigl(\log M-3-\log(1/\eta)\bigr)E_b,
\qquad \eta=\min\{1,\pi,A\pi/(4D^2)\},
$$
for every finite family on scales $n+1\ge M\ge2$ and every real $b$. This is
the abstract law for any **admissible source**: a mass floor plus a low-band
exclusion gives logarithmic Lévy growth in the band edge. The critical envelope
inherits high-scale archimedean coercivity exactly as the canonical envelope
does, although its absolute prime majorant diverges.

**Growing patterns and the $\ell^1$ obstruction.** On a dyadic block at $M$ the
prime admission constant is at most $384B_1^2$ and the mass at most $4B_1^2$,
so the arithmetic channels are bounded below by $-C\,B_1^2$ with
$C=4\lvert\Omega(0)\rvert+288+768\sum\Lambda(r)/r^2$, and
$$
E_{\mathrm{crit}}(b)\ \ge\ s(\log M-c_0)\sum b_j^2-C\Bigl(\sum\lvert b_j\rvert\Bigr)^2
\qquad\text{on every dyadic block at }M,
$$
positive for every nonzero pattern once $C\lvert S\rvert<s(\log M-c_0)$. The
admissible pattern size is logarithmic in the scale: the exact trade-off
between an $\ell^1$ prime budget and an $\ell^2$ Lévy gain. The $\ell^1$ is
not intrinsic to the dilation structure. For any weight $\varphi$ integrable on
$(1,\infty)$ whose cosine transform is bounded by $A$ and by $B/f^2$, every
dyadic block and every integer dilation $r\ge1$ satisfy the **dyadic dilation
inequality**
$$
\Bigl\lvert\int_1^\infty\varphi(v)B_b(v)B_b(rv)\,dv\Bigr\rvert\ \le\ \frac4{\pi^4}K(A,B)\,r^{-1/2}\sum b_j^2 ,
$$
proved by a Schur test on the cross-scale kernel: the branches of distinct
scales are $11/12$-spaced, resonance is localised to $k\asymp lr$ where the
transform contributes $A+O(B/q^2)$, and the harmonic weight $1/k^2$ is traded
against $\sqrt{lr}\ge\sqrt r$. The raw critical weight $v^{-2}\mathbf 1_{v>1}$
fails the $1/f^2$ hypothesis only because of its jump at $v=1$: the endpoint
layer is the sole $\ell^1$ source.

**The collar.** Multiplying the critical source by $\sigma(e^{-x}-1)$ removes
the endpoint layer. Second-order cosine decay,
$\int\varphi\cos(\omega v)=-\omega^{-2}\int\varphi''\cos(\omega v)$ for weights
flat at the endpoint, puts the collar weight $\psi$ under the dyadic dilation
inequality; the correlation law
$\int g^c_b\,g^c_b(\cdot-\log r)=r^{-1/2}\int_1^\infty\psi(v)B_b(v)B_b(rv)\,dv$
for $r\ge2$ then gives the **$\ell^2$-uniform collared prime channel**
$\lvert\sum_r\Lambda(r)r^{-1/2}a_{g^c_b}(\log r)\rvert\le C_c\sum b_j^2$ on every
dyadic block, with $C_c=(4/\pi^4)K(\|\psi\|_1,\|\psi''\|_1/4\pi^2)\sum\Lambda(r)r^{-3/2}$.
The flat nonstationary phase bound gives the collared low-frequency exclusion,
a window beyond the collar gives the collared mass floor, and the admissible
source law gives collared logarithmic coercivity
$\mathrm{L\acute evy}(g^c_b)\ge s_c(\log M-c_c)E_b$ on all scales $\ge M$. The
Gamma constant term is bounded by an $\ell^2$ ceiling
($\int_1^\infty v^{-2}\lvert B_b\rvert^2\le(\pi^2/6)J\sum b_j^2$ from unit
windows with weights $j^{-2}$), and the two collared polar readouts are each
$O(\sum\lvert b_n\rvert/(n+1))$ by parts against the bounded primitive, so
their product is $O(\sum b_j^2)$. Altogether, on every dyadic block at $M\ge2$,
$$
E^c_{\mathrm{crit}}(b)\ \ge\ \bigl(s_c(\log M-c_c)-K\bigr)\sum b_j^2 ,
$$
and there is an absolute threshold $M_0$ such that for every $M\ge M_0$, every
dyadic block at $M$ and every nonzero pattern the complete collared critical
form is strictly positive, with no restriction on the number of offsets. Once
the endpoint is collared the critical Weil-type form splits into an
$\ell^2$-log-growing archimedean part and $\ell^2$-bounded prime, polar and
constant parts. The uncollared form differs by the endpoint layer alone: its
self-interaction with the prime channel vanishes for $r\ge2$ by disjointness of
supports, and its cross terms with the far part carry the Hilbert $1/f$ kernel.

**The endpoint layer is paid by Montgomery–Vaughan.** The critical prime atoms
of a dyadic block are $\Lambda(r)r^{-1}\int_{v>1}v^{-2}B_b(v)B_b(rv)\,dv$, and
$v^{-2}=\psi+\varphi_e$ splits each into a collared part, covered by the dyadic
dilation inequality, and an endpoint part whose weight transform is $j+e$. The
remainder $e$ has the $1/f^2$ decay the dilation inequality needs. The jump
kernel is an average of cosines over $[-1,1]$, so its bilinear form over two
separated frequency families splits by Cauchy–Schwarz into two mean squares of
exponential sums over a unit interval, and the Montgomery–Vaughan interval
inequality bounds each by $(2+26/(\pi D))\sum b_n^2$ with no separation needed
between the two families; away from the resonance $k\approx lr$ the trivial
$1/f$ bound suffices. With the harmonic reduction of the dyadic dilation
inequality the endpoint correlations decay like $r^{-1/2}$, exactly as the
collared ones, and
$$
\Bigl\lvert\sum_r\Lambda(r)r^{-1/2}a_{g_b}(\log r)\Bigr\rvert\ \le\ C_P\sum b_j^2
\qquad\text{on every dyadic block},
$$
uniformly in the scale, the number and the positions of the offsets. The
Hilbert tail of the endpoint jump was the only obstruction to $\ell^2$-uniformity
of the uncollared prime channel, and it is removed without the collar.

### 3.13 Many scales, compact truncations, and the passage to compact tests

**High blocks, uncollared.** With the Gamma term under its $\ell^2$ ceiling and the
uncollared prime channel $\ell^2$-bounded, the complete uncollared critical form
satisfies $E_{\mathrm{crit}}\ge(s(\log M-c_0)-K)\sum b_j^2$ on every dyadic block,
so beyond an absolute $M_0$ it is positive definite on every block with no
restriction on the pattern (`exists_criticalCompleteEnergy_pos`). Positivity of
the critical form can fail only at low scales or across blocks.

**Windows of scales.** On a scale window $[M,LM]$ the prime channel grows only like
the logarithm of the width. The correlation of two dilation rings is
$O(\min(1,\sqrt{L/r}))$, so the window prime cost is governed by the
**dilation-ring majorant**
$$
\mathcal M_{\mathrm{win}}(L)=\sum_{r\ge2}\frac{\Lambda(r)}r\min\Bigl(1,\sqrt{L/r}\Bigr),\qquad
\log L-(\log4+4)\ \le\ \mathcal M_{\mathrm{win}}(L)\ \le\ \log L+O(1),
$$
proved by direct dyadic slicing (`windowRingMajorant_bounds`,
`tendsto_windowRingMajorant_div_log`). The width cost $\Theta(\log L)$ is therefore sharp,
and $\lvert P\rvert\le C_W(3+\log L)\sum b_j^2$ (`abs_criticalPrimeEnergy_le_of_window`).
The archimedean gain is $\log$ of the smallest scale and the prime cost $\log$ of the width,
so the form is positive definite on every window $[M,M^{1+\delta}]$ spanning polynomially
many dyadic blocks (`exists_criticalCompleteEnergy_pos_of_window`,
`exists_direct_polynomial_window_all_five_forms_pos`). An earlier route through the tempered
sum $\sum\Lambda(r)r^{-1-\varepsilon}$ at $\varepsilon=1/(2+\log L)$ proves the same law with a
constant worse by $6e$; it is kept because of what it reveals about selectivity.

**The temperedness gate, wide-window selectivity against $\zeta(s-a)\zeta(s+a)$, and Beurling
infrastructure invariance.** On the critical line the raw weight $\Lambda(r)/r$ diverges, and
the window exponent $\varepsilon(L)=1/(2+\log L)$ restores summability with an explicit
width-logarithmic sum, $\sum_r\Lambda(r)r^{-1-\varepsilon(L)}\le6(3+\log L)$
(`summable_vonMangoldt_windowDilationExponent`). The shifted pair
$\zeta(s-a)\zeta(s+a)$, $a\ne0$, has von Mangoldt weight $\Lambda_a(r)=\Lambda(r)(r^a+r^{-a})\ge\Lambda(r)r^{\lvert a\rvert}$,
so its version of the same sum diverges for *every* $\varepsilon\le\lvert a\rvert$, in
particular on every window with $\log L\ge1/\lvert a\rvert-2$
(`not_summable_shiftedPairVonMangoldt_div_rpow_of_le_abs`,
`not_summable_shiftedPairVonMangoldt_windowDilationExponent`). Moreover,
[WideWindowSelectivityAndBeurlingInfrastructure](WideWindowSelectivityAndBeurlingInfrastructure.lean)
establishes the exact dividing line between wide-window prime-driven selectivity and critical-family
infrastructure invariance:
- *Wide-window prime-driven failure of Weil positivity for $\zeta(s-a)\zeta(s+a)$:* For every real
  shift $a\ne0$, every nonnegative bump $g\in C^2_c([-1/4,1/4])$ with $\int g\ne0$, and every
  horizon $L_0\ge0$, integrating finite partial sums of $\mathrm{windowValue}\,g\,L\,n\cdot e^{-\sigma L}$
  at $\sigma=1/2+\lvert a\rvert>1/2$ over $L\in(L_0,\infty)$ against `integral_shiftMajorant_mul_exp`
  and comparing with the divergence of $\sum_n\Lambda(n)/n$ produces a wide window shift
  $L>\max(L_0,\log2)$ (where only prime powers $r\in[e^{L-1/2},e^{L+1/2}]$ enter the window sum) at
  which $\mathrm{windowSum}(g,\Lambda_a,L)>\mathrm{shiftMajorant}(g,2c_{\mathrm{pole}}+2c_{\mathrm{arch}},L)$
  and the full Weil functional of $\Lambda_a$ on the wide shift pair $g+g(\cdot-L)$ is strictly
  negative (`exists_wide_windowSum_shiftedPairVonMangoldt_gt_shiftMajorant`,
  `exists_wide_shiftPair_shiftedPairVonMangoldt_neg`,
  `exists_wide_shiftPair_narrowG_shiftedPairVonMangoldt_neg`).
- *Dilation-ring majorant divergence and sign reversal of the critical harmonic charge $A_a(m)$:*
  For $\lvert a\rvert\ge1/2$, the dilation-ring majorant $r\mapsto(\Lambda_a(r)/r)\min(1,\sqrt{L/r})$
  diverges on every scale window $L\ge1$ (`not_summable_shiftedPairWindowRingMajorant_of_half_le`),
  and its prefix $2\le r\le L$ dominates $\sum_{2\le r\le L}\Lambda(r)r^{\lvert a\rvert-1}$
  (`shiftedPairWindowRingMajorant_prefix_ge`). On the critical harmonic side, the divisor charge
  $A_a(m)=\chi(m)\sum_{d\mid m}d\Lambda_a(d)\chi(m/d)$ has $A_a(2)=-2\log2(2^a+2^{-a})<0$ as its
  unique negative harmonic and $A_a(p)=p\log p(p^a+p^{-a})>0$ at every odd prime $p$
  (`shiftedPairHarmonicCharge_sign`, `shiftedPairHarmonicCharge_odd_prime`). Whereas for $\zeta$
  ($a=0$) the cubic cumulative charge $\sum_{m=1}^N A_0(m)/m^3$ is strictly negative at $N=2,3,4$,
  for $\lvert a\rvert\ge2$ the odd prime $m=3$ flips $\sum_{m=1}^N A_a(m)/m^3>0$ already at
  $N=3,4$ (`shiftedPairCumulativeCharge_three_pos_of_two_le`), for $\lvert a\rvert\ge1$ it is
  strictly positive for all $N\ge5$ (`shiftedPairCumulativeCharge_pos_of_one_le`), for
  $\lvert a\rvert\ge2$ the cubic charge series $\sum_m A_a(m)/m^3$ diverges
  (`not_summable_shiftedPairHarmonicCharge_div_cube_of_two_le`), and for $\lvert a\rvert\ge3$ the
  singleton critical prime series $\sum_m A_a(m)J_m/m^4$ diverges
  (`not_summable_shiftedPairSingletonPrimeSeries_of_three_le`).
- *Tempered prime-weight infrastructure invariance, Beurling off-line zero systems, and quantifier
  separation:* Every arithmetic weight $w:\mathbb N\to\mathbb R$ satisfying the temperedness bound
  `TemperedPrimeWeight w C` ($\lvert w(r)\rvert\le C\Lambda(r)$ for $r\ge2$, requiring neither
  multiplicativity nor prime-power support nor nonnegativity) obeys the exact identity
  $\Re\mathcal W_w(g^V)=Q(g^V)+2P_\Lambda(g^V)-2P_w(g^V)$
  (`re_weilFullFunctional_criticalTruncatedTest_eq`), the uniform-in-$V$ window bound
  $\lvert P_w(g^V)\rvert\le C\cdot C_{TW}(3+\log L)\sum b_n^2$
  (`abs_weightedTruncatedPrimeEnergy_le_of_window`), and uniform-in-$V$ polynomial scale-window
  Weil positivity $\Re\mathcal W_w(g^V)\ge(s_T/4)\log M\sum b_n^2>0$
  (`exists_temperedWeight_polynomial_window_weilFullFunctional_pos`). In particular, the
  Liouville-twisted weight $(-1)^{\Omega(r)}\Lambda(r)$, the node-$4$-deleted weight
  $\Lambda\cdot\mathbf 1_{r\ne4}$, and the primes-only weight $\Lambda\cdot\mathbf 1_{r\text{ prime}}$
  all satisfy uniform-in-$V$ polynomial-window Weil positivity on the critical family, even though
  adding an arbitrarily small positive generalized-prime density with reciprocal mass $<\varepsilon$
  creates an off-line zero $\beta+i\gamma$ (`RHTower.BeurlingSensitivity.rh_sensitivity_threshold`)
  and deleting $4$ or prime squares unconditionally refutes `ZeroPoleBlindPositiveOn` with exact
  deletion price $-(\log2)/2$ (`beurling_offLine_zero_system_vs_critical_infrastructure`). Moreover,
  at any *fixed* truncation $V$, **every** arithmetic weight $w$ whatsoever (including $\Lambda_a$)
  satisfies polynomial-window Weil positivity once $M\ge M_0(w,V)$ because only $r\le\lfloor2V\rfloor$
  enter $g^V$ (`exists_fixedV_polynomial_window_pos_for_any_weight`); what separates tempered
  weights from $\Lambda_a$ on the critical family is **uniformity in $V$**
  ($\exists M_0,\forall M\ge M_0,\forall V\ge V_0$).

**Compact truncations.** The doubly collared source $g^V=\chi(e^{-x}/V)\,g_c$ is
compact, supported in $[-\log2V,0]$. The two cutoffs merge in the correlation law,
the transforms of the truncated weights are bounded uniformly in the truncation,
the tail mass of the archimedean energy is at most $(U/V)E$, and block positivity
survives with a margin uniform in $V$ (`exists_criticalTruncatedCompleteEnergy_pos`).
On these compact tests the complete energy is the Weil functional,
$\operatorname{Re}W_\Lambda(g^V\star\tilde g^V)=E(g^V)$, so the Weil form of $\zeta$ is
positive on compact tests of arbitrarily long support at every high block, unconditionally
(`exists_compactFullWeilEnergy_criticalTruncatedTest_pos`). This positivity is not the
small-support regime: it comes from the logarithmic coercivity of the critical family against
an $\ell^2$-uniform prime channel.

**Windows and truncations together.** The window correlation bound holds for the truncated
collar weight with a constant independent of the truncation, so the window prime energy of a
compact doubly collared source obeys $\lvert P\rvert\le C_{TW}(3+\log L)\sum b_j^2$ uniformly in
$V>0$ (`abs_criticalTruncatedPrimeEnergy_le_of_window`). Against the truncated archimedean
slope,
$$
E(g^V)\ \ge\ \bigl(s_T(\log M-c_T)-K_{T,0}-2C_{TW}(3+\log L)\bigr)\sum_jb_j^2
$$
for every window $[M,LM]$ and every $V\ge V_0$. Hence there are $\delta>0$ and $M_0$ such that
on every polynomial window $L\le M^\delta$ with $M\ge M_0$, every truncation $V\ge V_0$ and every
nonzero pattern, the compact test $g^V$ (support $[-\log2V,0]$, arbitrary length, covering
every prime power $r\le\lceil2V\rceil$) has energy at least $(s_T/4)\log M\sum b_j^2$ in four of
the five names of §2.2 (`exists_polynomial_window_compact_weil_and_fullZeroForm_pos`).
Mollifying into $C^2_c(\mathbb R,\mathbb R)$ at rate $O(1/(k+1))$ carries half the margin into
the fifth name, the actual zeta divisor:
$$
\mathcal R(F_k)+\tfrac{s_T}8\log M\sum_jb_j^2\ \le\ \mathcal Z(F_k)
\qquad\text{for all large }k
$$
(`exists_smooth_actual_zeta_reflection_coercivity_of_compact_window`). On arbitrarily long
compact tests the readout of the literal zero divisor at a zero is strictly closer to the
readout at its mirror image than the trivial mass allows. The margin is still the archimedean
gain, so this is reach, not selectivity; what it removes is any suspicion that the critical
family's positivity is an artefact of short support, of one block, or of a noncompact source.

**Across blocks.** The multi-scale prime coupling is an $\ell^2$-sum over dilations. Two
estimates control it.

- *Downward decay.* Cauchy–Schwarz over $r$ with the Mertens partial sum gives
  $\bigl\lvert\sum_r(\Lambda(r)/r)\int\varphi_rB_b(v)B_c(rv)\bigr\rvert\le K\,\tau(m,n)\lVert b\rVert\lVert c\rVert$
  with $\tau(m,n)=(1+\log n)\sqrt{1/n+m\sqrt{m/n}}$ (`abs_sum_integral_crossBlock_down_le`):
  distinct blocks decouple once $n\gg m^3$.
- *Log-ratio coupling.* Interchanging the scale sum and the resonance sum in the Schur row
  test uses the $(11rl/12)$-spacing of $n'\mapsto rl\theta_j(n')$ below the resonance and the
  cancellation $(M'+1)/(lM')^2\le2/M'$ above it, bounding each row by
  $12(A+16B)(1+\log(1+6kM/M'))^2$ (`sum_row_dilationKernel_spaced_le`). The coupling of two
  blocks at $M$ and $M'$ is then at most $5K(A,B)(1+\log(1+6M/M'))^2\lVert b\rVert\lVert c\rVert$,
  a function of the ratio alone, and $O(1)$ whenever $M\le M'$
  (`abs_sum_integral_crossBlock_logRatio_le`, `abs_truncatedBlockCoupling_up_uniform_le`).

On lacunary families $M_{i+1}\ge M_i^8$ the decay sums, and the compact Weil form is positive on
patterns spread over any number of blocks (`exists_compactFullWeilEnergy_pos_of_lacunary`), and
more generally on any lacunary family of polynomial windows $[M_i,L_iM_i]$ with
$(L_iM_i)^8\le M_{i+1}$, the cross-window cost being at most $650K_{CB}\sum_iE_i$ independently
of the widths, the number of windows and the truncation
(`abs_criticalTruncatedPrimeEnergy_le_of_lacunaryWindows`,
`exists_lacunaryPolynomialWindows_all_five_forms_pos`). A single dense window $[1,LM]$ split at
an intermediate breakpoint $M$, with no lacunary gap, is positive whenever the upper band
dominates the lower one in coefficient energy by the explicit ratio its $\log M$ margin allows
(`dense_window_two_band_all_five_forms_pos`); the lower band is a cost, not a certificate.

*Resonance inside a window.* At dilation $r\le L$ on $[M,LM]$, a shifted-frequency difference
splits into the integer clock difference $k(n+1)-lr(n'+1)$, the constant $(k-lr)/12$, and the
dilated affine defect (`harmonic_factorialShiftedFreq_affine_gap`). Scales with
$k(n+1)\equiv j\pmod{lr}$ are spaced by at least $lr/\gcd(k,lr)$
(`resonant_scale_mod_eq_and_spacing`), and the dilated defect satisfies
$r e_{n'+1}\le L^2/(140M)$, below $1/140$ exactly up to $L\le\sqrt M$
(`dilated_factorialAffineDefect_window_bounds`). The square-root window is where the affine
model of the resonant progressions stops being exact to first order.

**Explicit constants.** Every block threshold is the closed form
$M_0=\max(2,\lfloor e^{c+C/s}\rfloor+1)$ in its slope $s$, offset $c$ and channel constant $C$,
and the window exponent is $\delta=s/(4(W+1))$ (`ExplicitBlockThresholdsOfTheCriticalFamily`).
Explicit derivative bounds on the smooth transition ($0\le\sigma'\le4$, $\lvert\sigma''\rvert\le95$),
exact mass conservation between collar and endpoint weights and
$\sum_r\Lambda(r)r^{-3/2}\le18$ bound every channel constant (the complete channel constant is
at most $125000$) and give $10^{-21}\le\delta\le1$ (`criticalCompleteChannelConstant_le`,
`criticalWindowExponent_bounds`). The constants are poor; the
point is that no threshold is hidden.

**Low modes and the Schur complement.** The Gamma–polar cost needs no lower scale cutoff:
$(\sum_n\lvert b_n\rvert/(n+1))^2\le(\pi^2/6)\sum_nb_n^2$ includes the mode $n=0$. What a low window
$[1,L_{\mathrm{low}}]$ costs against high blocks is decided by the archimedean channel, and a
naive high-band Plancherel split multiplies the low-mode penalty by $\log M_0$. Reading the
source in the clock variable removes that growth. Writing $g^V(y)=e^{y/2}F_V(e^{-y})$, the
profile $F_V$ is globally bounded and Lipschitz uniformly in $V\ge1$, and interpolating the
clock-Lipschitz increment $\lvert\Delta g^V\rvert\le Ke^{-u/2}x$ against the envelope
$\lvert\Delta g^V\rvert\le Ke^{u/2}$ gives
$$
(g^V(u)-g^V(u+x))^2\le K^2\sqrt x\,e^{u/2}\quad(u\le0,\ 0\le x\le1),\qquad
a_{g^V}(0)-a_{g^V}(x)\le K^2\sqrt x
$$
(`sourceAutocorrelation_criticalTruncatedSource_jump_le_sqrt`), so the Lévy energy of the
low window has a ceiling $C_{\mathrm{levy}}(L_{\mathrm{low}})E_{\mathrm{low}}$ independent of
$V$ and of every high scale (`biScaleLevyEnergy_criticalTruncatedTest_le`). Against any high lacunary block family with $L_{\mathrm{low}}^8\le M_0$, the
shift-adapted Young weight $\beta(x)=\gamma x^{1/4}$ on $(0,1]$, $\beta=\gamma$ beyond, gives in all
four channels the **bilinear Schur-complement inequality**
$$
Q(g^V_{\mathrm{low}}+g^V_{\mathrm{high}})\ \ge\ Q(g^V_{\mathrm{low}})+Q(g^V_{\mathrm{high}})
-2C_{\mathrm{Schur}}(L_{\mathrm{low}})\sqrt{E_{\mathrm{low}}E_{\mathrm{high}}}
$$
(`compactFullWeilEnergy_criticalTruncatedTest_schur_sqrt`), with a cross constant
that does not depend on $M_0$, the number of high blocks or $V$. Two consequences: a coupled
family $\sum_{n\in S_{\mathrm{low}}}b(n)(g^V_n+\gamma_ng^V_{\phi(n)})$ with $\lvert\gamma_n\rvert\ge\gamma_0>0$
is strictly positive for every nonzero low vector once $M_0$ exceeds an explicit
$M_0(L_{\mathrm{low}},\gamma_0^{-2})$ (`coupled_low_high_pos_for_unrestricted_low_modes`); and
any low-mode certificate $Q(g^V_{\mathrm{low}})\ge\mu_{\mathrm{low}}E_{\mathrm{low}}$ with
$\mu_{\mathrm{low}}>0$ extends to strict positivity on the whole product space
(`compactFullWeilEnergy_pos_of_lowMode_certificate_and_schur_complement`). The low window
itself is not proved positive: that is §7.1.

**Admissible stencils, non-Bernoulli filters, and cell kernels beyond the dyadic stencil.** The
mechanisms of §§3.7–3.13 do not depend on the specific dyadic stencil $\{1,2,4\}$: they hold for
every harmonic weight sequence $w:\mathbb N\to\mathbb R$ in the general class
`AdmissibleHarmonicWeight w C_w τ` satisfying $w_0=0$, $w_1=1$, $\lvert w_k\rvert\le C_w/k^2$, and
higher-harmonic tail $\sum_{k\ge2}\lvert w_k\rvert\le\tau<1$
([AdmissibleStencilsAndCellKernelsBeyondDyadic](AdmissibleStencilsAndCellKernelsBeyondDyadic.lean)).
Four explicit infinite families belong to this class:
1. the canonical dyadic stencil `dyadicHarmonicWeight` ($C_w=1$, $\tau=3/4<1$);
2. all $q$-adic $3$-scale sign-flip stencils on $\{1,q,q^2\}$ for every $q\ge2$
   (`qAdicSignFlipWeight q`, $C_w=1$, $\tau=3/4<1$,
   `admissibleHarmonicWeight_qAdicSignFlip`);
3. all $q$-adic $3$-scale **drift-free** stencils on $\{1,q,q^2\}$ for every $q\ge2$
   (`qAdicDriftFreeWeight q`, which simultaneously cancel both the linear secular ramp
   $\sum d\alpha(d)=0$ and the quadratic Bernoulli drift $\sum d^2\alpha(d)=0$, with
   $C_w=(q^2+q+1)/q^2\le7/4$ and $\tau=3/4<1$, `qAdicDriftFreeStencil_drifts_zero`,
   `admissibleHarmonicWeight_qAdicDriftFree`);
4. all **non-Bernoulli higher-order harmonic filters** $w_k=c_k/k^p$ ($p\ge3$, $c_1=1$,
   $\lvert c_k\rvert\le1$, built from higher periodic Bernoulli polynomials $B_{2m}(\{u\})$ with
   $2m\ge4$ or smooth periodic remainders, `higherOrderHarmonicWeight`, with $C_w=1$,
   $\tau=3/4<1$ and global $C^1$ regularity $\sum k\lvert w_k\rvert<\infty$,
   `admissibleHarmonicWeight_higherOrder`).

Every `AdmissibleHarmonicWeight w C_w τ` enjoys Bohr coercivity with margin $(1-\tau)^2/(2\pi^4)>0$,
window Riesz bounds on length $L(\tau)=4K/(1-\tau)^2$, collared and doubly-collared mass bounds,
nonstationary Mellin low-frequency exclusion, logarithmic Lévy coercivity, an $\ell^2$-uniform
dyadic dilation inequality with constant $C_w^2K(A,B)$, $\ell^2$-uniform collared and truncated
prime and polar channels, and uniform high-scale block positivity in all five forms of §2.2
(including the actual zeta reflection inequality $\mathcal R(F_k)+(s_T/8)\log M\sum b_j^2\le\mathcal Z(F_k)$
and $(\alpha,\beta)$-norm-controlled receiver landing via `generalCriticalEvenOddLanding`;
`exists_general_all_five_forms_and_actual_zeta_coercivity`,
`exists_qAdicSignFlip_and_DriftFree_and_higherOrder_all_five_forms_pos`). On the cell-kernel side,
for any bounded harmonic multiplier $\chi:\mathbb N\to\mathbb R$ with divisor charge
$A_\chi(m)=\chi(m)\sum_{d\mid m}d\Lambda(d)\chi(m/d)$, Poisson window closure yields the exact
identity $R_\chi(t)=\sum_m A_\chi(m)J_m/m^4-\tfrac12\sum_m(A_\chi(m)/m^3)(W_m(t)-2\int_0^m\gamma)$
on $[0,1]$ (`generalCriticalPrimeContinuousRealKernel_eq`), and exhibits a sharp sign trichotomy:
- **Positive-definite non-negative multipliers ($\chi\ge0$, $\chi(1)=1$, e.g. $q$-adic sign-flip
  for odd $q\ge3$ or positive higher-order filters):** $A_\chi(m)\ge0$ for all $m\ge1$ with
  $A_\chi(2)=(2\log2)\chi(2)$ and $A_\chi(3)=(3\log3)\chi(3)$, and every harmonic window satisfies
  $W_m(t)\le\pi^2/6$ so $T_m(t)+T_m(1-t)\ge0$ pointwise on $[0,1]$; whenever $\chi(2)>0$ or
  $\chi(3)>0$, $R_\chi(t)>0$ across all $t\in[0,1]$
  (`generalCriticalPrimeContinuousRealKernel_pos_of_nonneg_chi`,
  `qAdicSignFlip_odd_cellKernel_pos_on_Icc`).
- **Negative-definite dyadic and multi-scale sign-flip multipliers:** the canonical dyadic
  multiplier has $A(2)=-2\log2<0$ and $A(4)=0$, giving $R_{\mathrm{dyad}}(t)\le-1/7000<0$ on
  $[0,1]$, and by Lipschitz stability in the charge sequence every multi-scale perturbation
  $\chi_{d,\varepsilon}=\chi_{\mathrm{dyad}}+\varepsilon\mathbf 1_{d\mid k}$ ($d\ge3$) has an
  admissible weight sequence together with a strictly negative-definite cell kernel
  $R_{\chi_{d,\varepsilon}}(t)\le-1/14000<0$ across $[0,1]$
  (`generalCriticalPrimeContinuousRealKernel_neg_of_charge_perturbation`,
  `exists_nonDyadic_stencil_negative_definite_cellKernel`).

**What these theorems are.** Each positivity statement on the critical family is
paid by an archimedean gain of size $\log M$ against an $\ell^2$-bounded prime cost,
so by the no-subsidy criterion of the shared target it is nonselective by
construction; on the RH-complete cone the gain is absent and the limiting critical
prime channel is negative definite. The passage from the family to the receiver
needs a statement that survives the loss of the gain.

### 3.14 Full-form stability and the tent family as a receiver

For compact real sources with value bounds $M_f,M_g$, Lipschitz bounds
$K_f,K_g$ and $L^1$ distance $\Delta$, the identity
$R_f(t)-R_g(t)=\int(f-g)(x)[f(x+t)+g(x-t)]dx$ controls every channel at once:
$$
\lvert Q(f)-Q(g)\rvert\le\Delta\bigl[(M_f+M_g)(\lvert\Omega(0)\rvert+2\,\mathrm{mass}(N))+(K_f+K_g)\mathcal J\bigr],
\qquad \mathcal J=\int_0^\infty\frac{t\,e^{t/2}}{\sinh t}dt,
$$
where $\mathrm{mass}(N)$ is the literal prime-plus-polar budget on the common
support and the prime tail vanishes by support rather than being dropped. For a
finite tent pattern the mollifier error is $\le C(R,M,K)/(k+1)$ with explicit
dependence on radius, value and slope moments, so one accuracy index pays for
arbitrary simultaneous growth of support, scales, translations and
coefficients.

**Weil completeness and quantitative finite-scale transfer.** A grid tent pattern is
$e^{3x/2}$ times the piecewise-linear interpolant of its nodal data; the interpolant keeps the
Lipschitz constant of the data and is within $2Ld$ of it, and the stability bound gives
$\lvert Q(f_n)-Q(g)\rvert\le C_{\mathrm{grid}}(R,M_g,K_g,L)\,d_{n+1}\le C_{\mathrm{grid}}/(12(n+1))$
and $\lvert\int f_n^2-\int g^2\rvert\le C_{\mathrm{mass}}(R,M_g,L)\,d_{n+1}$ in all five names,
with the prime cutoff kept beyond the observation horizon
(`abs_compactFullWeilEnergy_gridTentPattern_sub_le`, `abs_integral_sq_gridTentPattern_sub_le`,
`abs_smoothGridTentDetector_sub_compactFullWeilEnergy_le`). Every compact $C^2$ test is a
simultaneous $Q$- and $L^2$-limit of single-scale grid tent patterns, and with mollification
in the other direction
$$
\text{RH}\iff Q(f)\ge0\ \text{for every finite tent pattern}\iff
\forall G,\ R\ge0:\ Q\bigl(\text{grid pattern of }G\text{ on }[-R-1,R+1]\text{ at scale }n\bigr)\ge0
\ \text{eventually in }n .
$$
The factorial tent family is a complete RH test family inside the laboratory:
positivity theorems on it are exactly partial RH information.

**Parity split and graded transfer.** On $C_c(\mathbb R,\mathbb R)$ the even–odd cross
autocorrelations cancel identically, so $a_{f_{\mathrm{even}}}+a_{f_{\mathrm{odd}}}=a_f$ at every
shift and $\int f^2$, the Lévy energy, the polar pairing and $Q$ split additively with no cross
term (`compactFullWeilEnergy_eq_evenCompactSource_add_oddCompactSource`). A truncation $g^V$ is
supported on $(-\infty,0]$ and vanishes at $0$, so each parity projection carries exactly half
its mass and half the logarithmic Lévy slope
(`integral_sq_oddCompactSource_criticalTruncatedTest`). A subfamily $\mathcal F_r$ is
**$(\alpha,\beta)$-norm-controlled** when it approximates odd receiver tests of aperture $r$ in
$Q$ with $\int g^2\le\alpha e^{2\beta r}\int F^2+\delta$. Such a family transfers a graded floor
$Q(g)\ge-Ce^{2\sigma r}\int g^2$ to $\mathrm{zetaZeroWidth}\le\sigma+\beta$
(`zetaZeroWidth_le_of_normControlled_subfamily_transfer`). Grid tents are $(1,0)$-controlled
(`hasNormControlledReceiverTransfer_gridTentFamily`), so on them a subexponential or a constant
floor is RH and self-improves to exact positivity
(`riemannHypothesis_iff_subexponential_gridTentPattern_odd_floor`,
`riemannHypothesis_iff_bddBelow_gridTentPattern_odd_floor`); conversely width $<\beta$ gives
the rate-$2\beta$ floor on $Q$ and on finite-scale grid tents
(`exists_compactFullWeilEnergy_and_gridTent_ge_neg_of_zetaZeroWidth_lt`).

**The receiver ledger and the rate-$1/2$ floors.** For every odd $F\in C^2_c[-r,r]$ the
complete energy is the archimedean gauge budget minus a single reflected prime–polar cost,
equivalently minus the horizon-localised two-pole Chebyshev-defect pairing
$\int_0^{2r}E(s)\,w_F(s)\,ds$ of §1.2, equivalently minus a second-order critical-scale prefix
integral (`compactFullWeilEnergy_eq_reflectedPrimePolar_and_chebyshev_ledgers`). Bounding
$E$ with what is known about primes gives unconditional floors on every odd test:
$$
Q(F)\ge-78e^r\!\int F^2,\qquad
Q(F)\ge-\bigl((8+\varepsilon)e^r+C_\varepsilon\bigr)\!\int F^2,\qquad
Q(F)\ge-Ke^re^{-c\sqrt r}\Bigl(\int F^2+\tfrac12\int F'^2\Bigr),
$$
the first elementary and transferred to grid tents, the second from the prime number theorem,
the third from the de la Vallée Poussin zero-free region
(`compactFullWeilEnergy_and_gridTent_ge_neg_seventy_eight_mul_exp`,
`exists_compactFullWeilEnergy_ge_neg_eight_add_eps_mul_exp`,
`exists_compactFullWeilEnergy_ge_neg_deLaValleePoussin_sobolev`). All three have rate $1/2$.
The reason is visible in the ledger: the prime measure and the polar measure $2\cosh(t/2)$
both have density $\asymp e^{t/2}$, the Lévy weight is smaller by $e^t$, and an odd edge test
has pole charge $\asymp e^r$ and prime correlation $\asymp-e^r$ of opposite sign. Beating rate
$1/2$ in pure $L^2$ mass is the PNT-level prime–polar cancellation inside $\int E\,w_F$; a
better constant is not progress.

**Detection on the actual zero set.** Through the visibility theorems of the
Square-Root Threshold programme, the real-part splitting of the RH tower, grid
convergence and joint smoothing, every zero $\rho_0$ of $\zeta$ off the line is
seen by the family: there are a nodal profile and a radius such that, at all
sufficiently large scales, the grid tent pattern and its $C^2_c$ smoothing have
strictly negative complete energy with an explicit margin in every one of the
five equal forms of §2.2. The same holds for finite residual off-line sets at
their explicit Nyquist–Ingham aperture, for depth-gap zeros and equal-depth
clusters at their apertures, and for attained maximal-depth zeros; eventual
grid-tent nonnegativity therefore forces the asymptotic abscissa law, and RH is
equivalent to "zeros approach the line" together with eventual grid-tent
nonnegativity.

**Quantitative finite-scale detection and excluded-depth laws.** For every complex test
$f\in C^2_c([-R,R],\mathbb C)$, $\Re\mathcal W_\zeta(f,f)=Q(f_{\mathrm{re}})+Q(f_{\mathrm{im}})$
(`zeta_W_re_eq_compactFullWeilEnergy_re_add_im`) and the sum $Q(P_{\mathrm{re}})+Q(P_{\mathrm{im}})$
of the two single-scale grid tent patterns at scale $n$ approximates $\Re\mathcal W_\zeta(f,f)$
within $2C_{\mathrm{grid}}(R,M_g,K_g,L)\,d_{n+1}\le C_{\mathrm{grid}}/(6(n+1))$ with the prime
cutoff kept beyond $2(R+1)$ (`abs_zeta_W_re_sub_gridTentPattern_re_add_im_le`). Thus nonnegativity
of $P_{\mathrm{re}},P_{\mathrm{im}}$ at a single finite scale $n$ gives the explicit lower floor
$\Re\mathcal W_\zeta(f,f)\ge-2C_{\mathrm{grid}}\,d_{n+1}$
(`zeta_W_re_ge_neg_two_gridTentApproximationConstant_of_gridTentPattern_nonneg_at_scale`), and
for unmodulated ($c=0$) difference lag tests the test is real and odd, so a single odd seed $G$
approximates $\Re\mathcal W_\zeta(f,f)$ within $C_{\mathrm{grid}}\,d_{n+1}$ and is unconditionally
positive through $v/2+w\le 353/1000$ past the first prime $(\log2)/2$
(`abs_zeta_W_re_twoBump_modScaledBump_zero_sub_gridTentPattern_le`,
`zeta_odd_gridTentPattern_pos_through_first_prime`). At any fixed radius $R\ge0$, eventual
grid-tent nonnegativity on seeds in $[-R,R]$ is equivalent to `ZetaWindowPositive R` and
`HodgeIndexAtLevel zetaZeroConfig R`, implies $R\le\mathrm{zetaContactAperture}$ off RH
(`zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius`), and exports
the full quantitative visibility and excluded-depth hierarchy to `gridTentPattern` and
`smoothGridTentDetector`:
- explicit-lag detection of $1/V$-near-top zeros at $V\ge\mathrm{oneParamLag}(w,\eta,\delta_0)$
  by an odd seed (`actual_zeta_oneParam_near_top_detected_by_gridTentPattern`), at
  $V\ge\mathrm{nearTopLag}(w,\gamma_0,\delta_0)$ (`actual_zeta_polylog_near_top_detected_by_gridTentPattern`),
  at the doubly-logarithmic lag $V\ge\mathrm{nearTopLogLogLagOffLine}(M,w,\gamma_0,\delta_0)=\Theta_{M,w}((1+\log\log(\lvert\gamma_0\rvert+4))/\delta_0)$
  under `OffLineCopiesLocallyBounded M`
  (`actual_zeta_loglog_near_top_detected_by_gridTentPattern_of_offLineCopiesLocallyBounded`), and
  of attained-top zeros at explicit $O(1/g)$ and $O(\log(1/g))$ lags
  (`actual_zeta_attained_top_detected_by_gridTentPattern_at_explicit_lag`,
  `actual_zeta_attained_top_detected_by_gridTentPattern_at_log_lag`);
- unconditional depth exclusion $\lvert\Re\rho-\tfrac12\rvert<1/R=2/\log X$ ($R\ge e^6$) for every
  zero below the cluster horizon $\mathrm{zetaClusterHorizonHeight}(A_0,R)=\exp(R/(10^5A_0(\log R)^2))-306$
  and below the local-multiplicity horizon $\mathrm{clusterHorizonHeight}(A_0,k,R)$ with no
  attainment or depth-gap premise
  (`zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg`,
  `zeta_excluded_depth_below_localCount_clusterHorizon_of_gridTentPattern_nonneg`), together with
  the near-top and equal-depth cluster excluded-depth bounds
  (`zeta_oneParam_excluded_depth_of_gridTentPattern_nonneg`,
  `zeta_polylog_near_top_excluded_depth_of_gridTentPattern_nonneg`,
  `zeta_loglog_near_top_excluded_depth_of_gridTentPattern_nonneg_of_offLineCopiesLocallyBounded`,
  `zeta_equalDepthCluster_excluded_depth_of_gridTentPattern_nonneg`) and the two-way
  aperture-to-zero / zero-to-aperture height-reduction duality
  (`zeta_gridTentPattern_visibility_and_height_reduction_duality`;
  [QuantitativeGridTentDetection](QuantitativeGridTentDetection.lean)).

**Lattices and clusters.** At a vertical lattice point $\tfrac12+\delta+ik(2\pi/L)$
the period difference $f(x)-f(x-L)$ multiplies the Weil summand of any zero
configuration by $-2(\cosh(\delta L)-1)$, independently of $k$: on-line lattice
points are annihilated and every off-line depth receives a strictly negative
multiplier. On a finite off-line cluster the period difference removes the
infinite on-line background and reduces Weil form, square mass and reflection
defect to finite sums; a nonnegative seed with support radius $R$ and
$\lvert k\rvert(2\pi/L)R\le1/4$ on the cluster adds the cluster pairs
constructively. Above the explicit scale $\lceil32\pi K/L\rceil$ the tent
detector approximates the literal full Weil functional within $1/(q+1)$ and has
negative Weil form $\le-\sum_{k\in S}(e^{\delta_kL}-1)(1-e^{-\delta_kL})e^{-6\delta_k/(n+1)}$
across any cluster or run in $[-K,K]$, including the small-total-variation
regime where every sub-Nyquist test and every height-windowed average is
nonnegative. On the lattice-plus-pair model without Euler product the same
computations calibrate the family; on $\zeta$ they are detection.

**Small apertures and large heights.** For every real $C^2_c$ source supported
in $[-a,a]$ the complete energy has an explicit unconditional floor:
$Q(F)\ge\tfrac1{25}\int F^2$ for $a\le1/100$ by the three-band archimedean
bound alone, and $Q(F)\ge\tfrac1{5000}\int F^2$ for $a\le3/10$ by the sharp
quartic gauges of Arithmetic Criticality Theory, still below the first prime
window $2a\ge\log2$; odd sources are positive through $a\le181/500$, past the
first prime, by the strip surplus and Schur lending of Arithmetic Incidence
Positivity, and both transfer at explicit finite scale $C_{\mathrm{grid}}\,d_{n+1}\le\mu$ to
grid tents and smooth detectors in all five names
(`compactFullWeilEnergy_and_gridTent_ge_of_support_le_threeTenths`,
`compactFullWeilEnergy_and_gridTent_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`). At
any aperture the localised explicit formula gives nonnegativity of $\mathcal Z-\mathcal R$ on
height shifts beyond an explicit horizon. Off RH the ground-energy path $\mu(A)$ has a first
contact aperture, beyond $3/10$, and a near-top zero seen by the lag family at lag $V$ forces
$\mu(A)<0$ for every $A\ge V/2+w$. High-height positivity is an archimedean fact; the
arithmetic question lives at finite height, on even tests beyond $3/10$ where the conductances
across $\log2$ turn negative, and at the critical scale.

### 3.15 Bridges

**Zero density and visibility.** Unconditional zero-density inputs replace the abscissa-blind
$O(\log T)$ count of §3.4 by Ingham–Huxley and density-hypothesis exponents on abscissa slabs,
Route-T zero-free annihilation above $1-\mathrm{width}$, Selberg's exponential near-line counts
at distance $a/\log T$ from the line, and the Nyquist law that a $C^2$ test of support radius
$a$ detects an off-line vertical lattice of period $L$ iff $a>L/2$. Baker's theorem supplies
the spectral disjointness of §3.10.

**Square-root threshold.** RH is equivalent to the localised prime-tail inequality
$\Re\Pi_f(\xi)\le\Re A_f(\xi)$ for all apertures, profiles and heights, equivalently to a
$2\times2$ pole compression, while every compact $C^2$ profile is unconditionally positive at all
sufficiently large heights and the archimedean–pole budget cannot be frozen at height zero.

**Arithmetic Criticality Theory.** The five-way identity of §2.2 transports the single-shift
pole-free variation form to the actual-zeta difference $\mathcal Z-\mathcal R$ on theta
translates, and the polar energy of a Doob source graph equals
$\cosh\text{-mass}(v^2)-2\cosh\text{-mass}(v)^2+2\sinh\text{-mass}(v)^2$, so on odd profiles the
pole term strengthens the odd Dirichlet–Poincaré inequality by a square while remaining
RH-equivalent. The Markov form of §1.2 agrees with the Markov energy of that theory beyond the
support, and the odd capacity ratio $S(g)^2/(2\mathcal M_N(g))$ tends to one along plateaus,
with no uniform margin at large aperture.

**The zero width.** The width $\sup_\rho\lvert\Re\rho-\tfrac12\rvert$ is read by the lag family as
the exponential rate at which its dyadic prime windows turn negative, by the ground-energy path
as the rate in $\mu(A)\ge-Ce^{2\sigma A}$, by this theory as the rate of a grid-tent floor, and
bounds the de Bruijn–Newman heat time by half its square; RH is width zero.

**Suzuki boundary limits.** The literal Suzuki arithmetic source has a positive-shift first
variation equal to the complete Weil energy on every compact real $C^2$ source, with all prime,
Gamma and polar terms (RHTower, `Suzuki/`). A source-independent first-variation envelope
$\mathrm{suzukiFirstVariationEnvelope}(A,E_0,B,\omega)\to 0$ ($\omega\to 0^+$), homogeneous of
degree $1$ in $(E_0,B)$, controls
$\lvert(a_f(0)-P_\omega(f))/\omega-\Re\mathcal W_\Lambda(f\star\tilde f)\rvert$ across all compact
$C^2$ sources with correlation cutoff $A$, energy $a_f(0)\le E_0$, and increment slope
$a_f(0)-a_f(t)\le Bt$ (`abs_suzukiCriticalSourcePairing_firstVariation_sub_le`). Because
mollification contracts correlation increments (`autocorr_smooth_sub_le`), all mollifications
$g_k$ ($k\in\mathbb N$) of `criticalTruncatedTest hV S b` share a single $k$-independent envelope,
yielding a **common smoothing threshold $k_0$** and a **common shift interval $(0,\omega_0)$**
uniform across all dyadic blocks $S\subseteq[M,2M]$, all nonzero patterns $b$, all $k\ge k_0$,
any bounded scale horizon $[M_0,M_{\max}]$, and any lacunary polynomial-width multi-window family
(`exists_common_suzuki_shift_dyadic_blocks`, `exists_common_suzuki_shift_bounded_block_horizon`,
`exists_common_suzuki_shift_lacunary_windows`). The literal unsubtracted polar integral grows like
$e^{(1/2-\omega)s}$ over $A_V\asymp 2\log V$, whereas the untruncated source
`criticalFactorialSource` has correlation decay $\lvert a_g(\log r)\rvert\le K r^{-3/2}$ via the
bounded phase primitive (`abs_criticalFactorialSource_correlation_le_rpow`). Without any
archimedean scale subsidy, common-shift Suzuki deficits hold on small-aperture receiver tests
($[-3/10,3/10]$ and odd $[-181/500,181/500]$ past $(\log 2)/2$), and small-shift Suzuki deficit
floors on odd receiver tests transfer directly to $\mathrm{zetaZeroWidth}\le\sigma$ and
`RiemannHypothesis` (`exists_common_suzuki_shift_small_aperture_receiver`,
`exists_common_suzuki_shift_odd_receiver_past_two`, `zetaZeroWidth_le_of_graded_odd_suzuki_deficit`,
`riemannHypothesis_iff_suzuki_small_shift_non_overshoot`).

**Moving sources and apertures.** First variation is not restricted to a smooth,
fixed source. On a common compact window, $f_j\to g$ in $L^2$ and
$\omega_j\to0^+$ imply
$$
W_{\mathrm{ext}}(g)\le\liminf_j
\frac{a_{f_j}(0)-P_{\omega_j}(f_j)}{\omega_j},
$$
including infinite Lévy energy; the constant source sequence attains the limit.
For moving or infinite apertures the same lower bound holds under a common
correlation bound $|a_{f_j}(t)|\le K e^{-\beta t}$, $\beta>1/2$, without coupling
aperture growth to the shift. Alternatively, arbitrary compact approximants to a
supercritically decaying target are admitted when
$e^{2A_j}\|f_j-g\|_2\to0$, where $A_j$ is their correlation cutoff. These are
transport theorems, not new signs: a positive inherited deficit still requires
a lower bound for $W_{\mathrm{ext}}(g)$. See
[SuzukiCriticalMovingWindowDeficit](../RHTower/Suzuki/SuzukiCriticalMovingWindowDeficit.lean)
and [SuzukiCriticalMovingAperture](../RHTower/Suzuki/SuzukiCriticalMovingAperture.lean).
The distinction matters for the factorial family: its $r^{-3/2}$ correlation
decay supplies an admissible target, but a bound for each source is not a
common decay constant over every growing family.

**Consumers.** The linear-window negativity of the isolated critical prime channel (§3.11) is
the prime-side input of the signed prime scheduling route FU; the window, lacunary and dense
positivity of §3.13 and the receiver transfer of §3.14 are the high-scale inputs of the even
pole-weight route EWU; and the critical family is the test class on which the Suzuki route SZ
has its strict deficit.

---

## 4. Foundational pillar theorems

Every result below is unconditional and holds at the stated scope; together they are the
theory's load-bearing walls.

1. **Universal reflection identity.** For every zero configuration and every square-summable
   source, $\mathcal Z(f)-\Re\mathcal W(f,f)=\mathcal R(f)$; on the actual zeta divisor the gap
   between trivial mass and Weil energy is exactly the mirror distance of the readouts
   (`configurationSquareMass_sub_re_W_eq_reflectionDefect`). It is the dictionary through which
   every positivity statement is read on the zero side.
2. **Logarithmic sampling.** $\mathcal Z(T_n)+\mathcal Z(U_{n,k})\le C(1+\log N)/N$ uniformly in
   $n,k$, sharp up to constants, and $\mathcal Z(H_{n,k})\le C_H/N$ for the corrected source
   (`exists_factorialTail_raw_and_smoothed_zeroSquare_bound`, `factorialCorrected_zeroSquare_le`).
   Physical mass underestimates spectral sampling by exactly one logarithm.
3. **Sharp Krein stability radius.** Positivity transfers across $r=h-u$ through the independent
   form $\mathcal Z$ iff $\varepsilon<(\sqrt{1+\delta}-1)^2$, attained by a two-mode involution
   pair; the binary Schur law gives the exact criterion and the negative direction
   (`relative_stability_factor_pos_iff`, `exists_two_mode_involution_extremizer`,
   `schur_binary_quadratic_nonneg_iff`).
4. **High-scale span coercivity.** $\Re\mathcal W(f_b,f_b)\ge(\tfrac A2\log M-C)\sum\lvert b_N\rvert^2$
   on every finite span supported on $N\ge M$ (`factorialTailSpan_re_W_coercivity`): physical
   Riesz bounds plus nonstationary Mellin exclusion become spectral coercivity.
5. **The critical prime kernel is negative definite.** $R(t)\le-1/7000$ on the cell, strictly
   decreasing on $[0,\tfrac12]$ and increasing on $[\tfrac12,1]$, so
   $P_\infty(b)\le-(4/7000\pi^4)\sum b_j^2$ for every finite real pattern with exact Rayleigh range
   $[(4/\pi^4)R(\tfrac12),(4/\pi^4)R(0)]$; the actual prime form is eventually negative on each
   fixed translated support and uniformly on every linear window $N\le m+1\le(1+\delta)N$ of
   dimension $>\delta N$ (`factorialCriticalTranslatedPrimeLimit_le_neg_energy`,
   `isLUB_factorialCriticalPrimeRayleighSet_exact`, `isGLB_factorialCriticalPrimeRayleighSet_exact`,
   `exists_linearWindow_criticalPrimeEnergy_le`,
   `exists_fullLinearWindowSupport_criticalPrimeEnergy_neg_definite`). The arithmetic sign of the
   critical prime channel is favourable, with no archimedean input.
6. **Archimedean domination of the critical form.** The critical limit has rational spectrum, the
   source decorrelates at almost every shift, and the complete critical energy of every nonzero
   pattern tends to $+\infty$, uniformly in the coefficient vector on a fixed support
   (`tendsto_criticalTranslatedCompleteEnergy_top`,
   `eventually_criticalTranslatedCompleteEnergy_coercive`).
7. **$\ell^2$-uniform prime channel.** The dyadic dilation inequality for weights with $1/f^2$
   cosine decay, together with Montgomery–Vaughan for the endpoint jump kernel, bounds the
   critical prime channel by $C_P\sum b_j^2$ on every dyadic block, independently of the scale and
   of the number and positions of offsets (`abs_integral_weight_realPhaseCombination_dilate_le`,
   `abs_criticalPrimeEnergy_le_of_dyadic`); across windows the cost is the sharp
   $\mathcal M_{\mathrm{win}}(L)=\log L+O(1)$ (`windowRingMajorant_bounds`).
8. **Positivity on compact tests of every length.** The complete critical form is positive
   definite on every high dyadic block, on polynomial windows, on compact doubly collared
   truncations uniformly in the truncation, on lacunary unions of blocks and of polynomial
   windows, on dense two-band windows under high-band dominance and on coupled low–high families, in all five names, and
   reaches the actual zeta divisor as $\mathcal R(F)+\tfrac{s_T}8\log M\sum b_j^2\le\mathcal Z(F)$
   (`exists_criticalCompleteEnergy_pos`, `exists_direct_polynomial_window_all_five_forms_pos`,
   `exists_lacunaryPolynomialWindows_all_five_forms_pos`, `dense_window_two_band_all_five_forms_pos`,
   `coupled_low_high_pos_for_unrestricted_low_modes`,
   `exists_smooth_actual_zeta_reflection_coercivity_of_compact_window`).
9. **Bilinear Schur complement across scales.** Low and high critical sources interact through
   a cross term $2C_{\mathrm{Schur}}(L_{\mathrm{low}})\sqrt{E_{\mathrm{low}}E_{\mathrm{high}}}$
   against any lacunary high family, independent of the high scale, the number of blocks and the
   truncation (`compactFullWeilEnergy_criticalTruncatedTest_schur_sqrt`): any positive low-window
   certificate becomes positivity on the whole product space.
10. **The tent family is a complete RH test family that sees every off-line zero quantitatively.**
    RH iff every finite tent pattern has nonnegative complete energy, iff grid patterns are
    eventually nonnegative, iff a constant floor holds on odd grid tents; at a single finite scale
    $n$ and radius $R$, complex receiver tests are approximated within $2C_{\mathrm{grid}}\,d_{n+1}$,
    and eventual grid-tent nonnegativity on $[-R,R]$ ($R\ge e^6$) unconditionally excludes every
    zero of depth $\ge1/R$ below $\mathrm{zetaClusterHorizonHeight}(A_0,R)$ and every near-top or
    equal-depth cluster zero above its explicit excluded-depth threshold
    (`riemannHypothesis_iff_factorialTentPattern_nonneg`,
    `riemannHypothesis_iff_eventually_gridTentPattern_nonneg`,
    `riemannHypothesis_iff_bddBelow_gridTentPattern_odd_floor`,
    `abs_zeta_W_re_sub_gridTentPattern_re_add_im_le`,
    `zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg`,
    `zeta_gridTentPattern_visibility_and_height_reduction_duality`).
11. **The receiver ledger.** On every odd compact $C^2$ test the complete energy is archimedean
    budget minus $\int_0^{2r}E\,w_F$, and the elementary, PNT and de la Vallée Poussin bounds on
    the two-pole Chebyshev defect give floors of rate exactly $1/2$
    (`compactFullWeilEnergy_eq_reflectedPrimePolar_and_chebyshev_ledgers`,
    `compactFullWeilEnergy_and_gridTent_ge_neg_seventy_eight_mul_exp`,
    `exists_compactFullWeilEnergy_ge_neg_deLaValleePoussin_sobolev`).
12. **Collar arithmetic.** Near-resonances of shifted harmonics are exactly the affine relations
    $a(12N+1)=b(12M+1)$; the single-scale affine error has the sharp constant
    $7\zeta(3)/(256\pi^2)$; Baker's theorem separates the collar spectrum from the prime
    spectrum (`factorial_small_harmonic_gap_iff_affine`, `tendsto_factorialAffineCollarError_sharp`,
    `primeLog_linearForm_ne_collar_linearForm`).
13. **Wide-window prime selectivity vs. tempered Beurling infrastructure invariance.** The window
    exponent $\varepsilon(L)=1/(2+\log L)$ makes the critical-line prime sum $\le6(3+\log L)$, while
    for every $a\ne0$ and every horizon $L_0\ge0$ the shifted pair $\zeta(s-a)\zeta(s+a)$ has a wide
    window shift $L>\max(L_0,\log2)$ where its prime window sum strictly exceeds the polar–archimedean
    budget and its full Weil functional on $g+g(\cdot-L)$ is strictly negative; for $\lvert a\rvert\ge2$
    the odd prime $m=3$ flips the critical cumulative harmonic charge positive at $N=3,4$ and makes
    $\sum_m A_a(m)/m^3$ diverge; conversely, every $C$-tempered weight $\lvert w(r)\rvert\le C\Lambda(r)$
    (including $(-1)^{\Omega(r)}\Lambda(r)$, $\Lambda\cdot\mathbf 1_{r\ne4}$, and
    $\Lambda\cdot\mathbf 1_{r\text{ prime}}$) satisfies uniform-in-$V$ polynomial-window Weil
    positivity on the critical family, while at fixed $V$ every weight $w$ is eventually positive
    (`summable_vonMangoldt_windowDilationExponent`,
    `exists_wide_shiftPair_shiftedPairVonMangoldt_neg`,
    `shiftedPairCumulativeCharge_three_pos_of_two_le`,
    `exists_temperedWeight_polynomial_window_weilFullFunctional_pos`,
    `beurling_offLine_zero_system_vs_critical_infrastructure`,
    `exists_fixedV_polynomial_window_pos_for_any_weight`).
14. **Admissible harmonic weights and cell-kernel sign trichotomy beyond the dyadic stencil.**
    Every weight sequence in `AdmissibleHarmonicWeight w C_w τ` (including all $q$-adic sign-flip
    stencils, all $q$-adic drift-free stencils with vanishing linear and quadratic drifts, and all
    higher-order non-Bernoulli filters $w_k=c_k/k^p$, $p\ge3$) satisfies Bohr and window Riesz
    coercivity, $\ell^2$-uniform prime and polar bounds, and high-scale block positivity in all
    five forms; on the unit cell $[0,1]$, non-negative multipliers $\chi\ge0$ with $\chi(2)>0$ or
    $\chi(3)>0$ have strictly positive cell kernels $R_\chi(t)>0$, while dyadic and perturbed
    multi-scale sign-flip multipliers $\chi_{d,\varepsilon}$ ($d\ge3$) have strictly
    negative-definite cell kernels $R_\chi(t)\le-1/14000<0$
    (`exists_general_all_five_forms_and_actual_zeta_coercivity`,
    `generalCriticalPrimeContinuousRealKernel_pos_of_nonneg_chi`,
    `exists_nonDyadic_stencil_negative_definite_cellKernel`).
15. **Source selection in the full Weil cone and the additional sign estimates.** Narrow pair tests
    `pairTest m σ` ($m\ge2$, $\sigma=\pm1$) have Kronecker-delta $\ell$-vectors
    $2\sigma(\int h_m^2)/\sqrt m\cdot e_m$, strictly lower the Weil functional of every single-index
    perturbation $w+\delta\mathbf 1_{n=m}$ ($\delta\ne0$) under $\sigma=\operatorname{sgn}\delta$,
    uniquely identify every coefficient $w(m)$ ($m\ge2$) from `pairTest m 1`, and transfer via
    `realPairTest m σ` to single-scale factorial grid tent patterns within $O(1/(n+1))$; truncated
    Riemann kernels `truncatedRiemannKernelReal L` unconditionally refute $\Lambda+\delta\mathbf 1_{n=m}$
    for $\delta>0$, while $\Lambda+\delta\mathbf 1_{n=m}$ is unconditionally outside the full Weil cone
    for every $\delta\ne0$; the one-sided cones satisfy
    $\mathrm{PositiveOnNonposCone}(U)\iff\mathrm{RH}\wedge\forall n\ge2,\Lambda(n)\le U(n)$ and
    $\mathrm{PositiveOnNonnegCone}(L)\iff\mathrm{RH}\wedge\forall n\ge2,L(n)\le\Lambda(n)$ with no
    summability premise; and for any source-identified weight `SourceIdentifiedWithVonMangoldt lam`,
    full-cone positivity `WeilPositiveFull lam` is unconditionally equivalent to one-sided cone
    positivity, prime-power node-deletion symbol slack $\le\mathrm{lam}(m)/\sqrt m$, a constant or
    subexponential odd `gridTentPattern` floor, and `RiemannHypothesis`
    (`re_weilFullFunctional_singleIndexPerturbation_pairTest`,
    `forall_two_le_eq_iff_forall_re_weilFullFunctional_pairTest_eq`,
    `exists_truncatedRiemannKernelReal_weilFullFunctional_singleIndexPerturbation_neg`,
    `positiveOnNonposCone_iff_riemannHypothesis_and_vonMangoldt_le`,
    `weilPositiveFull_of_sourceIdentified_iff_additional_estimates`).
16. **Universal Suzuki first-variation envelope, block-uniform common shifts, and subsidy-free
    receiver transfer.** `suzukiFirstVariationEnvelope A E₀ B ω` vanishes as $\omega\to 0^+$ and
    uniformly bounds $\lvert(a_f(0)-P_\omega(f))/\omega-\Re\mathcal W_\Lambda(f\star\tilde f)\rvert$
    for every compact $C^2$ real source of correlation cutoff $A$, energy $\le E_0$, and increment
    slope $\le B$; on `criticalTruncatedTest hV S b` it yields a common smoothing index $k_0$ and a
    common shift interval $(0,\omega_0)$ independent of the pattern $b$, the block $S\subseteq[M,2M]$,
    and $k\ge k_0$ (as well as across bounded horizons $[M_0,M_{\max}]$ and lacunary polynomial-width
    multi-windows); on untruncated `criticalFactorialSource` the logarithmic correlation decays as
    $O(r^{-3/2})$; and without any archimedean scale subsidy, common shifts hold on $[-3/10,3/10]$
    and odd $[-181/500,181/500]$ while graded odd small-shift Suzuki floors certify
    $\mathrm{zetaZeroWidth}\le\sigma$ and characterize `RiemannHypothesis`
    (`abs_suzukiCriticalSourcePairing_firstVariation_sub_le`,
    `exists_common_suzuki_shift_dyadic_blocks`, `exists_common_suzuki_shift_lacunary_windows`,
    `abs_criticalFactorialSource_correlation_le_rpow`,
    `zetaZeroWidth_le_of_graded_odd_suzuki_deficit`,
    `riemannHypothesis_iff_suzuki_small_shift_non_overshoot`).

---

## 5. Traps and sharp boundaries

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
| Entire-function disk inequalities on the tail readout | The readout is holomorphic only on $\Re s>-1$; use the localised half-plane version. |
| Bohr orthogonality gives uniform physical decoupling | The prime-thirteen family has gaps $\to0$ and physical correlation $\to1$ while every fixed-scale Bohr mean is zero. A uniform cross-scale oscillatory gain is false. |
| The Minkowski affine constant $(4/\pi^2)(\sum\lvert w_k\rvert\sqrt k)^2$ is sharp | The harmonic error layers are orthogonal up to $k\approx140N^2$; the sharp per-defect constant is $(63/16\pi^2)\zeta(3)$. |
| Divergence of $\sum\Lambda(r)/r^{\beta+1/2}$ at $\beta=1/2$ means negative energy | It is failure of an absolute majorant; the oscillatory majorant converges for all $\beta>-1/2$. |
| Fixed-pattern limit justifies a growing pattern | Constants retain $B_1,B_w$ and the limit is taken at fixed $(S,b)$; growing patterns need the dyadic-block or linear-window laws. |
| Harmonic signs decide the total sign | $A(2)<0$ and all other $A(m)\ge0$, but the masses $J_m(b)$ are not independent; the sign comes from the Poisson-closed kernel. |
| Negative prime channel means negative Weil form | The Weil form subtracts the prime channel; the critical prime negativity is a positive contribution to the complete form. |
| Linear-window prime negativity removes the archimedean subsidy | It signs the isolated prime channel on windows of fixed relative width at high scale. The polar cost, the low modes and the cross-window couplings are still paid elsewhere, and the receiver tests do not live on such windows. |
| The spectral range of $P_\infty$ is attained by short patterns | The extremal patterns are long frequency-modulated patterns concentrating at the extrema of $R$; short patterns see averaged couplings. |
| Irrational dilations contribute to the prime channel | The critical limit has rational spectrum; primes read only the integer atoms $\log r$, the atoms at $\log(p/q)$ feed the archimedean channel. |
| The archimedean channel is bounded at the critical scale | It diverges: the source decorrelates at almost every shift and $\omega(x)\ge e^{-1/2}/x$ is not integrable at the origin. |
| An $\ell^1$ prime bound transfers to $\ell^2$ | The admission bound is quadratic in $\sum\lvert b_j\rvert$; the $\ell^2$-uniform bound on dyadic blocks needs the dilation inequality for the collared part and Montgomery–Vaughan for the jump kernel of the endpoint. |
| A threshold "eventually in $n$" is uniform in the support | On a fixed support the threshold depends on $S$; $\ell^2$-uniform statements are made on dyadic blocks or linear windows, where the logarithm is common. |
| The collar changes the prime channel materially | For $r\ge2$ the endpoint layer has no self-prime interaction; only its cross terms with the far part remain, through a Hilbert kernel. |
| Model detection is a zeta sign | The lattice-plus-pair model lacks the Euler product and calibrates the family; the actual-zeta detection theorems go through the visibility laws of the zero configuration. |
| The five names of the form are different quantities | They coincide on compact continuous (resp. $C^2_c$) real sources; re-proving a fact in another programme's form is duplication. |
| Period or Bohr averaging at fixed scale is the physical limit | It erases the slow collar phase; the correct limit keeps $1-\cos(2\pi mv/12)$. |
| Replace the conditionally convergent polar readout by a Lebesgue integral | At $\beta=1/2$ the endpoint is defined through the bounded primitive, $-G(1)+\int_1^\infty G(v)v^{-2}dv$, with cutoff error $\le(24/T)\sum\lvert b_n\rvert/(n+1)$. |
| The pointwise envelope of the critical source pays its infinite prime head | The envelope has exponent $1/2$ only; the decay $e^{-3t/2}$ of the correlation comes from the bounded phase primitive, i.e. from oscillation. |
| An endpoint value of the $L^1$ periodisation is a sign witness | The $L^1$ kernel and its continuous representative differ at integers; only pattern integrals matter. |
| Zero-density bounds exclude a zero | They are upper counts; a single fixed off-line zero survives all of them. |
| Fixed-$V$ window positivity on $g^V$ separates tempered weights from $\zeta(s-a)\zeta(s+a)$ | At fixed $V$, only primes $r\le\lfloor2V\rfloor$ enter $g^V$, so *every* weight $w$ is positive for $M\ge M_0(w,V)$ (`exists_fixedV_polynomial_window_pos_for_any_weight`). What separates tempered weights from $\Lambda_a$ on the critical family is uniformity in $V$, while wide shift pairs $g+g(\cdot-L)$ refute $\Lambda_a$ unconditionally (`exists_wide_shiftPair_shiftedPairVonMangoldt_neg`). |
| Compact support of arbitrary length is the receiver's regime | The truncated window positivity holds at every support length with constants uniform in $V$, yet its margin is still the archimedean $\log M$. Long support removes the short-support objection, not the subsidy. |
| Coupled low–high positivity settles the low scales | It needs every low mode tied to a high mode with $\lvert\gamma_n\rvert\ge\gamma_0$, or a standalone low-window certificate; the isolated low window is not proved positive. |
| A strict Suzuki deficit on the critical family is a sign of the Suzuki form | Even with a shift interval $(0,\omega_0)$ uniform across all patterns $b$, all blocks $S\subseteq[M,2M]$, and all $k\ge k_0$ (`exists_common_suzuki_shift_dyadic_blocks`), the critical-family deficit is paid by the $\log M$ archimedean gain while the literal unsubtracted polar window grows as $A_V\asymp 2\log V$; genuine zero-width progress requires a graded odd receiver Suzuki floor without archimedean subsidy (`zetaZeroWidth_le_of_graded_odd_suzuki_deficit`). |
| Window or high-height positivity is critical-scale progress | Windows through $3/10$ (all profiles) and $181/500$ (odd) are paid by sign-changing gauges on the archimedean conductance and one prime atom, heights beyond the horizon by the Gamma factor alone; neither sees the critical scale. |
| A window through $3/10$ is a theorem about $\zeta$ | No prime power enters an aperture-$3/10$ window ($\log2>3/5$), so every arithmetic weight is Weil-positive there. |
| A sign is required of the complete form | A floor losing less than an exponential in the aperture already gives RH: $\hat Z(F)\ge-C\int F^2$ on all odd $C^2_c$ tests is RH, and $-C_\sigma e^{2\sigma r}$ is the strip $\frac12+\sigma$. The demand is an exponent, not a sign. |
| A better constant in the rate-$1/2$ floor is progress | $78$, $8+\varepsilon$ and the de la Vallée Poussin saving all keep rate $1/2$, the depth of the polar pair. Progress is an exponent below $1/2$. |
| Buying the exponent at the archimedean place | An inequality boosted by an archimedean term of exponent $\theta>1/4$ is satisfied by the all-ones weight, of maximal defect; the boost removes the criterion. A loss constant or linear in the aperture is harmless, one growing with the frequency of the test is fatal. |
| Enlarging the aperture is free progress | At aperture $a$ the $\ell^1$ prime cost is $\asymp2e^{a}$ while a depth-$\delta$ off-line zero amplifies by $e^{2\delta a}$; the exponents coincide at $\delta=\frac12$. Every height-uniform aperture method floors at width $\frac12$; improvement needs a power saving in the single-height prime bound. |
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
not with a hidden threshold premise. Energies that may diverge are valued in
`EReal`, so that an infinite Lévy integral is $+\infty$ and finiteness of the
arithmetic channels is a separate theorem. Positive-integer ranges are encoded
by natural offsets such as `n+1`; dyadic blocks are the predicate
`DyadicScaleBlock S M`, scale windows `ScaleWindow S M L`; public capstones carry data
parameters only and no analytic, positivity or zero-location hypotheses. Constants are named
definitions (`factorialTailTranslationConstant`, `criticalArchLogSlope`,
`criticalCollaredPrimeConstant`, …) rather than inline numerals. RH appears only as the
conclusion of an implication or inside an equivalence.

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **Which independently checkable features of an exact source pay the sign of the complete
   form?** Across the full class `AdmissibleHarmonicWeight w C_w τ` (including all $q$-adic
   sign-flip and drift-free divisor stencils and all higher-order non-Bernoulli filters): a
   dominant first harmonic ($\sum_{k\ge2}\lvert w_k\rvert\le\tau<1$) and inverse-square harmonic
   envelope ($\lvert w_k\rvert\le C_w/k^2$), which yield physical window Riesz bounds, low-band
   Mellin exclusion, and an $\ell^2$-uniform prime channel on dyadic blocks, while the sign of the
   Poisson-closed cell kernel $R_\chi(t)$ is governed by whether $\chi(2)$ flips sign.
2. **Which sign does the arithmetic itself carry?** At the critical envelope the limiting prime
   channel is negative definite with an exactly known spectral range, and the actual channel
   keeps that sign on windows of linearly growing dimension: the primes help. What they do not
   do is pay the polar pair, which is where the rate-$1/2$ floor comes from.
3. **When is positivity of a large explicit family information about RH?** Only through a
   transfer to the complete receiver whose norm cost survives the loss of the archimedean gain
   $\log M$. The tent family shows that the laboratory contains a complete RH test family with a
   $(1,0)$-norm-controlled transfer; the critical family shows that it contains large positive
   subfamilies; no theorem connects the two with a controlled norm.
4. **At what rate may a floor lose in the aperture?** The receiver is graded: a subexponential
   loss on all odd compact tests suffices, and a loss $C_\sigma e^{2\sigma r}$ gives the strip
   $\tfrac12+\sigma$. Known prime inputs give rate $1/2$; the question is which source estimate
   beats it.
5. **Is the statement selective, or only the proof?** Wide-window positivity on shift pairs
   $g+g(\cdot-L)$ ($L>\max(L_0,\log2)$) is unconditionally selective against the non-tempered shifted
   pair $\zeta(s-a)\zeta(s+a)$ for every $a\ne0$, driven purely by prime powers in
   $[e^{L-1/2},e^{L+1/2}]$ (`exists_wide_shiftPair_shiftedPairVonMangoldt_neg`), and in the critical
   prime channel the odd prime $m=3$ flips the cumulative harmonic charge $\sum_{m=1}^N A_a(m)/m^3$
   strictly positive at $N=3,4$ for $\lvert a\rvert\ge2$ while $\sum_m A_a(m)/m^3$ diverges
   (`shiftedPairCumulativeCharge_three_pos_of_two_le`,
   `not_summable_shiftedPairHarmonicCharge_div_cube_of_two_le`). By contrast, on the compact
   critical family $g^V$, every $C$-tempered weight $\lvert w(r)\rvert\le C\Lambda(r)$ (including
   Beurling/node-deleted weights such as $\Lambda\cdot\mathbf 1_{r\ne4}$ and
   $\Lambda\cdot\mathbf 1_{r\text{ prime}}$) satisfies uniform-in-$V$ polynomial-window Weil
   positivity (`exists_temperedWeight_polynomial_window_weilFullFunctional_pos`), and at fixed $V$
   every weight whatsoever is eventually positive (`exists_fixedV_polynomial_window_pos_for_any_weight`):
   the admissible-source law, collared dilation inequality, and Montgomery–Vaughan endpoint bound are
   purely $C$-tempered infrastructure, and node-criticality tests (`not_zeroPoleBlindPositiveOn_diff_four`)
   are what refute prime-square deletions.
6. **Which source space carries a positive realisation of the complete arithmetic form?** A
   positivity theorem on the complete critical family and a spectral realisation of it would be
   the same theorem.
7. **What does a finite amount of nonnegativity exclude?** At a single finite scale $n$ and
   radius $R$, nonnegativity of the real and imaginary grid patterns gives the explicit lower floor
   $\Re\mathcal W_\zeta(f,f)\ge-2C_{\mathrm{grid}}(R,M_g,K_g,L)\,d_{n+1}$, and eventual grid-tent
   nonnegativity on $[-R,R]$ ($R\ge e^6$) unconditionally excludes all zeros of depth $\ge 1/R$
   below $\mathrm{zetaClusterHorizonHeight}(A_0,R)=\exp(R/(10^5A_0(\log R)^2))-306$ without an
   attainment or depth-gap premise, as well as near-top zeros above $\mathrm{oneParamExcludedDepth}$,
   $\mathrm{nearTopExcludedDepth}$ and $\mathrm{nearTopLogLogExcludedDepthOffLine}$.

### 6.2 Tools

Built and reusable:

- *Clock calculus.* Regularity read through the clock $v=e^{-x}$, translation energy split at the
  arithmetic scale $h=1/N$, physical weights $v^{-(2\beta+1)}$ and the envelope table of §2.6;
  global clock-Lipschitz interpolation for autocorrelation jumps.
- *Zero-divisor sampling.* Half-plane local holomorphy, multiplicity-exact disk overlap and strip
  energy give bounds on $\mathcal Z$ with no zero location.
- *Independent comparison form.* Positivity transfers through $\mathcal Z$ with the sharp Krein
  radius; Cauchy–Schwarz is never applied to $\mathcal W$ itself.
- *Nonstationary Mellin exclusion* (with and without boundary term) and the *admissible-source
  law*: a mass floor plus a low-band exclusion gives logarithmic Lévy growth in the band edge.
- *Dilation calculus.* The dyadic dilation inequality (a Schur test on the cross-scale kernel),
  the Montgomery–Vaughan bound for the endpoint jump kernel, the sharp ring majorant
  $\mathcal M_{\mathrm{win}}(L)=\log L+O(1)$, the log-ratio cross-block coupling and the
  downward decay $\tau(m,n)$.
- *Critical kernel calculus.* The divisor charge $A(m)$ and its cumulative charge, the
  band-limited Poisson closure of the cell, the Toeplitz symbol, the spectral perturbation bound
  around the curvature constant $I_0$, two-sided $1/k^2$ coupling laws, and the quadratic shape
  of $R$.
- *Linear-window limit comparison.* Uniform prime and harmonic tails, the cardinality-free
  affine clock comparison and resonance-exact affine heads, with parameters chosen in the order
  $R,K,\delta,N_0$: the template for comparing an actual arithmetic form with its limit on
  supports of growing dimension.
- *Full-form stability.* Every channel is Lipschitz in $L^1$ distance with explicit value and
  slope moments, so one accuracy index pays for tents of arbitrary support.
- *Receiver transfer and quantitative grid-tent detection.* The channel-by-channel parity split,
  $(\alpha,\beta)$-norm-controlled subfamily transfer to the zero width, the reflected prime–polar
  ledger of odd tests, finite-scale complex-to-tent approximation within $2C_{\mathrm{grid}}\,d_{n+1}$,
  and the fixed-aperture excluded-depth and horizon-height laws.
- *Scale-free Schur complement.* Shift-adapted Young weights give a bilinear Schur-complement
  inequality across all four channels with a cross constant independent of the high scales.
- *General admissible-weight and stencil calculus.* The `AdmissibleHarmonicWeight w C_w τ`
  interface unifying $q$-adic sign-flip stencils, $q$-adic drift-free stencils, and higher-order
  non-Bernoulli filters through Bohr/window Riesz coercivity, general dyadic dilation bounds,
  all-five-forms block positivity, receiver landing, and Poisson-closed cell-kernel sign laws.
- *Wide-window prime selectivity and tempered infrastructure calculus.* Laplace-transform integration
  of finite prime window sums over $L\in(L_0,\infty)$ against `shiftMajorant`, shifted-pair harmonic
  charge sign classification and cumulative-charge reversal, and the `TemperedPrimeWeight w C`
  transfer on compact critical sources separating uniform-in-$V$ ($\exists M_0,\forall V$) from
  fixed-$V$ ($\forall V,\exists M_0$) positivity.
- *Universal Suzuki first-variation envelope and common-shift calculus.* Source-independent Beta-tangent
  remainder `suzukiUniversalPrimaryRemainder`, degree-$1$ homogeneous envelope
  `suzukiFirstVariationEnvelope`, $k$-uniform mollified correlation envelopes via
  `autocorr_smooth_sub_le`, and subsidy-free graded receiver transfer from small-shift Suzuki deficits.

To be built:

- a standalone positivity certificate on the isolated low window;
- a norm-controlled transfer from a positive subfamily to the receiver that does not consume
  the archimedean gain.

---

## 7. Research boundaries and open questions

### 7.1 The isolated low window

Every high block, window, truncation and lacunary or dense union is positive, and low modes
coupled to high modes are positive. What remains at low scales is a standalone certificate: is
$Q(g^V_{\mathrm{low}})\ge\mu_{\mathrm{low}}E_{\mathrm{low}}$ with $\mu_{\mathrm{low}}>0$ for every
pattern on a window $[1,L_{\mathrm{low}}]$ below the block threshold, with no high-scale
coupling? By the Schur complement of §3.13 such a certificate is all that stands between the
critical family and positivity on the whole product space of scales. The archimedean gain is
bounded there, so a certificate has to come from the arithmetic channels, and it is a genuine
test of whether the family carries information beyond the subsidy.

### 7.2 From the critical family to the receiver without an archimedean subsidy

Which compact approximants of critical sources inherit block positivity with a margin
surviving truncation, stated so that the gain $\log M$ plays no role? The target is graded: a
floor losing $Ce^{2\sigma r}$ at aperture $r$ reports the strip $\tfrac12+\sigma$, and a loss
bounded uniformly in the aperture reports RH. Through the receiver ledger the problem is
concrete: beat rate $1/2$ in $\int_0^{2r}E(s)\,w_F(s)\,ds$, the prime–polar pairing of the
two-pole Chebyshev defect against the lag weight of an odd test, using cancellation between the
prime measure and the polar density $2\cosh(t/2)$ rather than bounds on either. A margin that
grows with the frequency of the test is not a weaker form of the same statement: it is
satisfied by the all-ones weight and reports nothing. Arithmetic Compensation Theory and
Bi-Scale Uncertainty attack the same cancellation from the prime side.

### 7.3 A power saving over the $\ell^1$ prime cost at a single height

The certified aperture of single-height positivity is $\log\log T-\log4$, where the $\ell^1$ cost
$\asymp2e^{a}$ meets the archimedean $\asymp\log T$; a depth-$\delta$ zero at that height is
visible from aperture $(\log\log T)/(2\delta)$. Improving the width through the aperture face
means certifying aperture $(1+\varepsilon)\log\log T$, that is a single-height prime bound
$\ll(\log T)^{1+\varepsilon}$ for $X=(\log T)^{2+2\varepsilon}$. Uniform-in-height bounds cannot give
it, and excluding near-alignment at a given height is a simultaneous-approximation problem on
prime logarithms whose effective bounds are far too weak. Which arithmetic input, using the
actual height-dependent phases, replaces them? Trans-Threshold Pair Correlation studies the
mean-square counterpart.

### 7.4 Quantitative detection

The grid-tent detection theorem of §3.14 gives a starting point: nonnegativity of the real and imaginary grid patterns at a
single finite scale $n$ and radius $R$ certifies the explicit lower floor
$\Re\mathcal W_\zeta(f,f)\ge-2C_{\mathrm{grid}}(R,M_g,K_g,L)\,d_{n+1}$, and eventual grid-tent
nonnegativity on $[-R,R]$ ($R\ge e^6$) unconditionally excludes every zero of depth $\ge 1/R$ below
$\mathrm{zetaClusterHorizonHeight}(A_0,R)=\exp(R/(10^5A_0(\log R)^2))-306$ (and below
$\mathrm{clusterHorizonHeight}(A_0,k,R)$ under local count $\le k$) with no attainment or depth-gap
premise, as well as near-top and equal-depth cluster zeros above their explicit excluded-depth
thresholds (`zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg`,
`zeta_gridTentPattern_visibility_and_height_reduction_duality`). What remains on the quantitative
detection face is to replace the cluster-packet horizon $\exp(R/(10^5A_0(\log R)^2))$ by the
doubly-exponential log-log horizon $\exp(\exp(\Omega(R)))$ unconditionally (currently proved under
`OffLineCopiesLocallyBounded M` in `zeta_loglog_near_top_excluded_depth_of_gridTentPattern_nonneg_of_offLineCopiesLocallyBounded`).

### 7.5 Beyond the factorial family

The admissible-weight calculus of §3.13 already covers every harmonic weight sequence in
`AdmissibleHarmonicWeight w C_w τ` ($w_0=0$, $w_1=1$, $\lvert w_k\rvert\le C_w/k^2$,
$\sum_{k\ge2}\lvert w_k\rvert\le\tau<1$) — including all $q$-adic $3$-scale sign-flip stencils on
$\{1,q,q^2\}$, all $q$-adic $3$-scale drift-free stencils with vanishing linear and quadratic
drifts, and all higher-order non-Bernoulli filters $w_k=c_k/k^p$ ($p\ge3$) — satisfies the mass
floor, low-band Mellin exclusion, $\ell^2$-uniform prime and polar bounds, high-scale block
positivity in all five forms of §2.2, and explicit $(\alpha,\beta)$-norm-controlled receiver
landing (`exists_general_all_five_forms_and_actual_zeta_coercivity`, `generalCriticalEvenOddLanding`).
Moreover, the Poisson-closed cell kernel $R_\chi(t)$ exhibits a sharp sign dichotomy: non-negative
multipliers $\chi\ge0$ with $\chi(1)=1$ and $\chi(2)>0$ or $\chi(3)>0$ (such as odd-$q$ sign-flip
stencils and positive higher-order filters) have strictly positive cell kernels $R_\chi(t)>0$ on
$[0,1]$ (`generalCriticalPrimeContinuousRealKernel_pos_of_nonneg_chi`), whereas dyadic and
multi-scale sign-flip perturbations $\chi_{d,\varepsilon}$ ($d\ge3$) have strictly
negative-definite cell kernels $R_\chi(t)\le-1/14000<0$ across $[0,1]$
(`exists_nonDyadic_stencil_negative_definite_cellKernel`). What remains open beyond the admissible
harmonic class is whether a multi-scale stencil with $\chi(2)<0$ can simultaneously make the cell
kernel $R_\chi(t)$ negative definite *and* cancel the polar pair at low scales without archimedean
subsidy.

### 7.6 The prime channel beyond linear windows

The actual critical prime form is negative definite on windows $[N,(1+\delta)N]$, with
$\delta\le1/(4K(R+1))$ forced by the affine head, and the dilated collar drift stays below
$1/140$ exactly up to the square-root window $L\le\sqrt M$. Does negativity persist on windows
$[N,N^{1+\delta}]$, or on all scales at once? Beyond $\sqrt M$ the resonant congruence progressions
leave the affine regime and the limit comparison must be replaced by an argument that sees the
progressions themselves.

### 7.7 Selectivity beyond the calibration families

Wide shift pairs already refute every nonzero shifted zeta pair, and the
critical-family estimates already extend to every tempered prime weight
(§§3.13, 4). These are established boundaries, not missing tests. The open
question is which source mechanism distinguishes the literal von Mangoldt
weight from tempered perturbations while controlling the complete form at
arbitrary aperture. A candidate must retain the prime-power information that
high-scale archimedean domination discards. Node-deletion and narrow-pair tests
provide exact diagnostics; passing those diagnostics alone supplies no sign.

### 7.8 A positive spectral realisation

Which arithmetic construction produces a positive realisation of the complete
form, with a source space and topology strong enough for receiver transfer?
Self-adjoint and indefinite realisations already exist. The prime perturbation
is not disposed of by declaring it finite rank, trace class, or finite
deficiency. Any proposed limiting ground transform must prove its convergence
to the completed zeta function and the sign of the remaining prime contribution.
The spectral representation is useful only if those facts follow from
independent arithmetic estimates.

### 7.9 From identification to sign

Narrow pair tests recover every coefficient $w(m)$, and full-cone uniqueness
excludes every nonzero single-index perturbation of $\Lambda$. One-sided cone
selection is also characterised exactly (§4): its assertion already contains
RH. Thus identifying the actual source, separating perturbations, and deriving
equivalent sign criteria are available tools.

The remaining problem is to prove one of the additional estimates for that
identified source: an aperture-uniform odd-test floor, its subexponential
version, or the equivalent prime-power deletion slack. A proof must use more
than the fact that the source equals $\Lambda$. These formulations locate the
arithmetic input; none supplies it.

### 7.10 Suzuki transport at the critical boundary

Common shifts on bounded-envelope families, joint $L^2$ limits on a fixed
window, and moving-aperture transport under supercritical correlation decay
are established mechanisms (§3.15). Their constants and hypotheses specify
what may vary together. In particular, a shrinking threshold from the compact
polar majorant is not an impossibility theorem for every truncation scheme.

The research questions are whether critical-decay families can be controlled
without the absolute $\beta>1/2$ margin, and whether the literal source gives a
graded odd-receiver deficit with exponent below the elementary rate $1/2$.
The latter would improve the zero-width bound. A familywise common shift,
without that receiver estimate, does not. Any extension must preserve the
signed prime–polar cancellation while allowing the source, shift and aperture
to move; exchanging their limits without a common bound is precisely the trap.

---

## 8. Working in the theory

Start from the source dictionary of §2.3 and keep the clock substitution
$v=e^{-x}$ explicit: every estimate is proved on $v\ge1$ with the physical
weight $v^{-(2\beta+1)}$ and transported back. Prove integrability and
summability before integrating or summing, and prove limits in every channel
rather than in a convenient one. Make $\ell^2$-uniform statements on dyadic
blocks or linear windows and fixed-support statements with nested eventual quantifiers; never
hide a threshold. Reuse the corpus: Montgomery–Vaughan interval mean squares,
the scalar $\int(1-\cos tv)/v^2=\pi\lvert t\rvert$ kernel, scalar
integer-cosine orthogonality, the real $L^1$ periodisation and its zero Fourier
mode, the band-limited sinc-square identities and their Poisson sum, the
Gamma–Lévy identity and the logarithmic weight comparison, the Lévy symbol
bound, the nonstationary Mellin bounds with and without boundary term, the
dyadic dilation inequality, the admissible-source law, the receiver ledger, and the unit-height
packet count. Before proving anything about the complete form, check whether
the statement is already a theorem in one of its other four names. Search the
corpus before proving anything new, and verify each name in a scratch file in
this toolchain. State every new result at its exact scope: family, scale range,
smoothing quantifiers, block structure, and which channels are included. Report a partial
result as a rate or a strip, not as progress towards a sign. When a mechanism fails, extract
its strongest positive survivor as a sharp boundary or classification before retiring it.
Comments in Lean are mathematics; status, dates and logs belong on the pipeline cards.
