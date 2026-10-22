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

## The shared target: the sign of the critical arithmetic form

Nine programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
one critical arithmetic form, and the form can be read in three equivalent faces:

- the **incidence face** (Arithmetic Incidence Positivity, `ArithmeticIncidencePositivity`):
  conductance by conductance, on pairs of points `(x, y)` of the logarithmic line, with the
  arithmetic edges indexed by divisibility (`a ∣ b`) and by products (`ab` a prime power), and the
  pole as the only positive source on crossing pairs;
- the **lag face** (Square-Root Threshold, `SquareRootThreshold`): one window inequality `P_v ≥ 0`
  per scale on the prime side, for the difference tests of one generic width, at height `T` and
  bandwidth `λ = log X / log T`;
- the **aperture face** (Arithmetic Criticality Theory, `ArithmeticCriticalityTheory`; Arithmetic
  Positivity Theory, `ArithmeticPositivityTheory`; the odd Weil-weight route OWU in `RHTower`): the
  ground-energy path `μ(A)` of the restricted Weil form at aperture `A`, which must never cross zero,
  and the gauge and source theories that would prove it.

The finite arithmetic programmes (Bézout–Valuation Incidence, `BezoutValuationIncidence`;
Trans-Horizon Incidence Mechanics, `TransHorizonIncidenceMechanics`; Bi-Scale Uncertainty,
`BiScaleUncertainty`) supply the additive, single-modulus structure of the integers that the three
faces cannot see on their own: Bézout relations, residue classes, pronic Gram matrices, horizon
mechanics, and the two-scale constraint of the integer grid against the hyperbolic weight.

The continuation layer (Arithmetic Continuation and Critical Energy,
`ArithmeticContinuationAndCriticalEnergy`) supplies what no face states on its own: the transport
of a finite critical energy along a parameter — damping, coefficient cutoff or aperture — so that a
certificate at one parameter becomes a certificate at another, with the observation horizon
quantified uniformly throughout.

The admissibility layer (Scale-Signed Incidence Criticality, `ScaleSignedIncidenceCriticality`)
supplies the price list. A mechanism is not the arithmetic it studies but a *reading* of it — a map
from its data to the observables it actually uses — and each reading has an exact resolution limit:
the best bound on the target invariant that any method reading it can prove. The layer computes
those limits, so a route can be priced before it is built, and states the separations a reading must
perform to be admissible at all.

**Why one theory.** Each existing layer stops where the corpus proves it stops. Sieve and bilinear
methods see the additive structure of `ℕ` only after averaging over a family, and below half
damping no sign-blind datum decides the receiver. Multiplicative, spectral and explicit-formula
methods hold verbatim for Beurling systems with off-line zeros. Dirichlet-form and criticality
identities hold for every even positive kernel, and positivity on restricted families is paid by an
archimedean gain that is absent on the RH-complete cone. A closing theorem must at once see both
operations of `ℕ` at a single modulus, carry a sign structure (one negative square, the pole plane,
the signs of the Möbius row), and be resolved at the zero spacing, at square-root precision at every
scale. No existing field has its basic objects built with all three; the nine programmes build
them.

**The mechanisms the shared target needs**, with the programme that owns each:

1. A prime-side inequality with no slack: payment of each anti-diagonal atom `Λ(n) n^{−1/2}` by
   same-side atoms and the variance, on all even profiles, in sign-changing gauges, with a
   Harnack-type propagation across the prime shifts `log 2, log 3, …`
   (`ArithmeticIncidencePositivity` with `ArithmeticCriticalityTheory`).
2. Single-modulus bilinear dispersion on the pronic Gram, through the reciprocity
   `{N/pq} ↔ p̄/q + q̄/p`, for the actual Möbius or prime row; it reduces exactly to the
   single-modulus statistics `Σ_p |Λ_p(c')|/p` of that row (`BezoutValuationIncidence`).
3. A no-crossing law for the ground-energy path, equivalently the absence of a first negative lag
   for `ζ` (`ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory` and OWU on the aperture side;
   `SquareRootThreshold` on the lag side).
4. A definite spectral realization with a prime modification as large as `S(T)`: a Hilbert space
   and a self-adjoint operator whose spectral measure is the critical-zero measure, with
   non-unit-modulus Euler factors (`ArithmeticPositivityTheory` for the source class and the
   realization problem; the operators of the routes HF, CHMD and Connes–Consani–Moscovici in
   `RHTower`). Every certificate of positivity is the critical-zero measure, so this is mechanism 3
   seen from the other side.
5. A sign-reading additive input at a single modulus: below half damping a bound on the receiver
   must read the signs of the coefficients, through first-order data at prime moduli (`k ↦ pk`) or
   odd-degree additive moments (`k ↦ k + v`) (`TransHorizonIncidenceMechanics` with
   `BezoutValuationIncidence`; `BiScaleUncertainty` for the node criticality `log 4` against
   `log 6`).
6. A continuation theorem transporting a finite critical energy from the unconditionally admitted
   end of a parameter range towards the critical end: a horizon-free bound on the negative part of
   one complete signed pairing on each compact subinterval, which is weaker than a bound on the
   corresponding norm and already yields an explicit zero-free strip when it covers only part of
   the range (`ArithmeticContinuationAndCriticalEnergy`).
7. An admissible reading: a mechanism presented as a reading of its own data whose fibres fail to
   realise the maximum of the invariant it claims to bound. On the zero side this forces the
   aperture past the Nyquist aperture of the configuration addressed and forces the *size* of the
   Weil deficit to be estimated rather than its sign; on the prime side it forces `Λ` to be
   separated from each of its single-index perturbations
   (`ScaleSignedIncidenceCriticality`).

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH (test models: `BiScaleUncertainty`).
- *No family average.* One character, modulus one, shift zero. This is an exact floor and not a
  preference: the worst width inside a joint certificate over a family of any cardinality is the
  trivial one, because the extremal datum is already uniform across the family.
- *Square-root precision beyond the diagonal.* Prime sums of length at least the height,
  controlled beyond the mean-value regime: one inequality per window at every scale on the lag
  family, `θ = 2` on the Gram. On the aperture face the same demand is a theorem: a method
  controlling the Weil deficit of a configuration of scale `L` to precision `η` resolves depths
  only down to `√(η/L³)`, so excluding depth `β` costs precision `β²L³`.
- *Every scale, not almost every.* A statement about an exceptional set, a proportion or a typical
  member is infrastructure (the every-height problem: `SquareRootThreshold`). The two monotone
  faces may be verified along an unbounded sequence of apertures or radii, with nothing proved in
  between; the incidence face admits no sampling at all, since every prime power is individually
  necessary.
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Signs read.* Below half damping the mechanism uses first-order data at prime moduli or
  odd-degree additive moments; magnitude, two-point and translated-moment data are blind, since the
  parity pairs exist at every damping `ε ≤ 1/2`.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction. The dividing line
  is growth, not size: a subsidy growing with the frequency of the test is satisfied by the
  all-ones weight and removes the criterion outright, while a subsidy constant or linear in the
  aperture leaves it intact.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)` and by
  the visibility lag `V₀(w, η, δ₀)`; damping by the smallest `ε` at which the receiver is bounded;
  admissibility by the pair (class of readings, exact resolution limit). Identities, finite
  classifications and nonselective positivity count as zero in these units.
- *Grading.* A sign criterion with no partial value is incomplete. Every face of the target now has
  a one-parameter family whose endpoint is RH and whose interior is an explicit zero-free strip:
  the graded odd-sector floor and the graded incidence allocation at rate `2σ`, the graded pole
  cross entry at rate `1 + 2α`, and the partial damping continuation above `a₀`. State which member
  of the family a partial result reaches.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done
  (`BiScaleUncertainty`).
- *Pairs.* Every invisibility theorem comes with a visibility witness, every identity with the
  estimate it enables or the sharp boundary it proves, every obstruction with its replacement
  hypothesis proved sufficient.

### This programme's role

APT is the source theory of the aperture face. It owns the complete Weil form on exact arithmetic
sources with every endpoint, collar, Gamma and polar term kept, the critical factorial family, block
positivity, and the two universal receivers as destinations. It must supply the passage from the
critical family, where the arithmetic is favourable, to the compact tests of the receiver without an
archimedean subsidy (mechanism 3 and the criteria of complete expression and no subsidy), and the
admissible source class on which the prime modification of mechanism 4 can be realized. It is the
programme home of mechanism 4, the definite spectral realization: the operators themselves (HF,
CHMD, the finite-aperture operators of Connes–Consani–Moscovici) live in `RHTower`, and APT owns
the question of which sources and which Hilbert space carry a prime modification as large as
`S(T)`. Every certificate of positivity of the complete form is the critical-zero measure, so a
positivity proof and such a realization are one object.

The obligation is graded rather than binary. The sign of the complete form on odd compact tests may
be replaced by any floor that loses less than an exponential in the aperture: a floor
`Ẑ(F) ≥ −C ∫F²` on all odd `C²_c` tests is RH, and a loss `C_σ e^{2σ r}` at aperture `r` is the
zero-free strip `Θ ≤ ½ + σ`. The unconditionally available floor has rate `1` — the prime `ℓ¹` norm
`Σ_{n ≤ e^{2r}} Λ(n) n^{−1/2} ≍ 2e^{r}` — and the true rate of the floor is `2 · width`. So APT is
asked for an exponent, not a sign, and the exponent must be bought by a power saving over the
`ℓ¹` cost. What is excluded is paying for the exponent at the archimedean place: an inequality
boosted by an archimedean term of exponent `θ > ¼` is satisfied by the all-ones weight, which
differs from `Λ` already at the index `2`, so a boosted cone pins no source at all while the
unboosted cone pins `Λ` at every index.

### How the programme connects to the other programmes

APT is the one programme of the family built on a concrete noncompact exact source rather than on
a space of test functions. Everything it proves is transported to the others through the
dictionary of §2.2 (one form, five names), and most of its analytic inputs come from them.

- **Bi-Scale Uncertainty supplies the sources.** The factorial Müntz family (the tail primitive,
  the analytic repair of the readout across the negative pole, the zero-side smoothing limit, the
  prime–polar budget, the Weil smoothing and the Gram decoupling of the tent direction) and the
  signed prime–polar jump domain are BiScale objects (`SignedPrimePolar`); APT's sampling,
  Gram-margin and smoothing-limit theorems continue them. The archimedean log-coercivity of the
  critical scale uses BiScale's logarithmic increment energy and origin-collar leverage; the
  compact truncations use its compact Lipschitz Lévy energy and its polar moment identity. In the
  other direction BiScale owns the test models (the shifted pair `ζ(s−a)ζ(s+a)`, Beurling
  systems, the Liouville twist) and the function-field calibration against which every APT
  positivity statement is audited; the windows-of-scales theorem of §3.13 is the APT statement
  whose proof is selective, and the separation is now a theorem rather than a remark: the
  summability hypothesis the proof consumes, `Σ Λ(r) r^{−1−ε(L)} ≤ 6(3 + log L)`, fails for the
  shifted pair at every exponent `ε ≤ |a|`, hence on every window of width `log L ≥ 1/|a| − 2`.
- **Square-Root Threshold supplies the zero side.** APT never locates a zero. The configuration
  object, the pairing `𝒲`, the mass `𝒵`, the reflection defect `ℛ` and the visibility laws
  (isolated pairs, finite off-line sets, depth gaps, equal-depth clusters, attained depths, large
  dyadic prime windows, windowed blindness, the prime-tail coupling criterion, single-height
  positivity above the archimedean horizon) are SRT theorems; the tent family becomes a detector
  on the actual zero set by composing them with APT's grid convergence and joint smoothing. SRT's
  explicit visibility lags `V₀(w, η, δ₀)` and its horizon law are the units in which APT's
  quantitative-detection problem has to be answered, and SRT's zero width `sup|Re ρ − ½|` is the
  quantity the tent detectors measure.
- **Arithmetic Criticality Theory supplies the receiver's coordinates on compact tests.** ACT's
  full zero form equals APT's complete physical energy on continuous compact sources, its Markov
  energy equals APT's Markov form beyond the support, and its ground-energy path `μ(A)` is the
  aperture-face reading of what APT proves at high scale. ACT's all-profile window through `3/10`
  and the criticality of `μ` at infinity bound APT's task from both sides: positivity through
  `3/10` is paid by sign-changing gauges with no critical-scale input, APT's block positivity is
  paid by `log M` with no small-aperture input, and neither crosses into the other's regime.
- **Arithmetic Incidence Positivity works on the same form at the opposite scale:** pairs of
  points and single prime atoms at apertures up to `181/500` on odd tests, against APT's
  unbounded-support patterns at scales beyond `M₀`. APT's parity decoupling (odd tests carry the
  whole pole risk `S(g)²/2`, §3.9) is the statement AIP's odd gauges address, and AIP's Harnack
  propagation across the prime shifts is what a passage from APT's family to the receiver would
  have to reproduce at every scale.
- **Trans-Horizon Incidence Mechanics and Bézout–Valuation Incidence hold the finite arithmetic
  APT does not see.** APT's prime channel on dyadic blocks is bounded by mean-value inputs
  (Montgomery–Vaughan, Mertens) and never by cancellation in a single arithmetic row. THIM's
  parity pairs explain why such size-only bounds cannot select `ζ` below half damping; BVI's
  coherent-block ceiling is the general statement that size-only bilinear bounds on arithmetic
  rows stop short of the receiver, and APT's cross-block decay, a size-only Cauchy–Schwarz bound
  over dilations, decouples only lacunary blocks for the same reason. The critical-scale receiver
  `D(T) ≤ B(1+T)e^{T/2}` of §1.2 is the receiver these programmes study at finite modulus.
- **Arithmetic Continuation and Critical Energy supplies the parameter direction.** APT proves
  positivity at a fixed scale, a fixed aperture and a fixed damping; the continuation layer owns
  the transport of such a bound along a parameter towards its critical end, with the observation
  horizon quantified uniformly. Its aperture instance is APT's own ground-energy path: a bounded
  *relative* decay of a positive ground floor forbids a crossing, with an explicit floor
  `μ(a) exp(−(β c − β a))`, and the certified endpoint `3/10` supplies the initial value. In the
  other direction APT's complete-expression discipline is what forbids the continuation layer from
  dropping an endpoint or a collar term when it differentiates in the parameter.
- **Scale-Signed Incidence Criticality prices the receivers.** It proves the two facts APT's
  central problem turns on: that an archimedean boost of exponent `θ > ¼` admits a weight of
  maximal defect and therefore removes the criterion, while a loss constant or linear in the
  aperture leaves it intact; and that the full Weil cone is a single point — a weight in it agrees
  with `Λ` at every index — so the admissible-source question of mechanism 4 is an identification,
  index by index, and not an inequality. It also supplies the quiet zone: no arithmetic weight
  whatsoever fails Weil positivity inside aperture `3/10`, so inside that window a certificate is
  constant and certifies nothing about any source.
- **RHTower supplies the analytic infrastructure:** the Weil–Markov–pole split, the full-cone
  Plancherel and Herglotz representations, the von Mangoldt mollifier mean square, van der Corput
  and Poisson summation, the CHMD divisor pairing, Baker's theorem, the Selberg near-line and
  Ingham–Huxley densities, the non-tempered shifted-pair countermodel and the causal von Mangoldt
  wall, and the operators (HF, CHMD, Connes–Consani–Moscovici) of mechanism 4 whose source class
  APT is to supply.

The other programmes use APT through its statements rather than its modules: the dictionary of
§2.2, the dyadic dilation inequality and the admissible-source law (§3.12), the parity decoupling
of the pole plane (§3.9), and the factorial tent family as an RH-complete receiver (§3.14).

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

The **absolute square-sampling mass**, the **zero-side Weil pairing** and the
**reflection defect** are
$$
\mathcal Z(f)=\sum_\rho m_\rho\lvert F_f(\rho)\rvert^2,\qquad
\mathcal W(f,g)=\sum_\rho m_\rho F_f(\rho)\,\overline{F_g(1-\overline\rho)},\qquad
\mathcal R(f)=\sum_\rho\frac{m_\rho}2\bigl\lvert F_f(\rho)-F_f(\overline\rho)\bigr\rvert^2 .
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
uniformly in the pattern. The Cesàro means of the long modulated patterns
$b_j=\cos(2\pi jt)$, $\sin(2\pi jt)$ on $j<L$ give
$(P_\infty(\cos_L)+P_\infty(\sin_L))/L\to(4/\pi^4)R(t)$, so the Rayleigh set
has supremum $(4/\pi^4)\max R$ and infimum $(4/\pi^4)\min R$: the exact
$\ell^2$ spectral range of the limiting prime form over all finite patterns is
the range of $R$, the optimal negativity constant is $-(4/\pi^4)\max R$, and
the extremal patterns are long frequency-modulated patterns concentrating at
the extrema of $R$. Sign and size questions about the limiting critical prime
channel are pointwise questions about $R$.

**Finite-scale negativity.** The actual prime energy of a pattern translated to
scale $n$ is the quadratic form of the finite-scale prime matrix $M_n(i,j)$,
obtained by expanding the translated autocorrelation bilinearly in the
single-scale sources; polarisation of the translated prime limit gives
$M_n(i,j)\to(4/\pi^4)\kappa(\lvert i-j\rvert)$ entrywise. Hence for every finite
support $S$, eventually in $n$ and for all coefficient vectors at once, the von
Mangoldt channel on the span of the critical sources at scales $n+S$ is at most
$-(2/(7000\pi^4))\sum b_j^2$: the favourable sign is a finite-scale fact, not
only a limit.

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
the logarithm of the width: the correlation of two dilation rings is
$O(\min(1,\sqrt{L/r}))$, and summing $\Lambda(r)r^{-1}(L/r)^{\varepsilon}$ at
$\varepsilon=1/(2+\log L)$ against the tempered critical-line bound gives
$\lvert P\rvert\le C_W(3+\log L)\sum b_j^2$ (`abs_criticalPrimeEnergy_le_of_window`).
The archimedean gain is $\log$ of the smallest scale and the prime cost $\log$ of
the width, so the form is positive definite on every window $[M,M^{1+\delta}]$
spanning polynomially many dyadic blocks (`exists_criticalCompleteEnergy_pos_of_window`).
**The temperedness gate.** The exponent $\varepsilon(L)=1/(2+\log L)$ is the hinge of
the window bound, and it is a gate rather than a convenience. On one side the raw
critical-line weight $\Lambda(r)/r$ diverges, while the window exponent restores
summability with an explicit width-logarithmic sum,
$\sum_r\Lambda(r)r^{-1-\varepsilon(L)}\le6(3+\log L)$ for every $L\ge1$
(`summable_vonMangoldt_windowDilationExponent`). On the other side the shifted pair
$\zeta(s-a)\zeta(s+a)$, $a\ne0$, has von Mangoldt weight
$\Lambda(r)(r^a+r^{-a})$, which dominates $\Lambda(r)r^{\lvert a\rvert}$, so
$\sum_r\Lambda(r)(r^a+r^{-a})r^{-1-\varepsilon}$ diverges for *every*
$\varepsilon\le\lvert a\rvert$ and in particular on every window with
$\log L\ge1/\lvert a\rvert-2$
(`not_summable_shiftedPairVonMangoldt_div_rpow_of_le_abs`,
`not_summable_shiftedPairVonMangoldt_windowDilationExponent`). The separation is
therefore proved, not observed: the shifted pair does not merely fail to satisfy the
window conclusion, it fails the single summability hypothesis the proof consumes, and it
fails it on all wide windows at once. This is the one place where the selectivity
criterion of the shared target is met by an identified arithmetic input — the
temperedness of the prime channel of $\zeta$ — rather than by a sign. It separates the
*proof* from the shifted pair; whether the *statement* also separates them is open, since
nothing here forbids a wide-window positivity for a non-tempered twin proved another way.

**Compact truncations.** The doubly collared source $g^V=\chi(e^{-x}/V)\,g_c$ is
compact, supported in $[-\log2V,0]$. The two cutoffs merge in the correlation law,
the transforms of the truncated weights are bounded uniformly in the truncation,
the tail mass of the archimedean energy is at most $(U/V)E$, and block positivity
survives with a margin uniform in $V$
(`exists_criticalTruncatedCompleteEnergy_pos`). On these compact tests the complete
energy is the Weil functional, $\operatorname{Re}W_\Lambda(g^V\star\tilde g^V)=E(g^V)$,
so the Weil form of $\zeta$ is positive on compact tests of arbitrarily long
support at every high block, unconditionally
(`exists_compactFullWeilEnergy_criticalTruncatedTest_pos`). This positivity is not
the small-support regime: it comes from the logarithmic coercivity of the critical
family against an $\ell^2$-uniform prime channel.

**Windows and truncations together.** The two mechanisms compose, and the composition is
the strongest unconditional positivity statement the theory has on compact tests. The
window correlation bound holds for the *truncated* collar weight with a constant
independent of the truncation, so the window prime energy of a compact doubly collared
source obeys $\lvert P\rvert\le C_{TW}(3+\log L)\sum b_j^2$ uniformly in $V>0$
(`abs_criticalTruncatedWindowCorrelation_le`,
`abs_criticalTruncatedPrimeAtom_le_of_window`,
`abs_criticalTruncatedPrimeEnergy_le_of_window`). Against the truncated archimedean
slope this gives
$$
E(g^V)\ \ge\ \bigl(s_T(\log M-c_T)-K_{T,0}-2C_{TW}(3+\log L)\bigr)\sum_jb_j^2
$$
for every window $[M,LM]$ and every $V\ge V_0$, with no constant depending on $V$. Hence
there are $\delta>0$ and $M_0$ such that on every polynomial window $L\le M^\delta$ with
$M\ge M_0$, every truncation $V\ge V_0$ and every nonzero pattern, the compact test
$g^V$ — of support $[-\log2V,0]$ and therefore of *arbitrary* length, covering every prime
power $r\le\lceil2V\rceil$ — has strictly positive energy with margin
$(s_T/4)\log M\sum b_j^2$, simultaneously in four of the five names of §2.2 — the complete
critical energy, the compact full energy, the full zero form of Arithmetic Criticality Theory, and
the real part of the literal $\Lambda$-weighted explicit-formula functional, all equal on $g^V$
(`exists_polynomial_window_compact_weil_and_fullZeroForm_pos`). Mollifying into
$C^2_c(\mathbb R,\mathbb R)$ at rate $O(1/(k+1))$ carries half the margin into the fifth
name, the actual zeta divisor:
$$
\mathcal R(F_k)+\tfrac{s_T}8\log M\sum_jb_j^2\ \le\ \mathcal Z(F_k)
$$
for all large $k$ (`exists_smooth_actual_zeta_reflection_coercivity_of_compact_window`).
So on arbitrarily long compact tests, built from arbitrarily wide polynomial scale
windows, the readout of the literal zeta zero divisor at a zero is strictly closer to the
readout at its mirror image than the trivial mass allows — unconditionally, with an
explicit margin growing like $\log M$. The margin is still the archimedean gain, so this
is reach, not selectivity; what it removes is every remaining suspicion that the critical
family's positivity is an artefact of short support, of a single dyadic block, or of a
noncompact source.

**Across blocks.** The multi-scale prime coupling is an $\ell^2$-sum over dilations:
Cauchy–Schwarz over $r$ with the Mertens partial sum gives the cross-block decay law
$\bigl\lvert\sum_r(\Lambda(r)/r)\int\varphi_rB_b(v)B_c(rv)\bigr\rvert\le K\,\tau(m,n)\lVert b\rVert\lVert c\rVert$,
$\tau(m,n)=(1+\log n)\sqrt{1/n+m\sqrt{m/n}}$ (`abs_sum_integral_crossBlock_down_le`):
distinct blocks decouple once $n\gg m^3$. On lacunary families $M_{i+1}\ge M_i^8$
the decay sums, and the compact Weil form is positive on every pattern spread over
any number of such blocks (`exists_compactFullWeilEnergy_pos_of_lacunary`). Low
modes enter through a two-band split of the archimedean energy and scale-free
bounds on the polar and Gamma readouts, at a cost $O(\log)$ of the low window and no
exponential loss. The divisibility structure of the resonances $k(n+1)\equiv j\pmod{lr}$,
which would control dense windows uniformly, survives only for scale ratios up to
about the square root of the scale.

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

**Weil completeness.** A grid tent pattern is $e^{3x/2}$ times the
piecewise-linear interpolant of its nodal data; the interpolant keeps the
Lipschitz constant of the data and is within $2Ld$ of it, the exponential
transports Lipschitz control, and the stability bound gives
$\lvert Q(f_n)-Q(g)\rvert\le C\,d_n\to0$ with $C$ uniform. Hence every compact
$C^2$ test is a limit of single-scale grid tent patterns in the complete form,
and together with mollification of tent patterns in the other direction,
$$
\text{RH}\iff Q(f)\ge0\ \text{for every finite tent pattern}\iff
\forall G,\ R\ge0:\ Q\bigl(\text{grid pattern of }G\text{ on }[-R-1,R+1]\text{ at scale }n\bigr)\ge0
\ \text{eventually in }n .
$$
The factorial tent family is a complete RH test family inside the laboratory:
positivity theorems on it are exactly partial RH information.

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
Positivity. At any aperture the localised explicit formula gives nonnegativity
of $\mathcal Z-\mathcal R$ on height shifts beyond an explicit horizon. Off RH
the ground-energy path $\mu(A)$ has a first contact aperture, beyond $3/10$,
and a near-top zero seen by the lag family at lag $V$ forces $\mu(A)<0$ for
every $A\ge V/2+w$. High-height positivity is an archimedean fact; the
arithmetic question lives at finite height, on even tests beyond $3/10$ where
the conductances across $\log2$ turn negative, and at the critical scale.

### 3.15 Bridges

Unconditional zero-density inputs replace the abscissa-blind $O(\log T)$ count
of §3.4 by Ingham–Huxley and density-hypothesis exponents on abscissa slabs,
Route-T zero-free annihilation above $1-\mathrm{width}$, Selberg's exponential
near-line counts at distance $a/\log T$ from the line, and the Nyquist law that
a $C^2$ test of support radius $a$ detects an off-line vertical lattice of
period $L$ iff $a>L/2$. Baker's theorem supplies the spectral disjointness of
§3.10. The square-root-threshold bridge records that RH is equivalent to the
localized prime-tail inequality $\Re\Pi_f(\xi)\le\Re A_f(\xi)$ for all
apertures, profiles and heights, equivalently to a $2\times2$ pole
compression, while every compact $C^2$ profile is unconditionally positive at
all sufficiently large heights and the archimedean–pole budget cannot be frozen
at height zero. The five-way identity of §2.2 transports the single-shift
pole-free variation form of Arithmetic Criticality Theory to the exact
actual-zeta difference $\mathcal Z-\mathcal R$ on theta translates, and the
polar energy of a Doob source graph equals
$\cosh\text{-mass}(v^2)-2\cosh\text{-mass}(v)^2+2\sinh\text{-mass}(v)^2$, so on
odd profiles the pole term strengthens the odd Dirichlet–Poincaré inequality
by a square while remaining RH-equivalent. The Markov form of §1.2 agrees with
the Markov energy of Arithmetic Criticality Theory beyond the support, and that
theory shows the odd capacity ratio $S(g)^2/(2\mathcal M_N(g))$ tends to one
along plateaus, with no uniform margin at large aperture. The zero width
$\sup_\rho\lvert\Re\rho-\tfrac12\rvert$ is read by the lag family as the exact
exponential rate at which its dyadic prime windows turn negative, by the
ground-energy path as the rate in $\mu(A)\ge-Ce^{2\sigma A}$, and it bounds the
de Bruijn–Newman heat time by half its square; RH is width zero, and the tent
detectors of this programme measure the same width through the depths they
see.

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
| The Minkowski affine constant $(4/\pi^2)(\sum\lvert w_k\rvert\sqrt k)^2$ is sharp | The harmonic error layers are orthogonal up to $k\approx140N^2$; the sharp per-defect constant is $(63/16\pi^2)\zeta(3)$. |
| Divergence of $\sum\Lambda(r)/r^{\beta+1/2}$ at $\beta=1/2$ means negative energy | It is failure of an absolute majorant; the oscillatory majorant converges for all $\beta>-1/2$. |
| Fixed-pattern limit justifies a growing pattern | Constants retain $B_1,B_w$ and the limit is taken at fixed $(S,b)$; growing patterns need the dyadic-block laws. |
| Harmonic signs decide the total sign | $A(2)<0$ and all other $A(m)\ge0$, but the masses $J_m(b)$ are not independent; the sign comes from the Poisson-closed kernel. |
| The singleton mean is only a necessary condition | The kernel deviates from its mean by less than the mean's margin, so $R<0$ on the whole cell and the singleton decides every pattern. |
| Negative prime channel means negative Weil form | The Weil form subtracts the prime channel; the critical prime negativity is a positive contribution to the complete form. |
| The spectral range of $P_\infty$ is attained by short patterns | The extremal patterns are long frequency-modulated patterns concentrating at the extrema of $R$; short patterns see averaged couplings. |
| Irrational dilations contribute to the prime channel | The critical limit has rational spectrum; primes read only the integer atoms $\log r$, the atoms at $\log(p/q)$ feed the archimedean channel. |
| The archimedean channel is bounded at the critical scale | It diverges: the source decorrelates at almost every shift and $\omega(x)\ge e^{-1/2}/x$ is not integrable at the origin. |
| An $\ell^1$ prime bound transfers to $\ell^2$ | The admission bound is quadratic in $\sum\lvert b_j\rvert$; the $\ell^2$-uniform bound on dyadic blocks needs the dilation inequality for the collared part and the Montgomery–Vaughan inequality for the jump kernel of the endpoint. |
| A threshold "eventually in $n$" is uniform in the support | On a fixed support the threshold depends on $S$; $\ell^2$-uniform statements are made on dyadic blocks, where the logarithm is common. |
| The collar changes the prime channel materially | For $r\ge2$ the endpoint layer has no self-prime interaction; only its cross terms with the far part remain, through a Hilbert kernel. |
| Model detection is a zeta sign | The lattice-plus-pair model lacks the Euler product and calibrates the family; the actual-zeta detection theorems go through the visibility laws of the zero configuration. |
| The compact full energy, the full zero form, the explicit-formula functional and $\Re\mathcal W$ are different quantities | They coincide on compact continuous (resp. $C^2_c$) real sources; re-proving a fact in another programme's form is duplication. |
| Period or Bohr averaging at fixed scale is the physical limit | It erases the slow collar phase; the correct limit keeps $1-\cos(2\pi mv/12)$. |
| Replace the conditionally convergent polar readout by a Lebesgue integral | At $\beta=1/2$ the endpoint is defined through the bounded primitive, $-G(1)+\int_1^\infty G(v)v^{-2}dv$, with cutoff error $\le(24/T)\sum\lvert b_n\rvert/(n+1)$. |
| An endpoint value of the $L^1$ periodisation is a sign witness | The $L^1$ kernel and its continuous representative differ at integers; only pattern integrals matter. |
| Zero-density bounds exclude a zero | They are upper counts; a single fixed off-line zero survives all of them. |
| A window bound that holds for $\zeta$ holds for any twin | The window exponent $\varepsilon(L)=1/(2+\log L)$ is a gate: $\sum\Lambda(r)r^{-1-\varepsilon(L)}\le6(3+\log L)$, but the shifted pair's weight $\Lambda(r)(r^a+r^{-a})r^{-1-\varepsilon}$ diverges for every $\varepsilon\le\lvert a\rvert$. The hypothesis fails before the conclusion is reached, on all wide windows at once. |
| The temperedness gate makes the window theorem selective | It separates the *proof*. Nothing proved here forbids wide-window positivity for a non-tempered twin obtained by another argument; selectivity of the statement is open. |
| Compact support of arbitrary length is the receiver's regime | The truncated window positivity holds at every support length $[-\log2V,0]$ with constants uniform in $V$, yet its margin is still the archimedean $\log M$. Long support removes the short-support objection, not the subsidy. |
| Window or high-height positivity is critical-scale progress | Windows through $3/10$ (all profiles) and $181/500$ (odd) are paid by sign-changing gauges on the archimedean conductance and one prime atom, heights beyond the horizon by the Gamma factor alone; neither sees the critical scale, and the block positivity of the critical family sees no small aperture. |
| A window through $3/10$ is a theorem about $\zeta$ | No prime power enters an aperture-$3/10$ window ($\log 2>3/5$), so *every* arithmetic weight is Weil-positive there; inside that aperture the certificate is a constant reading and certifies nothing about any source. |
| A sign is required of the complete form | A floor losing less than an exponential in the aperture already gives RH: $\hat Z(F)\ge-C\int F^2$ on all odd $C^2_c$ tests is RH, and $-C_\sigma e^{2\sigma r}$ at aperture $r$ is the strip $\Theta\le\frac12+\sigma$. The demand is an exponent, not a sign. |
| Buying the exponent at the archimedean place | An inequality boosted by an archimedean term of exponent $\theta>1/4$ is satisfied by the all-ones weight, of maximal defect; the boost removes the criterion instead of weakening it. A loss constant or linear in the aperture is harmless, one growing with the frequency of the test is fatal. |
| Enlarging the aperture is free progress | At aperture $a$ the $\ell^1$ prime cost is $\asymp2e^{a}$ while a depth-$\delta$ off-line zero amplifies by $e^{2\delta a}$; the exponents coincide exactly at $\delta=\frac12$, the depth of the polar pair. Every height-uniform aperture method therefore floors at width $\frac12$, and improvement needs a *power* saving in the single-height prime bound, not a constant. |
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
`DyadicScaleBlock S M`; public capstones carry data parameters only and no
analytic, positivity or zero-location hypotheses. Constants are named
definitions (`factorialTailTranslationConstant`, `criticalArchLogSlope`,
`criticalCollaredPrimeConstant`, …) rather than inline numerals. No heartbeat
settings are raised. RH appears only as the conclusion of an implication or
inside an equivalence.

---

## 5. The frontier

**Low scales.** The complete critical form, collared or not, is positive definite
on every dyadic block beyond an absolute $M_0$, on polynomial windows, on compact
truncations uniformly in the truncation, on polynomial windows *and* compact
truncations jointly — hence on compact tests of arbitrary support length, in all five
names of the form — and on lacunary unions of blocks. Below $M_0$ nothing is proved;
the constants (the threshold and the slope) decide how much of the form is covered.
The low-scale gap is the only remaining restriction on the scale variable that is not
a width restriction, and it is an unavoidable one: the archimedean gain is $\log M$, so
no argument of this shape reaches $M=O(1)$, where the prime atoms of the smallest
primes are not yet dominated.

**Explicit thresholds and the range of $R$.** Every block threshold is the
closed form $M_0=\max\bigl(2,\lfloor e^{c+C/s}\rfloor+1\bigr)$ in its slope $s$,
offset $c$ and channel constant $C$, and the window exponent is
$\delta=s/(4(W+1))$ (`ExplicitBlockThresholdsOfTheCriticalFamily`). A numerical
value of $M_0$ needs explicit bounds on the collar integrals
$\int\lvert\psi'\rvert,\int\lvert\psi''\rvert$ of the smooth transition and on
$\sum_r\Lambda(r)r^{-3/2}$, which enter $C$. The exact values
of $\max R$ and $\min R$ on the cell, their locations, and the first couplings
$\kappa(1),\kappa(2)$ decide the optimal negativity constant
$-(4/\pi^4)\max R$ and how far it is from the singleton mean $-\log2/390$.
Whether $R$ is monotone on $[0,1/2]$ is open.

**Dense windows.** Across blocks the prime coupling decays like $\tau(m,n)$ and
lacunary families are covered; windows wider than $M^\delta$ that are not
lacunary, where $\log L\asymp\log M$ and the constants $s$ and $C_W$ decide, are
open. The exponent $\delta$ is now the single quantity separating the proved regime
from the full scale range, at every support length: the window and truncation
constants are independent of each other and of $V$, so $\delta=s/(4(W+1))$ is
determined by the archimedean slope against the width cost alone. A window with
$\log L\ge\delta^{-1}$ times the archimedean gain is beyond reach by this argument,
and whether the width cost $3+\log L$ is sharp — the correlation of two dilation rings
is $O(\min(1,\sqrt{L/r}))$, and only the $\varepsilon$-trick converts it — is open. The resonance structure $k(n+1)\equiv j\pmod{lr}$ that would make dense
windows uniform survives only for scale ratios up to about the square root of the
scale.

**From the family to the receiver.** The tent family is Weil-complete and
detects every actual off-line zero, and doubly collared truncations carry block *and
polynomial-window* positivity to compact tests of every length, through to the actual
zeta divisor as reflection dominance $\mathcal R(F)<\mathcal Z(F)$ with an explicit
margin. What is missing is the passage to
the compact tests of the receiver on which RH is decided, those without the
archimedean gain $\log M$: every positivity theorem on the critical family is paid
by that gain, and on the RH-complete cone it is absent. The passage is now a
quantitative target rather than a sign: a floor on all odd compact tests whose
loss grows subexponentially in the aperture suffices, and the obstruction is the
rate. Beyond lag $O(1)$ the floor is exactly the prime–polar difference
$\psi(e^t)-e^t$ — the prime measure has density $\asymp e^{t/2}dt$ at lag $t$, the
polar measure $2\cosh(t/2)$ has the same density, and the archimedean density
$\omega(t)\asymp e^{-t/2}$ is smaller by $e^{t}$ — so the archimedean surplus
contributes nothing at the lags that carry the mass, and no amount of it buys the
exponent. Oddness, edge decay of the autocorrelation and the strip structure give
no power saving either: an odd test concentrated in an $O(1)$ window at the edge
of its support has pole charge $\asymp e^{r}$ and prime correlation $\asymp-e^{r}$,
of the same size and opposite sign, so the floor is their PNT-level difference.

**Quantitative detection.** On the lag face the units exist: a near-top zero
of depth $\delta_0$ with readout at least $\eta$ is visible at an explicit lag
$V_0(w,\eta,\delta_0)$, an attained top at a logarithmic lag, and a near-top zero
seen at lag $V$ makes $\mu(A)$ negative beyond $V/2+w$. On the tent family only
the qualitative statement is proved: eventual grid-tent nonnegativity at scale
$n$ forces the asymptotic abscissa law. The missing law is "nonnegativity of
all grid patterns at scale $n$ and radius $R$ excludes zeros of depth
$>\delta(n,R)$ below height $T(n,R)$", with $\delta(n,R)$ read from the explicit
lags through the grid convergence of §3.14; it would turn the family into a
computable receiver.

**Beyond the factorial family.** The admissible-source law needs only a mass
floor and a low-band exclusion. Which other arithmetic sources, built from
divisor stencils other than the dyadic one or from non-Bernoulli remainders,
satisfy both at the critical envelope with an $\ell^2$-bounded prime channel,
and whether their cell kernels are also sign-definite, is open.

### Research topics toward the shared target

1. **From the critical family to the receiver without an archimedean subsidy.** Which compact
   approximants of critical sources inherit block positivity with a margin surviving truncation,
   stated so that the gain `log M` of the critical Lévy energy plays no role (mechanism 3 and the
   criterion of no subsidy). The target is graded: a floor whose loss at aperture `r` is
   `C e^{2σ r}` reports the strip `½ + σ`, and a loss bounded uniformly in the aperture reports RH.
   A margin that grows with the frequency of the test is not a weaker form of the same statement —
   it is satisfied by the all-ones weight and reports nothing.
2. **A power saving over the `ℓ¹` prime cost at a single height.** The certified aperture of
   single-height positivity is `log log T − log 4`, where the `ℓ¹` cost `≍ 2e^{a}` meets the
   archimedean `≍ log T`; a depth-`δ` zero at that height is visible from aperture
   `(log log T)/(2δ)`. Improving the width through the aperture face means certifying aperture
   `(1+ε) log log T`, that is a single-height prime bound `≪ (log T)^{1+ε}` for
   `X = (log T)^{2+2ε}`. Uniform-in-height bounds cannot give it, and excluding near-alignment at a
   given height is a simultaneous-approximation problem on prime logarithms whose effective bounds
   are far too weak; the question is which arithmetic input replaces them.
3. **Quantitative detection.** Nonnegativity of all grid patterns at scale `n` and radius `R`
   excludes zeros of depth `> δ(n, R)` below height `T(n, R)`; the unit is `δ(n, R)`.
4. **The spectral realization (mechanism 4).** In which Schatten or deficiency class, on which
   Hilbert space, do the primes modify the archimedean operator so that the spectral measure is the
   critical-zero measure, and under what condition do the finite-aperture ground transforms of the
   Connes–Consani–Moscovici operators converge to `Ξ`. Known constraints: the prime part is not
   trace class, finite rank or finite deficiency, and is as large as the unbounded `S(T)`; unitary
   producers have unit-modulus Euler factors; the finite-aperture logarithmic Dirac operator is
   real-rooted in its η-branch and reaches `Ξ` only under an unproved premise; the archimedean
   Sonin-trace domination has an exact decomposition `−W = Tr ϑS + Tr ϑG` with the sign of
   `Re Tr ϑG` open. The candidate source class is the complete critical family on blocks, windows,
   compact truncations and lacunary unions; a positivity theorem and a realization theorem would be
   the same theorem.
5. **Selectivity audit.** One separation is now proved: the window bound's own hypothesis, the
   tempered critical-line sum `Σ Λ(r) r^{−1−ε}` at `ε(L) = 1/(2 + log L)`, diverges for
   `ζ(s−a)ζ(s+a)` at every `ε ≤ |a|`, so no wide window admits the proof for the shifted pair. The
   audit is unfinished in both directions. Upwards: is the *statement* selective — does some
   non-tempered twin satisfy wide-window positivity by another route, or does the conclusion itself
   fail there? Downwards: which of block positivity, the admissible-source law, the collared
   dilation inequality and the Montgomery–Vaughan endpoint bound survive verbatim for a Beurling
   system with an off-line zero, and are therefore not about RH. A statement that survives all
   three test models is infrastructure, and should be labelled as such in place.
6. **The source class of the one-point cone.** The full Weil cone contains exactly one weight, so
   the realization problem is the identification of `Λ` index by index rather than an inequality.
   Which admissible sources of this theory present a weight whose single-index perturbations are
   separated by the data the source actually exposes, and what replaces a cone membership proof
   when the cone is a point.

---

## 6. Working in the theory

Start from the source dictionary of §2.3 and keep the clock substitution
$v=e^{-x}$ explicit: every estimate is proved on $v\ge1$ with the physical
weight $v^{-(2\beta+1)}$ and transported back. Prove integrability and
summability before integrating or summing, and prove limits in every channel
rather than in a convenient one. Make $\ell^2$-uniform statements on dyadic
blocks and fixed-support statements with nested eventual quantifiers; never
hide a threshold. Reuse the corpus: Montgomery–Vaughan interval mean squares,
the scalar $\int(1-\cos tv)/v^2=\pi\lvert t\rvert$ kernel, scalar
integer-cosine orthogonality, the real $L^1$ periodisation and its zero Fourier
mode, the band-limited sinc-square identities and their Poisson sum, the
Gamma–Lévy identity and the logarithmic weight comparison, the Lévy symbol
bound, the nonstationary Mellin bounds with and without boundary term, the
dyadic dilation inequality, the admissible-source law, and the unit-height
packet count. Before proving anything about the complete form, check whether
the statement is already a theorem in one of its other four names. Search the
corpus before proving anything new, and verify each name in a scratch file in
this toolchain. State every new result at its exact scope: family, scale range,
smoothing quantifiers, block structure, and which channels are included. When a
mechanism fails, extract its strongest positive survivor as a sharp boundary or
classification before retiring it. Comments in Lean are mathematics; status,
dates and logs belong on the pipeline cards.
