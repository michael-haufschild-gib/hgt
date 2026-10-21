# Square-Root Threshold (`GaloisForLFunctions.SquareRootThreshold`)

**One question.** At height `T`, which information in the explicit formula makes an off-line zero
visible, and which unconditional mechanisms can reach that information?

The Square-Root Threshold (SRT) is a theory of *visibility*. It fixes a height, a resolution and
a zero configuration, and asks whether Weil positivity at that resolution can tell the
configuration apart from one with all zeros on the critical line. Every statement in SRT is made
at a given height and resolution, and every invisibility statement is paired with a visibility
witness.

---

## The shared target: the sign of the critical arithmetic form

Seven programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
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

**The mechanisms the shared target needs**, with the programme that owns each:

1. A prime-side inequality with no slack: payment of each anti-diagonal atom `Λ(n) n^{−1/2}` by
   same-side atoms and the variance, on all even profiles, in sign-changing gauges
   (`ArithmeticIncidencePositivity` with `ArithmeticCriticalityTheory`).
2. Single-modulus bilinear dispersion on the pronic Gram, through the reciprocity
   `{N/pq} ↔ p̄/q + q̄/p` (`BezoutValuationIncidence`).
3. A no-crossing law for the ground-energy path, equivalently the absence of a first negative lag
   for `ζ` (`ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory` and OWU on the aperture side;
   `SquareRootThreshold` on the lag side).
4. A definite spectral realization with a prime modification as large as `S(T)` (the operator
   routes HF and CHMD in `RHTower`, on the complete sources of `ArithmeticPositivityTheory`).
5. A parity-breaking additive input at a single modulus (`TransHorizonIncidenceMechanics` with
   `BezoutValuationIncidence`; `BiScaleUncertainty` for the node criticality `log 4` against `log 6`).

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH.
- *No family average.* One character, modulus one, shift zero.
- *Square-root precision beyond the diagonal*, at every scale rather than almost every.
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)`.
  Identities, finite classifications and nonselective positivity count as zero in these units.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done.

### This programme's role

SRT is the lag face. It owns the lag family `P_v`, the square-root threshold `X = T` between
visibility and invisibility, the height localization of the explicit formula, and the
first-negative-lag law on crystals and finite off-line sets. It supplies the window tests
(`lagPrimeWindow`) whose internal incidence `ArithmeticIncidencePositivity` classifies, and the
units `θ`, `V` and `δ(n, R)` in which the shared target measures progress. Its part of mechanism 3
is the lag version of the no-crossing law: why the actual zero configuration of `ζ` has no first
negative lag when every crystal and every finite off-line set has one.

---

## 1. Why: motivation

**Weil positivity sees zeros through tests.** For a test `f` with Weil kernel `k = f ⋆ f̃`, the
explicit formula equates a zero side `Σ_ρ m_ρ h_k(γ_ρ)` with a prime side, an archimedean term and
the pole terms. A zero on the critical line contributes `|h_f(γ)|² ≥ 0`. A reflected off-line pair
contributes an indefinite rank-two term. Weil's criterion turns RH into positivity of the zero side
over all tests, so the question is always: *which tests can expose the indefinite terms?*

**A test has a resolution and a prime length.** A test supported in `[-a, a]` (its *aperture* `a`)

* reads the prime powers up to `X = e^{2a}` on the prime side, and
* resolves ordinates only to scale `π/a` on the zero side.

The zeros of `ζ` near height `T` are spaced by `2π/L`, `L = log(T/2π)`. So a test of aperture `a`
sees about `a L/π` zeros inside one resolution cell.

**Where the difficulty sits.** Every positivity route that is uniform in height has an open
inequality that is either RH-equivalent or a quasi-RH half-plane statement (`Re ρ ≤ σ` for a fixed
`σ < 1`), and leaves the same unpaid term: the signed pairing between the primes and the polar
terms. At height `T` that term has to be controlled at the resolution `2π/log T` of the zero
spacing. SRT therefore studies the problem *at a given height and resolution* rather than
globally.

**The threshold.** Isolated off-line pairs are visible at small apertures. Dense configurations are
different: an off-line lattice `{½ ± δ + 2πik/L}`, at the density of the zeros of `ζ`, is
indistinguishable from an on-line lattice for every aperture `a ≤ L/2`, whatever its depth
`δ`, and visible beyond (`RHTower.offLineLattice_weil_positive_iff`). At `a = L/2` the test itself
has length `e^{a} ≍ √T` and its Weil kernel reads primes up to `X ≍ T`. This is the
**square-root threshold**. It is also the diagonal threshold of the mean value theorem for Dirichlet
polynomials and the threshold of the density hypothesis on the zero side.

So the two basic questions of SRT are:

1. **Below the threshold:** which configurations can hide, and what geometric feature of a
   configuration makes it visible early?
2. **Beyond the threshold:** which unconditional information about primes reaches apertures
   `a > L/2`?

---

## 2. What: objects and language

The objects come from `Zeta23` (`formal/.lake/packages/Zeta23`) and `RHTower`. Do not redefine
them.

| Object | Meaning | Lean |
|---|---|---|
| Paper Fourier transform | `h_f(z) = ∫ f(u) e^{izu} du` | `Zeta23.paperFT` |
| Zero ordinate | `γ_ρ = (ρ − ½)/i`; `Im γ_ρ = ½ − Re ρ` | `Zeta23.gammaOf` |
| Depth | `δ = |Re ρ − ½|` | — |
| Zero configuration | locally finite multiset in the strip, invariant under `ρ ↦ 1 − ρ̄` | `Zeta23.ZeroConfig` |
| Weil form | `W(f,g) = Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))` | `Zeta23.ZeroConfig.W` |
| Weil kernel | `k = f ⋆ g̃`; `h_k(z) = h_f(z) conj(h_g(conj z))` | `Zeta23.EF.weilTest`, `EF.paperFT_weilTest` |
| Zeros of `ζ` | with the explicit formula | `Zeta23.zetaZeroConfig`, `WeilEF.EF_lit_zetaZeroConfig` |
| Hodge index at level `a` | Weil positivity on tests of aperture `a` with `h_f(±i/2) = 0` | `RHTower.HodgeIndexAtLevel` |
| Lattices | doubled on-line lattice / off-line lattice pair of spacing `2π/L` | `RHTower.onLineLatticeConfig`, `RHTower.offLineLatticeConfig` |
| Periodic configurations | lattice ordinates with a periodic depth profile; off-line patterns with arbitrary offsets | `profileConfig`, `patternConfig` |
| Lag symbol | `D(m)` in `W(f,f) = ℓ Σ_m k(mℓ) D(m)`; for depths `d_r`, offsets `θ_r`: `Σ_r 2cosh(d_r mℓ) e^{2πiθ_r m}` | `depthSymbol`, `patternSymbol` |
| Toeplitz form | `Σ_{j,j'} c_j conj(c_{j'}) D(j − j')` | `toeplitzForm` |
| Height shift | `S_ξ f(u) = e^{2πiξu} f(u)`, so `h_{S_ξ f}(z) = h_f(z + 2πξ)` | `heightShift` |
| Window slice | `g_s(u) = f(u + s) η(u)` | `windowSlice` |
| Windowed Weil form | the Weil form of `k_f · k_η`; equals `∫ |h_η(−2πξ)|² W(S_ξ f, S_ξ f) dξ` | `windowedW` |
| Tempered configuration | `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞` | `TemperedConfig` |
| Pair energy | `S(a) = ∫_{-a}^{a} sinh²(δu) du = sinh(2δa)/(2δ) − a` | `pairEnergy` |
| Exponential sum | `Q(ξ) = Σ_j c_j e^{2πiξν_j}` | `expSum` |
| Prime polynomial | `Π_f(ξ) = Σ_{2≤n≤X} Λ(n) n^{−1/2}(k_f(log n) n^{2πiξ} + k_f(−log n) n^{−2πiξ})` | `primePolynomial` |
| Archimedean–pole part | `A_f(ξ) = h_k(i/2) + h_k(−i/2) + ∫ h_k μ` with `k = S_ξ f ⋆ (S_ξ f)~` | `archPart` |
| Diagonal energy | `V_f = Σ_{2≤n≤X} Λ(n)²/n (|k_f(log n)|² + |k_f(−log n)|²)` | `primeVariance` |
| Prime-only polynomial and envelope | the prime terms of `Π_f`; the `ℓ¹` envelope `M_f` of its coefficients | `primeOnlyPolynomial`, `primeEnvelope` |
| Prime window functional | `P_v(k) = Σ_n Λ(n)/√n (k(log n) + k(−log n))` read on `|log n − v| ≤ 2w` | `lagPrimeWindow`, `lagPrimeWindowRHS` |

The configurations and the probes of the theory:

| Object | Meaning | Lean |
|---|---|---|
| Isolated pair, run, cluster | one reflected off-line pair; a contiguous run of off-line lattice points; a finite off-line set of comparable depths | `isolatedPairConfig`, `runConfig`, `clusterConfig` |
| Periodic patterns and profiles | `P` off-line pairs per period at offsets `θ_r` and depths `d_r`; a periodic depth profile on a lattice | `patternConfig`, `profileConfig` |
| Jittered and diluted lattices | ordinates `2πk/L + (−1)^k ε`; a sparse off-line lattice of spacing `2π/ℓ` inside the on-line lattice of spacing `2π/L` | `jitterConfig`, `dilutedLatticeConfig` |
| On-line shadow | a weighted on-line periodic configuration with moments `M(m) = Σ_k w_k e^{ic_k mℓ}` | `onLineShadow`, `shadowMoment` |
| Symbols and floors | depth, pattern and lattice symbols `D(m)`; the shifted symbol; the lattice ground energy `L(n − √(S₊S₋))` | `depthSymbol`, `patternSymbol`, `latticeSymbol`, `shiftSymbol`, `latticeFloor` |
| Modulated bumps | the corpus bump `κ` scaled to width `w` and modulated to height `γ`; its polar-free version with transform vanishing at `±i/2` | `RHTower.modScaledBump`, `RHTower.scaledBumpPolarFree`, `modBump` |
| Two-bump test | `β(t + v/2) + τβ(t − v/2)`, lag `v`, coupling `τ`; unimodular when `|τ| = 1`, difference test when `τ = −1` | `twoBump` |
| Lag structure | `S(v) = Σ_ρ m_ρ h_{β⋆β̃}(γ_ρ) e^{iγ_ρ v}`, so that `W(twoBump) = (1 + |τ|²)S(0) + τS(v) + τ̄S(−v)` | `lagStructure`, `lagTerm`, `lagCoeff`, `evenCoeff` |
| Minor deficit | `2 Re S(0) − |S(v) + conj S(−v)|`, the least `Re W` over unimodular two-bump tests at lag `v` | `minorDeficit` |
| Right zeros, off-line weights | the zeros `Re ρ > ½`; the weight `q_t = m_t h_b(γ_t − iδ_t) conj h_b(γ_t + iδ_t)` of a pair at the bump | `rightZeros`, `offLineWeight`, `pairWeight` |
| On-line mass | `Σ_{on-line} m_ρ |h_β(γ_ρ − γ₀)|²`, the local on-line mass seen by a bump at height `γ₀` | `onLineMass`, `onLineMassOf` |
| Depth-deficit and depth-excess transforms, level tail | `G(v) = Σ_{δ_t < D} |q_t| e^{−(D − δ_t)v}`, `E(v) = Σ_{δ_t > D} |q_t| e^{(δ_t − D)v}`, and the weight of a level outside a finite part | `depthDeficit`, `depthExcess`, `levelTail` |
| Ingham kernel and constant | `∫_{−T}^{T} cos(πt/2T) e^{ixt} dt` and the constant `C(T, g) > 0` for `Tg > π` | `inghamKernel`, `inghamConst` |
| Exponential-sum profile, resolvent | the Mellin profile `x ↦ Σ q_t x^{−λ_t}` of `Σ q_t e^{λ_t v}` and its resolvent `Σ q_t/(s − λ_t)` | `expSumProfile`, `resolventSum` |
| Polar-free kernel | the autocorrelation of the polar-free two-bump test | `polarFreeKernel` |
| Three archimedean bands | the piecewise lower bounds of the archimedean symbol below aperture `1/100` | `muLow`, `muMid`, `muHigh` |

**Words.**
* **Aperture `a`:** the support radius of the test; resolution `π/a`, prime length `e^{2a}`.
* **Visible at aperture `a`:** some `C²` test supported in `[-a, a]` makes `Re W(f, f) < 0`.
* **Invisible (hides):** the form is nonnegative on all such tests.
* **Isolated:** one reflected off-line pair inside an on-line background.
* **Dense:** off-line points spaced like the background.
* **Cluster:** finitely or infinitely many off-line points of comparable depths, with no depth gap.
* **Depth profile:** the depths along a lattice of ordinates, read as a function of the lattice
  index.
* **Crystal:** a periodic off-line configuration with uniform depth whose ordinates form one
  arithmetic progression.
* **Shadow:** a weighted on-line configuration whose Weil form coincides with that of a given
  configuration on all tests of some aperture.
* **Level:** the off-line zeros of one common depth; the **top level** is the deepest one, and a
  depth is **attained** when some zero has it.
* **Minor:** the two-point inequality `|S(v) + conj S(−v)| ≤ 2 Re S(0)` forced by invisibility;
  a configuration is seen at lag `v` when the minor fails there.
* **Nyquist aperture:** the aperture `Pℓ/2` at which a periodic configuration with `P` ordinates per
  period `2π/ℓ` becomes resolvable; position and depth become visible there.

---

## 3. How: mechanisms

### Zero side

1. **Lag representation.** `W(f,g) = Σ_ρ m_ρ h_k(γ_ρ)`. An aperture-`a` test sees the
   configuration only through lags `|v| ≤ 2a`. A depth `δ` enters through the weight `e^{±δv}`;
   a reflected pair through `2cosh(δv)`.
2. **Poisson on lattices.** On a lattice of spacing `2π/L` the zero sum becomes
   `L Σ_m k(mL) e^{±δmL}`. Below `L/2` only the lag-zero atom survives, and the depth is invisible.
3. **Toeplitz law.** Whenever `W(f,f) = ℓ Σ_m k(mℓ) D(m)`, the configuration hides at aperture `a`
   iff the Toeplitz matrix `[D(j − j')]` of size `⌈2a/ℓ⌉` is positive semidefinite. One direction
   uses narrow bumps at the lag points; the other periodizes the test into Toeplitz forms of its
   samples. Visibility questions for periodic configurations become matrix questions about the
   cosh-weighted modes `D(m)`.
4. **Hiding is mimicry.** A positive semidefinite Toeplitz section is the moment matrix of finitely
   many atoms on the circle (Carathéodory–Fejér), and each atom is an on-line translate of the
   lattice (Poisson). So a configuration hides at aperture `a` iff, on every test of aperture `a`,
   its Weil form *is* that of a positively weighted on-line configuration with the same number of
   zeros per period and at most `2⌈2a/ℓ⌉ − 1` ordinates per period.
5. **Position is resolved at the same aperture.** By the same Toeplitz route, the Weil form of a
   weighted on-line configuration on tests of aperture `a` is its list of moments
   `M(m) = Σ_k w_k e^{ic_k mℓ}`, `|m| < ⌈2a/ℓ⌉`. A configuration with `r` ordinates per period is
   determined by them iff `⌈2a/ℓ⌉ > r` (its vanishing polynomial has degree `r`); below, the
   `r`-point crystal and its half-step rotation coincide. Height position and depth become visible
   at the same Nyquist aperture. Reading an off-line configuration completely takes at most twice
   as much: its modes are two-sided exponential moments `Σ_r (λ_r^m + μ_r^m)` with
   `λ_r, μ_r = e^{±d_rℓ + 2πiθ_r}`, and `|m| ≤ 2P` of them determine all `2P` nodes, hence every
   depth and ordinate.
6. **Ground state.** `inf Re W(f,f)/∫|f|²` over tests of aperture `a` is `ℓ` times the lowest
   eigenvalue of the Toeplitz section, with or without the polar constraint. For the off-line
   lattice it is `L(n − √(S₊S₋))`, `S_± = Σ_{j<n} e^{±2δjL}`: it decays like `−e^{2δa}`. For every
   periodic configuration the decay exponent is exactly twice the maximal depth: the relaxed
   Hodge index `Re W ≥ −e^{θa}∫|f|²` holds at all large apertures for `θ > 2d_max` and fails for
   `θ < 2d_max`. On the off-line lattice the ground energy is explicit,
   `L(n − U_{n−1}(cosh δL))` with `U` the Chebyshev polynomial of the second kind, for apertures in
   `((n−1)L/2, nL/2]`: a strictly decreasing step function of the aperture, right-discontinuous
   at every multiple of `L/2`.
7. **Modes are amplified by `cosh`.** For offsets `θ_r` and depths `d_r`, the mode `D(m)` is the
   `m`-th Fourier coefficient of the ordinate pattern weighted by `2cosh(d_r mℓ)`. Hiding up to
   the Nyquist aperture needs `|D(m)| ≤ D(0)` for every mode below the period. At growing density
   the weights grow exponentially, so the pattern's Fourier coefficients must be exponentially
   small: the deepest points dominate, and only uniform depth with crystalline ordinates survives
   (Newton's identities turn vanishing power sums into an arithmetic progression). At every single
   scale the crystal is also the variational extremum: it is exactly the uniform-depth pattern
   whose Weil floor up to the Nyquist aperture equals the on-line value `ℓ D(0)`.
8. **Edges and variation.** Inside an on-line background the off-line part enters as
   `∫ k(u) Σ_k 2(cosh(d_k u) − 1) e^{2πiku/L} du`. Summation by parts in `k` turns the exponential
   sum into differences of depths. So a small aperture reads the *variation* of the depth profile,
   not the depth: the edge of a long run (a jump `0 → δ`) in a dense background is visible at an
   aperture of order `1/δ` that depends neither on the length of the run nor on the density;
   slowly varying profiles hide much longer.
9. **Two-point minors for any configuration.** For every tempered configuration and bump `β`
   supported in `[−w, w]`, the test `β(t + v/2) + τβ(t − v/2)` has Weil form
   `(1 + |τ|²)S(0) + τS(v) + τ̄S(−v)`, with the smeared lag structure
   `S(v) = Σ_ρ m_ρ h_{β⋆β̃}(γ_ρ) e^{iγ_ρ v}`. Invisibility forces `|S(v) + conj S(−v)| ≤ 2 Re S(0)`.
   Modulated to a height `γ₀`, on-line zeros contribute positive multiples of phases, bounded in
   total by their mass at lag `0`, while an off-line pair at `γ₀` contributes a term growing like
   `e^{δv}`: an isolated off-line pair is seen once `e^{δv}` exceeds the local on-line mass, whatever
   the arrangement of the on-line zeros. The same holds for any finite off-line set: the deepest
   level `D` cannot cancel itself, since its phase sum `Σ q_t e^{iγ_t v}` stays bounded below on
   every window of `|T|` grid lags. The levels below lose `e^{−gv}`, `g` the depth gap, so the
   aperture is `(1/2g) log M + O(1)`, uniformly in the on-line background. Without a gap, the
   levels below enter only through the depth-deficit transform `G(v) = Σ_{δ_t < D} |q_t| e^{−(D − δ_t)v}`,
   which relaxes to `0`. If the top depth is attained, at finitely or infinitely many heights, the
   minor fails in every window of length `4π/g` once `G` and the weight of the top level outside a
   finite part `F` are below `|q_{t₀}|/8` and `|q_{t₀}| e^{Dv}` exceeds `4(2M + 3Σ|q_t|)`. Here `g`
   is the height separation of `F`: by Ingham's inequality, the top phase sum over `F` exceeds
   `|q_{t₀}|/2` somewhere in every such window. Visibility is local. Any level, deepest or not, is
   seen in such a window once its shallower zeros have relaxed, provided the depth-excess transform
   `E(v) = Σ_{δ_t > D} |q_t| e^{(δ_t − D)v}` of the deeper zeros within reach of the bump has not yet
   taken over. With the polar-free bump
   the same tests lie in the Hodge class. Without a gap, and with infinitely many off-line zeros,
   every off-line zero is still seen at some aperture. Invisibility would keep the off-line sum
   `Σ_t q_t e^{(δ_t + iγ_t)v}` bounded for `v ≥ 0`. Its Laplace transform is then holomorphic on
   `Re s > 0` and equals `Σ_t q_t/(s − δ_t − iγ_t)` to the right of all poles. Continued along the
   pole-free strip at any height `γ`, it reaches the rightmost pole on that line, whose residue
   `q_t` must therefore vanish. The modulated bump makes that residue nonzero. Zero-side Weil
   positivity on compactly supported tests is thus equivalent to all zeros on the critical line,
   for every tempered configuration. Only the unimodular two-bump tests
   `κ_γ(t + v/2) + τκ_γ(t − v/2)`, `|τ| = 1`, are needed, and of these only `τ = ±1`: two real
   parameters and a sign decide the line. By reflection symmetry `conj S(−v) = S(v)`, so the even
   and odd tests have `Re W = 2 Re S(0) ± 2 Re S(v)`. `2 Re S(v)` is an exponential sum over the
   zeros with exponents `ρ − ½`. Its coefficient at a right zero `t` merges `t` with its conjugate
   `t̄`, as `m h(x − iδ)² + m* h(2γ − x − iδ)²`, where `x` is the offset from the bump's height.
   Suppose this vanished at every height. Then `|h(x − iδ)|²` would be multiplied by the fixed
   ratio `m/m*` or `m*/m` at each step `±2γ`, and hence could not decay. So some height leaves
   the top pole a nonzero residue. Without real zeros (`ζ` included), one sign suffices: the
   difference tests `κ_γ(t + v/2) − κ_γ(t − v/2)` only bound `2 Re S(v)` from above. By Landau's
   theorem, the abscissa of the Laplace transform of a function bounded on one side is a real
   singularity. The exponents keep away from the real axis, so the transform continues to
   `Re s > 0`, and the top residue vanishes again. The height parameter can be dropped too. For
   the unmodulated bump the conjugate zeros add, and the merged coefficient is
   `(m_t + m_{t̄}) h_w(γ − iδ)²`. Since `w ↦ h_w(p)` is a rescaled entire function with
   `h(0) = ∫κ > 0`, it vanishes for only countably many widths. So for all but countably many `w`
   the one-parameter family `κ_w(t + v/2) − κ_w(t − v/2)`, `v ≥ 0`, decides the line. Real
   zeros cannot hide from it. At the center `0` a real zero `½ + δ` has coefficient
   `2m h_w(−iδ)² > 0`. Once Landau has removed everything to the right of the largest real
   exponent `δ*`, the Abel means `(s − δ*)∫_0^∞ e^{−sv} 2 Re S(v) dv` tend to that positive
   coefficient as `s ↓ δ*`, which the one-sided bound forbids. No hypothesis on real zeros
   remains.
   The same argument measures the rate: the least `Re W` over these tests at lag `v` is
   `≥ −Ce^{Dv}` when every depth is at most `D`, and is not `O(e^{σv})` for any `σ` below the
   depth of a zero. Negativity grows exactly at the rate of the deepest zero.
10. **Faithfulness.** The Weil form determines the configuration: two tempered configurations
   that agree on the modulated two-bump tests have the same zeros with the same multiplicities.
   Polarization at `τ = 0, 1, i` recovers each lag structure `S_γ`. The difference is the lag
   structure of the signed multiplicity, whose off-line part dies at its top poles and whose
   on-line part dies under Cesàro means. A finite aperture suffices for on-line configurations
   with separated heights, and the threshold is sharp: a `g`-separated union is resolved at every
   aperture `a > π/(2g)` by Ingham's inequality (cosine kernel on `[−T, T]`, threshold `Tg > π`
   from `Σ 2/(4n² − 1) = 1`), and not at `π/(2g)`, where the double lattice of spacing `2π/L` and
   the simple lattice of spacing `π/L` share their Weil form. The one-parameter family of
   mechanism 21 is faithful up to exactly two invisible data. For a width at which `h_w` vanishes
   at no zero ordinate, two configurations agree on `κ_w(t + v/2) − κ_w(t − v/2)` for all
   `v ≥ V` iff `m(ρ) + m(ρ̄)` agree at every `ρ ≠ ½`. Equal lag data make `2 Re S` differ by a
   constant, and an exponential sum vanishing on a half-line has no coefficient with `Re z ≥ 0`;
   the merged coefficient at `z` is `(m(½ + z) + m(½ + z̄)) h_w(−iz)²`. The exponent `0` carries
   `s = ½` and cancels, and a real test cannot tell `ρ` from `ρ̄`.
11. **Rank-two pair estimate.** A reflected pair contributes `2 Re(A conj B)` with
   `A = ⟨F, e^{δ·}⟩` and `B = ⟨F, e^{−δ·}⟩`. On `[-a, a]` this is at least
   `(2a − sinh(2δa)/δ)‖F‖²`, with equality at `F = sinh(δ·)`.
12. **The pole is a pair.** The pole terms `h_k(i/2) + h_k(−i/2)` have the shape of a depth-`½`
   pair at height `0`. For an odd real profile they equal `−2(∫ f sinh(u/2))²`. The pole of `ζ` at
   `s = 1` is the contribution of the whole infinite prime tail.
13. **Polar blindness.** Constraining tests by `h_f(±i/2) = 0` (the Hodge class) removes the pole
   terms, but costs nothing against lag-lattice configurations: the bump `κ'' − κ/4` has transform
   vanishing at `±i/2`, and so does every combination of its translates. On such configurations the
   Hodge index at level `a` is full Weil positivity at aperture `a`. The Hodge class is blind to
   exactly two points, the zeros `s = 0, 1` at heights `∓i/2`: for every tempered configuration
   the Hodge index holds at every level iff every off-line zero is `0` or `1`. For finitely many
   off-line zeros the violation occurs at `(1/2g) log M + O(1)`.

### Windows and heights

14. **Slice factorization.** `k_f · k_η = ∫ k_{g_s} ds`, and every slice lies in the support of
    `η`.
15. **Height averaging.** `k_η(v) = ∫ |h_η(−2πξ)|² e^{2πiξv} dξ`. So windowed forms are height
    averages of localized forms, and positivity at aperture `r` passes to every windowed form of
    resolution `r`, whatever the aperture of the test.
16. **Windowed Gram identity.**
    `∫ |h_η(−2πξ)|² |Q(ξ)|² dξ = Σ_{j,k} c_j c̄_k k_η(ν_j − ν_k)`. Since `k_η` vanishes beyond
    `2r`, only pairs of frequencies closer than `2r` interact.
17. **Minimum-aperture resolution.** Averaging with two windows of apertures `r` and `ρ` multiplies
    their kernels, so only frequency pairs closer than `2 min(r, ρ)` interact. A secondary window
    that separates the frequencies restores the exact diagonal even when the primary window lies
    beyond the threshold.

### Prime side

18. **Height phase of prime pairs.** At height `T` a pair `(n, m)` enters with the phase
    `(m/n)^{iT}`. In Zeta23 this is the kernel `Aminus`, an integral over `t ∈ [T, 2T]`. For
    `m = n + h` the phase `e^{iTh/n}` changes sign as `n` varies.
19. **Reality and windowed mean zero.** `k_f(−v) = conj(k_f(v))` for every `f`, so the prime
    polynomial `Π_f` is real at every height. A window of aperture `2r ≤ log 2` sees no prime
    frequency `± log n`, so the windowed mean of `Π_f` is exactly `0`: its positive and negative
    excursions balance, and it exceeds `V_f / M_f` somewhere (`M_f` the `ℓ¹` envelope of its
    coefficients).
20. **Kronecker alignment costs height.** The `log p` are linearly independent, so the prime phases
    `p^{iξ}` can be aligned to any target; the prime-only polynomial comes arbitrarily close to
    `±M_f`, and stays near it on intervals of explicit length. The archimedean part grows only like
    `log(1 + |ξ|)`. A coherent prime excursion of size `B` therefore either makes the localized
    Weil form negative or occurs at a height with `log(1 + 2π|ξ|) ≳ (B − C_f)/‖f‖²`.
21. **One parameter decides the line.** Through the explicit formula the two-bump criteria
    become prime-side ones. Every zero of `ζ` is on the critical line iff `Re P(f ⋆ f̃) ≥ 0` for
    the difference tests `f = κ_γ(t + v/2) − κ_γ(t − v/2)`, `γ ∈ ℝ`, `v ≥ 0`. For all but
    countably many widths the height can be fixed at `γ = 0`, leaving the lag as the only
    parameter. Here
    `P(k) = h_k(i/2) + h_k(−i/2) − Σ_n Λ(n)/√n (k(log n) + k(−log n)) + (1/2π)∫ h_k Γ`. The kernel
    `f ⋆ f̃` lives on `[−2w, 2w] ∪ ±[v − 2w, v + 2w]`. For `2w < log 2` the lag `v` therefore reads
    `Λ(n)` only on the window `|log n − v| ≤ 2w`, inside `(X/2, 2X)` for `X = e^v`. Any tail of
    lags `v ≥ V` already decides, for the difference tests as for the unimodular ones. On `[0, V]`
    the deficit is bounded a priori by the upper rate, so the unbounded negativity forced by an
    off-line zero lies beyond `V`. RH is thus a conjunction of
    single-window statements over `X ≥ X₀`, for any `X₀`: no prime below `X₀/2` enters, and prime
    information about a bounded range cannot decide the line. With the polar-free bump the pole
    terms vanish, and each statement reads: the window prime sum against `k` is at most the
    archimedean term `(1/2π) ∫ h_k Γ`. The same holds for every primitive Dirichlet
    `L(s, χ)`, with `χ(n)Λ(n)` in place of `Λ(n)` and no pole terms: for all but countably many
    widths, GRH is one real inequality per dyadic window, possible real zeros included. At lag
    `v = log X` the least value of `Re P` over the unimodular tests is `≥ −C X^{Θ − 1/2}`,
    `Θ = sup Re ρ`, and not `O(X^σ)` for `σ < Θ − ½`, in windows beyond every `X₀`: RH is the
    absence of any power growth, the square-root threshold itself. The one-parameter family
    alone measures `Θ`: for generic widths and every `σ ≥ 0`, all zeros satisfy `Re ρ ≤ ½ + σ`
    iff its window functional at `X` is `≥ −C X^σ` for large `X`, for `ζ` and every primitive
    `L(s, χ)`. A real exponent beyond `σ` is isolated by Landau's theorem at its own level and
    then excluded by Abel means after the shift `e^{−σv}`. Each quasi-RH half-plane is one growth
    condition on one family of dyadic windows. A geometric progression of windows, `v = kℓ`,
    decides the line up to chains (off-line depths without a largest value). After dividing by
    `e^{Dkℓ}`, a one-sided grid bound gives `limsup ≤ 0`, so the Cesàro mean of `|b_k|` is minus
    the mean of `b_k`. That mean collects only the real top exponents, whose coefficients are
    positive, and so every frequency `e^{iγℓ}` of an attained top gets weight `0`. This works for
    every grid step outside the countably many resonances `(γ − γ')ℓ ∈ 2πℤ`. Chains are the exact
    limit. On a grid a height counts only modulo `2π/ℓ`, so a chain with heights approaching
    `(2π/ℓ)ℤ` looks like exponents accumulating at a real point. With negative coefficients its
    grid values stay `≤ 0`, while on the continuum Landau's theorem still sees it. On the
    off-line lattice of spacing `2π/L > 4w` the family is a comb. It is silent for `v ≤ L − 2w`,
    where the aperture is at most `L/2`. At every tooth `v = nL` it equals
    `4L‖κ_w‖²(1 − cosh(nδL)) < 0`, and between the teeth it is `4L‖κ_w‖²`. So the minimal
    receiver meets the crystal at the threshold aperture, up to the bump width, for every depth;
    tests of much larger aperture see nothing between the teeth. On any configuration with a lag
    formula `W(f, f) = ℓ Σ_m k(mℓ) D(m)` the teeth read the modes:
    `W(f_{nℓ}) = ℓ‖κ_w‖²(2D(0) − D(n) − D(−n))`, and the gaps read `2ℓ‖κ_w‖²D(0)`. For a periodic
    pattern a tooth therefore sees only `Re(e^{ic_r nℓ})`, while the Toeplitz law sees the
    modulus. A quarter turn separates them. One off-line line per period at offset `π/(2ℓ)` is seen
    by tests of aperture `3ℓ/4`, but the family stays nonnegative until lag `4ℓ − 2w`. So the
    minimal receiver is threshold-exact on crystals but not aperture-optimal.

---

## 4. Traps

| Trap | What is true instead |
|---|---|
| Treating aperture as a height cutoff | Aperture is a frequency resolution. A small aperture sees deep isolated zeros at any height. |
| Expecting thresholds for finite configurations | A finite configuration with an off-line pair is visible at every aperture. Thresholds come from the density of the background. |
| Expecting some off-line configuration to hide from every aperture | None does: a tempered configuration with an off-line zero is visible at some finite aperture. Hiding is always a statement about bounded apertures. |
| Thinking depth is what a test sees | Below the threshold a test sees depth only through variation: edges and rough profiles are seen at `O(1/δ)`, uniform depth only at `L/2`. |
| Treating the off-line lattice as a typical dense configuration | Its invisibility up to `L/2` is crystalline. A jitter of relative size `η` is seen at `L/2` once `cosh(δL/2) sin(πη) > 1`, and every periodic off-line pattern or depth profile of fixed shape other than the uniform crystal (in particular any shape mixing on-line and off-line zeros) is seen strictly below `L/2` at large height. |
| Expecting the polar constraint to help against dense configurations | On lag-lattice configurations the Hodge index equals full Weil positivity. |
| Reading the Hodge index as "all zeros on the line" | It cannot see zeros at `s = 0, 1`: a configuration whose only off-line zeros are `0` and `1` satisfies the Hodge index at every level. |
| Expecting more off-line zeros to mean more visibility | Visibility is not monotone: the off-line lattice of spacing `2π/L` is visible on `(L/2, L]`, yet adding its half-step translate at the same depth gives a crystal that hides up to `L`. Positivity is a collective property. |
| Counting on critical zeros to supply mass `A∫|f|²` at every aperture | On-line zeros sample the tests of aperture `a` only below the Nyquist aperture of their ordinates; a periodic on-line configuration with `r` ordinates per period gives `A > 0` iff `⌈2a/ℓ⌉ ≤ r`, and above that some test of positive mass sees no on-line zero at all. |
| Expecting sparse off-line structure to hide as long as dense structure | An off-line lattice of density `ℓ/2π` inside an on-line background of density `L/2π` hides only up to `≈ (1/2δ) log(L/ℓ)`, like isolated pairs; only a crystal of the full density reaches `L/2`. |
| Expecting averaged information to reach depth | Window averages of resolution `r` are integrals of aperture-`r` Weil forms. Off-line lattices of spacing at most `π/r`, and clusters invisible at aperture `r`, pass them. |
| Looking for a quantity that certifies an off-line zero below its visibility aperture | There is none in the Weil form: an invisible lag-lattice configuration has exactly the Weil form of a weighted on-line configuration on every test of that aperture. |
| Expecting the prime side to keep a sign along a short height window | For windows of aperture `2r ≤ log 2` the windowed mean of `Π_f` is exactly `0`; its positive and negative excursions balance. |
| Expecting the small primes to carry the criterion | RH is decided by the two-bump tests at lags `v ≥ V`, each reading one dyadic window of primes near `e^v`, for any `V`. Finite prime data can be discarded entirely. |
| Reading the one-parameter criterion as a local detector | The unmodulated tests see a zero at height `γ` with weight `|h_w(γ − iδ)|²`, which decays in `γ`. The criterion is exact through the Laplace–Landau argument, but it gives no visibility aperture; apertures come from modulating to the zero's height. |
| Positivity on a restricted family as evidence for RH | State the family's resolution and compare it with the lattice law first. |
| Weakening to "fixed σ < 1" | These are quasi-RH half-planes, open for every `σ < 1`. |
| Applying an upper-bound sieve beyond `X = T` | The sieve bounds prime pairs only against weights `w ≥ 0`. The height phase `(m/n)^{iT}` changes sign, so the sieve reverts to the size-only bound. |
| Treating `X = T` as a technical limit of one method | It is the diagonal threshold of the mean value theorem, the point where the sieve loses the height phase, and the density-hypothesis threshold of the zero side. |
| Using `Re W` without the conjugation convention | `W(f, f)` uses `conj(h_f(conj γ))`. For an off-line pair it is `2 Re(A conj B)`. |
| Expecting a bounded exponential sum over the zeros to keep a top pole | A sum `Σ q_t e^{λ_t v}` bounded on `v ≥ 0`, or bounded on one side, has zero coefficient at every rightmost, unshared exponent; its growth rate is the abscissa of its top poles. |
| Expecting the visibility aperture to depend on the arrangement of the on-line zeros | It depends on the on-line background only through the logarithm of the local on-line mass at the bump; the arrangement is irrelevant. |
| Expecting the ground energy to vary continuously with the aperture | On lag lattices it is a step function with jumps at every `nL/2`; continuity is a property of the restricted operator of `ζ`, not of configurations. |
| Expecting the minimal receiver to be aperture-optimal | It is exact on crystals, but its teeth read only the real part of each rotated mode: a quarter-turn pattern visible at aperture `3ℓ/4` is first seen by the family at lag `4ℓ`. |
| Expecting a lag grid to decide the line | A grid `v = kℓ` sees every attained top for non-resonant `ℓ`, but a chain whose heights approach `(2π/ℓ)ℤ` can keep a one-sided grid bound. Only the continuum of lags excludes chains. |
| Expecting all couplings `τ` to be needed in the two-bump criteria | Unimodular `τ`, and for `ζ` the single sign `τ = −1`, suffice; the lag `v` and the height `γ` are the only parameters. |

---

## 5. Open problems

1. **Beyond the square-root threshold.** Bound the off-diagonal prime pairs at bandwidth
   `λ = log X/log T > 1`. A bound for the pair correlation of the zeros on `(1, λ)` turns into a
   proportion of simple zeros on the critical line above `2/3`. Each known route stops at `X = T`,
   for a different reason:
   * **Coefficient sizes.** Size-only bounds have an excess `O(rX)` that is attained for aligned
     phases.
   * **Upper-bound sieve.** It requires `w ≥ 0`, but the height phase changes sign
     (mechanism 18). Using the phase requires prime-pair asymptotics with error terms: the parity
     problem.
   * **Zero side.** An off-line zero of depth `δ` has weight `T^{2λδ}`, so the needed estimate is
     `N(½ + δ, T) ≪ T^{1 − 2λδ + ε}`. The density hypothesis gives `λ ≤ 1` exactly.

   The pair-correlation conjecture is open on `(1, λ)` even under RH.
2. **Clusters without a depth gap.** For periodic configurations visibility is a Toeplitz question
   about cosh-weighted modes; for finite off-line sets the aperture is `(1/2g) log M` with `g` the
   gap below the deepest level (mechanism 9). Every off-line zero is visible at some aperture,
   whatever the other off-line zeros do. When the top depth is attained, the aperture is, up to
   one Ingham window `4π/g`, the larger of half the relaxation lag of the depth-deficit transform
   and `(1/2D) log M`, whether or not depths accumulate at the top. When the top depth is not
   attained, a level is still seen in any window where the deficit of the shallower zeros and the
   excess of the deeper ones are both small. Open: whether such a window always exists at a
   controlled lag, at `ζ`-density and with irregularly spaced ordinates. Equivalently: how fast
   the excess transform at the height of a zero can grow compared with the relaxation of its
   deficit.
3. **Sharper constants.** Weil positivity of `ζ` holds unconditionally on every test of aperture
   `a ≤ 3/10`, with `Re W ≥ ‖f‖²/5000` (`ZetaWeilPositivityThroughApertureThreeTenths`: the
   zero-side form splits as `Ẑ(Re f) + Ẑ(Im f)`, so every all-profile window of the full zero form
   transfers with its constant; the three archimedean bands alone give `a ≤ 1/100`,
   `Re W ≥ ‖f‖²/25`). The remaining distance to Yoshida's aperture `(log 2)/2` is the all-profile
   window of the aperture face. The archimedean
   horizon is `exp(C_ε + (4 + ε)√X)`, so the localized forms at height `T` are positive for
   `√X ≤ (¼ − ε) log T`. The coefficient `4` is optimal for bounds on the prime symbol that are
   uniform in height, since `P_X(0) = −(1/π) Σ_{n ≤ X} Λ(n)/√n ~ −(2/π)√X`. A larger single-height
   range must use how the prime phases depend on the height (mechanism 20).

### Research topics toward the shared target

1. **`P_v ≥ 0` beyond an explicit lag `V` for one generic width**: the first selective, cofinal,
   weight-specific estimate; the unit is `V`.
2. **The attainment premise.** What replaces it for the actual zero configuration of `ζ`: why there
   is no first negative lag when every crystal and every finite off-line set has one (mechanism 3,
   lag side).
3. **Localized explicit formula at height `T`** with the off-diagonal pair structure at bandwidth
   `λ > 1`, organized around the square-root threshold rather than the cutoff.
4. **The visibility tradeoff.** The exact relation between aperture, height localization and
   arithmetic length needed to make a given off-line configuration visible, and the strongest
   estimate available at that length; the unit is `δ(n, R)` below `T(n, R)`.
5. **Window incidence.** The window tests `lagPrimeWindow` carry the incidence structure proved in
   `ArithmeticIncidencePositivity` (doublings, triplings, consecutive powers of `2` and `3`); turn it
   into a lag-side statement about which prime pairs a window inequality must pay.
6. **Calibration** of the threshold and of the first-negative-lag law over `F_q[T]`.

---

## 6. Principles

1. **Search the corpus before proving:** `../scripts/formal_tools.py research "<query>"`. The
   lattice, tilt, `paperFT`, explicit-formula and Hodge-index tools already exist in Zeta23 and
   RHTower.
2. **Pair every invisibility theorem with a visibility witness,** and conversely.
3. **Calibrate.** Every statement names its height, its resolution or aperture, and the strongest
   unconditional value known.
4. **Unconditional statements on honest classes.** `C²` compactly supported tests; configurations
   quantified as classes (finite, lattice, periodic, tempered) or concrete (`zetaZeroConfig`); no
   hypotheses that only restate the conclusion.
5. **Choose the coordinates by the configuration.** Periodic configurations are Toeplitz questions
   about their symbol `D(m)`; aperiodic ones are questions about the lag structure `S(v)` of a bump,
   where the zeros enter as an exponential sum and the Laplace transform, Landau's theorem and
   Ingham's inequality are the tools. The two meet on lag lattices, where both apply.
6. **Keep the other programmes in view.** The packet laws of the bi-scale theory and the tent
   detectors of the arithmetic positivity theory consume the visibility theorems here; the Hodge
   index, the lattice tools and the explicit formula live in `RHTower` and `Zeta23`.
