# Square-Root Threshold (`GaloisForLFunctions.SquareRootThreshold`)

**One question.** At height `T`, which information in the explicit formula makes an off-line zero
visible, and which unconditional mechanisms can reach that information?

The Square-Root Threshold (SRT) is a theory of *visibility*. It fixes a height, a resolution and
a zero configuration, and asks whether Weil positivity at that resolution can tell the
configuration apart from one with all zeros on the critical line. Every statement in SRT is made
at a given height and resolution, and every invisibility statement is paired with a visibility
witness.

---

## Place in the research

SRT supplies the resolution theory and the common quantitative units of the positivity programmes.
Its model configurations show what a bounded observation can miss; its lag tests turn a failure of
RH into a negative prime-window functional; its width dictionary compares estimates obtained in
different coordinates. An equivalence translates the target. It does not supply its missing bound.

The foundational chain is: **aperture → accessible lags → Toeplitz or exponential-sum data →
visibility → zero width**. On periodic configurations this is finite matrix algebra. On general
tempered configurations it uses two-bump tests, Laplace transforms, Landau's theorem, and quantitative
record estimates. Arithmetic enters when the explicit formula identifies these readings with the
actual prime source.

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Provides complete test families whose arithmetic energy SRT measures. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Shares packet envelopes, blind directions, and the distinction between observation and a complete receiver. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Its Möbius receiver damping threshold equals the zero width; finite horizons still need uniform payment. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Supplies arithmetic relations inside windows and source-specific Gram estimates. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Supplies restricted ground energies and gauges; the Rayleigh bridge converts their floors into lag floors. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Allocates prime and archimedean costs; an allocation loss at rate `2σ` bounds the width by `σ`. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Transports estimates in aperture or damping and must preserve their normalisation. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Determines what bounded certificates can establish and keeps sign information across scales. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Couples flux and forcing to the receiver budget that the width dictionary reads. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Seeks an arithmetic source of the Hodge-type sign, beyond knowing its equivalent receivers. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Resolves source signs and cancellation before applying the growth receivers. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | The programme dedicated to open problem 1: prime pairs beyond $X=T$, organised around the Frobenius surplus of the explicit-formula Gram and the form factor on $(1,\lambda)$. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Collects the endpoint equivalences of the units in one theorem, `widthDictionary_tfae`. Its Nyquist rank bound reads the threshold $N\asymp T$ as a dimension count of sections at separated heights. |

`RHTower` and `Zeta23` supply the explicit formula, lattice configurations, zero counts and analytic
continuation tools.

**The shared target.** The positivity programmes work on RH as the sign of one critical arithmetic
form, read through pairwise incidence, lag and aperture. SRT owns the lag face — one window
inequality $P_v\ge0$ per scale for the difference tests of one generic width — and the common units
in which every face reports progress: the zero width, the aperture, the visibility lag and the
excluded depth below a height.

Read §2 for conventions; the lattice and lag mechanisms in §3 are the basic pillars, collected with
their Lean names in §4; §§6–7 give the questions and open problems. The later width dictionary records both equivalences and one-way implications: fixed-aperture
odd, even, polar and blind certificates must remain distinct.

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
has about `L/(2a)` mean spacings inside a resolution cell of width `π/a` (up to the
chosen full-width convention). Increasing the aperture improves the resolution.

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
| Depth | `δ = \|Re ρ − ½\|` | — |
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
| Windowed Weil form | the Weil form of `k_f · k_η`; equals `∫ \|h_η(−2πξ)\|² W(S_ξ f, S_ξ f) dξ` | `windowedW` |
| Tempered configuration | `Σ_ρ m_ρ/(1 + \|γ_ρ\|²) < ∞` | `TemperedConfig` |
| Pair energy | `S(a) = ∫_{-a}^{a} sinh²(δu) du = sinh(2δa)/(2δ) − a` | `pairEnergy` |
| Exponential sum | `Q(ξ) = Σ_j c_j e^{2πiξν_j}` | `expSum` |
| Prime polynomial | `Π_f(ξ) = Σ_{2≤n≤X} Λ(n) n^{−1/2}(k_f(log n) n^{2πiξ} + k_f(−log n) n^{−2πiξ})` | `primePolynomial` |
| Archimedean–pole part | `A_f(ξ) = h_k(i/2) + h_k(−i/2) + ∫ h_k μ` with `k = S_ξ f ⋆ (S_ξ f)~` | `archPart` |
| Diagonal energy | `V_f = Σ_{2≤n≤X} Λ(n)²/n (\|k_f(log n)\|² + \|k_f(−log n)\|²)` | `primeVariance` |
| Prime-only polynomial and envelope | the prime terms of `Π_f`; the `ℓ¹` envelope `M_f` of its coefficients | `primeOnlyPolynomial`, `primeEnvelope` |
| Prime window functional | `P_v(k) = Σ_n Λ(n)/√n (k(log n) + k(−log n))` read on `\|log n − v\| ≤ 2w` | `lagPrimeWindow`, `lagPrimeWindowRHS` |

The configurations and the probes of the theory:

| Object | Meaning | Lean |
|---|---|---|
| Isolated pair, run, cluster | one reflected off-line pair; a contiguous run of off-line lattice points; a finite off-line set of comparable depths | `isolatedPairConfig`, `runConfig`, `clusterConfig` |
| Periodic patterns and profiles | `P` off-line pairs per period at offsets `θ_r` and depths `d_r`; a periodic depth profile on a lattice | `patternConfig`, `profileConfig` |
| Jittered and diluted lattices | ordinates `2πk/L + (−1)^k ε`; a sparse off-line lattice of spacing `2π/ℓ` inside the on-line lattice of spacing `2π/L` | `jitterConfig`, `dilutedLatticeConfig` |
| On-line shadow | a weighted on-line periodic configuration with moments `M(m) = Σ_k w_k e^{ic_k mℓ}` | `onLineShadow`, `shadowMoment` |
| Symbols and floors | depth, pattern and lattice symbols `D(m)`; the shifted symbol; the lattice ground energy `L(n − √(S₊S₋))` | `depthSymbol`, `patternSymbol`, `latticeSymbol`, `shiftSymbol`, `latticeFloor` |
| Modulated bumps | the corpus bump `κ` scaled to width `w` and modulated to height `γ`; its polar-free version with transform vanishing at `±i/2` | `RHTower.modScaledBump`, `RHTower.scaledBumpPolarFree`, `modBump` |
| Two-bump test | `β(t + v/2) + τβ(t − v/2)`, lag `v`, coupling `τ`; unimodular when `\|τ\| = 1`, difference test when `τ = −1` | `twoBump` |
| Lag structure | `S(v) = Σ_ρ m_ρ h_{β⋆β̃}(γ_ρ) e^{iγ_ρ v}`, so that `W(twoBump) = (1 + \|τ\|²)S(0) + τS(v) + τ̄S(−v)` | `lagStructure`, `lagTerm`, `lagCoeff`, `evenCoeff` |
| Minor deficit | `2 Re S(0) − \|S(v) + conj S(−v)\|`, the least `Re W` over unimodular two-bump tests at lag `v` | `minorDeficit` |
| Right zeros, off-line weights | the zeros `Re ρ > ½`; the weight `q_t = m_t h_b(γ_t − iδ_t) conj h_b(γ_t + iδ_t)` of a pair at the bump | `rightZeros`, `offLineWeight`, `pairWeight` |
| On-line mass | `Σ_{on-line} m_ρ \|h_β(γ_ρ − γ₀)\|²`, the local on-line mass seen by a bump at height `γ₀` | `onLineMass`, `onLineMassOf` |
| Depth-deficit and depth-excess transforms, level tail | `G(v) = Σ_{δ_t < D} \|q_t\| e^{−(D − δ_t)v}`, `E(v) = Σ_{δ_t > D} \|q_t\| e^{(δ_t − D)v}`, and the weight of a level outside a finite part | `depthDeficit`, `depthExcess`, `levelTail` |
| Ingham kernel and constant | `∫_{−T}^{T} cos(πt/2T) e^{ixt} dt` and the constant `C(T, g) > 0` for `Tg > π` | `inghamKernel`, `inghamConst` |
| Exponential-sum profile, resolvent | the Mellin profile `x ↦ Σ q_t x^{−λ_t}` of `Σ q_t e^{λ_t v}` and its resolvent `Σ q_t/(s − λ_t)` | `expSumProfile`, `resolventSum` |
| Polar-free kernel | the autocorrelation of the polar-free two-bump test | `polarFreeKernel` |
| Three archimedean bands | the piecewise lower bounds of the archimedean symbol below aperture `1/100` | `muLow`, `muMid`, `muHigh` |

Finite lag ranges, records and the height window:

| Object | Meaning | Lean |
|---|---|---|
| Laplace lag window | `E_V(z) = ∫_0^V e^{zu} du`, the Laplace window of the lag range `[0, V]` | `lapWin` |
| Fejér windows | the windows of the weights `sin^{2k}(πu/V)`, `k ≥ 1`; order `k` decays like `\|z\|^{−(2k+1)}` | `fejerWin`, `fejerPowWin` |
| Grid window | `Q_K(w) = Σ_{k≤K} w^k`, the window of the lag grid `v = kℓ`, `k ≤ K` | `geomWin` |
| Record | at lag `V`, the right exponent `z` maximizing `\|D(z)\| e^{Re z · V}`; it exists at every lag, attained top or not | — |
| Visibility lags | `V₀(w, η, δ₀)` for a zero of depth `δ₀` with `η = \|h_w(γ₀ − iδ₀)\|`; `V(a, σ)` for a record of size `a` and depth `σ`; `V_w(γ₀, δ₀)` for the bump modulated to `γ₀`; the zone lag `V_μ` | `oneParamLag`, `recordLag`, `nearTopLag`, `zoneLag` |
| Horizon of a zero | `V₀(w, \|h_w(−iz)\|, Re z)`: zeros with `V₀ ≤ V` are inside the horizon of the lag range `[0, V]` | `oneParamHorizon` |
| Window prime polynomial | `Re Π_ℓ(T) = Σ_{n ≤ e^{2ℓ}} a_n cos(T log n)`, `a_n = 2Λ(n)n^{−1/2}K_ℓ(log n) ≥ 0`, the prime part of the Weil form of the bump of aperture `ℓ` modulated to height `T` | `windowPrime` |
| Off-line correction | `Corr_ℓ(T) = Σ_ρ m_ρ (Re K̂_ℓ(γ_ρ − T) − ψ_ℓ(Im ρ − T))`, zero under RH | `offLineCorrection` |
| Zero-count remainder | `S(T) = N(T) − (T/2π) log(T/2πe) − 7/8` | `rvmRemainder` |

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
* **Near-top zero:** a zero whose depth is within `1/V` (or `μ/V`, a **zone**) of the supremum of
  the depths; it exists at every lag when RH fails, whether or not the supremum is attained.
* **Loud, quiet:** a record is loud when its coefficient dominates the potential of the other
  exponents; the **loudness ratio** compares them at the lag itself.
* **Twin, cluster, collapsed cluster:** a companion zero of a record within a radius `r`; a set of
  `p` companions; a cluster whose geometric-mean radius is exponentially small in `Vr/p`, an
  approximate multiple zero.

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
   small. Exact cancellation has a rigid equality case: Newton's identities turn the required
   vanishing power sums into crystalline ordinates in the stated uniform-depth class. This is not
   a classification of every configuration that hides at one aperture. At a single scale the
   crystal is also the variational extremum: it is exactly the uniform-depth pattern
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
    every grid step outside the countably many resonances `(γ − γ')ℓ ∈ 2πℤ`. When the step is a
    prime logarithm the resonances are sparse in the primes: two distinct zeros collide at
    `ℓ = log p` only if they have the same real part and ordinates differing by a multiple of
    `2π/log p`, and by independence of prime logarithms this happens for at most one prime. So for a
    configuration with finitely many right zeros all but finitely many primes separate them, and
    at each such prime the Gram form of the tower `g(· − k log p)` of one spectrally generic test
    has exactly as many negative squares as there are right zeros
    (`almost_every_prime_tower_sees_every_right_zero`, Arithmetic Castelnuovo–Severi). Chains are the exact
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

### Finite lag ranges: records, twins and horizons

The criteria of mechanisms 9 and 21 decide the line through Landau's theorem, which is not
effective: it says that some lag is negative, not which one. On a finite lag range the same
argument becomes quantitative.

22. **The record-potential law.** If the difference family is nonnegative on `[0, V]`, the Laplace
    window `G` of the nonnegative function `φ(0) − φ` satisfies `|G(σ + it)| ≤ G(σ)`. Expanding `φ`
    over the exponents gives, for every exponent `z₀` and every `s = σ + it`,
    `|D(z₀)E_V(z₀ − s)| ≤` the archimedean and pole terms plus the potential `Σ_{z ≠ z₀}|D(z)||E_V(z − s)|`
    of the other exponents (`norm_evenCoeff_mul_lapWin_le`). This is an effective Landau theorem that
    tests every exponent, not only the top. Once the loudness ratio of the record is bounded, the first
    negative lag is at most `θ⁻¹ log(2 + (4|M|/σ + κΣ|D|)/(κN|D(z₀)|))`, `θ` the depth of the record
    above `σ` (`exists_lag_neg_of_loudness`). What replaces attainment is the loudness of the record at
    the lag itself. Fejér weights `sin^{2k}(πu/V)` keep the positivity and raise the decay of the
    potential to `|z|^{−(2k+1)}`, through the exact recursion
    `(z² + ((2k+2)π/V)²)K_{k+1} = (2k+2)(2k+1)(π/V)²K_k`; already at `k = 1` the loudness ratio enters
    only as `N^{1/3}`. On a grid `v = kℓ` the distances become aliasing gaps `|1 − e^{(z − s)ℓ}|`
    (`norm_evenCoeff_mul_geomWin_le`): a chain hides from the grid exactly when its loud members alias
    onto the record and onto the real axis at the record's own scale, and the continuum family sees
    such a chain at a lag `O(log M)` (`exists_re_gridChainSum_gt`).
23. **For `ζ`, hiding needs twins, twins need triples, clusters collapse.** With the local zero count
    (at most `160 log(180(|a| + 5))` zeros with height in `[a, a + 1]`) and the Lorentzian zero mass,
    positivity of the modulated family on `[0, V]` forces every loud near-top record to have a
    companion within `73(κ_w + π log log(180(Γ + 6)) + 4π)/V`, with `κ_w` explicit in the width
    (`zeta_uniform_twin_radius`): the uncertainty scale `1/V` up to `log log γ`. Two Fejér orders
    eliminate a twin exactly (`dipole_elimination`), so an isolated twin is exponentially tight; and the
    coefficients of nearby zeros are phase-coherent, because nearby squares of a smooth transform cannot
    cancel, so a tight twin adds to its record instead of hiding it (`zeta_isolated_twins_cannot_hide`).
    Iterated elimination shows that a cluster of `p` zeros hiding a record has geometric-mean radius
    `O(r e^{−cVr/p})`, `p ≤ 80 log(180Γ)`: positivity forces approximate multiple zeros near the top
    (`zeta_near_top_cluster_collapse`). An empty annulus among nested ones splits a cluster into a
    coherent core and loose members; eliminating only the loose members closes the collapsed-cluster
    alternative.
24. **Explicit lags.** A zero `1/V`-near the top at height `γ₀`, attained or not, is seen by a
    modulated difference test at a lag at most `V_w(γ₀, δ₀) ≍_w (log γ₀)² log log γ₀/δ₀`
    (`zeta_near_top_visible_at_polylog_lag`). For the one-parameter family `P_v` itself, with
    `η = |h_w(γ₀ − iδ₀)| > 0`, the lag is `V₀(w, η, δ₀) ≍ (log Γ₀)² log log Γ₀/δ₀ + Γ₀^{3/2}(log Γ₀)^{1/2}`,
    `Γ₀ ≍ η^{−2/3}`, with no height condition (`one_param_near_top_visible_at_explicit_lag`), and every
    such statement reduces to one record lemma at
    `V(a, σ) ≍ log²(1/a) log log(1/a)/σ + (log(1/a)/a)^{1/2}` (`one_param_record_visible_at_explicit_lag`).
    The Fejér order is `≍ P² log P`, `P ≍ log(1/a)`, from both sides; the second term is the coherence
    drift `8w e^{w/2} J_w/H₀(a)`, and `√a V(a, σ) → ∞`, `η V₀ → ∞` (`OrderOfTheExplicitVisibilityLags`).
    An attained top, and in particular every finite set of zeros right of the line, gives `P_v < 0` at
    some `v ≤ V₀(z₀)`, with no separation hypothesis (`one_param_first_negative_lag_of_finite`); the
    prime-window forms hold for `2w < log 2`.
25. **The horizon law.** `P_v ≥ 0` on `[0, V]` forces a depth gap: every zero inside the horizon lies at
    least `1/V` below the top. Iterated, from every zero inside the horizon a zero beyond it, deeper by
    more than `1/V`, is reached in fewer than `V/2` steps (`one_param_horizon_law`); on zones of width
    `μ/V` the gap is `≍ (δ₀/(V log V))^{1/2}` (`one_param_zone_depth_gap`). The attainment premise of
    the grid theorems is replaced by a condition on the zeros beyond the horizon: a configuration that
    hides from every lag in `[0, V]` must have zeros beyond it, approaching the top with ever smaller
    transform amplitude or ever larger height. What remains is the pair-correlation barrier, twins
    closer than `log log γ/V`.

### The lag face and its neighbours

26. **The unconditional envelope of `ζ`.** With the corpus zero-free regions, for every
    `w ∈ (0, ½ log 2)` and `v ≥ V₀ = max(230², 1/(100η₀²))`,
    `P_v ≥ −|φ(0)| − (W + S₂)e^{v/2 − √v/10}` (`zeta_lag_envelope`): an explicit lag at de la Vallée
    Poussin strength. The exact tradeoff behind it: a zero-free width `η` below height `G` gives
    `|φ(v)| ≤ e^{v/2}(W e^{−ηv} + S₂/(1 + G)²)`. The Vinogradov–Korobov region in the same tradeoff,
    cut at `G = exp(v^θ)` with `θ = (ex + 3/5)/2`, gives for every `0 < ex < 3/5` and all large lags
    `P_v ≥ −|φ(0)| − (W + S₂)e^{v/2 − v^ex}` (`zeta_lag_envelope_vinogradovKorobov`): the envelope
    carries exactly the strength of the zero-free region that enters.
27. **The ground-energy bridge to the aperture face.** For every smooth test supported in the closed
    interval `[−A, A]`, `μ(A)∫|g|² ≤ Re W_ζ(g, g)`; on the centred difference test at `A = v/2 + w` this
    reads `2‖κ_w‖² μ(v/2 + w) ≤ Re P_v` (`two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS`),
    so every aperture floor of `ArithmeticCriticalityTheory` is a lag floor. Conversely a ground-energy
    bound `μ(A) ≥ −Ce^{2σA}` forces `|Re ρ − ½| ≤ σ` for every zero, unconditionally
    (`re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`), and along one non-resonant geometric grid of
    windows RH is equivalent to grid positivity together with the approach of the zeros to the line
    (`riemannHypothesis_iff_zerosApproachLine_and_grid_primeWindow_nonneg`). The no-crossing of `μ(A)`
    and the absence of a first negative lag are one law in two coordinates.
    The difference test `f_{w,v}` is odd (`twoBump_modScaledBump_zero_neg`), so the odd-sector
    windows of `ArithmeticIncidencePositivity` transfer to the family without passing through the
    all-profile `μ(A)`: `Re P_{w,v} ≥ (1/500)‖κ_w‖²` for every `2w < v` with `v/2 + w ≤ 353/1000`
    (`one_div_500_mul_le_re_lagPrimeWindowRHS_of_le`), that is for every lag `v ≤ 706/1000 − 2w`,
    past the first prime. For `w < 1/12` and `|v − log 2| ≤ 2w` the window read by the test is
    exactly `{2}` (`lagPrimeWindow_eq_singleton_two`) and the inequality reads
    `(log 2/√2) Re(k(log 2) + k(−log 2)) + (1/500)‖κ_w‖² ≤ Re(polar + archimedean)`, `k` the
    autocorrelation of `f_{w,v}` (`firstPrime_atom_paid_on_lagFamily`): the first prime atom is paid
    on the problem's own family; for `w ≤ 3/1000` every lag of the prime-`2` window is covered. A
    negative lag of the family has `v/2 + w > 353/1000` (`lt_of_re_lagPrimeWindowRHS_neg`). The
    second prime window `log 3/2 ≈ 0.549` lies beyond the archimedean odd ceiling, so this mechanism
    stops before the prime `3`.
28. **The window prime polynomial reads `S(T)`.** The localized Weil form at height `T` is the
    archimedean part minus `Re Π_ℓ(T)`, a cosine polynomial with nonnegative coefficients over the
    prime powers `n ≤ e^{2ℓ}`. Through the Stieltjes identity it is a smoothed derivative of the
    zero-count remainder, `Re Π_ℓ(T) = ∫_1^{2T} S(t)ψ_ℓ'(t − T) dt − Corr_ℓ(T) + o(1)`
    (`tendsto_windowPrime_add_offLineCorrection_sub`). On the prime torus the aligned value
    `F_ℓ(1) ≥ ℓϑ²e^{ℓ/4}` is visited on a positive proportion of heights (Kronecker–Weyl), and the
    off-line correction is small outside a sparse set of heights (Selberg-type density); hence `S(T)`
    is unbounded, unconditionally (`rvmRemainder_unbounded`). A bounded spectral shift is the
    signature of a finite-rank modification of a reference operator, so no such model of the zeros
    exists: this excludes finite-rank spectral models with bounded spectral shift.
29. **The zero width and the de Bruijn–Newman heat time.** The zero width
    `zetaZeroWidth = sup |Re ρ − ½|` lies in `[0, ½]`, RH is `zetaZeroWidth = 0`, and for all but
    countably many widths `w` and every `σ ≥ 0`: `zetaZeroWidth ≤ σ` iff `P_{w,v} ≥ −Ce^{σv}` for
    all large lags (`zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp`): the width is the exact
    negativity rate of the lag family. A zero `w` of `Ξ(w) = ξ(½ + iw)` is the nontrivial zero
    `½ + iw` of `ζ`, so `Ξ` has the zero strip `(Im w)² ≤ zetaZeroWidth²`, which the de Bruijn–Newman
    flow `H_t = ∫Φ(x)e^{tx²}e^{izx}dx` contracts: every zero of `H_t` has
    `(Im z)² ≤ max(zetaZeroWidth² − 2t, 0)` and `H_t` is real-rooted for every `t ≥ zetaZeroWidth²/2`
    (`riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le`); de Bruijn's heat time `1/8` is the
    case `zetaZeroWidth = ½`. A lag envelope `−Ce^{σv}` is therefore a heat time `σ²/2`
    (`LagRateBoundsTheDeBruijnNewmanHeatTime`).
30. **Near-top zeros and the contact aperture of `μ(A)`.** A negative value of the difference test
    at lag `v` is a negative ground energy, `μ(v/2 + w) < 0`, by the Rayleigh bridge of mechanism 27
    (`ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_neg`). Hence a zero `½ + z₀` right of the
    line with `η ≤ |h_w(−iz₀)|`, seen at the explicit lag `V ≥ V₀(w, η, Re z₀)` of mechanism 25, with
    no zero deeper than `Re z₀ + 1/V`, makes `μ(A) < 0` for every aperture `A ≥ V/2 + w`
    (`ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero`): the first contact aperture of a
    hypothetical near-top zero is at most half its visibility lag plus the width, and every certified
    aperture `μ(A) ≥ 0` is the bound `V > 2(A − w)` on the visibility lag of every near-top zero
    (`NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture`).

31. **The width bounds the Weil floor in the energy normalisation.** The arrow from the width to a
    floor is unconditional once the floor is normalised by an `H¹`-type datum: if
    `zetaZeroWidth < β` then `Ẑ(F) ≥ −C(1 + A)e^{2βA}(∫F² + D)` for every `C²_c` test supported in
    `[−A, A]` whose autocorrelation has gauge derivative `a' − a/2` bounded by `D`
    (`TheWidthBoundsTheEnergyNormalisedWeilFloor`). No hypothesis on the distribution of the zeros
    appears. The mechanism is that the prime side needs no zero-density input at all: the signed
    prime–polar pairing of an autocorrelation is a Stieltjes integral against the normalised
    Chebyshev error, whose size is exactly the width, and the only test datum it costs is that sup;
    the two inputs are the exact Gamma–Lévy form of the Weil functional (the nonnegative Lévy energy
    dropped) and generalised von Koch in the Chebyshev gauge. The `L²`-normalised version is the one
    that needs the local density of the off-line zeros in a single window, and that is the open
    direction of mechanism 27.
32. **The incidence ledger graded by the zero width.** The difference tests of the lag family are
    odd and supported in `[−(v/2 + w), v/2 + w]`, and the lag rate *is* the width (mechanism 29), so
    every aperture-indexed floor of the odd sector converts into a width statement
    (`TheIncidenceLedgerGradedByTheZeroWidth`): an odd-sector floor `Ẑ(F) ≥ −C e^{2σ r}∫F²` at every
    aperture `r` gives the strip `|Re ρ − ½| ≤ σ`; written on the incidence ledger of
    `ArithmeticIncidencePositivity`, the allocation may *fail* by `C e^{2σ r}∫F²` at aperture `r`
    and still certify `½ + σ`; and at rate `0` — a constant deficit times the mass at every
    aperture — it already gives RH. Hence the sign in Weil's criterion may be replaced by any
    estimate losing less than an exponential in the aperture: polynomial and logarithmic losses are
    free. The gradation is sharp and not a reduction: the unconditional floor is rate `1` (the prime
    `ℓ¹` norm `≍ 2e^{r}`, with the smoothed on-line part only polynomial in `r`), one off-line zero
    of depth `δ` contributes `e^{2δr}`, so the lag family detects the exact width and supplies a lower bound on the exponent of any
    all-test floor. Equality for the `L²`-normalised ground-energy rate requires the additional
    argument of mechanism 36; it is not supplied by this implication alone. What the gradation buys is a unit: a
    partial allocation estimate reports an explicit strip instead of nothing. Bounded-aperture
    windows keep reporting nothing, since the gradation quantifies over every aperture.
33. **Unsigned depth sampling detects local mass.** A source-uniform bound at one positive aperture
    already controls squared depths on every unit-height window, with literal complex smooth
    interior probes (`UnsignedDepthSamplingDetectsLocalMass`). The quantity controlled is the
    unsigned conjugate-difference energy, not the signed Weil floor, so this is the sampling
    counterpart of the visibility laws: it bounds how much depth a window can hold without deciding
    any sign, and it is the shape in which a local non-clustering hypothesis becomes usable.
34. **Sampling an interval source on a locally bounded point set.** The analytic tool behind the
    floors is elementary and costs no zero-density input. Let `f` be continuous and supported in
    `[−a, a]`, `Φ(z) = ∫ f(u)e^{izu}du` its entire transform, and let `z_q = x_q + iy_q` be points
    with at most `M` heights in any unit interval and depths `|y_q| ≤ σ`. Then
    `Σ_q |Φ(z_q)|² ≤ M(2a + 2π)e^{2π}e^{2σa}∫|f|²`
    (`sum_norm_sq_testTransform_le_of_locallyBounded`). The proof is a grid Parseval identity on the
    window of length `L = 2a + 2π` plus a factorial expansion: each point is a grid point `g ∈ hℤ`,
    `h = 2π/L ≤ 1`, plus an offset `w` with `|w| ≤ h + σ`; expanding `e^{iwu}` writes `Φ(z)` as a
    series in the transforms of the moment sources `u^jf(u)`, whose grid energies are
    `L∫|u^jf|² ≤ La^{2j}∫|f|²`, and weighted Cauchy–Schwarz sums the factorial series twice. Two
    separate exponentials appear and must not be confused: `e^{2σa}` is the *depth* cost — the only
    place the configuration enters — while `M(2a + 2π)e^{2π}` is the *density* cost, linear in the
    aperture.
35. **The unconditional floor in the archimedean normalisation.** The unconditional local zero count
    is logarithmic in the height, so sampling at depth against a logarithmic density bounds the whole
    zero side by the *logarithmically weighted* transform energy — which is precisely the archimedean
    weight of the form:
    `Re W(f, f) ≥ −C(a) ∫ ‖𝓕f(y)‖² log(|y| + 3) dy`
    for every `C²` test supported in `[−a, a]`
    (`TheUnconditionalWeilFloorInTheArchimedeanNormalisation`). Nothing is assumed about how the
    zeros are distributed; the three inputs are the unconditional window count, the strip
    `0 ≤ β ≤ 1` (which bounds every depth), and the sampling inequality, and all that is used of the
    Weil summand is `Re(u conj v) ≥ −(|u|² + |v|²)/2`. This is the correct reading of mechanism 31:
    the Weil form of `ζ` is *never* unbounded below in its own archimedean normalisation, so every
    difficulty of the aperture face is a difficulty of normalisation, not of boundedness.
36. **The width is the ground-energy rate when the off-line zeros do not cluster.** The arrow from a
    ground-energy rate to the width is unconditional (mechanism 27); the converse holds under
    one explicit single-window hypothesis, `OffLineCopiesLocallyBounded M` — at most `M` off-line
    copies in any unit height window. Then
    `μ(A) ≥ −M(2A + 2π)e^{2π}e^{2σA}` at every aperture, `σ = zetaZeroWidth`
    (`neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy`): on the zero side the on-line copies
    contribute `|Φ(−z_q)|² ≥ 0` and each off-line copy at least `−(|Φ(−z_q)|² + |Φ(−z̄_q)|²)/2`, and
    mechanism 34 bounds that sum since every depth is at most the width; density carries the floor
    from smooth sources to the form vectors, and a pure-parity ground state turns it into a bound on
    `μ`. Three consequences. The *exponent identity*: the polar ground-energy exponent equals the
    zero width (`polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded`). The
    *finite case*: if only finitely many zeros are off the line, they form a top layer at depth
    exactly `zetaZeroWidth` and the fall is two-sided, `c e^{2σA} ≤ −μ(A) ≤ C e^{2σA}`. And the
    *dichotomy* (`polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster`): either the
    ground-energy exponent equals the width, or the off-line zeros cluster without bound on unit
    windows — in particular a strict inequality between exponent and width forces infinitely many
    off-line zeros. Thus a uniform local bound is a sufficient arithmetic input. It is not proved necessary for
    the exponent identity: the dichotomy says that failure of the identity forces unbounded
    clustering, not that clustering forces failure. The same local bound makes every constant of the
    near-top visibility law of mechanism 23 uniform in the height, and the dichotomy holds verbatim
    for the degree-defect rate of the scaling surface
    (`scalingSurface_defectRate_eq_zetaZeroWidth_or_offLine_cluster`, Arithmetic Castelnuovo–Severi):
    one hypothesis, one alternative, in every chart.
37. **The coupling of finitely many primes to the prime tail.** At aperture `a` the localized Weil
    form splits as `W_ζ(S_ξf, S_ξf) = A_f(ξ) − Π_f(ξ)`, with `Π_f` a polynomial over the *finitely
    many* prime powers `n ≤ e^{2a}` and `A_f` the pole term plus the archimedean term. The pole of
    `ζ` at `s = 1` is the contribution of the whole infinite prime tail, and the archimedean growth
    `μ(τ) ≈ log|τ|/2π` is the zero density, which the functional equation transports from that same
    tail. RH is exactly `Re Π_f(ξ) ≤ Re A_f(ξ)` at every aperture, profile and height
    (`riemannHypothesis_iff_primePolynomial_le_archPart`). The coupling of the two sides is
    *necessary*, not an artefact: for the odd profile `sinh(u/2)(a² − u²)₊^{5/2}` the pole terms are
    `−2(∫ f sinh(u/2))²`, the depth-`½` pair at height `0` with its extremal witness, and for large
    `a` this dominates the archimedean term, so `Re A_f(0) < 0`; since `Π_f` has windowed mean zero
    it is nonnegative at some height, and the inequality with the archimedean–pole side frozen at
    height `0` fails (`exists_archPart_zero_lt_primePolynomial`). Under RH, therefore, the primes at
    height `0` must themselves be negative (`re_primePolynomial_zero_neg`): **the finitely many
    primes below `e^{2a}` must cancel the pole**, which is the tail they are not. In minimal form the
    criterion is the rank-two `2 × 2` prime–Gamma inequality on the two pole directions `e^{±u/2}`
    (`primePolynomial_le_archPart_iff_poleCompression`), so the depth-`½` pair sector at height zero
    already carries the whole statement; Bagchi's strong recurrence implies it
    (`primePolynomial_le_archPart_of_zetaStronglyRecurrent`); and both criteria have unconditional
    density-zero shadows, the heights with `Re W_ζ < 0` having proportion `O((log X/log T)²)`.
38. **Companions for the one-parameter family, from the zero count alone.** Mechanism 23 gives the
    twin radius for the *modulated* family. For the unmodulated lag function
    `φ(v) = Σ_z D(z)e^{zv}`, `P_v = φ(0) − φ(v)`, the same conclusion holds with the attainment
    premise removed entirely. At the lag `V` the loudness `|D(z)|e^{Re z·V}` of the exponents right
    of the line attains its maximum at a **Legendre record** `z*`, because the coefficients are
    summable and only finitely many exponents are louder than any given one
    (`exists_right_record`) — whether or not the largest real part is attained. The local count
    bounds the exponents in a unit height window by `160 log(180(|a| + 5))`, hence a cubic potential
    bound `Σ|z − s|^{−3} ≤ 480 L_s(r^{−3} + 3)` for families at distance `≥ r`. Evaluating the Fejér
    window at `s = Re z* − κ/V + i Im z*` gives the **companion law** (`zeta_companion_law`): at every
    lag `V`, positivity of `P_v` on `[0, V]` forces one of three things — the record is quiet, the lag
    family is already negative on `[0, V]`, or another zero lies within
    `r ≍ κ(log|Im z*|)^{1/3}/V` of that point. A companion just below the record, closer as `V`
    grows, with nothing but the local zero count used.

### The dictionary: one aperture, one zero width

The programme's second job, after the lag face itself, is to keep the corpus's routes commensurable.
Two theorems do that, and they are the reason a partial result anywhere in the family can be priced.

39. **The positivity routes measure one aperture.** The routes that attack RH through positivity of
    the Weil form state their certificates in different languages: the restricted Weil ground energy
    `μ(A)` of the Connes–Consani–Moscovici operator (route RW), the single-shift variation inequality
    on even profiles (ACT), the sinh-capacity inequality on odd tests (OWU), the even blind minimum
    (EWU), the all-profile and odd windows `Ẑ(F) ≥ c∫F²` (AIP, APT), the complex window
    `Re W_ζ(f, f) ≥ 0` and the lag functional `P_v` (SRT). At a fixed aperture their relationships are organised by
    `TheRoutesMeasureOneAperture` around window positivity of the full zero form,
    `ZetaWindowPositive A : Ẑ(F) ≥ 0` for every real `C²_c` test vanishing outside `[−A, A]`:
    * `0 ≤ μ(A)` iff `ZetaWindowPositive A'` for every `0 < A' < A`; the forward arrow mollifies a
      `C²` window test into the strict interior, where a smooth source's Rayleigh quotient is bounded
      by `μ(A)`, and the backward arrow uses Suzuki's continuity of `μ`. Window positivity at the
      closed aperture gives `0 ≤ μ(A)` directly.
    * Parity splits it exactly: `ZetaWindowPositive A` iff the even and odd windows are both
      positive, since `Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)`.
    * The odd window *is* the OWU capacity inequality: it holds iff every odd window test satisfies
      `sinhPairing g² ≤ 2·markovForm N g` at the prime cutoff `N = ⌈e^{2A}⌉`.
    * ACT's pole-free variation form is exactly `Ẑ(m_a u)`. At one shift it is equivalent to
      the odd-window statement on tests vanishing near the origin
      (`shiftVariationWindowOffOrigin_iff_zetaOddWindowPositiveOffOrigin`). The Markov form is
      larger by `8(∫ u dμ_a)²`; its positivity only gives the polar odd-window statement
      without a further estimate on the pole direction.
    * The even blind minimum dominates `μ(A)`. Below `2A < log 2` its blind constraint is void,
      and it equals the **even polar** ground energy, not the all-test ground energy
      (`evenBlindMinimum_eq_evenGroundEnergy_of_two_mul_lt_log_two`). The full even window
      additionally requires `markovEnergy(F) ≥ −2` on the affine slice `∫F cosh(x/2) = 1`
      (`zetaEvenWindowPositive_iff_polar_and_unitCoshMoment`).
    * The Rayleigh bridge gives a lag floor from an all-test ground-energy floor. Positivity of
      the lag family on a bounded range has no converse giving all-test window positivity.
    * At the endpoint, RH iff every aperture is window positive iff every ground energy is
      nonnegative.

    So **the aperture through which all-profile positivity is proved is the common unit of RW, ACT,
    OWU, EWU, AIP, APT and the SRT window, and an improvement on one face counts once.** A result
    announced in one of these languages is not independent evidence for the others; it is the same
    number read in another chart.
40. **The prime-side and zero-side routes measure one zero width.** The walls dictionary reads
    `zetaZeroWidth = sup|Re ρ − ½|` in the languages of the walls (Chebyshev deficit, mean-square
    band, window ceiling, lag family, ground-energy floor, heat time, Jensen integral); this extends
    it to the frontier map's routes, so each route's "quantitative progress" is the same number
    (`TheRoutesMeasureOneZeroWidth`). `zetaZeroWidth ≤ σ` iff:
    * **PBM** — the series `Σ((Λ(n) − 1)/log n)n^{−s}` converges at every real `s > ½ + σ`,
      equivalently the regularized prime zeta series does, equivalently the `Λ − 1` series does;
    * **WL** — one-sided packet growth at exponent `σ` for every test, equivalently the
      spline-weighted prime inequality at exponent `1 + σ`;
    * **TT** — finite natural Wold energy at every radius `t < ½ − σ`, equivalently the raw directed
      covariance bounded above at every such radius;
    * **HCF** — the complete Gaussian Hedenmalm Hankel tail cone above `σ`;
    * **SZ** — zero-freeness right of the shifted critical line;
    * **TH** — the thermal projective moments grow at most like `σ^m`;
    * **RW / HF** — analyticity of the critical Mellin defect, and of the inverse-tilted dyadic
      source, above `½ + σ`;
    * **FU / MC** — a dyadic weighted prime-window power bound at exponent `σ`;
    * **PA** — vertical type of the canonical Poisson trace at most `σ`;
    * the horizontal support radius of the Xi divisor equals the width; and
    * **LA / TT / SZ / TH** — every cosine shift `cos(hD)Ξ` with `h > zetaZeroWidth` lies in the
      Laguerre–Pólya class, the unconditional `h ≥ ½` and the RH case `h > 0` being the two ends of
      the strip.

    Every one of these is a composition of the width dictionary with a receiver the corpus proves
    for the half-plane bound, and **none of them supplies a bound on the width.** That is the point
    of the dictionary: it converts route-local progress into one comparable exponent, and it makes
    visible that no route has yet produced an exponent below `½` at all. The endpoint equivalences
    of the programmes' own units (Hodge index, effectivity, positive inertia, damping, pronic
    energy, mean-square band, finite-radius refutation) are collected in Arithmetic Orientation
    Theory as one theorem, `widthDictionary_tfae`.

### Arithmetic inside one lag window

For `2w < log 2`, the prime-power window `|log n − v| ≤ 2w` has multiplicative ratio less than
`4`. Valuations make its low-order multiplicative relations rigid. In any half-open window
`Y ≤ n < 4Y`, a relation `Σ c_n log n = 0` with
`(Σ |c_n|) log 3 ≤ 2 log Y` is trivial (`window_relation_eq_zero_of_log`). Consequently the
corresponding low-order multiplicative energies are exactly diagonal. On the lag family the
allowed relation order grows at least as `2(v − 2w)/log 3`
(`lagPrimeWindow_relation_eq_zero`).

The order and the window endpoint matter. Consecutive powers `2^k, 2^{k+1}` give a relation of
size `2k + 1`, showing the logarithmic order is sharp. A closed window of ratio `4` contains
`2^k · 2^{k+2} = (2^{k+1})²`, a relation of size `4` at every scale. These are arithmetic inputs
for moment and phase calculations; diagonal low moments alone do not determine the signed
prime–polar pairing at every height. The tool to seek is an estimate converting this growing
independence order into control at the lag and height actually required by the receiver.

---

## 4. Foundational pillar theorems

Unconditional; RH appears only inside equivalences or as a conclusion.

1. **The square-root threshold.** An off-line lattice at the density of the zeros of $\zeta$ is
   indistinguishable from an on-line lattice at every aperture $a\le L/2$, whatever its depth, and
   visible beyond (`RHTower.offLineLattice_weil_positive_iff`).
2. **The Toeplitz law.** For periodic configurations hiding at aperture $a$ is positive
   semidefiniteness of a Toeplitz section of the cosh-weighted modes
   (`profileConfig_weil_nonneg_iff`); by Carathéodory–Fejér, hiding is mimicry of on-line translates.
3. **Faithfulness.** The one-parameter lag family determines the zero configuration with
   multiplicities (`lag_weil_eq_iff_symmMult_eq`, `eq_zetaZeroConfig_of_lag_weil_eq`).
4. **One parameter decides the line, and measures the abscissa.** For one generic width, RH iff the
   prime windows $P_v$ are nonnegative at every lag (`zeta_onLine_iff_lag_primeWindow_nonneg`), and
   $\Re\rho\le\tfrac12+\sigma$ iff $P_v\ge-Ce^{\sigma v}$ (`zeta_re_le_iff_lag_primeWindow_ge_neg_exp`).
5. **Finite-range visibility.** The record-potential law gives explicit lags: a near-top zero is seen
   at a polylogarithmic lag (`zeta_near_top_visible_at_polylog_lag`), and nonnegativity on $[0,V]$
   forces a depth gap (`one_param_horizon_law`, `zeta_depth_gap_of_lag_positivity`).
6. **Lag floors are ground-energy floors.** $2\lVert\kappa_w\rVert^2\mu(v/2+w)\le\Re P_v$; a near-top zero
   seen at lag $V$ makes $\mu(A)<0$ beyond $V/2+w$ (`ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero`,
   `theContactApertureOfTheGroundEnergyPath`).
7. **The width dictionaries.** The routes read one zero width and one aperture
   (`theRoutesMeasureOneZeroWidth`, `theRoutesMeasureOneAperture`); the side of a zero is its depth
   and the width is the supremum of the depth meters (`theSideIsTheDepth`,
   `theWidthIsTheSupremumOfTheDepthMeters`); the lag rate bounds the de Bruijn–Newman heat time
   (`riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le`).
8. **The width bounds the floor.** Width $<\beta$ gives a Weil floor at rate $2\beta$ in the energy
   normalisation (`exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt`); the form is unconditionally
   bounded below in the archimedean normalisation (`exists_re_W_ge_logWeighted_rate_sharp`); and the
   ground-energy rate equals the width unless off-line depth mass clusters without bound on unit
   windows (`polarGroundEnergyRate_eq_zetaZeroWidth_or_depthMass_clusters`).
9. **The graded incidence ledger.** A graded allocation deficit $Ce^{2\sigma r}$ bounds the width by
   $\sigma$, and a zero deficit is RH (`zetaZeroWidth_le_of_gradedIncidenceAllocation`,
   `riemannHypothesis_of_gradedIncidenceAllocation_zero`).
10. **Weil positivity through $3/10$.** $\Re W(f,f)\ge\lVert f\rVert^2/5000$ for every test of aperture
    $\le3/10$ (`zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths`) — a nonselective certificate: it
    holds for every prime weight (`WindowCertificatesAndThePrimeWeight`).

---

## 5. Traps

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
| Counting on critical zeros to supply mass `A∫\|f\|²` at every aperture | On-line zeros sample the tests of aperture `a` only below the Nyquist aperture of their ordinates; a periodic on-line configuration with `r` ordinates per period gives `A > 0` iff `⌈2a/ℓ⌉ ≤ r`, and above that some test of positive mass sees no on-line zero at all. |
| Expecting sparse off-line structure to hide as long as dense structure | An off-line lattice of density `ℓ/2π` inside an on-line background of density `L/2π` hides only up to `≈ (1/2δ) log(L/ℓ)`, like isolated pairs; only a crystal of the full density reaches `L/2`. |
| Expecting averaged information to reach depth | Window averages of resolution `r` are integrals of aperture-`r` Weil forms. Off-line lattices of spacing at most `π/r`, and clusters invisible at aperture `r`, pass them. |
| Looking for a quantity that certifies an off-line zero below its visibility aperture | There is none in the Weil form: an invisible lag-lattice configuration has exactly the Weil form of a weighted on-line configuration on every test of that aperture. |
| Expecting the prime side to keep a sign along a short height window | For windows of aperture `2r ≤ log 2` the windowed mean of `Π_f` is exactly `0`; its positive and negative excursions balance. |
| Expecting the small primes to carry the criterion | RH is decided by the two-bump tests at lags `v ≥ V`, each reading one dyadic window of primes near `e^v`, for any `V`. Finite prime data can be discarded entirely. |
| Reading the one-parameter criterion as a local detector | The unmodulated tests see a zero at height `γ` with weight `\|h_w(γ − iδ)\|²`, which decays in `γ`. The Laplace–Landau criterion alone is ineffective; the record theorems give explicit unmodulated lags depending on that amplitude. Modulation gives a different, height-localised bound. |
| Positivity on a restricted family as evidence for RH | State the family's resolution and compare it with the lattice law first. |
| Weakening to "fixed σ < 1" | These are quasi-RH half-planes, open for every `σ < 1`. |
| Applying an upper-bound sieve beyond `X = T` | The sieve bounds prime pairs only against weights `w ≥ 0`. The height phase `(m/n)^{iT}` changes sign, so the sieve reverts to the size-only bound. |
| Treating `X = T` as a technical limit of one method | It is the diagonal threshold of the mean value theorem, the point where the sieve loses the height phase, and the density-hypothesis threshold of the zero side. |
| Using `Re W` without the conjugation convention | `W(f, f)` uses `conj(h_f(conj γ))`. For an off-line pair it is `2 Re(A conj B)`. |
| Expecting a bounded exponential sum over the zeros to keep a top pole | A sum `Σ q_t e^{λ_t v}` bounded on `v ≥ 0`, or bounded on one side, has zero coefficient at every rightmost, unshared exponent; its growth rate is the abscissa of its top poles. |
| Expecting the visibility aperture to depend on the arrangement of the on-line zeros | It depends on the on-line background only through the logarithm of the local on-line mass at the bump; the arrangement is irrelevant. |
| Expecting the ground energy to vary continuously with the aperture | On lag lattices it is a step function with jumps at every `nL/2`; continuity is a property of the restricted operator of `ζ`, not of configurations. |
| Expecting the minimal receiver to be aperture-optimal | It is exact on crystals, but its teeth read only the real part of each rotated mode: a quarter-turn pattern visible at aperture `3ℓ/4` is first seen by the family at lag `4ℓ`. |
| Expecting a lag grid to decide the line | A grid `v = kℓ` sees every attained top for non-resonant `ℓ`, but a chain whose heights approach `(2π/ℓ)ℤ` can keep a one-sided grid bound. Only the continuum of lags excludes chains. With finitely many right zeros, every prime-logarithm grid except finitely many is non-resonant; with infinitely many, the eigenvalues may accumulate and no single prime is guaranteed. |
| Expecting all couplings `τ` to be needed in the two-bump criteria | Unimodular `τ`, and for `ζ` the single sign `τ = −1`, suffice; the lag `v` and the height `γ` are the only parameters. |
| Reading Landau's theorem as a visibility lag | It is not effective. Lags come from the record-potential law on a finite range, and they need the loudness of the record at that lag. |
| Expecting an unattained top to escape every explicit lag | A `1/V`-near-top zero exists at every lag and is seen at `V₀(w, η, δ₀)`; what escapes is a configuration with zeros beyond the horizon. |
| Expecting a twin to hide a record | Nearby coefficients are phase-coherent, so a tight twin adds to the record; hiding needs at least triples, and then a collapsed cluster. |
| Mixing the visibility lags | `V₀(w, η, δ₀)` is for `P_v` itself and carries the transform amplitude `η`; `V_w(γ₀, δ₀)` is for the bump modulated to the zero's height and carries `log γ₀`. |
| Treating the ground-energy floor and the lag floor as different problems | `2‖κ_w‖²μ(v/2 + w) ≤ Re P_v`: aperture floors are lag floors, and the two no-crossing laws are one. |
| Treating the sign of the critical form as the thing to be proved | An estimate losing less than an exponential in the aperture suffices (mechanism 32); the lag family reads the width exactly. Equality with the all-test `L²` ground-energy exponent is established under the local bound of mechanism 36. |
| Accumulating bounded-aperture windows into a width bound | The gradation quantifies over every aperture. A family of windows with a bounded supremum of apertures reports nothing in the width unit, whatever its constants. |
| Reading the energy-normalised floor as the `L²` one | The unconditional arrow from the width costs an `H¹` datum, the sup of the gauge derivative of the autocorrelation; the `L²`-normalised floor needs the local density of off-line zeros in one window, which no averaged zero-density theorem supplies. Under an explicit local bound `M` per unit window it is a theorem, with the exponent equal to the width; without one the alternative is unbounded clustering. |
| Reading the Weil form of `ζ` as unbounded below | It is not: `Re W(f, f) ≥ −C(a)∫‖𝓕f‖² log(\|y\| + 3)dy` unconditionally, from the local zero count alone. Every difficulty of the aperture face is one of normalisation. |
| Taking the depth cost and the density cost of a sampling bound as one factor | `e^{2σa}` is the depth cost, the only place the configuration enters; `M(2a + 2π)e^{2π}` is the density cost, linear in the aperture. A method improving one does not improve the other. |
| Treating a positivity result in one route's language as independent evidence for the others | Track the arrows in mechanism 39: all-test positivity implies restricted tests; polar and blind windows omit directions. Their common global endpoint does not make all bounded readings equivalent. |
| Reading a graded receiver of some route as progress on the width | Every route's graded receiver is the width dictionary composed with a proved half-plane receiver; none of them bounds the width (mechanism 40). |
| Expecting the finitely many primes below `e^{2a}` to be bounded by the archimedean part alone | They must cancel the pole, which is the whole infinite prime tail: with the archimedean–pole side frozen at height `0` the inequality fails, so under RH the primes at height `0` are themselves negative (mechanism 37). |

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **What can a test of aperture $a$ see?** Lags up to $2a$, primes up to $e^{2a}$, ordinates to
   scale $\pi/a$. Isolated and finite configurations are visible at small apertures; a crystal at the
   full zero density hides up to $L/2$; visibility is a Toeplitz question on periodic configurations
   and a record question on tempered ones.
2. **Which configurations can hide, and from what?** Below the threshold, crystals and their
   mimicry classes; for $\zeta$ itself, hiding from $[0,V]$ needs twins, twins need triples, and
   clusters must collapse — or zeros must lie beyond the horizon.
3. **What one quantity do all positivity and cancellation routes measure?** The zero width, through
   exact dictionaries; and the aperture, through one-way and two-way arrows that must be kept
   distinct.
4. **In which normalisation is a floor the width?** In the energy and archimedean normalisations,
   unconditionally; in $L^2$, unless off-line zeros cluster without bound on unit windows.
5. **What unconditional information about primes reaches beyond $X=T$?** The question the theory
   exists for; every known route stops at the square-root threshold for its own reason.

### 6.2 Tools

Built and reusable:

- *Lag representation* of the Weil form and *Poisson on lattices*.
- *The Toeplitz law* with Carathéodory–Fejér mimicry, ground-state laws on lag lattices.
- *Two-point minors* and *Ingham windows* for arbitrary tempered configurations.
- *The one-parameter lag family* $P_v$: the two-bump difference tests at one generic width.
- *The record-potential law*, explicit visibility lags and the horizon law.
- *The Rayleigh bridge* from lag tests to the ground-energy path.
- *Width dictionaries* across routes, with the graded ledger in the width unit.
- *Sampling on locally bounded point sets* for unsigned depth detection.

To be built:

- a single-height prime estimate using the height phases beyond $X=T$;
- control of zeros beyond every finite horizon;
- the $L^2$-normalised width arrow without a local count, or the exclusion of the clustering branch;
- a quantitative visibility tradeoff $\delta(n,R)$ below $T(n,R)$.

---

## 7. Open problems

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

   The pair-correlation conjecture is open on `(1, λ)` even under RH. Trans-Threshold Pair
   Correlation works on this problem at `λ = 4/3`. There the diagonal, archimedean and pole core of
   the Gram trace drops to `43/36`, and three-quarters of the zeros on the line reduces to a
   prime-surplus bound with budget `1/18`, equivalently `∫_1^{4/3}(4/3 − α)F(α)dα ≤ 1/9`. The
   sine half of the off-diagonal kernel has no close-pair pole, the cosine half reduces to a mixed
   mean value of prime Dirichlet polynomials, and Jackson grid weights confine what is left to the
   close pairs `|log(n/m)| < 4b` — but not to the coalescent band `|log(n/m)| ≲ 1/T` itself, since
   their cubic tails force `b ≫ T^{−5/9}`; averaging over the height does reach the band, at fixed
   prime cutoff. Montgomery's shifted Fejér majorant, which uses only `F ≥ 0` and the sub-threshold
   identity, misses the budget by the factor `8/3` (`fejer_shifted_bound_gap`): the missing input is
   arithmetic information on `[1, 4/3]`, the signed correlation of prime pairs `(m, m + h)`,
   `h ≪ m/T`.
2. **Clusters without a depth gap.** For periodic configurations visibility is a Toeplitz question
   about cosh-weighted modes; for finite off-line sets the aperture is `(1/2g) log M` with `g` the
   gap below the deepest level (mechanism 9). Every off-line zero is visible at some aperture,
   whatever the other off-line zeros do. When the top depth is attained, the aperture is, up to
   one Ingham window `4π/g`, the larger of half the relaxation lag of the depth-deficit transform
   and `(1/2D) log M`, whether or not depths accumulate at the top. When the top depth is not
   attained, a level is still seen in any window where the deficit of the shallower zeros and the
   excess of the deeper ones are both small. For `ζ` itself the finite-range theory of mechanisms
   22–25 answers the near-top question: a near-top zero is seen at an explicit polylogarithmic lag,
   and hiding from `[0, V]` needs zeros beyond the horizon. Open: control of the zeros beyond every
   finite horizon, that is of tops approached by zeros of vanishing transform amplitude or growing
   height, and the removal of the residual pair-correlation alternative (twins closer than
   `log log γ/V`); for general configurations, how fast the excess transform at the height of a zero
   can grow compared with the relaxation of its deficit.
3. **Sharper constants.** Weil positivity of `ζ` holds unconditionally on every test of aperture
   `a ≤ 3/10`, with `Re W ≥ ‖f‖²/5000` (`ZetaWeilPositivityThroughApertureThreeTenths`: the
   zero-side form splits as `Ẑ(Re f) + Ẑ(Im f)`, so every all-profile window of the full zero form
   transfers with its constant; the three archimedean bands alone give `a ≤ 1/100`,
   `Re W ≥ ‖f‖²/25`). The remaining distance to Yoshida's aperture `(log 2)/2` is the all-profile
   window of the aperture face; on the family `P_v` itself the odd window reaches
   `v/2 + w ≤ 353/1000`, past `(log 2)/2` (mechanism 27). The archimedean
   horizon is `exp(C_ε + (4 + ε)√X)`, so the localized forms at height `T` are positive for
   `√X ≤ (¼ − ε) log T`. The coefficient `4` is optimal for bounds on the prime symbol that are
   uniform in height, since `P_X(0) = −(1/π) Σ_{n ≤ X} Λ(n)/√n ~ −(2/π)√X`. A larger single-height
   range must use how the prime phases depend on the height (mechanism 20). These window
   certificates are nonselective (`WindowCertificatesAndThePrimeWeight`): the Weil functional of a
   weight `w` reads `w(n)` only where `log n` meets the support of `f ⋆ f̃`, so the aperture-`3/10`
   certificate holds verbatim for every prime weight (the Liouville twist `λΛ` included), and the
   odd window `[−181/500, 181/500]` for every weight with `w(2) = log 2`; the Liouville twist
   reverses the atom at `2` and adds `√2 log 2 (k(log 2) + k(−log 2))`.

### Research topics

1. **`P_v ≥ 0` beyond an explicit lag `V` for one generic width**: the first selective, cofinal,
   weight-specific estimate; the unit is `V`.
2. **Beyond the horizon.** The attainment premise of the grids is replaced by the horizon law
   (mechanism 25): a first negative lag exists, at an explicit lag, unless zeros lie beyond the
   horizon. Whether the actual zero configuration of `ζ` has no negative lag is RH itself. The remaining
   arithmetic task is to control what can lie beyond every finite horizon; finite-range visibility
   alone does not exclude that escape.
3. **Localized explicit formula at height `T`** with the off-diagonal pair structure at bandwidth
   `λ > 1`, organized around the square-root threshold rather than the cutoff.
4. **The visibility tradeoff.** The exact relation between aperture, height localization and
   arithmetic length needed to make a given off-line configuration visible, and the strongest
   estimate available at that length; the unit is `δ(n, R)` below `T(n, R)`.
5. **Window incidence.** The window tests `lagPrimeWindow` carry the incidence structure proved in
   `ArithmeticIncidencePositivity` (doublings, triplings, consecutive powers of `2` and `3`); turn it
   into a lag-side statement about which prime pairs a window inequality must pay.
6. **Calibration** of the threshold and of the first-negative-lag law over `F_q[T]`.
7. **Every height.** Conditioned-tail estimates for the orbit `τ ↦ ζ(· + iτ)` on a prescribed disc
   (the Bagchi lane of `RHTower`): recurrence holds on every zero-free disc, RH is local disc
   recurrence at every point of the strip, and the object to control is the tail conditioned on the
   return set of the finite Euler head. The conditioning itself costs nothing: head-conditioned
   decoupling (`RHTower/HeadConditionedRoughDecoupling`) proves a mean value theorem at arbitrary
   *distinct* integer frequencies and, from it, that weighting the heights by any probe built on
   the primes below `y` — in particular by one concentrated on the return set — leaves a `y`-rough
   Dirichlet polynomial's mean square unchanged, with the effective error coming from integrality
   of the frequencies (`|log(A/B)| ≥ 1/max(A, B)`) and therefore native to `ℕ`: a Beurling system
   keeps the exact diagonal and loses the effective form. The residual is that the rough mean
   square is *unchanged*, not small, while the lane needs the tail to return: the uncontrolled
   object is `log ζ(s) − Σ_{p ≤ y} p^{−s}` at a single fixed `s`, and with it the control of
   near-top zeros beyond a finite horizon (mechanism 25).
   The orbit lane has Voronin universality and recurrence modulo the local zero divisor at
   every point (`RHTower/ZetaVoroninUniversalityOnSmallDiscs`,
   `RHTower/ZetaRecurrenceAtEveryPointModuloItsZeros`); the cofactor-return heights fix the phases
   of the primes `≤ y` only through the disc values `Σ Λ(n) ω(n) n^{−z} ≈ −g′/g`, weights `n^{−Re z}`
   with `Re z > 1/2`, which leave `Σ_{p ≤ N} Λ(p) p^{−1/2} k_f(log p) ω_p` free once `N` exceeds the
   base cutoff: the orbit reads the prime phases at bandwidth zero, the localized criterion needs
   them at `√X ≳ log T`. The two lanes meet only at the square-root threshold (open problem 1).
8. **The `L²`-normalised width arrow, and the clustering alternative.** Mechanism 31 proves
   `width < β ⟹` floor at rate `2β` with an `H¹` datum in the normalisation. The `L²` form, which is
   what the ground-energy path and the graded ledger consume, is proved under one explicit
   single-window hypothesis: at most `M` off-line copies per unit height window gives
   `μ(A) ≥ −M(2A + 2π)e^{2π}e^{2σA}` and the exponent identity, and the alternative is sharp — either
   the ground-energy exponent equals the width, or the off-line zeros cluster without bound on unit
   windows (mechanism 36). The open problem is to rule out the clustering branch, or to prove the
   exponent identity without a local count. Note what the clustering branch would cost:
   unboundedly many off-line copies per unit window, which is far stronger than anything a
   zero-density theorem permits on average — and yet no unconditional theorem excludes it, because
   the log-mean route cannot be pushed further (Littlewood's lemma on a unit window has horizontal
   edges of size `S(T)`, which mechanism 28 proves unbounded). The unconditional archimedean-
   normalised floor (mechanism 35) shows the difficulty is purely one of normalisation: the form is
   bounded below in the weight that the zero count naturally supplies, and the question is whether
   `L²` is reachable from it.

---

## 8. Principles

1. **Search the corpus before proving:** `scripts/formal_tools.py research "<query>"` from the repository root. The
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
