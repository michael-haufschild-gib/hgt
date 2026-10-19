# Square-Root Threshold (`GaloisForLFunctions.SquareRootThreshold`)

**One question.** At height `T`, which information in the explicit formula makes an off-line zero
visible, and which unconditional mechanisms can reach that information?

The Square-Root Threshold (SRT) is a theory of *visibility*. It fixes a height, a resolution and
a zero configuration, and asks whether Weil positivity at that resolution can tell the
configuration apart from one with all zeros on the critical line. Every statement in SRT is made
at a given height and resolution, and every invisibility statement is paired with a visibility
witness.

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
   at the same Nyquist aperture.
6. **Ground state.** `inf Re W(f,f)/∫|f|²` over tests of aperture `a` is `ℓ` times the lowest
   eigenvalue of the Toeplitz section, with or without the polar constraint. For the off-line
   lattice it is `L(n − √(S₊S₋))`, `S_± = Σ_{j<n} e^{±2δjL}`: it decays like `−e^{2δa}`, with
   exponent the depth.
7. **Modes are amplified by `cosh`.** For offsets `θ_r` and depths `d_r`, the mode `D(m)` is the
   `m`-th Fourier coefficient of the ordinate pattern weighted by `2cosh(d_r mℓ)`. Hiding up to
   the Nyquist aperture needs `|D(m)| ≤ D(0)` for every mode below the period. At growing density
   the weights grow exponentially, so the pattern's Fourier coefficients must be exponentially
   small: the deepest points dominate, and only uniform depth with crystalline ordinates survives
   (Newton's identities turn vanishing power sums into an arithmetic progression).
8. **Edges and variation.** Inside an on-line background the off-line part enters as
   `∫ k(u) Σ_k 2(cosh(d_k u) − 1) e^{2πiku/L} du`. Summation by parts in `k` turns the exponential
   sum into differences of depths. So a small aperture reads the *variation* of the depth profile,
   not the depth: the edge of a long run (a jump `0 → δ`) in a dense background is visible at an
   aperture of order `1/δ` that depends neither on the length of the run nor on the density;
   slowly varying profiles hide much longer.
9. **Rank-two pair estimate.** A reflected pair contributes `2 Re(A conj B)` with
   `A = ⟨F, e^{δ·}⟩` and `B = ⟨F, e^{−δ·}⟩`. On `[-a, a]` this is at least
   `(2a − sinh(2δa)/δ)‖F‖²`, with equality at `F = sinh(δ·)`.
10. **The pole is a pair.** The pole terms `h_k(i/2) + h_k(−i/2)` have the shape of a depth-`½`
   pair at height `0`. For an odd real profile they equal `−2(∫ f sinh(u/2))²`. The pole of `ζ` at
   `s = 1` is the contribution of the whole infinite prime tail.
11. **Polar blindness.** Constraining tests by `h_f(±i/2) = 0` (the Hodge class) removes the pole
   terms, but costs nothing against lag-lattice configurations: the bump `κ'' − κ/4` has transform
   vanishing at `±i/2`, and so does every combination of its translates. On such configurations the
   Hodge index at level `a` is full Weil positivity at aperture `a`.

### Windows and heights

12. **Slice factorization.** `k_f · k_η = ∫ k_{g_s} ds`, and every slice lies in the support of
    `η`.
13. **Height averaging.** `k_η(v) = ∫ |h_η(−2πξ)|² e^{2πiξv} dξ`. So windowed forms are height
    averages of localized forms, and positivity at aperture `r` passes to every windowed form of
    resolution `r`, whatever the aperture of the test.
14. **Windowed Gram identity.**
    `∫ |h_η(−2πξ)|² |Q(ξ)|² dξ = Σ_{j,k} c_j c̄_k k_η(ν_j − ν_k)`. Since `k_η` vanishes beyond
    `2r`, only pairs of frequencies closer than `2r` interact.
15. **Minimum-aperture resolution.** Averaging with two windows of apertures `r` and `ρ` multiplies
    their kernels, so only frequency pairs closer than `2 min(r, ρ)` interact. A secondary window
    that separates the frequencies restores the exact diagonal even when the primary window lies
    beyond the threshold.

### Prime side

16. **Height phase of prime pairs.** At height `T` a pair `(n, m)` enters with the phase
    `(m/n)^{iT}`. In Zeta23 this is the kernel `Aminus`, an integral over `t ∈ [T, 2T]`. For
    `m = n + h` the phase `e^{iTh/n}` changes sign as `n` varies.
17. **Reality and windowed mean zero.** `k_f(−v) = conj(k_f(v))` for every `f`, so the prime
    polynomial `Π_f` is real at every height. A window of aperture `2r ≤ log 2` sees no prime
    frequency `± log n`, so the windowed mean of `Π_f` is exactly `0`: its positive and negative
    excursions balance, and it exceeds `V_f / M_f` somewhere (`M_f` the `ℓ¹` envelope of its
    coefficients).
18. **Kronecker alignment costs height.** The `log p` are linearly independent, so the prime phases
    `p^{iξ}` can be aligned to any target; the prime-only polynomial comes arbitrarily close to
    `±M_f`, and stays near it on intervals of explicit length. The archimedean part grows only like
    `log(1 + |ξ|)`. A coherent prime excursion of size `B` therefore either makes the localized
    Weil form negative or occurs at a height with `log(1 + 2π|ξ|) ≳ (B − C_f)/‖f‖²`.

---

## 4. Traps

| Trap | What is true instead |
|---|---|
| Treating aperture as a height cutoff | Aperture is a frequency resolution. A small aperture sees deep isolated zeros at any height. |
| Expecting thresholds for finite configurations | A finite configuration with an off-line pair is visible at every aperture. Thresholds come from the density of the background. |
| Thinking depth is what a test sees | Below the threshold a test sees depth only through variation: edges and rough profiles are seen at `O(1/δ)`, uniform depth only at `L/2`. |
| Treating the off-line lattice as a typical dense configuration | Its invisibility up to `L/2` is crystalline. A jitter of relative size `η` is seen at `L/2` once `cosh(δL/2) sin(πη) > 1`, and every periodic off-line pattern of fixed shape other than a crystal is seen strictly below `L/2` at large height. |
| Expecting the polar constraint to help against dense configurations | On lag-lattice configurations the Hodge index equals full Weil positivity. |
| Expecting sparse off-line structure to hide as long as dense structure | An off-line lattice of density `ℓ/2π` inside an on-line background of density `L/2π` hides only up to `≈ (1/2δ) log(L/ℓ)`, like isolated pairs; only a crystal of the full density reaches `L/2`. |
| Expecting averaged information to reach depth | Window averages of resolution `r` are integrals of aperture-`r` Weil forms. Off-line lattices of spacing at most `π/r`, and clusters invisible at aperture `r`, pass them. |
| Looking for a quantity that certifies an off-line zero below its visibility aperture | There is none in the Weil form: an invisible lag-lattice configuration has exactly the Weil form of a weighted on-line configuration on every test of that aperture. |
| Expecting the prime side to keep a sign along a short height window | For windows of aperture `2r ≤ log 2` the windowed mean of `Π_f` is exactly `0`; its positive and negative excursions balance. |
| Positivity on a restricted family as evidence for RH | State the family's resolution and compare it with the lattice law first. |
| Weakening to "fixed σ < 1" | These are quasi-RH half-planes, open for every `σ < 1`. |
| Applying an upper-bound sieve beyond `X = T` | The sieve bounds prime pairs only against weights `w ≥ 0`. The height phase `(m/n)^{iT}` changes sign, so the sieve reverts to the size-only bound. |
| Treating `X = T` as a technical limit of one method | It is the diagonal threshold of the mean value theorem, the point where the sieve loses the height phase, and the density-hypothesis threshold of the zero side. |
| Using `Re W` without the conjugation convention | `W(f, f)` uses `conj(h_f(conj γ))`. For an off-line pair it is `2 Re(A conj B)`. |

---

## 5. Open problems

1. **Beyond the square-root threshold.** Bound the off-diagonal prime pairs at bandwidth
   `λ = log X/log T > 1`. A bound for the pair correlation of the zeros on `(1, λ)` turns into a
   proportion of simple zeros on the critical line above `2/3`. Each known route stops at `X = T`,
   for a different reason:
   * **Coefficient sizes.** Size-only bounds have an excess `O(rX)` that is attained for aligned
     phases.
   * **Upper-bound sieve.** It requires `w ≥ 0`, but the height phase changes sign
     (mechanism 16). Using the phase requires prime-pair asymptotics with error terms: the parity
     problem.
   * **Zero side.** An off-line zero of depth `δ` has weight `T^{2λδ}`, so the needed estimate is
     `N(½ + δ, T) ≪ T^{1 − 2λδ + ε}`. The density hypothesis gives `λ ≤ 1` exactly.

   The pair-correlation conjecture is open on `(1, λ)` even under RH.
2. **Aperiodic clusters.** For periodic configurations visibility is a Toeplitz question about
   cosh-weighted modes. Find the visibility aperture of a cluster of `ζ`-density with no depth gap
   and no periodic structure, e.g. with irregularly spaced ordinates, and the quantity that
   replaces the Toeplitz matrix.
3. **Sharper constants.** Improve the small-aperture constant `e^{−50}` towards Yoshida's
   aperture. Replace the horizon `68√X` by the sharp prime-sum constant.

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
