# Square-Root Threshold (`GaloisForLFunctions.SquareRootThreshold`)

**One question.** At height `T`, which information in the explicit formula makes an individual
off-line zero visible, and which unconditional mechanisms can reach that information?

The programme was started by the 19 October 2026 review
([`docs/reports/review-1910/opus.md`](../../../docs/reports/review-1910/opus.md)). Its central
observations:

* every live RH route is already at full height: its open inequality is RH-equivalent or a
  quasi-RH half-plane statement;
* every positivity route leaves the same unpaid term, the signed prime−polar pairing;
* the four older programmes are organized around the cutoff `N` and the scale `log n`, while the
  difficulty sits at the height `T` and at the resolution of the local zero spacing `2π/log T`.

SRT states every problem at a given height and resolution, and proves matching **visibility** and
**invisibility** theorems.

---

## 1. Motivation in one paragraph

A test `f` supported in `[-a, a]` (the *aperture* `a`) reads primes up to `e^{2a}` and resolves
ordinates only to scale `π/a`. Zeros near height `T` are spaced by `2π/log(T/2π)`. A
Dirichlet polynomial of length `N`, averaged over `[T, 2T]`, is controlled by its diagonal exactly
when `N ≪ T` (mean value theorem). The corpus lattice law
`RHTower.offLineLattice_weil_positive_iff` shows that a dense off-line configuration becomes
visible only above the Nyquist aperture `L/2`, whatever its depth; for zeros this means prime
support beyond `T`. That is where the diagonal regime ends: the **square-root threshold**. SRT
makes this picture exact, finds the positive statements that survive below the threshold, and
isolates the arithmetic input needed above it.

---

## 2. Objects and language

All objects come from the `Zeta23` library (`formal/.lake/packages/Zeta23`) and the RHTower lattice
module. Do not redefine them.

| Object | Meaning | Lean |
|---|---|---|
| Paper Fourier transform | `h_f(z) = ∫ f(u) e^{izu} du` (entire for compact support) | `Zeta23.paperFT` |
| Zero ordinate | `γ_ρ = (ρ − ½)/i`; real iff `Re ρ = ½`; `Im γ_ρ = ½ − Re ρ` | `Zeta23.gammaOf` |
| Depth | `δ = |Re ρ − ½|` | — |
| Zero configuration | locally finite multiset in the strip, invariant under `ρ ↦ 1 − ρ̄` | `Zeta23.ZeroConfig` |
| Weil form | `W(f,g) = Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))` | `Zeta23.ZeroConfig.W` |
| Weil kernel | `k = f ⋆ g̃`, `k(x) = ∫ f(t) conj(g(t − x)) dt`; `h_k(z) = h_f(z) conj(h_g(conj z))` | `Zeta23.EF.weilTest`, `EF.paperFT_weilTest` |
| Aperture | radius `a` with `tsupport f ⊆ [-a, a]`; kernel support `[-2a, 2a]` | — |
| Actual ζ zeros | the zero configuration of `ζ`, with the explicit formula proved | `Zeta23.zetaZeroConfig`, `WeilEF.EF_lit_zetaZeroConfig` |
| Lattices | doubled on-line lattice / off-line lattice pair of spacing `2π/L` | `RHTower.onLineLatticeConfig`, `RHTower.offLineLatticeConfig` |
| Tilt identity | a vertical shift `−iδ` of the transform is the tilt `e^{δu}` of the test | `RHTower.paperFT_sub_I_mul` |
| Window slice | `g_s(u) = f(u + s) η(u)`: the part of `f` seen through the window `η` at offset `s` | `SquareRootThreshold.windowSlice` |
| Windowed Weil form | the Weil form of the product kernel `k_f · k_η`; equals `∫ |h_η(−2πξ)|² W(S_ξ f, S_ξ f) dξ` | `SquareRootThreshold.windowedW` |
| Height shift | `S_ξ f(u) = e^{2πiξu} f(u)`, so `h_{S_ξ f}(z) = h_f(z + 2πξ)` | `SquareRootThreshold.heightShift` |
| Tempered configuration | `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞`; true for lattices, isolated-pair configurations and `ζ` | `SquareRootThreshold.TemperedConfig` |
| Pair energy | `S(a) = ∫_{-a}^{a} sinh²(δu) du = sinh(2δa)/(2δ) − a` | `SquareRootThreshold.pairEnergy` |

**Words.**

* **Visible at aperture `a`:** some `C²` test supported in `[-a, a]` makes `Re W(f, f) < 0`.
* **Invisible:** the form is nonnegative on all such tests.
* **Dense:** off-line points spaced like the background.
* **Isolated:** one reflected off-line pair inside an on-line background.

---

## 3. Mechanisms

1. **Lag representation.** `W(f,g) = Σ_ρ m_ρ h_k(γ_ρ)` with `k = f ⋆ g̃`. An aperture-`a` test
   sees the configuration only through lags `|v| ≤ 2a`. A depth `δ` enters only through the
   weight `e^{±δv}` on those lags.
2. **Poisson on lattices.** On a lattice of spacing `2π/L`, the zero sum becomes the lag sum
   `L Σ_m k(mL) e^{±δmL}`. Below `L/2` only the lag-zero atom survives: the doubled on-line lattice
   contributes exactly `2L‖f‖²`, whatever the depths elsewhere.
3. **Rank-two pair estimate.** An isolated reflected pair contributes `2 Re(A conj B)` with
   `A = ⟨F, e^{δ·}⟩` and `B = ⟨F, e^{−δ·}⟩`. On `[-a, a]` this is at least
   `−½‖e^{δ·} − e^{−δ·}‖²‖F‖² = (2a − sinh(2δa)/δ)‖F‖²`, with equality at `F = sinh(δ·)`.
4. **Slice factorization.** `k_f · k_η = ∫ k_{g_s} ds` with `g_s = f(· + s) η`. Every slice is
   supported in the support of the window `η`, whatever the aperture of `f`. Hence a windowed Weil
   form at any aperture is an integral of Weil forms at the window's aperture.
5. **Height averaging.** Fourier inversion of the window kernel, `k_η(v) = ∫ |h_η(−2πξ)|² e^{2πiξv} dξ`,
   identifies the windowed form with the height average `∫ |h_η(−2πξ)|² W(S_ξ f, S_ξ f) dξ`. Here
   `S_ξ f = e^{2πiξ·} f`, so that `h_{S_ξ f}(z) = h_f(z + 2πξ)`. The zero-side exchange uses the
   Peetre bound `1 + |x| ≤ (1 + |x + y|)(1 + |y|)`.
6. **The pole is a pair.** The pole terms `h_k(i/2) + h_k(−i/2)` of the explicit formula have
   exactly the shape of an off-line pair at depth `½` and height `0`. Hence the rank-two estimate
   (mechanism 3) bounds their cost at aperture `a` by `2(sinh a − a)‖f‖²`.

---

## 4. Pitfalls

| Pitfall | What is true instead |
|---|---|
| Treating aperture as a height cutoff | Aperture is a **frequency resolution**. A small aperture can see deep isolated zeros at any height. A large aperture is needed for zeros that are shallow relative to the local spacing. |
| Expecting a visibility threshold for finite configurations | A finite configuration with an off-line pair is visible at **every** aperture: finitely many linear conditions are always solvable. Thresholds come from the density of the background. |
| Expecting averaged information to reach depth | Window averages of resolution `r` are integrals of aperture-`r` Weil forms (mechanism 4). Off-line lattices of spacing at most `π/r` are invisible to them at every depth. |
| Positivity on a restricted family as evidence for RH | A family whose resolution is bounded is compatible with dense off-line lattices. State the family's resolution and compare it with the lattice law first. |
| Weakening the quantifiers to "fixed ε" or "fixed σ < 1" | These are quasi-RH half-planes, open for every `σ < 1`. They are not easier targets. |
| Conjugation symmetry | `ZeroConfig` requires only `ρ ↦ 1 − ρ̄`. Modulated complex tests make the conjugate quadruple irrelevant in model statements; actual-ζ statements must keep it. |
| Using `Re W` on complex tests without the conjugation convention | `W(f, f)` uses `conj(h_f(conj γ))`. For real `γ` this is `|h_f(γ)|²`; for an off-line pair it is `2 Re(A conj B)`. |

---

## 5. Research topics and status

**Current map** (height `T`, prime length `X = e^{2a}`, height-window length `ℓ ≈ 1/r`):

| Regime | Status for `ζ` | Calibration |
|---|---|---|
| windows `ℓ ≳ e^{50}`, every `X` | averages nonnegative **[Lean]** (SRT-3) | off-line lattices pass too: no information on zeros |
| single heights, `X ≲ (log T/68)²` | nonnegative **[Lean]** (SRT-5a) | visibility range of depth-`½` zeros |
| windows `ℓ ≥ 2X`, `X ≤ T` | variance exactly diagonal; negative heights `O((log X/log T)²)` **[Lean]** (SRT-4) | mean value theorem as an identity |
| single heights, `X ≲ (log T)^{1/δ}` | expected to match a zero-free region of depth `δ`; one direction is proved: visibility under a depth gap **[Lean]** (SRT-5b′) | quasi-RH half-planes; no gap means lattice invisibility |
| `X > T` | off-diagonal shifted sums; Zeta23 stops at `λ = 1` | parity for `Λ` |


### Within reach (all proved, unconditional)

* **SRT-1 · Visibility law** —
  [`IsolatedOffLinePairVisibilityLaw`](IsolatedOffLinePairVisibilityLaw.lean). Exact threshold for
  one off-line pair of depth `δ` and ordinate `γ₀` in a doubled on-line lattice of spacing `2π/L`.
  * `isolatedPairConfig_weil_nonneg_iff`: for `0 < a ≤ L/2`, the configuration is invisible at
    aperture `a` **iff** `sinh(2δa)/δ ≤ 2L + 2a`. The witness is `F = sinh(δ·)` on `[-a, a]`.
  * `isolatedPairConfig_weil_nonneg_nyquist_iff`: the pair is visible below the Nyquist aperture iff
    `sinh(δL) > 3δL`, that is `δL > x₀ ≈ 2.84`, where `sinh x₀ = 3x₀`.
  * Deep zeros (`δL ≫ 1`) are visible at aperture `≈ (1/2δ) log(4δL)`
    (`isolatedPairConfig_weil_nonneg_of_le_log`, `exists_re_W_isolatedPairConfig_neg_of_log_le`).
  * Shallow zeros (`δ ≲ 2.8/L`) stay invisible up to `L/2`: this is the square-root threshold.
  * **Contrast:** the off-line lattice pair has threshold `L/2` at every depth
    (`RHTower.offLineLattice_weil_positive_iff`).
  * The one-sided general statement is `RHTower.IsolatedDeepZeroWeilDetection`: a positive
    configuration has an off-line companion near every isolated deep zero.
* **SRT-2 · Insensitivity of averaged information** —
  [`WindowedWeilFormSliceTransfer`](WindowedWeilFormSliceTransfer.lean),
  [`WindowedPositivityNoGoForOffLineConfigurations`](WindowedPositivityNoGoForOffLineConfigurations.lean).
  * **Slice transfer law** (`windowedW_eq_integral_W`). For every tempered configuration
    (`Σ m_ρ/(1+|γ_ρ|²) < ∞`), the windowed form equals `∫ W(g_s, g_s) ds`, where
    `g_s = f(· + s) η`.
  * **Positivity transfer** (`re_windowedW_nonneg_of_aperture_nonneg`). Positivity at aperture `r`
    implies nonnegativity of every windowed Weil form whose window is supported in `[-r, r]`,
    at every aperture of the test.
  * **Depth-blindness** (`windowedW_offLineLattice_eq_onLine`). For windows in `[-L/2, L/2]`, the
    off-line lattice pair and the doubled on-line lattice have the same windowed form,
    `2L‖f‖²‖η‖²`.
  * **No-go** (`exists_offLine_lattice_windowed_nonneg`, `exists_isolatedPair_windowed_nonneg`).
    At every resolution, some configurations with off-line zeros of any prescribed depth have
    nonnegative windowed forms. This holds for dense configurations, and for a single pair in a
    dense enough background. Window-averaged positivity therefore cannot imply RH.
* **SRT-3 · Positivity in height windows** —
  [`HeightWindowAverageRepresentation`](HeightWindowAverageRepresentation.lean),
  [`ZetaSmallApertureHeightWindowPositivity`](ZetaSmallApertureHeightWindowPositivity.lean).
  * **Representation** (`windowedW_eq_integral_heightShift`). For tempered configurations,
    `windowedW Z f η = ∫ |h_η(−2πξ)|² W(S_ξ f, S_ξ f) dξ`, where `S_ξ f = e^{2πiξ·} f`.
  * **Small-aperture positivity of `ζ`** (`zetaZeroConfig_re_W_ge_of_small_support`,
    `zetaZeroConfig_re_W_nonneg_of_small_aperture`). This is a Yoshida-type theorem with a crude
    constant: `Re W_ζ(f, f) ≥ 0` for every `C²` test supported in `[−e^{−50}, e^{−50}]`.
  * **Height-window positivity of `ζ`** (`re_integral_heightShift_zetaZeroConfig_nonneg`). For
    windows in `[−e^{−50}, e^{−50}]` and tests of **every** aperture,
    `Re ∫ |h_η(−2πξ)|² W_ζ(S_ξ f, S_ξ f) dξ ≥ 0`.
  * **Calibration** (`integral_heightShift_offLineLattice_eq`). The off-line lattice pair of
    spacing `πe^{50}` has the same height averages, `4r‖f‖²‖η‖²` with `r = e^{−50}`, at every
    depth. The ζ theorem is true and carries no information on the real parts of the zeros.

### Research frontier

Proved frontier pieces are marked **[Lean]**; everything else is open.

* **SRT-4 · Off-diagonal structure.**
  * **[Lean] Exact windowed mean value** —
    [`WindowedMeanValueDiagonalLaw`](WindowedMeanValueDiagonalLaw.lean).
    For a window on `[-r, r]` and `Q(ξ) = Σ c_j e^{2πiξν_j}`:
    `∫ |h_η(−2πξ)|²|Q|² = Σ_{j,k} c_j c̄_k k_η(ν_j − ν_k)` (`integral_pairTransform_mul_normSq_expSum`).
    The identity is exactly diagonal for `2r`-separated frequencies. For Dirichlet polynomials
    of length `X`, this holds whenever `2rX ≤ 1`, that is, for windows longer than about twice
    the prime length (`integral_normSq_mul_normSq_dirichletSum`). This is the square-root
    threshold as an identity.
  * **[Lean] Variance law for `ζ`** —
    [`ZetaLocalizedFormWindowedVarianceLaw`](ZetaLocalizedFormWindowedVarianceLaw.lean).
    * `W_ζ(S_ξ f) = A_f(ξ) − Π_f(ξ)`, the archimedean part minus the prime polynomial
      (`zetaZeroConfig_W_heightShift_eq_sub`).
    * Below the threshold, the windowed mean square of `W_ζ − A_f` is exactly
      `‖η‖² V_f`, with `V_f = Σ Λ(n)²/n (|k_f(log n)|² + |k_f(−log n)|²)`
      (`integral_windowed_sq_deviation_eq`).
    * `V_f ≤ 2‖f‖⁴ · 2a(2a + C)` (`exists_primeVariance_le`).
    * Chebyshev (`lintegral_bad_heights_le_of_height`): at heights `|ξ| ≥ Ξ`, the window
      proportion of heights with `Re W_ζ(S_ξ f) < 0` is at most `V_f/A₀²`, with
      `A₀ ≈ ‖f‖² log Ξ`. So it is `O((log X/log T)²)`: most heights are positive below the
      square-root threshold.
  * **Calibration with Zeta23.** The vendored Zeta23 proof that more than two thirds of the
    zeros lie on the line is a localized-explicit-formula argument at aperture
    `L = λ log(T/2π)`, i.e. `X = (T/2π)^λ`, with `λ ≤ 1` (`Zeta23.Params.Valid.lam_le_one`).
    Its proportion `H(λ) = 2 − 1/λ − λ/3` keeps growing up to `λ = √3`. Only the prime-side
    traces stop it at `λ = 1`: beyond `X = T` they meet the off-diagonal above.
  * *Target (SRT-4c):* control the pairs `n ≠ m` with `|log(m/n)| < 2r`. With `Λ` as source these
    are prime-pair correlations, limited by parity. With mollified sources they are divisor
    shifted convolutions, which spectral and Kloosterman methods handle. A trace bound at some
    `λ > 1` would raise Zeta23's `2/3`.
* **SRT-5 · Single heights.**
  * **[Lean] Positivity above the archimedean horizon** —
    [`ZetaSingleHeightPositivityAboveArchimedeanHorizon`](ZetaSingleHeightPositivityAboveArchimedeanHorizon.lean).
    * `Re W_ζ(S_ξ f) ≥ (log(1 + π|ξ|/4) − 10 − 68√X − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`
      (`zetaZeroConfig_re_W_heightShift_ge`).
    * Every fixed profile is positive at all large heights
      (`exists_zetaZeroConfig_re_W_heightShift_nonneg`).
    * The unconditional single-height range is `X ≲ (log T/68)²`. This is the visibility range
      `X ≈ 4L²` of depth-`½` zeros, up to constants. Single-height positivity for
      `X ≲ (log T)^{1/δ}` is the localized form of a zero-free region of depth `δ`.
  * Kronecker–Bohr: short prime polynomials take every phase pattern at suitable heights. So the
    finite-prime part of a localized form reaches its trivial negative bound somewhere.
    Positivity at every height must therefore come from the coupling, through the functional
    equation, between finitely many primes and the infinite tail.
  * **[corpus] Converse visibility for `ζ`, isolated form.**
    `RHTower.re_W_modulatedTest_le_of_isolated` and `RHTower.zeta_weil_positive_forces_offLine_companion`
    (`RHTower/IsolatedDeepZeroWeilDetection`). A zero `½ + δ + iγ₀` whose neighbours within
    ordinate distance `R` lie on the line makes a localized form at height `γ₀` negative once
    `2P² > 384 A₀ log(|γ₀| + 3) N²(1 + e^a/(1 + R))`, where `P = ∫ s sinh(δ·)` grows like
    `e^{2δa}`. The isolation hypothesis cannot be dropped. Write `c` for the odd part and `s` for
    the even part of the tilted test. Each zero contributes `c² − s²`, and an off-line neighbour of
    depth `δ'` inflates its `c²` by `cosh²(δ'a)`. Near depth `δ` that is the same order `e^{2δa}`
    as the pair term itself. This is the zero-side form of the lattice no-go.
  * **[Lean] The depth-gap visibility law** —
    [`DepthGapVisibilityLaw`](DepthGapVisibilityLaw.lean). Suppose the neighbours of `ρ₀` within
    distance `R` have depth `≤ δ'`. Then
    `Re W ≤ −2m P² + 384 A₀ log(|γ₀| + 3) N² (e^{2δ'a} + e^a/(1 + R))`
    (`re_W_modulatedTest_le_of_depthGap`). So `ρ₀` is visible once
    `2(δ − δ')a ≳ log(A₀ log γ₀) + O(log a)`.
    * `δ' = 0` is the isolated law.
    * `δ' = δ` is the lattice no-go.
    * For `ζ` (`zeta_weil_positive_forces_deep_companion`): Weil positivity at aperture `a` forces
      every deep zero to have a companion within `R` of depth `> δ'`, whenever the size condition
      holds. Off-line zeros can coexist with positivity only in clusters of comparable depth.
  * *Target (SRT-5c):* state the minimal global inequality for the prime–tail coupling and
    compare it with Bagchi's recurrence criterion (route BAG).

---

## 6. Working rules

1. **Search before proving.** Run `../scripts/formal_tools.py research "<query>"`. The lattice, tilt,
   `paperFT` and explicit-formula tools already exist (Zeta23, `RHTower/ZeroLatticeDepthNyquistLaw`,
   `RHTower/WeilMarkovOddSectorTrivialZeroSquares`).
2. **Pair every invisibility theorem with a visibility witness,** and conversely. A one-sided
   statement does not locate a threshold.
3. **Calibrate.** Every new statement names its resolution or aperture and states the strongest
   unconditional value known.
4. **Lean discipline.**
   * Unconditional theorems only; `C²` compactly supported tests.
   * Configurations quantified as classes (finite, lattice, tempered) or concrete (`zetaZeroConfig`).
   * One foreground `lake --old env lean -j 1 -o …` compilation at a time.
   * Imported `#print axioms` audit from a scratch file.
   * Wire new modules into [`SquareRootThreshold.lean`](../SquareRootThreshold.lean).
