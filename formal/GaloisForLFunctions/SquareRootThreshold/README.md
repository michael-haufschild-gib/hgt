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
| Windowed Weil form | the Weil form of the product kernel `k_f · k_η`; equals the average of `W(M_t f, M_t f)` over heights with weight `|h_η(t)|²/2π` | `SquareRootThreshold.windowedW` |

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
5. **Height averaging.** Fourier inversion identifies the windowed form with the height average
   `∫ |h_η(t)|²/(2π) · W(M_t f, M_t f) dt`, where `M_t` is the modulation that shifts heights by
   `t`.

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

### Within reach

* **SRT-1 · Visibility law** —
  [`IsolatedOffLinePairVisibilityLaw`](IsolatedOffLinePairVisibilityLaw.lean). Exact threshold for
  one off-line pair of depth `δ` and ordinate `γ₀` in a doubled on-line lattice of spacing `2π/L`.
  * For `0 < a ≤ L/2`, the configuration is invisible at aperture `a` **iff**
    `sinh(2δa)/δ ≤ 2L + 2a`.
  * **Consequence:** the pair is visible below the Nyquist aperture iff `sinh(δL) > 3δL`, that is
    `δL > x₀ ≈ 2.49`. Deep zeros (`δL ≫ 1`) are visible at aperture `≈ (1/2δ) log(4δL)`.
    Shallow zeros (`δ ≲ 2.5/L`) stay invisible up to `L/2`, which is the square-root threshold.
  * **Contrast:** the off-line lattice pair has threshold `L/2` at every depth
    (`RHTower.offLineLattice_weil_positive_iff`).
* **SRT-2 · Insensitivity of averaged information** —
  [`WindowedWeilFormSliceTransfer`](WindowedWeilFormSliceTransfer.lean).
  * **Transfer law:** for every tempered configuration, positivity at aperture `r` implies
    nonnegativity of every windowed Weil form whose window is supported in `[-r, r]`, at every
    aperture of the test.
  * **No-go:** off-line lattice pairs of every depth have nonnegative windowed forms at resolution
    `L/2`. Window-averaged positivity therefore cannot imply RH.
* **SRT-3 · Positivity in height windows** —
  [`HeightWindowAverageRepresentation`](HeightWindowAverageRepresentation.lean). Identifies windowed
  forms with height averages of localized Weil forms. Applies the transfer law to every
  configuration with a proved small-aperture positivity.

### Research frontier

* **SRT-4 · Off-diagonal structure.**
  * The terms `n ≠ m` with `|log(n/m)| ≲ 1/T` are shifted sums. With `Λ` as source they are
    prime-pair correlations, limited by parity. With mollified `ζ` they are divisor shifted
    convolutions, which spectral and Kloosterman methods handle.
  * *Target:* reproduce a mollifier range `θ > ½` in the language of localized Weil forms, then
    measure how far it reaches toward single heights.
* **SRT-5 · Single heights.**
  * Kronecker–Bohr: short prime polynomials take every phase pattern at suitable heights. So the
    finite-prime part of a localized form reaches its trivial negative bound somewhere.
  * Positivity at every height must therefore come from the coupling, through the functional
    equation, between finitely many primes and the infinite tail.
  * *Target:* state the minimal global inequality expressing that coupling. Compare it with
    Bagchi's recurrence criterion (route BAG).

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
