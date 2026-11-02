# Explicit Tent Gap Probe: Rational Semilocal Collapse, Logarithmic Zero-Crossing Ceiling, and Dyadic Chebyshev Lower Bound

- **ID:** `tent-gap-probe-explicit-semilocal-collapse`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Sharpening of `finite-prime-semilocal-zero-crossing-and-syndeticity` (3-formalized): its gap probe used a `ContDiffBump` source, so `gapProbeConst`, `gapProbeCoeff` and every downstream constant were inexplicit.
- **Lean modules:**
  - `GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.TentGapProbeVector`
  - `GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.FinitePrimeSetSemilocalObstruction`
- **Statement:** With `μ_S(A) = (finitePrimeSetSemilocalFamily S).energy A`, for every `S : Finset ℕ` and `A ≥ 4`: `μ_S(A) ≤ 536 (|S| + 1)² − (15/1024) e^A` (sharper: `≤ 1606/3 + 4|S| − (15/1024) e^A`). Hence `μ_S(A) < −1` for `A ≥ 2 log(|S| + 2) + 11`. If `(weightedPrimeFamily w).energy ≥ B` everywhere, then for every `κ > 1` and all large `X`: `Σ_{X < n ≤ κX} |w(n)| ≥ (min(log κ / 4, 1/16) / 16) · X`.

## Goal
Replace the inexplicit smooth bump of the gap probe by the tent `τ_a(x) = (1 − |x|/a)⁺ ∈ H¹₀((−a, a))`, making every constant an explicit rational; remove the probe's need for an exact logarithmic gap by charging the prime operator only on the window `|log n − 2L| < 2a`; read off a logarithmic ceiling and a quantitative short-interval Chebyshev bound.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof below, no open dependency
- [x] 2 → 3  formalized: `lake --old env lean` green on both modules; `#print axioms` = `[propext, Classical.choice, Quot.sound]` for `norm_sq_tentFormVector_le`, `weightedPrimeFamily_energy_le_window`, `dyadic_chebyshev_lower_bound_of_energy_bddBelow`, `dyadic_chebyshev_lower_bound_of_primeSetSemilocal_bddBelow`, `finitePrimeSetSemilocal_energy_le_linear`, `finitePrimeSetSemilocal_energy_le_rational`, `finitePrimeSetSemilocal_energy_lt_neg_one_of_ceiling_le`, `weightedPrimeFamily_energy_le_neg_exp_of_finitePrimePowers`, `finite_prime_semilocal_complete_resolution`

## Paper proof `[PROVED HERE]`

Notation: `0 < a ≤ 1/16`; `w(ξ) = ccmArchimedeanFormWeight ξ = 1 + 2(θ'(2π|ξ|) − θ'(0))`; `𝓕` the unitary Fourier transform.

**Lemma 1 (weight).** `w(ξ) ≤ 75 + ξ²/2`. — `ccmArchimedeanFormWeight_le_quadratic`
*Proof.* `θ'(0) = −(3 log 2 + γ + π/2)/2 − (log π)/2 ≥ −3` (`neg_three_le_gammaHardyPhaseRate_zero`) using `log 2 < 0.6932`, `γ < 2/3`, `π < 3.15`, `log π < log 4`. For `|ξ| ≥ 1`, `|θ'(2π|ξ|) − log|ξ|/2| ≤ 34` gives `w ≤ 75 + log|ξ| ≤ 75 + |ξ| − 1 ≤ 75 + ξ²/2`. For `|ξ| ≤ 1`, monotonicity gives `w(ξ) ≤ w(1) ≤ 75`. ∎

**Lemma 2 (tent data).** `∫τ_a = a`, `∫τ_a² = 2a/3`, `𝓕τ_a(ξ) = a sinc²(πaξ)`, `∫ e^{sx} τ_a ≥ e^{−|s|a} a`. — `integral_triangleFn_real`, `integral_triangleFn_sq`, `fourier_tentL2` (via `fourier_triangleFn`), `exp_neg_abs_mul_le_tentMoment`, `norm_sq_tentApertureVector`, `inner_ccmPolarApertureVector_tent`
*Proof.* Polynomial antiderivatives on `[−a, 0]`, `[0, a]`; `e^{sx} ≥ e^{−|s|a}` on the support. ∎

**Lemma 3 (form norm).** `τ_a` lies in the archimedean form domain at aperture `a` and `‖u_a‖² = ∫ w |𝓕τ_a|² ≤ 150a + 1/(π² a) ≤ 150a + 1/(9a)`. — `tentFormVector`, `norm_sq_tentFormVector_le`, `norm_sq_tentFormVector_le_rational`
*Proof.* With `y = πaξ`, `s = sinc²y ∈ [0, 1]`, `s y² = sin² y ≤ 1`, so `s(1 + y²) ≤ 2` and `(75 + ξ²/2) a² s² (1 + y²) ≤ 150 a² s + y² s/π² ≤ 150 a² + 1/π²` (`weight_mul_norm_sq_fourier_tent_le`). `∫ (1 + (πaξ)²)^{-1} dξ = 1/a`. Weighted `L²` membership yields the form vector (`exists_ccmArchimedeanFormDomain_of_fourier_memLp`); its norm is the weighted integral (`ccmFormDomain_ae_eq_fourier`). ∎

**Proposition 4 (windowed tent probe).** For any `w : ℕ → ℝ`, `δ > 0`, `a = min(δ, 1/16)`, `L ≥ 1/4`, `b = a + L`:
`E_w(b) ≤ 450 + 1/(3a²) − a (e^{L/2} − e^{−L/2})² + 2 Σ_{2 ≤ n ≤ e^{2b}, |log n − 2L| < 2a} |w(n)|/√n`. — `weightedPrimeFamily_energy_le_window` (`gapProbeConst`, `gapProbeCoeff`, `gapProbeWindowSum`); empty window: `weightedPrimeFamily_energy_le_of_log_gap`
*Proof.* Test vector `v = T_{−L}u_a − T_L u_a`, physical image `f`, `‖f‖² = 2F`, `F = 2a/3`; `‖v‖² ≤ 4U`, `U = ‖u_a‖²`. Scalar term `(2θ'(0) − 1)‖f‖² ≤ 0` since `2θ'(0) + 4 < 0`. Polar term `= −2 sinh-diff² · m₊m₋` with `m₊m₋ ≥ e^{−a} a² ≥ (2/3)a²`. A prime block `n` contributes `w(n) n^{−1/2} Re(⟨T_h f, f⟩ + ⟨T_{−h} f, f⟩)`, `h = log n`; the shifts `±h` and `h + 2L` exceed `2a`, so the block vanishes unless `|h − 2L| < 2a`, and in any case its modulus is `≤ |w(n)| n^{−1/2} · 2‖f‖²`. Rayleigh: `E · 2F ≤ 4U − 2 sinh-diff² m₊m₋ + 4F Σ`, and `4U ≤ 2F (450 + 1/(3a²))`. ∎

**Theorem 5 (rational semilocal collapse).** `S : Finset ℕ`, `A ≥ 4`: `μ_S(A) ≤ 1606/3 + 4|S| − (15/1024) e^A ≤ 536(|S| + 1)² − (15/1024) e^A`. — `finitePrimeSetSemilocal_energy_le_linear`, `finitePrimeSetSemilocal_energy_le_rational`
*Proof.* Proposition 4 with `δ = 1/16`, `L = A − 1/16`, `b = A`; `sinh-diff² ≥ e^L/4 ≥ (15/64) e^A`. In the window (length `1/4 < log 2`) each prime of `S` has at most one power; `n ↦ minFac n` injects the active window into `S`; `Λ(n)/√n ≤ log n/√n ≤ 2` (`gapProbeWindowSum_semilocalVonMangoldt_le`, `log_div_sqrt_le_two`). ∎

**Corollary 6 (logarithmic ceiling).** `finitePrimeZeroCrossingCeiling r = 2 log(r + 2) + 11`; `|S| ≤ r`, `A ≥ 2 log(r + 2) + 11` ⇒ `μ_S(A) < −1`. — `finitePrimeSetSemilocal_energy_lt_neg_one_of_ceiling_le`; zero crossings in `(½ log 2, 2 log(|S| + 2) + 11]`: `exists_finitePrimeSetSemilocal_zero_crossing`
*Proof.* `e^{11} > 2.7182818283^{11} > 36660` (`thirtySixThousand_lt_exp_eleven`), so `(15/1024) e^A > 537 (r + 2)² > 1606/3 + 4r + 1`. ∎

**Theorem 7 (dyadic Chebyshev lower bound).** If `E_w ≥ B` everywhere, then for `κ > 1`, `a = min(log κ/4, 1/16)`, `G = 450 + 1/(3a²)`, `M = max(0, G − B)` and `X ≥ max(e^4, (8M/a)²)`: `Σ_{n ∈ (⌊X⌋, ⌊κX⌋]} |w(n)| ≥ (a/16) X`. — `dyadic_chebyshev_lower_bound_of_energy_bddBelow`; for `Λ_P`: `dyadic_chebyshev_lower_bound_of_primeSetSemilocal_bddBelow`
*Proof.* `L = (log X)/2 + a ≥ 2`. The window `|log n − 2L| < 2a` is `X < n < e^{4a}X ≤ κX`, where `1/√n ≤ 1/√X`. With `s = √X`: `B ≤ G − a s/4 + 2T/s`, so `2T ≥ a s²/4 − M s ≥ a s²/8`. ∎

**General weights (explicit form of the earlier collapse).** `(weightedPrimeFamily w).energy A ≤ 450 + 256(5r + 2)²/3 − e^A/(512(5r + 2))` for `w` on `S`-prime powers, `|S| ≤ r`, `A ≥ 4` (`finitePrimeCollapseConst`, `finitePrimeCollapseCoeff`, `weightedPrimeFamily_energy_le_neg_exp_of_finitePrimePowers`; ceiling `weightedFinitePrimeCeiling`). The coefficient of `e^A` must decay like `1/r` along this route: a probe that avoids every prime-power shift has width `≲ 1/r`, and its polar gain is proportional to its width. The uniform coefficient `15/1024` for `Λ_S` uses the size bound `Λ(n) ≤ log n`, unavailable for arbitrary weights.

## Log
- 2026-11-02 — created in 1-in-progress with complete paper proof
- 2026-11-02 — formalized; moved to 3-formalized
