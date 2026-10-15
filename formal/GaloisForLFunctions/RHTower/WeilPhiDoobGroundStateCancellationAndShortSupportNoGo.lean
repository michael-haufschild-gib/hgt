import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.RHTower.MarkovResolventCoercivityAndEulerMaclaurinPBAP

/-!
# Doob Ground-State Cancellation (`K_M ⋆ Φ = -cosh(x/2)`), Biane–Pitman–Yor Spectral-Gap Criteria for RH, and the Short-Support No-Go for Finite-Ratio Resolvent Bounds

Building on `WeilPhiDoobPrimeAtoms` and `MarkovResolventCoercivityAndEulerMaclaurinPBAP`, this
module proves two structural theorems for Route HF / PBAP:

1. **Section 1 (Exact Short-Support Prime-Blindness on `(-log 2 / 2, log 2 / 2)` and the No-Go
   Closure for `rightCellQuadratureDefect + bochnerResolventEnergy > 0`):**
   - Any function `f : ℝ → ℝ` vanishing outside `(-log 2 / 2, log 2 / 2)` has autocorrelation
     `crossCorr f f y = 0` for all `|y| ≥ log 2` (`crossCorr_eq_zero_of_support_half_log_two`), and
     is therefore automatically prime-blind at all `n ≥ 2`:
     `primeBlindCounterterm lam (realWeilTestFn f hf hfc) = 0` for **every** weight sequence `lam`.
   - Consequently, on the primitive hyperplane `coshHalfMoment f = 0` (and in particular on all odd
     tests), the exact conservation law forces
     `rightCellQuadratureDefect (weilContinuumLogProfile F) N + bochnerResolventEnergy k_F = -2 * sinhHalfMoment f ^ 2 ≤ 0`
     (`rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_neg_two_mul_sinh_sq_of_support_half_log_two`),
     which is strictly negative (`< 0`) whenever `sinhHalfMoment f ≠ 0`. This closes the no-go on
     proving RH by pushing finite spectral-moment ratio bounds `S / L ≤ C` for
     `rightCellQuadratureDefect + bochnerResolventEnergy > 0` to `∞`: above the Dirichlet eigenvalue
     of `(-log 2 / 2, log 2 / 2)`, short-support odd tests with `sinhHalfMoment f ≠ 0` exist and
     make `rightCellQuadratureDefect + bochnerResolventEnergy` strictly negative.
   - The positive survivor for short-support tests (`markovEnergy_eq_levy_of_support_half_log_two`)
     is that `markovEnergy F` reduces identically to the pure archimedean Lévy form
     `EF.gammaBracket 0 * ∫ f² + (jumpEnergy f).toReal`.

2. **Section 2 (The Exact `Φ`-Smoothed PNT / Doob Mass Identity `K_M ⋆ Φ = -cosh(x/2)`):**
   - Using `integral_riemannKernelReal_exp_half` (`∫ Φ(x) e^{x/2} dx = 1/2`) and evenness of `Φ`,
     we prove `paperFT riemannPhiKernel (±I / 2) = 1 / 2` and evaluate the mixed pole term for any
     continuous compactly supported `H : ℝ → ℝ`:
     `weilPoleTerm (EF.weilTest riemannPhiKernel H) = (coshHalfMoment H : ℂ)`
     (`weilPoleTerm_mixed_riemannPhiKernel_eq_coshHalfMoment`).
   - Combining with `mixed_explicit_formula_riemannPhiKernel` (`weilFullFunctional Λ (Φ ⋆ H̃) = 0`),
     we obtain the unconditional **`Φ`-smoothed PNT / Doob mass identity** for every `H ∈ C²_c(ℝ)`:
     `atomPairing Λ (crossCorr riemannKernelReal H) = mixedPhiArchRe H + coshHalfMoment H`
     (`atomPairing_vonMangoldt_crossCorr_riemannKernelReal_eq_mixedPhiArchRe_add_coshHalfMoment`),
     closing the open ground-state cancellation noted in `WeilPhiDoobPrimeAtoms`.

3. **Section 3 (Termwise and Series-Level Doob Prime Jump Cancellation):**
   - For every continuous compactly supported `v : ℝ → ℝ` and `n : ℕ`, we prove that the `n`-th
     Mangoldt term of the mixed pairing `(Φ, Φ v²)` equals `∫ x, phiDoobPrimeDiagonal v n x`
     (`vonMangoldtAtom_mul_crossCorr_mixed_eq_integral_phiDoobPrimeDiagonal`), while the `n`-th
     Mangoldt term of the quadratic pairing `(Φ v, Φ v)` equals `∫ x, phiDoobPrimeCross v n x`
     (`vonMangoldtAtom_mul_crossCorr_quad_eq_integral_phiDoobPrimeCross`).
   - Subtracting the two series yields the **manifestly nonnegative** all-prime Doob jump series:
     `atomPairing Λ (crossCorr Φ (Φ v²)) - atomPairing Λ (crossCorr (Φ v) (Φ v)) = ∑' n : ℕ, ∫ x, phiDoobPrimeJump v n x ≥ 0`
     (`atomPairing_mixed_sub_quad_eq_tsum_integral_phiDoobPrimeJump`,
     `tsum_integral_phiDoobPrimeJump_nonneg`).

4. **Section 4 (Shift-by-Shift Archimedean Doob Jump Integral and the Complete Ground-State
   Decomposition of `markovEnergy (Φ v)`):**
   - Integrating `phiDoob_jump_shift_identity` over `x ∈ ℝ` at any shift `t ∈ ℝ` yields the exact
     archimedean shift decomposition (`integral_phiDoobTest_shift_sq_eq`):
     `∫ (Φv(x) - Φv(x+t))² dx = ∫ Φ(x)Φ(x+t)(v(x) - v(x+t))² dx + 2 ∫ (Φv)² - crossCorr Φ (Φv²)(t) - crossCorr Φ (Φv²)(-t)`.
   - Combining Sections 2 and 3 yields the **Exact Doob Ground-State Cancellation Identity** for
     `markovEnergy (Φ v)` (`phiDoob_markovEnergy_groundState_cancellation`):
     `markovEnergy (Φ v) = (markovArchRe k_{Φv} - mixedPhiArchRe (Φ v²)) + (∑' n, ∫ phiDoobPrimeJump v n) - phiDoobCoshMass (v²)`.

5. **Section 5 (Bijectivity of the Doob Gauge Map `v ↦ Φ v` on `C²_c(ℝ)` and Unconditional
   Doob–Biane–Pitman–Yor Poincaré Criteria for `RiemannHypothesis`):**
   - Since `riemannKernelReal x > 0` and `ContDiff ℝ 2 riemannKernelReal`, the inverse gauge map
     `phiDoobInv f x = f x / riemannKernelReal x` is a `C²_c(ℝ)` bijection preserving oddness and
     mapping `coshHalfMoment f = 0` to `phiDoobCoshMass v = 0`.
   - We establish the unconditional equivalences
     `riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg`,
     `riemannHypothesis_iff_forall_phiDoobCoshMass_zero_markovEnergy_nonneg`,
     `riemannHypothesis_iff_forall_odd_phiDoob_poincare_inequality`, and
     `riemannHypothesis_iff_forall_phiDoobCoshMass_zero_poincare_inequality`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ContDiff
open Zeta23
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Exact Short-Support Prime-Blindness on `(-log 2 / 2, log 2 / 2)` and the No-Go Closure for `rightCellQuadratureDefect + bochnerResolventEnergy > 0` -/

/-- **Short-Support Autocorrelation Vanishing Beyond `log 2`**:
if `f : ℝ → ℝ` vanishes on `|x| ≥ log 2 / 2`, then `crossCorr f f y = 0` for all `|y| ≥ log 2`. -/
theorem crossCorr_eq_zero_of_support_half_log_two {f : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, Real.log 2 / 2 ≤ |x| → f x = 0) {y : ℝ}
    (hy : Real.log 2 ≤ |y|) :
    crossCorr f f y = 0 := by
  unfold crossCorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  change f t * f (t - y) = 0
  rcases le_or_gt (Real.log 2 / 2) |t| with ht | ht
  · rw [hsupp t ht, zero_mul]
  · have hty : Real.log 2 / 2 ≤ |t - y| := by
      have htri := abs_sub_abs_le_abs_sub y t
      rw [abs_sub_comm] at htri
      linarith
    rw [hsupp (t - y) hty, mul_zero]

/-- For any `f : ℝ → ℝ` vanishing on `|x| ≥ log 2 / 2` and any `x ≥ 2`,
`EF.weilTest F F (Real.log x) = 0` and `EF.weilTest F F (-Real.log x) = 0`. -/
theorem weilTest_eq_zero_of_support_half_log_two {f : ℝ → ℝ}
    (hsupp : ∀ u : ℝ, Real.log 2 / 2 ≤ |u| → f u = 0) {x : ℝ} (hx : 2 ≤ x) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (Real.log x) = 0 ∧
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-Real.log x) = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hpos : Real.log 2 ≤ |Real.log x| := by
    rw [abs_of_pos (lt_of_lt_of_le hlog2 hlogx)]
    exact hlogx
  have hneg : Real.log 2 ≤ |-Real.log x| := by
    rw [abs_neg]
    exact hpos
  rw [weilTest_real_crossCorr_eq f f (Real.log x),
    weilTest_real_crossCorr_eq f f (-Real.log x),
    crossCorr_eq_zero_of_support_half_log_two hsupp hpos,
    crossCorr_eq_zero_of_support_half_log_two hsupp hneg,
    Complex.ofReal_zero]
  exact ⟨rfl, rfl⟩

/-- **Automatic Prime-Blindness of Short-Support Tests (`|x| < log 2 / 2`)**:
for any `f : ℝ → ℝ` vanishing on `|x| ≥ log 2 / 2`, `logValue F n = 0` for all `n ≥ 2`. -/
theorem logValue_eq_zero_of_support_half_log_two {f : ℝ → ℝ}
    (hsupp : ∀ u : ℝ, Real.log 2 / 2 ≤ |u| → f u = 0) {n : ℕ} (hn : 2 ≤ n) :
    logValue (fun u => (f u : ℂ)) n = 0 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := weilTest_eq_zero_of_support_half_log_two hsupp hnR
  unfold logValue
  rw [h1, h2, add_zero, Complex.zero_re, zero_div]

/-- For any `f ∈ C²_c(ℝ)` vanishing on `|x| ≥ log 2 / 2`, `logVector (realWeilTestFn f hf hfc) = 0`. -/
theorem logVector_eq_zero_of_support_half_log_two {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ u : ℝ, Real.log 2 / 2 ≤ |u| → f u = 0) :
    logVector (realWeilTestFn f hf hfc) = 0 := by
  ext j
  rw [Finsupp.coe_zero, Pi.zero_apply, logVector_apply]
  exact logValue_eq_zero_of_support_half_log_two hsupp j.2

/-- **Universal Counterterm Vanishing on `(-log 2 / 2, log 2 / 2)`**:
for any `f ∈ C²_c(ℝ)` vanishing on `|x| ≥ log 2 / 2` and **every** weight sequence `lam : ℕ → ℝ`,
`primeBlindCounterterm lam (realWeilTestFn f hf hfc) = 0`. -/
theorem primeBlindCounterterm_eq_zero_of_support_half_log_two (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ u : ℝ, Real.log 2 / 2 ≤ |u| → f u = 0) :
    primeBlindCounterterm lam (realWeilTestFn f hf hfc) = 0 := by
  unfold primeBlindCounterterm
  rw [logVector_eq_zero_of_support_half_log_two hf hfc hsupp, map_zero]

/-- **The Exact Short-Support No-Go Theorem for `rightCellQuadratureDefect + bochnerResolventEnergy`**:
for any `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0` (in particular any odd test)
that vanishes on `|x| ≥ log 2 / 2`, and any cutoff `2 ≤ N`, the sum of the Euler–Maclaurin
quadrature defect and the Bochner–Poisson resolvent energy is **nonpositive**:
`rightCellQuadratureDefect (weilContinuumLogProfile F) N + bochnerResolventEnergy k_F = -2 * sinhHalfMoment f ^ 2 ≤ 0`,
and is strictly negative (`< 0`) whenever `sinhHalfMoment f ≠ 0`. -/
theorem rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_neg_two_mul_sinh_sq_of_support_half_log_two
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hsupp : ∀ u : ℝ, Real.log 2 / 2 ≤ |u| → f u = 0) {N : ℕ} (hN2 : 2 ≤ N) :
    rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
        bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) =
      -(2 * sinhHalfMoment f ^ 2) := by
  have hN1 : 1 ≤ N := by omega
  have hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0 := by
    intro x hx
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    exact weilTest_eq_zero_of_support_half_log_two hsupp (by linarith)
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  rw [primeBlindCounterterm_eq_zero_of_support_half_log_two unitStepCountertermWeight hf hfc hsupp]
    at hcons
  linarith

/-- Strict negativity of `rightCellQuadratureDefect + bochnerResolventEnergy` for any short-support
primitive-hyperplane test with `sinhHalfMoment f ≠ 0`. -/
theorem rightCellQuadratureDefect_add_bochnerResolventEnergy_neg_of_support_half_log_two
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hsupp : ∀ u : ℝ, Real.log 2 / 2 ≤ |u| → f u = 0)
    (hsinh : sinhHalfMoment f ≠ 0) {N : ℕ} (hN2 : 2 ≤ N) :
    rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
        bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) < 0 := by
  rw [rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_neg_two_mul_sinh_sq_of_support_half_log_two
    hf hfc hcosh hsupp hN2]
  have hpos : 0 < sinhHalfMoment f ^ 2 := sq_pos_of_ne_zero hsinh
  linarith

/-- **Positive Survivor on `(-log 2 / 2, log 2 / 2)`**:
for any `f ∈ C²_c(ℝ)` vanishing on `|x| ≥ log 2 / 2`, the prime counterterm vanishes identically
and `markovEnergy F` equals the pure archimedean Lévy jump energy
`EF.gammaBracket 0 * ∫ f² + (jumpEnergy f).toReal`. -/
theorem markovEnergy_eq_levy_of_support_half_log_two {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ u : ℝ, Real.log 2 / 2 ≤ |u| → f u = 0) :
    markovEnergy (fun u => (f u : ℂ)) =
      EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) + (jumpEnergy f).toReal := by
  rw [markovEnergy_real_eq_levy_sub_counterterm hf hfc,
    primeBlindCounterterm_eq_zero_of_support_half_log_two _ hf hfc hsupp, sub_zero]

/-! ## Section 2: The Exact `Φ`-Smoothed PNT / Doob Mass Identity (`K_M ⋆ Φ = -cosh(x/2)`) -/

/-- The left polar exponential moment of `Φ` also has mass `1 / 2` by evenness of `Φ`. -/
theorem integral_riemannKernelReal_exp_neg_half :
    (∫ x : ℝ, riemannKernelReal x * Real.exp (-x / 2)) = 1 / 2 := by
  have heven : ∀ x : ℝ, riemannKernelReal (-x) = riemannKernelReal x := by
    intro x
    simp [riemannKernelReal]
  have h1 := integral_mul_exp_half_of_even heven
  have hcongr : (∫ x : ℝ, riemannKernelReal x * Real.exp (-x / 2)) =
      ∫ x : ℝ, riemannKernelReal x * Real.exp (-(x / 2)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [show -x / 2 = -(x / 2) by ring]
  rw [hcongr, ← h1, integral_riemannKernelReal_exp_half]

/-- `paperFT riemannPhiKernel (I / 2) = 1 / 2`. -/
theorem paperFT_riemannPhiKernel_I_div_two :
    paperFT riemannPhiKernel (I / 2) = (1 / 2 : ℂ) := by
  have hΦ : riemannPhiKernel = fun u : ℝ => (riemannKernelReal u : ℂ) :=
    funext riemannPhiKernel_eq_ofReal
  rw [hΦ, WeilLevyPole.paperFT_ofReal_I_div_two, integral_riemannKernelReal_exp_neg_half]
  push_cast
  ring

/-- `paperFT riemannPhiKernel (-I / 2) = 1 / 2`. -/
theorem paperFT_riemannPhiKernel_neg_I_div_two :
    paperFT riemannPhiKernel (-I / 2) = (1 / 2 : ℂ) := by
  have hΦ : riemannPhiKernel = fun u : ℝ => (riemannKernelReal u : ℂ) :=
    funext riemannPhiKernel_eq_ofReal
  rw [hΦ, WeilLevyPole.paperFT_ofReal_neg_I_div_two, integral_riemannKernelReal_exp_half]
  push_cast
  ring

/-- **Exact Mixed Pole Formula for Riemann's Kernel `Φ`**:
for any continuous compactly supported real test `H : ℝ → ℝ`,
`weilPoleTerm (EF.weilTest riemannPhiKernel H) = (coshHalfMoment H : ℂ)`. -/
theorem weilPoleTerm_mixed_riemannPhiKernel_eq_coshHalfMoment {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    weilPoleTerm (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ))) =
      (coshHalfMoment H : ℂ) := by
  have hHcC : HasCompactSupport (fun x : ℝ => (H x : ℂ)) :=
    hHc.comp_left Complex.ofReal_zero
  have hHC : Continuous (fun x : ℝ => (H x : ℂ)) :=
    Complex.continuous_ofReal.comp hH
  unfold weilPoleTerm
  rw [paperFT_mixed_riemannPhiKernel hHC hHcC (I / 2),
    paperFT_mixed_riemannPhiKernel hHC hHcC (-I / 2),
    show (starRingEnd ℂ) (I / 2) = -I / 2 by rw [map_div₀, Complex.conj_I, map_ofNat],
    show (starRingEnd ℂ) (-I / 2) = I / 2 by rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat],
    paperFT_riemannPhiKernel_I_div_two, paperFT_riemannPhiKernel_neg_I_div_two,
    WeilLevyPole.paperFT_ofReal_neg_I_div_two H, WeilLevyPole.paperFT_ofReal_I_div_two H,
    Complex.conj_ofReal, Complex.conj_ofReal]
  obtain ⟨hp, hm⟩ := integral_mul_exp_half_eq_cosh_add_sinh hH hHc
  rw [hp, hm]
  push_cast
  ring

/-- Real part of `weilPoleTerm (EF.weilTest riemannPhiKernel H)` equals `coshHalfMoment H`. -/
theorem re_weilPoleTerm_mixed_riemannPhiKernel_eq_coshHalfMoment {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    (weilPoleTerm (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ)))).re =
      coshHalfMoment H := by
  rw [weilPoleTerm_mixed_riemannPhiKernel_eq_coshHalfMoment hH hHc, Complex.ofReal_re]

/-- For the Doob diagonal test `H = Φ v²`, the mixed pole term equals `phiDoobCoshMass (fun x => v x ^ 2)`. -/
theorem re_weilPoleTerm_mixed_phiDoob_sq_eq_phiDoobCoshMass {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (weilPoleTerm (EF.weilTest riemannPhiKernel
      (fun x => (phiDoobTest (fun y => v y ^ 2) x : ℂ)))).re =
      phiDoobCoshMass (fun x => v x ^ 2) := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  exact re_weilPoleTerm_mixed_riemannPhiKernel_eq_coshHalfMoment
    (continuous_riemannKernelReal.mul (hv.pow 2)) (hasCompactSupport_phiDoobTest hv2c)

/-- The mixed archimedean Gamma integral pairing `Φ` with a real test `H : ℝ → ℝ`:
`mixedPhiArchRe H = Re ((1 / (2 * π)) ∫ paperFT (EF.weilTest Φ H) r * gammaBracket r dr)`. -/
def mixedPhiArchRe (H : ℝ → ℝ) : ℝ :=
  ((1 / (2 * π) : ℂ) * ∫ r : ℝ,
    paperFT (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ))) r *
      (EF.gammaBracket r : ℂ)).re

/-- **The Exact `Φ`-Smoothed PNT / Doob Mass Identity (`K_M ⋆ Φ = -cosh(x/2)`)**:
for every real test `H ∈ C²_c(ℝ)`, the noncompact mixed explicit formula `weilFullFunctional Λ (Φ ⋆ H̃) = 0`
gives the exact identity
`atomPairing Λ (crossCorr riemannKernelReal H) = mixedPhiArchRe H + coshHalfMoment H`. -/
theorem atomPairing_vonMangoldt_crossCorr_riemannKernelReal_eq_mixedPhiArchRe_add_coshHalfMoment
    {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr riemannKernelReal H) =
      mixedPhiArchRe H + coshHalfMoment H := by
  have hzero : (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ)))).re = 0 := by
    rw [mixed_explicit_formula_riemannPhiKernel hH hHc, Complex.zero_re]
  unfold weilFullFunctional at hzero
  have hΦ : riemannPhiKernel = fun x : ℝ => (riemannKernelReal x : ℂ) :=
    funext riemannPhiKernel_eq_ofReal
  have hprime : (∑' n : ℕ,
      ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) *
        (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ)) (Real.log n) +
         EF.weilTest riemannPhiKernel (fun x => (H x : ℂ)) (-Real.log n))) =
      (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr riemannKernelReal H) : ℂ) := by
    rw [hΦ]
    exact vonMangoldtPrimeSum_real_crossCorr riemannKernelReal H
  have hpole : paperFT (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ))) (I / 2) +
      paperFT (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ))) (-I / 2) =
      (coshHalfMoment H : ℂ) :=
    weilPoleTerm_mixed_riemannPhiKernel_eq_coshHalfMoment hH.continuous hHc
  rw [hpole, hprime] at hzero
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hzero
  unfold mixedPhiArchRe
  linarith

/-- Integral form of the `Φ`-smoothed PNT / Doob mass identity against `weightKernelTransform Λ`:
`∫ x, H x * weightKernelTransform Λ x = mixedPhiArchRe H + coshHalfMoment H`. -/
theorem integral_mul_weightKernelTransform_vonMangoldt_eq_mixedPhiArchRe_add_coshHalfMoment
    {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    (∫ x : ℝ, H x *
        weightKernelTransform (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) x) =
      mixedPhiArchRe H + coshHalfMoment H := by
  rw [← atomPairing_riemannKernel_eq_integral summable_vonMangoldt_abs_div_sq hH.continuous hHc]
  exact atomPairing_vonMangoldt_crossCorr_riemannKernelReal_eq_mixedPhiArchRe_add_coshHalfMoment
    hH hHc

/-- Specialization of the `Φ`-smoothed PNT / Doob mass identity to the Doob diagonal test `H = Φ v²`:
`atomPairing Λ (crossCorr Φ (Φ v²)) = mixedPhiArchRe (Φ v²) + phiDoobCoshMass (v²)`. -/
theorem phiDoob_mixed_prime_pairing_eq_mixedPhiArchRe_add_phiDoobCoshMass {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2))) =
      mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2)) +
        phiDoobCoshMass (fun x => v x ^ 2) := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  exact atomPairing_vonMangoldt_crossCorr_riemannKernelReal_eq_mixedPhiArchRe_add_coshHalfMoment
    (contDiff_phiDoobTest (hv.pow 2)) (hasCompactSupport_phiDoobTest hv2c)

/-! ## Section 3: Termwise and Series-Level Doob Prime Jump Cancellation -/

/-- **Termwise Mixed Prime Identity (`phiDoobPrimeDiagonal`)**:
for any continuous compactly supported `v : ℝ → ℝ` and `n : ℕ`, the `n`-th prime summand in
`atomPairing Λ (crossCorr Φ (Φ v²))` equals `∫ x, phiDoobPrimeDiagonal v n x`. -/
theorem vonMangoldtAtom_mul_crossCorr_mixed_eq_integral_phiDoobPrimeDiagonal {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (n : ℕ) :
    vonMangoldtAtom n *
        (crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) (Real.log n) +
          crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) (-Real.log n)) =
      ∫ x : ℝ, phiDoobPrimeDiagonal v n x := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  have hHc : HasCompactSupport (phiDoobTest (fun x => v x ^ 2)) :=
    hasCompactSupport_phiDoobTest hv2c
  have hHcont : Continuous (phiDoobTest (fun x => v x ^ 2)) :=
    continuous_riemannKernelReal.mul (hv.pow 2)
  have h1 : crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) (Real.log n) =
      ∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + Real.log n) * v x ^ 2 := by
    unfold crossCorr
    rw [← integral_add_right_eq_self
      (fun t : ℝ => riemannKernelReal t * phiDoobTest (fun x => v x ^ 2) (t - Real.log n))
      (Real.log n)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [phiDoobTest, add_sub_cancel_right]
    ring
  have h2 : crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) (-Real.log n) =
      ∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + Real.log n) *
        v (x + Real.log n) ^ 2 := by
    unfold crossCorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [phiDoobTest, sub_neg_eq_add]
    ring
  have hi1 : Integrable (fun x : ℝ =>
      riemannKernelReal x * riemannKernelReal (x + Real.log n) * v x ^ 2) := by
    have hcont : Continuous (fun x : ℝ =>
        riemannKernelReal x * riemannKernelReal (x + Real.log n) * v x ^ 2) :=
      (continuous_riemannKernelReal.mul
        (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul (hv.pow 2)
    exact hcont.integrable_of_hasCompactSupport hv2c.mul_left
  have hi2 : Integrable (fun x : ℝ =>
      riemannKernelReal x * riemannKernelReal (x + Real.log n) * v (x + Real.log n) ^ 2) := by
    have hshift : HasCompactSupport (fun x : ℝ => v (x + Real.log n) ^ 2) := by
      have hs := hvc.comp_homeomorph (Homeomorph.addRight (Real.log n))
      rw [hasCompactSupport_iff_eventuallyEq] at hs ⊢
      filter_upwards [hs] with x hx
      change v (x + Real.log n) = 0 at hx
      simp [hx]
    have hcont : Continuous (fun x : ℝ =>
        riemannKernelReal x * riemannKernelReal (x + Real.log n) * v (x + Real.log n) ^ 2) :=
      (continuous_riemannKernelReal.mul
        (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
        ((hv.comp (continuous_id.add continuous_const)).pow 2)
    exact hcont.integrable_of_hasCompactSupport hshift.mul_left
  rw [h1, h2, ← integral_add hi1 hi2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  unfold phiDoobPrimeDiagonal
  ring

/-- **Termwise Quadratic Prime Identity (`phiDoobPrimeCross`)**:
for any `v : ℝ → ℝ` and `n : ℕ`, the `n`-th prime summand in
`atomPairing Λ (crossCorr (Φ v) (Φ v))` equals `∫ x, phiDoobPrimeCross v n x`. -/
theorem vonMangoldtAtom_mul_crossCorr_quad_eq_integral_phiDoobPrimeCross (v : ℝ → ℝ) (n : ℕ) :
    vonMangoldtAtom n *
        (crossCorr (phiDoobTest v) (phiDoobTest v) (Real.log n) +
          crossCorr (phiDoobTest v) (phiDoobTest v) (-Real.log n)) =
      ∫ x : ℝ, phiDoobPrimeCross v n x := by
  have hswap : crossCorr (phiDoobTest v) (phiDoobTest v) (Real.log n) =
      crossCorr (phiDoobTest v) (phiDoobTest v) (-Real.log n) :=
    crossCorr_swap (Real.log n)
  have hneg : crossCorr (phiDoobTest v) (phiDoobTest v) (-Real.log n) =
      ∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + Real.log n) *
        v x * v (x + Real.log n) := by
    unfold crossCorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [phiDoobTest, sub_neg_eq_add]
    ring
  rw [hswap, hneg, show vonMangoldtAtom n *
      ((∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + Real.log n) *
          v x * v (x + Real.log n)) +
        ∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + Real.log n) *
          v x * v (x + Real.log n)) =
      (2 * vonMangoldtAtom n) *
        ∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + Real.log n) *
          v x * v (x + Real.log n) by ring, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  unfold phiDoobPrimeCross
  ring

/-- Summability of the diagonal Doob prime integrals `n ↦ ∫ x, phiDoobPrimeDiagonal v n x`. -/
theorem summable_integral_phiDoobPrimeDiagonal {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    Summable (fun n : ℕ => ∫ x : ℝ, phiDoobPrimeDiagonal v n x) := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  have hs := summable_mixed_vonMangoldt_primeSeries
    (continuous_riemannKernelReal.mul (hv.pow 2)) (hasCompactSupport_phiDoobTest hv2c)
  refine hs.congr fun n => ?_
  rw [← vonMangoldtAtom_mul_crossCorr_mixed_eq_integral_phiDoobPrimeDiagonal hv hvc n]
  rfl

/-- Summability of the cross Doob prime integrals `n ↦ ∫ x, phiDoobPrimeCross v n x`. -/
theorem summable_integral_phiDoobPrimeCross {v : ℝ → ℝ}
    (_hv : Continuous v) (hvc : HasCompactSupport v) :
    Summable (fun n : ℕ => ∫ x : ℝ, phiDoobPrimeCross v n x) := by
  obtain ⟨R, _, hR⟩ := exists_vanish_of_hasCompactSupport (hasCompactSupport_phiDoobTest hvc)
  have hcorr : ∀ y : ℝ, R + R < |y| → crossCorr (phiDoobTest v) (phiDoobTest v) y = 0 :=
    fun y hy => crossCorr_eq_zero hR hR hy
  have hs := summable_atomPairing
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hcorr
  refine hs.congr fun n => ?_
  rw [← vonMangoldtAtom_mul_crossCorr_quad_eq_integral_phiDoobPrimeCross v n]
  rfl

/-- Summability of the nonnegative Doob prime jump integrals `n ↦ ∫ x, phiDoobPrimeJump v n x`. -/
theorem summable_integral_phiDoobPrimeJump {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    Summable (fun n : ℕ => ∫ x : ℝ, phiDoobPrimeJump v n x) := by
  have h1 := summable_integral_phiDoobPrimeDiagonal hv hvc
  have h2 := summable_integral_phiDoobPrimeCross hv hvc
  refine (h1.sub h2).congr fun n => ?_
  exact (integral_phiDoobPrimeJump_eq_diagonal_sub_cross hv hvc n).symm

/-- Nonnegativity of each integrated Doob prime jump `∫ x, phiDoobPrimeJump v n x ≥ 0`. -/
theorem integral_phiDoobPrimeJump_nonneg (v : ℝ → ℝ) (n : ℕ) :
    0 ≤ ∫ x : ℝ, phiDoobPrimeJump v n x :=
  integral_nonneg (phiDoobPrimeJump_nonneg v n)

/-- Nonnegativity of the infinite series of Doob prime jumps `∑' n, ∫ x, phiDoobPrimeJump v n x ≥ 0`. -/
theorem tsum_integral_phiDoobPrimeJump_nonneg (v : ℝ → ℝ) :
    0 ≤ ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x :=
  tsum_nonneg (integral_phiDoobPrimeJump_nonneg v)

/-- **Series-Level Doob Prime Jump Cancellation**:
for any continuous compactly supported `v : ℝ → ℝ`, subtracting the quadratic prime pairing of
`Φ v` from the mixed prime pairing of `(Φ, Φ v²)` equals the manifestly nonnegative infinite series
of Doob prime jump integrals:
`atomPairing Λ (crossCorr Φ (Φ v²)) - atomPairing Λ (crossCorr (Φ v) (Φ v)) = ∑' n : ℕ, ∫ x, phiDoobPrimeJump v n x`. -/
theorem atomPairing_mixed_sub_quad_eq_tsum_integral_phiDoobPrimeJump {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2))) -
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (phiDoobTest v) (phiDoobTest v)) =
      ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x := by
  have h1 : atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2))) =
      ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeDiagonal v n x := by
    unfold atomPairing
    refine tsum_congr fun n => ?_
    exact vonMangoldtAtom_mul_crossCorr_mixed_eq_integral_phiDoobPrimeDiagonal hv hvc n
  have h2 : atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (crossCorr (phiDoobTest v) (phiDoobTest v)) =
      ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeCross v n x := by
    unfold atomPairing
    refine tsum_congr fun n => ?_
    exact vonMangoldtAtom_mul_crossCorr_quad_eq_integral_phiDoobPrimeCross v n
  rw [h1, h2, ← (summable_integral_phiDoobPrimeDiagonal hv hvc).tsum_sub
    (summable_integral_phiDoobPrimeCross hv hvc)]
  refine tsum_congr fun n => ?_
  exact (integral_phiDoobPrimeJump_eq_diagonal_sub_cross hv hvc n).symm

/-! ## Section 4: Shift-by-Shift Archimedean Doob Jump Integral and the Complete Ground-State Decomposition of `markovEnergy (Φ v)` -/

/-- **Shift-by-Shift Archimedean Doob Jump Integral Identity**:
at every shift `t : ℝ` and for any continuous compactly supported `v : ℝ → ℝ`,
`∫ (Φv(x) - Φv(x+t))² dx = ∫ Φ(x)Φ(x+t)(v(x) - v(x+t))² dx + 2 ∫ (Φv(x))² dx - crossCorr Φ (Φv²)(t) - crossCorr Φ (Φv²)(-t)`. -/
theorem integral_phiDoobTest_shift_sq_eq {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (t : ℝ) :
    (∫ x : ℝ, (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2) =
      (∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2) +
        2 * (∫ x : ℝ, phiDoobTest v x ^ 2) -
        crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) t -
        crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) (-t) := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  have hvt : HasCompactSupport (fun x => v (x + t)) :=
    hvc.comp_homeomorph (Homeomorph.addRight t)
  have hdiff_c : HasCompactSupport (fun x => (v x - v (x + t)) ^ 2) := by
    have hsub : HasCompactSupport (fun x => v x - v (x + t)) := hvc.sub hvt
    rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
    filter_upwards [hsub] with x hx
    simp [hx]
  have hi_jump : Integrable (fun x : ℝ =>
      riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2) := by
    have hc : Continuous (fun x : ℝ =>
        riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2) :=
      (continuous_riemannKernelReal.mul
        (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
        ((hv.sub (hv.comp (continuous_id.add continuous_const))).pow 2)
    exact hc.integrable_of_hasCompactSupport hdiff_c.mul_left
  have hi_sq : Integrable (fun x : ℝ => phiDoobTest v x ^ 2) := by
    have hc : Continuous (fun x : ℝ => phiDoobTest v x ^ 2) :=
      (continuous_riemannKernelReal.mul hv).pow 2
    have hcs : HasCompactSupport (fun x : ℝ => phiDoobTest v x ^ 2) := by
      have hs := hasCompactSupport_phiDoobTest hvc
      rw [hasCompactSupport_iff_eventuallyEq] at hs ⊢
      filter_upwards [hs] with x hx
      simp [hx]
    exact hc.integrable_of_hasCompactSupport hcs
  have hi_c1 : Integrable (fun x : ℝ =>
      riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2) := by
    have hc : Continuous (fun x : ℝ =>
        riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2) :=
      (continuous_riemannKernelReal.mul
        (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul (hv.pow 2)
    exact hc.integrable_of_hasCompactSupport hv2c.mul_left
  have hi_c2 : Integrable (fun x : ℝ =>
      riemannKernelReal (x + t) * riemannKernelReal x * v (x + t) ^ 2) := by
    have hvt2 : HasCompactSupport (fun x => v (x + t) ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hvt ⊢
      filter_upwards [hvt] with x hx
      change v (x + t) = 0 at hx
      simp [hx]
    have hc : Continuous (fun x : ℝ =>
        riemannKernelReal (x + t) * riemannKernelReal x * v (x + t) ^ 2) :=
      ((continuous_riemannKernelReal.comp (continuous_id.add continuous_const)).mul
        continuous_riemannKernelReal).mul ((hv.comp (continuous_id.add continuous_const)).pow 2)
    exact hc.integrable_of_hasCompactSupport hvt2.mul_left
  have hi_d1 : Integrable (fun x : ℝ =>
      riemannKernelReal x * (riemannKernelReal x - riemannKernelReal (x + t)) * v x ^ 2) := by
    refine (hi_sq.sub hi_c1).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, phiDoobTest]
    ring
  have hi_sq_t : Integrable (fun x : ℝ => phiDoobTest v (x + t) ^ 2) :=
    hi_sq.comp_add_right t
  have hi_d2 : Integrable (fun x : ℝ =>
      riemannKernelReal (x + t) * (riemannKernelReal (x + t) - riemannKernelReal x) *
        v (x + t) ^ 2) := by
    refine (hi_sq_t.sub hi_c2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, phiDoobTest]
    ring
  have hsplit : (∫ x : ℝ, (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2) =
      (∫ x : ℝ, riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2) +
        (∫ x : ℝ, riemannKernelReal x * (riemannKernelReal x - riemannKernelReal (x + t)) *
          v x ^ 2) +
        (∫ x : ℝ, riemannKernelReal (x + t) * (riemannKernelReal (x + t) - riemannKernelReal x) *
          v (x + t) ^ 2) := by
    simp_rw [phiDoob_jump_shift_identity v t]
    have hadd1 := integral_add (hi_jump.add hi_d1) hi_d2
    have hadd2 := integral_add hi_jump hi_d1
    dsimp only [Pi.add_apply] at hadd1 hadd2
    rw [hadd1, hadd2]
  have hd1 : (∫ x : ℝ, riemannKernelReal x * (riemannKernelReal x - riemannKernelReal (x + t)) *
      v x ^ 2) =
      (∫ x : ℝ, phiDoobTest v x ^ 2) -
        crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) t := by
    have hcongr : (fun x : ℝ =>
        riemannKernelReal x * (riemannKernelReal x - riemannKernelReal (x + t)) * v x ^ 2) =
        fun x : ℝ => phiDoobTest v x ^ 2 -
          riemannKernelReal x * riemannKernelReal (x + t) * v x ^ 2 := by
      funext x
      dsimp only [phiDoobTest]
      ring
    rw [hcongr, integral_sub hi_sq hi_c1]
    congr 1
    unfold crossCorr
    rw [← integral_add_right_eq_self
      (fun u : ℝ => riemannKernelReal u * phiDoobTest (fun x => v x ^ 2) (u - t)) t]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [phiDoobTest, add_sub_cancel_right]
    ring
  have hd2 : (∫ x : ℝ, riemannKernelReal (x + t) *
      (riemannKernelReal (x + t) - riemannKernelReal x) * v (x + t) ^ 2) =
      (∫ x : ℝ, phiDoobTest v x ^ 2) -
        crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)) (-t) := by
    have hcongr : (fun x : ℝ =>
        riemannKernelReal (x + t) * (riemannKernelReal (x + t) - riemannKernelReal x) *
          v (x + t) ^ 2) =
        fun x : ℝ => phiDoobTest v (x + t) ^ 2 -
          riemannKernelReal (x + t) * riemannKernelReal x * v (x + t) ^ 2 := by
      funext x
      dsimp only [phiDoobTest]
      ring
    rw [hcongr, integral_sub hi_sq_t hi_c2,
      integral_add_right_eq_self (fun x : ℝ => phiDoobTest v x ^ 2) t]
    congr 1
    unfold crossCorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [phiDoobTest, sub_neg_eq_add]
    ring
  rw [hsplit, hd1, hd2]
  ring

/-- Equality between `primeBlindCounterterm lam (realWeilTestFn F hF hFc)` and
`atomPairing lam (crossCorr F F)` at `lam = Λ`. -/
theorem primeBlindCounterterm_vonMangoldt_eq_atomPairing {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (realWeilTestFn F hF hFc) =
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (crossCorr F F) := by
  have h1 := markovEnergy_eq_markovArchRe_sub_counterterm (realWeilTestFn F hF hFc)
  change markovEnergy (fun x => (F x : ℂ)) =
    markovArchRe (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ))) -
      primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (realWeilTestFn F hF hFc) at h1
  have h2 := markovEnergy_eq_arch_sub_primes_atom (fun x => (F x : ℂ))
  have hprime : (∑' n : ℕ, ((vonMangoldtAtom n : ℝ) : ℂ) *
      (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log n) +
       EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log n))) =
      (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (crossCorr F F) : ℂ) :=
    vonMangoldtPrimeSum_real_crossCorr F F
  rw [hprime, Complex.sub_re, Complex.ofReal_re, ← markovArchRe_eq_re_archIntegral] at h2
  linarith

/-- **The Exact Doob Ground-State Cancellation Identity for `markovEnergy (Φ v)`**:
for every `v ∈ C²_c(ℝ)`, subtracting the noncompact mixed explicit formula `0 = weilFullFunctional Λ (Φ ⋆ (Φ v²)̃)`
from `markovEnergy (Φ v)` converts the entire Mangoldt prime sum into the nonnegative Doob jump
series `∑' n, ∫ phiDoobPrimeJump v n` and isolates the Biane–Pitman–Yor variance weight
`-phiDoobCoshMass (fun x => v x ^ 2) = -∫ Φ(x) v(x)² cosh(x/2) dx`:
`markovEnergy (Φ v) = (markovArchRe k_{Φv} - mixedPhiArchRe (Φ v²)) + (∑' n : ℕ, ∫ x, phiDoobPrimeJump v n x) - phiDoobCoshMass (fun x => v x ^ 2)`. -/
theorem phiDoob_markovEnergy_groundState_cancellation {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      (markovArchRe (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
          (fun x => (phiDoobTest v x : ℂ))) -
        mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2))) +
        (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) -
        phiDoobCoshMass (fun x => v x ^ 2) := by
  have h1 := markovEnergy_eq_markovArchRe_sub_counterterm
    (realWeilTestFn (phiDoobTest v) (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc))
  change markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
    markovArchRe (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
      (fun x => (phiDoobTest v x : ℂ))) -
      primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (realWeilTestFn (phiDoobTest v) (contDiff_phiDoobTest hv)
          (hasCompactSupport_phiDoobTest hvc)) at h1
  rw [primeBlindCounterterm_vonMangoldt_eq_atomPairing (contDiff_phiDoobTest hv)
    (hasCompactSupport_phiDoobTest hvc)] at h1
  have h2 := phiDoob_mixed_prime_pairing_eq_mixedPhiArchRe_add_phiDoobCoshMass hv hvc
  have h3 := atomPairing_mixed_sub_quad_eq_tsum_integral_phiDoobPrimeJump hv.continuous hvc
  linarith

/-- Lévy-form version of `phiDoob_markovEnergy_groundState_cancellation`. -/
theorem phiDoob_markovEnergy_levy_groundState_cancellation {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      EF.gammaBracket 0 * (∫ x : ℝ, phiDoobTest v x ^ 2) +
        (jumpEnergy (phiDoobTest v)).toReal -
        mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2)) +
        (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) -
        phiDoobCoshMass (fun x => v x ^ 2) := by
  rw [phiDoob_markovEnergy_groundState_cancellation hv hvc,
    markovArchRe_ofReal_eq_levy (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc)]

/-! ## Section 5: Bijectivity of the Doob Gauge Map `v ↦ Φ v` on `C²_c(ℝ)` and Unconditional Doob–BPY Spectral-Gap Criteria for `RiemannHypothesis` -/

/-- The inverse Doob gauge transformation `v(x) = f(x) / Φ(x)`. -/
def phiDoobInv (f : ℝ → ℝ) (x : ℝ) : ℝ := f x / riemannKernelReal x

/-- Smoothness (`C²`) of `phiDoobInv f` for any `f ∈ C²(ℝ)`, since `riemannKernelReal x > 0`. -/
theorem contDiff_phiDoobInv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (phiDoobInv f) :=
  hf.div contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne'

/-- Compact support of `phiDoobInv f` for any compactly supported `f : ℝ → ℝ`. -/
theorem hasCompactSupport_phiDoobInv {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (phiDoobInv f) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hfc ⊢
  filter_upwards [hfc] with x hx
  simp [phiDoobInv, hx]

/-- Right inverse identity: `phiDoobTest (phiDoobInv f) = f`. -/
@[simp]
theorem phiDoobTest_phiDoobInv (f : ℝ → ℝ) (x : ℝ) :
    phiDoobTest (phiDoobInv f) x = f x := by
  unfold phiDoobTest phiDoobInv
  exact mul_div_cancel₀ (f x) (riemannKernelReal_pos x).ne'

/-- Left inverse identity: `phiDoobInv (phiDoobTest v) = v`. -/
@[simp]
theorem phiDoobInv_phiDoobTest (v : ℝ → ℝ) (x : ℝ) :
    phiDoobInv (phiDoobTest v) x = v x := by
  unfold phiDoobInv phiDoobTest
  exact mul_div_cancel_left₀ (v x) (riemannKernelReal_pos x).ne'

/-- Parity preservation of `phiDoobInv`: if `f` is odd, then `phiDoobInv f` is odd. -/
theorem phiDoobInv_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (x : ℝ) :
    phiDoobInv f (-x) = -phiDoobInv f x := by
  unfold phiDoobInv
  have heven : riemannKernelReal (-x) = riemannKernelReal x := by
    simp [riemannKernelReal]
  rw [hodd x, heven, neg_div]

/-- Primitive-hyperplane preservation of `phiDoobInv`:
`phiDoobCoshMass (phiDoobInv f) = coshHalfMoment f`. -/
@[simp]
theorem phiDoobCoshMass_phiDoobInv (f : ℝ → ℝ) :
    phiDoobCoshMass (phiDoobInv f) = coshHalfMoment f := by
  unfold phiDoobCoshMass coshHalfMoment
  simp_rw [phiDoobTest_phiDoobInv]

/-- **Unconditional Odd Doob Ground-State Criterion for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if `0 ≤ markovEnergy (Φ v)` for every odd `v ∈ C²_c(ℝ)`. -/
theorem riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
        0 ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ)) := by
  rw [riemannHypothesis_iff_forall_odd_markovEnergy_nonneg]
  constructor
  · intro h v hv hvc hodd
    exact h (phiDoobTest v) (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc)
      (phiDoobTest_odd hodd)
  · intro h f hf hfc hodd
    have h1 := h (phiDoobInv f) (contDiff_phiDoobInv hf) (hasCompactSupport_phiDoobInv hfc)
      (phiDoobInv_odd hodd)
    simpa only [phiDoobTest_phiDoobInv] using h1

/-- **Unconditional Primitive-Hyperplane Doob Ground-State Criterion for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if `0 ≤ markovEnergy (Φ v)` for every `v ∈ C²_c(ℝ)` with
`phiDoobCoshMass v = 0` (`∫ v(x) Φ(x) cosh(x/2) dx = 0`). -/
theorem riemannHypothesis_iff_forall_phiDoobCoshMass_zero_markovEnergy_nonneg :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → phiDoobCoshMass v = 0 →
        0 ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ)) := by
  rw [riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg]
  constructor
  · intro h v hv hvc hcosh
    exact h (phiDoobTest v) (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc) hcosh
  · intro h f hf hfc hcosh
    have hcosh' : phiDoobCoshMass (phiDoobInv f) = 0 := by
      rw [phiDoobCoshMass_phiDoobInv]
      exact hcosh
    have h1 := h (phiDoobInv f) (contDiff_phiDoobInv hf) (hasCompactSupport_phiDoobInv hfc) hcosh'
    simpa only [phiDoobTest_phiDoobInv] using h1

/-- **Unconditional Odd Biane–Pitman–Yor Poincaré Inequality Criterion for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if for every odd `v ∈ C²_c(ℝ)`, the Biane–Pitman–Yor second
moment `phiDoobCoshMass (fun x => v x ^ 2) = ∫ Φ(x) v(x)² cosh(x/2) dx` is bounded above by the
Doob archimedean-plus-prime jump energy. -/
theorem riemannHypothesis_iff_forall_odd_phiDoob_poincare_inequality :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
        phiDoobCoshMass (fun x => v x ^ 2) ≤
          (markovArchRe (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
              (fun x => (phiDoobTest v x : ℂ))) -
            mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2))) +
            ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x := by
  rw [riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg]
  refine forall₄_congr fun v hv hvc _ => ?_
  rw [phiDoob_markovEnergy_groundState_cancellation hv hvc]
  exact sub_nonneg

/-- **Unconditional Primitive-Hyperplane Biane–Pitman–Yor Poincaré Inequality Criterion for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if for every `v ∈ C²_c(ℝ)` with `phiDoobCoshMass v = 0`,
`phiDoobCoshMass (fun x => v x ^ 2)` is bounded above by the Doob archimedean-plus-prime jump energy. -/
theorem riemannHypothesis_iff_forall_phiDoobCoshMass_zero_poincare_inequality :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → phiDoobCoshMass v = 0 →
        phiDoobCoshMass (fun x => v x ^ 2) ≤
          (markovArchRe (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
              (fun x => (phiDoobTest v x : ℂ))) -
            mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2))) +
            ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x := by
  rw [riemannHypothesis_iff_forall_phiDoobCoshMass_zero_markovEnergy_nonneg]
  refine forall₄_congr fun v hv hvc _ => ?_
  rw [phiDoob_markovEnergy_groundState_cancellation hv hvc]
  exact sub_nonneg

end RHTower

end
