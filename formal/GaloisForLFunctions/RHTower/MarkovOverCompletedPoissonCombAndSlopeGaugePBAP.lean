import GaloisForLFunctions.RHTower.MarkovResolventCoercivityAndEulerMaclaurinPBAP

/-!
# Over-Completed Poisson Comb and the `θ`-Slope Gauge Family on the Primitive Hyperplane and Odd Sector

This module develops the **Over-Completed Poisson Comb and `θ`-Slope Gauge Family** on Route HF /
PBAP, synthesizing `MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean`,
`WeilMarkovOddPositivity.lean`, and `WeilMarkovPrimitiveHyperplane.lean`:

1. **Section 1 (The `θ`-Slope Gauge Family `lam = θ • unitStepCountertermWeight + shiftedDefectWeight lam θ`
   and Over-Completed Unit-Step Coercivity on the Primitive Hyperplane and Odd Sector):**
   - On the full Weil cone (`weilFullFunctional`), the growing pole term `+2 C(f)²` forced the
     Poisson comb slope `θ = 1`. At `θ = 1`, the Chebyshev remainder `ψ(n) - (n - 1)` oscillates in
     sign, creating the `PrimeBlindNodeCriticality` barrier when `logValue f` changes sign.
   - On the **primitive hyperplane** `coshHalfMoment f = 0` (and in particular on all **odd tests**
     `f(-x) = -f(x)`), the growing pole mode `C(f) = 0` vanishes identically and the pole term has
     already been subtracted in `markovCountertermEnergy`.
   - For any real slope parameter `θ : ℝ`, we decompose any counterterm weight `lam : ℕ → ℝ` on
     `n ≥ 2` as `lam n = θ * unitStepCountertermWeight n + shiftedDefectWeight lam θ n`, where
     `shiftedDefectWeight lam θ n := if 2 ≤ n then lam n - θ else 0`, and define
     `vonMangoldtSlopeDefect θ := shiftedDefectWeight Λ θ`.
   - Eliminating `primeBlindCounterterm unitStepCountertermWeight f` via the universal conservation
     law `unitStep + rightCellQuadratureDefect + bochnerResolventEnergy = (weilPoleTerm).re` from
     `MarkovResolventCoercivityAndEulerMaclaurinPBAP.lean` yields the **Master `θ`-Slope Gauge
     Identity** (`markovCountertermEnergy_eq_theta_slope_rightCell`,
     `markovCountertermEnergy_ofReal_eq_theta_slope_of_cosh_zero`):
     on the primitive hyperplane `coshHalfMoment f = 0`, for EVERY `θ ∈ ℝ` and cutoff `1 ≤ N`,
     `markovCountertermEnergy lam F = (lebesgueAtomWeilFunctional k_F).re + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - primeBlindCounterterm (shiftedDefectWeight lam θ) F`.
   - Whenever `1 ≤ θ` (**over-completed Poisson comb**), all three main spectral/moment energies are
     simultaneously nonnegative:
     1. `(lebesgueAtomWeilFunctional k_F).re ≥ (1 / 100) * ∫ ‖F‖² ≥ 0`,
     2. `(θ - 1) * bochnerResolventEnergy k_F ≥ 0`,
     3. `2 * θ * sinhHalfMoment f ^ 2 ≥ 0`.

2. **Section 2 (Full Linearity, Monotonicity, and Nonpositivity Laws of `countertermIteratedPrefixSum m`
   for `shiftedDefectWeight` and `vonMangoldtSlopeDefect`):**
   - We prove full linearity (`countertermIteratedPrefixSum_zero_weight`,
     `countertermIteratedPrefixSum_add`, `countertermIteratedPrefixSum_sub`,
     `countertermIteratedPrefixSum_smul`) and `Finset.Icc 2 N` congruence and monotonicity
     (`countertermIteratedPrefixSum_congr_Icc`, `countertermIteratedPrefixSum_mono_of_Icc`,
     `countertermIteratedPrefixSum_nonneg_of_Icc`, `countertermIteratedPrefixSum_nonpos_of_Icc`) for
     the `m`-th iterated prefix sum `countertermIteratedPrefixSum m`.
   - We prove the exact `m`-th Cesàro decomposition of `shiftedDefectWeight` and
     `vonMangoldtSlopeDefect` (`countertermIteratedPrefixSum_vonMangoldtSlopeDefect_eq_sub`), with
     explicit first-order (`ψ(n) - θ(n - 1)`) and second-order (`ψ₂(n) - θ(n - 1)n / 2`) closed
     forms.
   - Using `ArithmeticFunction.vonMangoldt_le_log`, we prove that on any finite cutoff `[2, N]`,
     choosing `θ ≥ Real.log N` makes `vonMangoldtSlopeDefect θ k = Λ(k) - θ ≤ 0` for all `k ≤ N`
     (`vonMangoldtSlopeDefect_nonpos_of_log_le`), and therefore makes the `m`-th iterated prefix sum
     `countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n ≤ 0` nonpositive at **every**
     Cesàro order `m : ℕ` and every `n ≤ N`
     (`countertermIteratedPrefixSum_vonMangoldtSlopeDefect_nonpos_of_log_le`).

3. **Section 3 (The Over-Completed `θ`-Slope + `m`-th Cesàro Decomposition and Finite-Cutoff
   Discrete-Prime Sign Elimination on the Primitive Hyperplane and Odd Sector):**
   - Combining Section 1 with boundary-free `m`-th order Cesàro summation by parts yields
     `markovCountertermEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero` and
     `markovEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero`.
   - Whenever `1 ≤ θ`, `Real.log N ≤ θ`, and `0 ≤ iteratedForwardDiff m (logValue F) n` on
     `Finset.Icc 2 N`, the discrete prime sum in `markovEnergy F` is **unconditionally nonnegative**
     and drops out of the lower bound
     (`one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero`,
     `one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_odd`), reducing positivity of
     `markovEnergy F` on that test purely to the continuum Euler–Maclaurin quadrature + atom pair vs
     the triple-coercive budget.
   - We establish the resulting `θ`-slope gauge sufficiency criteria for `MarkovPositiveOdd`,
     `MarkovPositivePrimitive`, and `RiemannHypothesis`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The `θ`-Slope Gauge Family and Over-Completed Unit-Step Coercivity on the Primitive Hyperplane and Odd Sector -/

/-- The **`θ`-Shifted Defect Counterterm Weight**: for any counterterm sequence `lam : ℕ → ℝ` and
slope parameter `θ : ℝ`, `shiftedDefectWeight lam θ n` equals `lam n - θ` for `n ≥ 2` and `0` for
`n < 2`. -/
def shiftedDefectWeight (lam : ℕ → ℝ) (θ : ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then lam n - θ else 0

/-- The **`θ`-Slope Von Mangoldt Defect Weight**: `Λ(n) - θ` for `n ≥ 2` and `0` for `n < 2`.
At `θ = 1` this recovers `vonMangoldtDefectCountertermWeight`; for `θ ≥ log N` it is nonpositive on
all `n ≤ N`. -/
def vonMangoldtSlopeDefect (θ : ℝ) (n : ℕ) : ℝ :=
  shiftedDefectWeight (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) θ n

@[simp]
theorem shiftedDefectWeight_zero_nat (lam : ℕ → ℝ) (θ : ℝ) :
    shiftedDefectWeight lam θ 0 = 0 := by
  simp [shiftedDefectWeight]

@[simp]
theorem shiftedDefectWeight_one_nat (lam : ℕ → ℝ) (θ : ℝ) :
    shiftedDefectWeight lam θ 1 = 0 := by
  simp [shiftedDefectWeight]

theorem shiftedDefectWeight_of_lt_two (lam : ℕ → ℝ) (θ : ℝ) {n : ℕ} (hn : n < 2) :
    shiftedDefectWeight lam θ n = 0 := by
  unfold shiftedDefectWeight
  exact if_neg (by omega)

theorem shiftedDefectWeight_of_two_le (lam : ℕ → ℝ) (θ : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    shiftedDefectWeight lam θ n = lam n - θ := by
  unfold shiftedDefectWeight
  exact if_pos hn

@[simp]
theorem vonMangoldtSlopeDefect_zero_nat (θ : ℝ) :
    vonMangoldtSlopeDefect θ 0 = 0 := by
  simp [vonMangoldtSlopeDefect]

@[simp]
theorem vonMangoldtSlopeDefect_one_nat (θ : ℝ) :
    vonMangoldtSlopeDefect θ 1 = 0 := by
  simp [vonMangoldtSlopeDefect]

theorem vonMangoldtSlopeDefect_of_lt_two (θ : ℝ) {n : ℕ} (hn : n < 2) :
    vonMangoldtSlopeDefect θ n = 0 :=
  shiftedDefectWeight_of_lt_two _ θ hn

theorem vonMangoldtSlopeDefect_of_two_le (θ : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    vonMangoldtSlopeDefect θ n = (ArithmeticFunction.vonMangoldt n : ℝ) - θ :=
  shiftedDefectWeight_of_two_le _ θ hn

/-- At `θ = 1`, `vonMangoldtSlopeDefect 1` coincides with `vonMangoldtDefectCountertermWeight`. -/
theorem vonMangoldtSlopeDefect_one :
    vonMangoldtSlopeDefect 1 = vonMangoldtDefectCountertermWeight :=
  rfl

/-- Pointwise decomposition `lam n = θ * unitStepCountertermWeight n + shiftedDefectWeight lam θ n`
for all `n ≥ 2`. -/
theorem eq_theta_mul_unitStep_add_shiftedDefect_of_two_le (lam : ℕ → ℝ) (θ : ℝ) {n : ℕ}
    (hn : 2 ≤ n) :
    lam n = θ * unitStepCountertermWeight n + shiftedDefectWeight lam θ n := by
  unfold unitStepCountertermWeight shiftedDefectWeight
  rw [if_pos hn, if_pos hn]
  ring

/-- If `lam 0 = 0` and `lam 1 = 0`, then `lam = θ • unitStepCountertermWeight + shiftedDefectWeight lam θ`
holds pointwise for all `n : ℕ`. -/
theorem eq_theta_smul_unitStep_add_shiftedDefect_of_lt_two_zero {lam : ℕ → ℝ} (θ : ℝ)
    (h0 : ∀ k < 2, lam k = 0) :
    lam = θ • unitStepCountertermWeight + shiftedDefectWeight lam θ := by
  funext n
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hn : 2 ≤ n
  · exact eq_theta_mul_unitStep_add_shiftedDefect_of_two_le lam θ hn
  · unfold unitStepCountertermWeight shiftedDefectWeight
    rw [if_neg hn, if_neg hn, h0 n (by omega)]
    ring

/-- Pointwise decomposition `Λ(n) = θ * unitStepCountertermWeight n + vonMangoldtSlopeDefect θ n`
for all `n : ℕ` and every slope `θ : ℝ`. -/
theorem vonMangoldt_eq_theta_mul_unitStep_add_slopeDefect (θ : ℝ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      θ * unitStepCountertermWeight n + vonMangoldtSlopeDefect θ n := by
  by_cases hn : 2 ≤ n
  · exact eq_theta_mul_unitStep_add_shiftedDefect_of_two_le _ θ hn
  · unfold unitStepCountertermWeight vonMangoldtSlopeDefect shiftedDefectWeight
    rw [if_neg hn, if_neg hn, vonMangoldt_eq_zero_of_lt_two (by omega)]
    ring

/-- **Exact `θ`-Slope Decomposition of `primeBlindCounterterm`**:
for every counterterm sequence `lam : ℕ → ℝ`, every slope `θ : ℝ`, and every `f : WeilTestFn`,
`primeBlindCounterterm lam f = θ * primeBlindCounterterm unitStepCountertermWeight f + primeBlindCounterterm (shiftedDefectWeight lam θ) f`. -/
theorem primeBlindCounterterm_eq_theta_mul_unitStep_add_shiftedDefect
    (lam : ℕ → ℝ) (θ : ℝ) (f : WeilTestFn) :
    primeBlindCounterterm lam f =
      θ * primeBlindCounterterm unitStepCountertermWeight f +
        primeBlindCounterterm (shiftedDefectWeight lam θ) f := by
  have hcongr : primeBlindCounterterm lam f =
      primeBlindCounterterm (θ • unitStepCountertermWeight + shiftedDefectWeight lam θ) f := by
    refine primeBlindCounterterm_congr (fun n hn => ?_) f
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact eq_theta_mul_unitStep_add_shiftedDefect_of_two_le lam θ hn
  rw [hcongr, primeBlindCounterterm_add, primeBlindCounterterm_smul]

/-- **Exact `θ`-Slope Decomposition of the Von Mangoldt Counterterm**:
for every slope `θ : ℝ` and every `f : WeilTestFn`,
`primeBlindCounterterm Λ f = θ * primeBlindCounterterm unitStepCountertermWeight f + primeBlindCounterterm (vonMangoldtSlopeDefect θ) f`. -/
theorem primeBlindCounterterm_vonMangoldt_eq_theta_mul_unitStep_add_slopeDefect
    (θ : ℝ) (f : WeilTestFn) :
    primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f =
      θ * primeBlindCounterterm unitStepCountertermWeight f +
        primeBlindCounterterm (vonMangoldtSlopeDefect θ) f :=
  primeBlindCounterterm_eq_theta_mul_unitStep_add_shiftedDefect _ θ f

/-- **Master `θ`-Slope Gauge Identity for `markovCountertermEnergy` (Right-Endpoint Form)**:
for every counterterm sequence `lam : ℕ → ℝ`, every slope `θ : ℝ`, every `f : WeilTestFn`, and
support cutoff `1 ≤ N`,
`markovCountertermEnergy lam f.1 = (lebesgueAtomWeilFunctional k_f).re + (θ - 1) * bochnerResolventEnergy k_f - θ * (weilPoleTerm k_f).re - atomPairRe k_f + θ * rightCellQuadratureDefect (weilContinuumLogProfile f.1) N - primeBlindCounterterm (shiftedDefectWeight lam θ) f`. -/
theorem markovCountertermEnergy_eq_theta_slope_rightCell
    (lam : ℕ → ℝ) (θ : ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    markovCountertermEnergy lam f.1 =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest f.1 f.1) -
        θ * (weilPoleTerm (EF.weilTest f.1 f.1)).re -
        atomPairRe (EF.weilTest f.1 f.1) +
        θ * rightCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) f := by
  have h1 :=
    markovCountertermEnergy_eq_re_lebesgueAtomWeilFunctional_sub_atomPairRe_sub_bochnerResolventEnergy_sub_counterterm
      lam f
  have h2 := primeBlindCounterterm_eq_theta_mul_unitStep_add_shiftedDefect lam θ f
  have h3 := unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    f hN1 hN
  have h3θ := congrArg (fun x => θ * x) h3
  linarith

/-- **Master `θ`-Slope Gauge Identity for `markovCountertermEnergy` (Left-Endpoint Form)**:
for every counterterm sequence `lam : ℕ → ℝ`, every slope `θ : ℝ`, every `f : WeilTestFn`, and
support cutoff `1 ≤ N`,
`markovCountertermEnergy lam f.1 = (lebesgueAtomWeilFunctional k_f).re + (θ - 1) * bochnerResolventEnergy k_f - θ * (weilPoleTerm k_f).re - atomPairRe k_f + θ * leftCellQuadratureDefect (weilContinuumLogProfile f.1) N - primeBlindCounterterm (shiftedDefectWeight lam θ) f`. -/
theorem markovCountertermEnergy_eq_theta_slope_leftCell
    (lam : ℕ → ℝ) (θ : ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    markovCountertermEnergy lam f.1 =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest f.1 f.1) -
        θ * (weilPoleTerm (EF.weilTest f.1 f.1)).re -
        atomPairRe (EF.weilTest f.1 f.1) +
        θ * leftCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) f := by
  have h1 :=
    markovCountertermEnergy_eq_re_lebesgueAtomWeilFunctional_sub_atomPairRe_sub_bochnerResolventEnergy_sub_counterterm
      lam f
  have h2 := primeBlindCounterterm_eq_theta_mul_unitStep_add_shiftedDefect lam θ f
  have h3 := unitStep_add_leftCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    f hN1 hN
  have h3θ := congrArg (fun x => θ * x) h3
  linarith

/-- **Master `θ`-Slope Gauge Identity for `markovCountertermEnergy` (Trapezoidal Form)**:
for every counterterm sequence `lam : ℕ → ℝ`, every slope `θ : ℝ`, every `f : WeilTestFn`, and
support cutoff `1 ≤ N`,
`markovCountertermEnergy lam f.1 = (lebesgueAtomWeilFunctional k_f).re + (θ - 1) * bochnerResolventEnergy k_f - θ * (weilPoleTerm k_f).re - atomPairRe k_f + θ * trapezoidalCellQuadratureDefect (weilContinuumLogProfile f.1) N - primeBlindCounterterm (shiftedDefectWeight lam θ) f`. -/
theorem markovCountertermEnergy_eq_theta_slope_trapezoidalCell
    (lam : ℕ → ℝ) (θ : ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    markovCountertermEnergy lam f.1 =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest f.1 f.1) -
        θ * (weilPoleTerm (EF.weilTest f.1 f.1)).re -
        atomPairRe (EF.weilTest f.1 f.1) +
        θ * trapezoidalCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) f := by
  have h1 :=
    markovCountertermEnergy_eq_re_lebesgueAtomWeilFunctional_sub_atomPairRe_sub_bochnerResolventEnergy_sub_counterterm
      lam f
  have h2 := primeBlindCounterterm_eq_theta_mul_unitStep_add_shiftedDefect lam θ f
  have h3 :=
    unitStep_add_trapezoidalCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
      f hN1 hN
  have h3θ := congrArg (fun x => θ * x) h3
  linarith

/-- **Real-Test `θ`-Slope Gauge Identity with Rank-2 `(1, 1)` Pole Moments**:
for every real test `f ∈ C²_c(ℝ)`, counterterm sequence `lam : ℕ → ℝ`, slope `θ : ℝ`, and support
cutoff `1 ≤ N`,
`markovCountertermEnergy lam F = (lebesgueAtomWeilFunctional k_F).re + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - 2 * θ * coshHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - primeBlindCounterterm (shiftedDefectWeight lam θ) F`. -/
theorem markovCountertermEnergy_ofReal_eq_theta_slope_rightCell
    (lam : ℕ → ℝ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 =
      (lebesgueAtomWeilFunctional (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        2 * θ * coshHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) (realWeilTestFn f hf hfc) := by
  have h := markovCountertermEnergy_eq_theta_slope_rightCell lam θ (realWeilTestFn f hf hfc) hN1 hN
  have hpole : (weilPoleTerm (EF.weilTest (realWeilTestFn f hf hfc).1
      (realWeilTestFn f hf hfc).1)).re =
      2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 :=
    re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf.continuous hfc
  rw [hpole] at h
  linarith

/-- **Over-Completed `θ`-Slope Gauge Identity on the Primitive Hyperplane (`coshHalfMoment f = 0`)**:
for every real test `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0`, every
counterterm `lam : ℕ → ℝ`, every slope `θ : ℝ`, and support cutoff `1 ≤ N`, the negative `-2 θ C(f)²`
term vanishes identically, leaving three positive-definite energies for `θ ≥ 1`:
`markovCountertermEnergy lam F = (lebesgueAtomWeilFunctional k_F).re + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - primeBlindCounterterm (shiftedDefectWeight lam θ) F`. -/
theorem markovCountertermEnergy_ofReal_eq_theta_slope_of_cosh_zero
    (lam : ℕ → ℝ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 =
      (lebesgueAtomWeilFunctional (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) (realWeilTestFn f hf hfc) := by
  have h := markovCountertermEnergy_ofReal_eq_theta_slope_rightCell lam θ hf hfc hN1 hN
  rw [hcosh] at h
  linarith

/-- **Over-Completed `θ`-Slope Gauge Identity on the Odd Sector (`∀ x, f (-x) = -f x`)**:
for every odd real test `f ∈ C²_c(ℝ)`, every counterterm `lam : ℕ → ℝ`, every slope `θ : ℝ`, and
support cutoff `1 ≤ N`,
`markovCountertermEnergy lam F = (lebesgueAtomWeilFunctional k_F).re + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - primeBlindCounterterm (shiftedDefectWeight lam θ) F`. -/
theorem markovCountertermEnergy_ofReal_eq_theta_slope_of_odd
    (lam : ℕ → ℝ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 =
      (lebesgueAtomWeilFunctional (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) (realWeilTestFn f hf hfc) :=
  markovCountertermEnergy_ofReal_eq_theta_slope_of_cosh_zero
    lam θ hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hN1 hN

/-- **Over-Completed `θ`-Slope Gauge Identity on the Even Primitive Sector (`EvenPrimitiveWeilTestFn`)**:
for every `f : EvenPrimitiveWeilTestFn`, every counterterm `lam : ℕ → ℝ`, every slope `θ : ℝ`, and
support cutoff `1 ≤ N`, both half-moments vanish, so
`markovCountertermEnergy lam f = (lebesgueAtomWeilFunctional k_f).re + (θ - 1) * bochnerResolventEnergy k_f - atomPairRe k_f + θ * rightCellQuadratureDefect (weilContinuumLogProfile f) N - primeBlindCounterterm (shiftedDefectWeight lam θ) f`. -/
theorem EvenPrimitiveWeilTestFn.markovCountertermEnergy_eq_theta_slope
    (lam : ℕ → ℝ) (θ : ℝ) (f : EvenPrimitiveWeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1 (Real.log x) = 0 ∧
        EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1 (-Real.log x) = 0) :
    markovCountertermEnergy lam f.toWeilTestFn.1 =
      (lebesgueAtomWeilFunctional (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1) -
        atomPairRe (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1) +
        θ * rightCellQuadratureDefect (weilContinuumLogProfile f.toWeilTestFn.1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) f.toWeilTestFn := by
  have h := markovCountertermEnergy_eq_theta_slope_rightCell lam θ f.toWeilTestFn hN1 hN
  rw [f.re_weilPoleTerm_eq_zero, mul_zero, sub_zero] at h
  exact h

/-- **Triple-Coercive `θ`-Slope Lower Bound on the Primitive Hyperplane (`coshHalfMoment f = 0`)**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, every counterterm `lam : ℕ → ℝ`,
every slope `θ : ℝ`, and support cutoff `1 ≤ N`,
`(1 / 100) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - primeBlindCounterterm (shiftedDefectWeight lam θ) F ≤ markovCountertermEnergy lam F`. -/
theorem one_hundredth_l2_add_resolvent_add_sinh_sq_add_theta_slope_le_markovCountertermEnergy_of_cosh_zero
    (lam : ℕ → ℝ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) (realWeilTestFn f hf hfc) ≤
      markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have hcoerc := lebesgueAtomWeilFunctional_coercive
    (realWeilTestFn f hf hfc).2.1 (realWeilTestFn f hf hfc).2.2
  have heq := markovCountertermEnergy_ofReal_eq_theta_slope_of_cosh_zero
    lam θ hf hfc hcosh hN1 hN
  linarith

/-- **Over-Completed (`1 ≤ θ`) Pure `L²`-Coercive Lower Bound on the Primitive Hyperplane**:
when `1 ≤ θ`, both `(θ - 1) * bochnerResolventEnergy k_F ≥ 0` and `2 * θ * sinhHalfMoment f ^ 2 ≥ 0`
are nonnegative, so for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` and cutoff `1 ≤ N`,
`(1 / 100) * ∫ ‖F‖² - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - primeBlindCounterterm (shiftedDefectWeight lam θ) F ≤ markovCountertermEnergy lam F`. -/
theorem one_hundredth_l2_add_theta_slope_le_markovCountertermEnergy_of_cosh_zero
    (lam : ℕ → ℝ) {θ : ℝ} (hθ : 1 ≤ θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        primeBlindCounterterm (shiftedDefectWeight lam θ) (realWeilTestFn f hf hfc) ≤
      markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have hbase :=
    one_hundredth_l2_add_resolvent_add_sinh_sq_add_theta_slope_le_markovCountertermEnergy_of_cosh_zero
      lam θ hf hfc hcosh hN1 hN
  have hres_nonneg : 0 ≤ (θ - 1) * bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc))
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-! ## Section 2: Full Linearity, Monotonicity, and Nonpositivity Laws of `countertermIteratedPrefixSum m` for `shiftedDefectWeight` and `vonMangoldtSlopeDefect` -/

@[simp]
theorem countertermPrefixSum_zero_weight (n : ℕ) :
    countertermPrefixSum 0 n = 0 := by
  simp [countertermPrefixSum]

theorem countertermPrefixSum_smul (a : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    countertermPrefixSum (a • lam) n = a * countertermPrefixSum lam n := by
  unfold countertermPrefixSum
  simp [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]

@[simp]
theorem countertermIteratedPrefixSum_zero_weight (m n : ℕ) :
    countertermIteratedPrefixSum m 0 n = 0 := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    unfold countertermIteratedPrefixSum
    have hfun : countertermIteratedPrefixSum m 0 = 0 := funext ih
    rw [hfun, countertermPrefixSum_zero_weight]

@[simp]
theorem countertermIteratedPrefixSum_zero_nat (m : ℕ) (lam : ℕ → ℝ) ( him : 1 ≤ m) :
    countertermIteratedPrefixSum m lam 0 = 0 := by
  cases m with
  | zero => omega
  | succ m => exact countertermPrefixSum_zero _

@[simp]
theorem countertermIteratedPrefixSum_one_nat (m : ℕ) (lam : ℕ → ℝ) (him : 1 ≤ m) :
    countertermIteratedPrefixSum m lam 1 = 0 := by
  cases m with
  | zero => omega
  | succ m => exact countertermPrefixSum_one _

theorem countertermIteratedPrefixSum_add (m : ℕ) (lam₁ lam₂ : ℕ → ℝ) (n : ℕ) :
    countertermIteratedPrefixSum m (lam₁ + lam₂) n =
      countertermIteratedPrefixSum m lam₁ n + countertermIteratedPrefixSum m lam₂ n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    unfold countertermIteratedPrefixSum
    have hfun : countertermIteratedPrefixSum m (lam₁ + lam₂) =
        countertermIteratedPrefixSum m lam₁ + countertermIteratedPrefixSum m lam₂ :=
      funext ih
    rw [hfun, countertermPrefixSum_add]

theorem countertermIteratedPrefixSum_sub (m : ℕ) (lam₁ lam₂ : ℕ → ℝ) (n : ℕ) :
    countertermIteratedPrefixSum m (lam₁ - lam₂) n =
      countertermIteratedPrefixSum m lam₁ n - countertermIteratedPrefixSum m lam₂ n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    unfold countertermIteratedPrefixSum
    have hfun : countertermIteratedPrefixSum m (lam₁ - lam₂) =
        countertermIteratedPrefixSum m lam₁ - countertermIteratedPrefixSum m lam₂ :=
      funext ih
    rw [hfun, countertermPrefixSum_sub]

theorem countertermIteratedPrefixSum_smul (m : ℕ) (a : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    countertermIteratedPrefixSum m (a • lam) n =
      a * countertermIteratedPrefixSum m lam n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    unfold countertermIteratedPrefixSum
    have hfun : countertermIteratedPrefixSum m (a • lam) =
        a • countertermIteratedPrefixSum m lam :=
      funext ih
    rw [hfun, countertermPrefixSum_smul]

/-- **Decomposition of `countertermIteratedPrefixSum m (shiftedDefectWeight lam θ)`**:
if `lam 0 = 0` and `lam 1 = 0`, then at every Cesàro order `m : ℕ` and every `n : ℕ`,
`countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n = countertermIteratedPrefixSum m lam n - θ * countertermIteratedPrefixSum m unitStepCountertermWeight n`. -/
theorem countertermIteratedPrefixSum_shiftedDefectWeight_eq_sub
    (m : ℕ) {lam : ℕ → ℝ} (θ : ℝ) (h0 : ∀ k < 2, lam k = 0) (n : ℕ) :
    countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n =
      countertermIteratedPrefixSum m lam n -
        θ * countertermIteratedPrefixSum m unitStepCountertermWeight n := by
  have hfun : shiftedDefectWeight lam θ = lam - θ • unitStepCountertermWeight := by
    funext k
    have hk := congrFun (eq_theta_smul_unitStep_add_shiftedDefect_of_lt_two_zero θ h0) k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    linarith
  rw [hfun, countertermIteratedPrefixSum_sub, countertermIteratedPrefixSum_smul]

/-- **Decomposition of `countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ)`**:
at every Cesàro order `m : ℕ` and every `n : ℕ`,
`countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n = countertermIteratedPrefixSum m Λ n - θ * countertermIteratedPrefixSum m unitStepCountertermWeight n`. -/
theorem countertermIteratedPrefixSum_vonMangoldtSlopeDefect_eq_sub
    (m : ℕ) (θ : ℝ) (n : ℕ) :
    countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n =
      countertermIteratedPrefixSum m (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) n -
        θ * countertermIteratedPrefixSum m unitStepCountertermWeight n :=
  countertermIteratedPrefixSum_shiftedDefectWeight_eq_sub m θ
    (fun _ hk => vonMangoldt_eq_zero_of_lt_two hk) n

/-- First-order prefix sum of `vonMangoldtSlopeDefect θ`: for all `n ≥ 1`,
`countertermPrefixSum (vonMangoldtSlopeDefect θ) n = countertermPrefixSum Λ n - θ * (n - 1)`. -/
theorem countertermPrefixSum_vonMangoldtSlopeDefect_of_one_le (θ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    countertermPrefixSum (vonMangoldtSlopeDefect θ) n =
      countertermPrefixSum (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) n -
        θ * ((n : ℝ) - 1) := by
  have h := countertermIteratedPrefixSum_vonMangoldtSlopeDefect_eq_sub 1 θ n
  dsimp [countertermIteratedPrefixSum] at h
  rw [h, countertermPrefixSum_unitStep_of_one_le hn]

/-- Second-order (Cesàro) sum of `vonMangoldtSlopeDefect θ`: for all `n ≥ 1`,
`countertermCesaroSum (vonMangoldtSlopeDefect θ) n = countertermCesaroSum Λ n - θ * ((n - 1) * n / 2)`. -/
theorem countertermCesaroSum_vonMangoldtSlopeDefect_of_one_le (θ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    countertermCesaroSum (vonMangoldtSlopeDefect θ) n =
      countertermCesaroSum (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) n -
        θ * (((n : ℝ) - 1) * (n : ℝ) / 2) := by
  have h := countertermIteratedPrefixSum_vonMangoldtSlopeDefect_eq_sub 2 θ n
  change countertermCesaroSum (vonMangoldtSlopeDefect θ) n =
    countertermCesaroSum (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) n -
      θ * countertermCesaroSum unitStepCountertermWeight n at h
  rw [h, countertermCesaroSum_unitStep_of_one_le hn]

/-- **Monotonicity of `countertermIteratedPrefixSum m` on `Finset.Icc 2 N`**:
if `lam₁ k ≤ lam₂ k` for all `k ∈ Finset.Icc 2 N`, then
`countertermIteratedPrefixSum m lam₁ n ≤ countertermIteratedPrefixSum m lam₂ n` for every order
`m : ℕ` and every `n ∈ Finset.Icc 2 N`. -/
theorem countertermIteratedPrefixSum_mono_of_Icc (m : ℕ) {lam₁ lam₂ : ℕ → ℝ} {N : ℕ}
    (h : ∀ k ∈ Finset.Icc 2 N, lam₁ k ≤ lam₂ k) :
    ∀ n ∈ Finset.Icc 2 N,
      countertermIteratedPrefixSum m lam₁ n ≤ countertermIteratedPrefixSum m lam₂ n := by
  induction m with
  | zero => exact h
  | succ m ih =>
    intro n hn
    unfold countertermIteratedPrefixSum countertermPrefixSum
    have hsub : Finset.Icc 2 n ⊆ Finset.Icc 2 N :=
      Finset.Icc_subset_Icc_right (Finset.mem_Icc.mp hn).2
    exact Finset.sum_le_sum fun k hk => ih k (hsub hk)

/-- **Nonnegativity of `countertermIteratedPrefixSum m` on `Finset.Icc 2 N`**:
if `0 ≤ lam k` for all `k ∈ Finset.Icc 2 N`, then `0 ≤ countertermIteratedPrefixSum m lam n` for
every order `m : ℕ` and every `n ∈ Finset.Icc 2 N`. -/
theorem countertermIteratedPrefixSum_nonneg_of_Icc (m : ℕ) {lam : ℕ → ℝ} {N : ℕ}
    (h : ∀ k ∈ Finset.Icc 2 N, 0 ≤ lam k) {n : ℕ} (hn : n ∈ Finset.Icc 2 N) :
    0 ≤ countertermIteratedPrefixSum m lam n := by
  have hle := countertermIteratedPrefixSum_mono_of_Icc m (lam₁ := 0) (lam₂ := lam) h n hn
  rwa [countertermIteratedPrefixSum_zero_weight] at hle

/-- **Nonpositivity of `countertermIteratedPrefixSum m` on `Finset.Icc 2 N`**:
if `lam k ≤ 0` for all `k ∈ Finset.Icc 2 N`, then `countertermIteratedPrefixSum m lam n ≤ 0` for
every order `m : ℕ` and every `n ∈ Finset.Icc 2 N`. -/
theorem countertermIteratedPrefixSum_nonpos_of_Icc (m : ℕ) {lam : ℕ → ℝ} {N : ℕ}
    (h : ∀ k ∈ Finset.Icc 2 N, lam k ≤ 0) {n : ℕ} (hn : n ∈ Finset.Icc 2 N) :
    countertermIteratedPrefixSum m lam n ≤ 0 := by
  have hle := countertermIteratedPrefixSum_mono_of_Icc m (lam₁ := lam) (lam₂ := 0) h n hn
  rwa [countertermIteratedPrefixSum_zero_weight] at hle

/-- On `Finset.Icc 2 N`, the von Mangoldt function satisfies `Λ(k) ≤ log N`. -/
theorem vonMangoldt_le_log_of_mem_Icc {N k : ℕ} (hk : k ∈ Finset.Icc 2 N) :
    (ArithmeticFunction.vonMangoldt k : ℝ) ≤ Real.log N := by
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hkpos (by exact_mod_cast hkN))

/-- **Pointwise Nonpositivity of `vonMangoldtSlopeDefect θ` on `[2, N]` for `θ ≥ log N`**:
if `Real.log N ≤ θ`, then `vonMangoldtSlopeDefect θ k ≤ 0` for all `k ∈ Finset.Icc 2 N`. -/
theorem vonMangoldtSlopeDefect_nonpos_of_log_le {N : ℕ} {θ : ℝ} (hθ : Real.log N ≤ θ)
    {k : ℕ} (hk : k ∈ Finset.Icc 2 N) :
    vonMangoldtSlopeDefect θ k ≤ 0 := by
  rw [vonMangoldtSlopeDefect_of_two_le θ (Finset.mem_Icc.mp hk).1]
  linarith [vonMangoldt_le_log_of_mem_Icc hk]

/-- **Universal `m`-th Order Cesàro Nonpositivity of `vonMangoldtSlopeDefect θ` for `θ ≥ log N`**:
if `Real.log N ≤ θ`, then for **every** Cesàro order `m : ℕ` and every `n ∈ Finset.Icc 2 N`,
`countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n ≤ 0`. -/
theorem countertermIteratedPrefixSum_vonMangoldtSlopeDefect_nonpos_of_log_le
    (m : ℕ) {N : ℕ} {θ : ℝ} (hθ : Real.log N ≤ θ) {n : ℕ} (hn : n ∈ Finset.Icc 2 N) :
    countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n ≤ 0 :=
  countertermIteratedPrefixSum_nonpos_of_Icc m
    (fun _ hk => vonMangoldtSlopeDefect_nonpos_of_log_le hθ hk) hn

/-! ## Section 3: The Over-Completed `θ`-Slope + `m`-th Cesàro Decomposition and Finite-Cutoff Discrete-Prime Sign Elimination on the Primitive Hyperplane and Odd Sector -/

/-- **Master `θ`-Slope + `m`-th Cesàro Decomposition of `markovCountertermEnergy` on `WeilTestFn`**:
for every order `m : ℕ`, counterterm sequence `lam : ℕ → ℝ`, slope `θ : ℝ`, `f : WeilTestFn`, and
support cutoff `1 ≤ N`,
`markovCountertermEnergy lam f.1 = (lebesgueAtomWeilFunctional k_f).re + (θ - 1) * bochnerResolventEnergy k_f - θ * (weilPoleTerm k_f).re - atomPairRe k_f + θ * rightCellQuadratureDefect (weilContinuumLogProfile f.1) N - ∑ n ∈ Finset.Icc 2 N, countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n * iteratedForwardDiff m (logValue f.1) n`. -/
theorem markovCountertermEnergy_eq_theta_slope_sub_iteratedCesaro
    (m : ℕ) (lam : ℕ → ℝ) (θ : ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    markovCountertermEnergy lam f.1 =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest f.1 f.1) -
        θ * (weilPoleTerm (EF.weilTest f.1 f.1)).re -
        atomPairRe (EF.weilTest f.1 f.1) +
        θ * rightCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
            iteratedForwardDiff m (logValue f.1) n := by
  have h1 := markovCountertermEnergy_eq_theta_slope_rightCell lam θ f hN1 hN
  have h2 := primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff m (shiftedDefectWeight lam θ) f
    (fun n hn => hN n (by exact_mod_cast hn))
  linarith

/-- **Over-Completed `θ`-Slope + `m`-th Cesàro Decomposition on the Primitive Hyperplane**:
for every order `m : ℕ`, counterterm sequence `lam : ℕ → ℝ`, slope `θ : ℝ`, real test `f ∈ C²_c(ℝ)`
with `coshHalfMoment f = 0`, and support cutoff `1 ≤ N`,
`markovCountertermEnergy lam F = (lebesgueAtomWeilFunctional k_F).re + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - ∑ n ∈ Finset.Icc 2 N, countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n * iteratedForwardDiff m (logValue F) n`. -/
theorem markovCountertermEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero
    (m : ℕ) (lam : ℕ → ℝ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 =
      (lebesgueAtomWeilFunctional (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n := by
  have h1 := markovCountertermEnergy_ofReal_eq_theta_slope_of_cosh_zero lam θ hf hfc hcosh hN1 hN
  have h2 := primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff m (shiftedDefectWeight lam θ)
    (realWeilTestFn f hf hfc) (fun n hn => hN n (by exact_mod_cast hn))
  linarith

/-- **Over-Completed `θ`-Slope + `m`-th Cesàro Decomposition for the Canonical `markovEnergy`**:
for every order `m : ℕ`, slope `θ : ℝ`, real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, and
support cutoff `1 ≤ N`,
`markovEnergy F = (lebesgueAtomWeilFunctional k_F).re + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N - ∑ n ∈ Finset.Icc 2 N, countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n * iteratedForwardDiff m (logValue F) n`. -/
theorem markovEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero
    (m : ℕ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    markovEnergy (realWeilTestFn f hf hfc).1 =
      (lebesgueAtomWeilFunctional (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1)).re +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n := by
  rw [← markovCountertermEnergy_vonMangoldt_eq_markovEnergy]
  exact markovCountertermEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero
    m (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) θ hf hfc hcosh hN1 hN

/-- **Finite-Cutoff Discrete-Counterterm Sign Elimination on the Primitive Hyperplane**:
if `0 ≤ iteratedForwardDiff m (logValue F) n` and
`countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n ≤ 0` for all `n ∈ Finset.Icc 2 N`,
then the discrete sum is nonpositive and drops out of the lower bound:
`(1 / 100) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N ≤ markovCountertermEnergy lam F`. -/
theorem one_hundredth_l2_add_theta_slope_quadrature_le_markovCountertermEnergy_of_cosh_zero
    (m : ℕ) (lam : ℕ → ℝ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hcesaro : ∀ n ∈ Finset.Icc 2 N,
      countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n ≤ 0) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have hcoerc := lebesgueAtomWeilFunctional_coercive
    (realWeilTestFn f hf hfc).2.1 (realWeilTestFn f hf hfc).2.2
  have heq := markovCountertermEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero
    m lam θ hf hfc hcosh hN1 hN
  have hsum_nonpos :
      (∑ n ∈ Finset.Icc 2 N,
        countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
          iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) ≤ 0 :=
    Finset.sum_nonpos fun n hn => mul_nonpos_of_nonpos_of_nonneg (hcesaro n hn) (hdiff n hn)
  linarith

/-- **Unconditional Finite-Cutoff Discrete-Prime Sign Elimination for `markovEnergy` on the
Primitive Hyperplane (`Real.log N ≤ θ`)**:
for ANY real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, support cutoff `1 ≤ N`, Cesàro order
`m : ℕ` with `0 ≤ iteratedForwardDiff m (logValue F) n` on `Finset.Icc 2 N`, and slope `θ ≥ log N`,
the discrete prime sum is unconditionally nonpositive (by `Λ(k) ≤ log N ≤ θ`) and drops out:
`(1 / 100) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N ≤ markovEnergy F`. -/
theorem one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    (m : ℕ) {θ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log N ≤ θ)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
  rw [← markovCountertermEnergy_vonMangoldt_eq_markovEnergy]
  exact one_hundredth_l2_add_theta_slope_quadrature_le_markovCountertermEnergy_of_cosh_zero
    m (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) θ hf hfc hcosh hN1 hN hdiff
    (fun _ hn => countertermIteratedPrefixSum_vonMangoldtSlopeDefect_nonpos_of_log_le m hθlog hn)

/-- **Unconditional Finite-Cutoff Discrete-Prime Sign Elimination for `markovEnergy` on the Odd
Sector (`Real.log N ≤ θ`)**:
for ANY odd real test `f ∈ C²_c(ℝ)`, support cutoff `1 ≤ N`, Cesàro order `m : ℕ` with
`0 ≤ iteratedForwardDiff m (logValue F) n` on `Finset.Icc 2 N`, and slope `θ ≥ log N`,
`(1 / 100) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 - atomPairRe k_F + θ * rightCellQuadratureDefect (weilContinuumLogProfile F) N ≤ markovEnergy F`. -/
theorem one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_odd
    (m : ℕ) {θ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log N ≤ θ)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 -
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      markovEnergy (realWeilTestFn f hf hfc).1 :=
  one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hN1 hθlog hN hdiff

/-- **Pointwise `θ`-Slope Gauge Sufficiency for `0 ≤ markovCountertermEnergy` on the Primitive
Hyperplane**:
if for some cutoff `1 ≤ N`, order `m : ℕ`, and slope `θ : ℝ`, the `m`-th Cesàro sum of
`shiftedDefectWeight lam θ` plus `atomPairRe` minus `θ * rightCellQuadratureDefect` is bounded by
the triple-coercive budget `(1 / 100) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2`,
then `0 ≤ markovCountertermEnergy lam F`. -/
theorem markovCountertermEnergy_nonneg_of_theta_slope_cesaro_le_coercive_of_cosh_zero
    (m : ℕ) (lam : ℕ → ℝ) (θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdom : (∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) +
        atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) -
        θ * rightCellQuadratureDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2) :
    0 ≤ markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have hcoerc := lebesgueAtomWeilFunctional_coercive
    (realWeilTestFn f hf hfc).2.1 (realWeilTestFn f hf hfc).2.2
  have heq := markovCountertermEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero
    m lam θ hf hfc hcosh hN1 hN
  linarith

/-- **Odd-Sector `MarkovPositiveOdd` from Test-Dependent `θ`-Slope Gauge Domination**:
if for every odd real test `f ∈ C²_c(ℝ)` there exist a cutoff `1 ≤ N`, a Cesàro order `m : ℕ`, and a
slope parameter `θ : ℝ` (which may depend on `f`) satisfying the triple-coercive `θ`-slope budget,
then `MarkovPositiveOdd lam` holds. -/
theorem markovPositiveOdd_of_forall_exists_theta_slope_dom {lam : ℕ → ℝ}
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      ∃ (N : ℕ) (m : ℕ) (θ : ℝ), 1 ≤ N ∧
        (∀ x : ℝ, (N : ℝ) < x →
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
            EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1
              (-Real.log x) = 0) ∧
        (∑ n ∈ Finset.Icc 2 N,
            countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
              iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) +
          atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) -
          θ * rightCellQuadratureDefect
            (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
        (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) +
          2 * θ * sinhHalfMoment f ^ 2) :
    MarkovPositiveOdd lam := by
  intro f hf hfc hodd
  obtain ⟨N, m, θ, hN1, hN, hdom⟩ := h f hf hfc hodd
  exact markovCountertermEnergy_nonneg_of_theta_slope_cesaro_le_coercive_of_cosh_zero
    m lam θ hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hN1 hN hdom

/-- **Primitive-Hyperplane `MarkovPositivePrimitive` from Test-Dependent `θ`-Slope Gauge Domination**:
if for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` there exist a cutoff `1 ≤ N`, a
Cesàro order `m : ℕ`, and a slope parameter `θ : ℝ` satisfying the triple-coercive `θ`-slope budget,
then `MarkovPositivePrimitive lam` holds. -/
theorem markovPositivePrimitive_of_forall_exists_theta_slope_dom {lam : ℕ → ℝ}
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      coshHalfMoment f = 0 →
      ∃ (N : ℕ) (m : ℕ) (θ : ℝ), 1 ≤ N ∧
        (∀ x : ℝ, (N : ℝ) < x →
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
            EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1
              (-Real.log x) = 0) ∧
        (∑ n ∈ Finset.Icc 2 N,
            countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
              iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) +
          atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) -
          θ * rightCellQuadratureDefect
            (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
        (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) +
          2 * θ * sinhHalfMoment f ^ 2) :
    MarkovPositivePrimitive lam := by
  intro f hf hfc hcosh
  obtain ⟨N, m, θ, hN1, hN, hdom⟩ := h f hf hfc hcosh
  exact markovCountertermEnergy_nonneg_of_theta_slope_cesaro_le_coercive_of_cosh_zero
    m lam θ hf hfc hcosh hN1 hN hdom

/-- **Unconditional `RiemannHypothesis` from Test-Dependent `θ`-Slope Gauge Domination on the Odd
Sector**:
if for every odd real test `f ∈ C²_c(ℝ)` there exist a counterterm `lam : ℕ → ℝ` dominating `Λ` on
`f`, a cutoff `1 ≤ N`, a Cesàro order `m : ℕ`, and a slope `θ : ℝ` satisfying the triple-coercive
`θ`-slope budget, then `RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_odd_exists_theta_slope_dom
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      ∃ (lam : ℕ → ℝ) (N : ℕ) (m : ℕ) (θ : ℝ), 1 ≤ N ∧
        (∀ x : ℝ, (N : ℝ) < x →
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
            EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1
              (-Real.log x) = 0) ∧
        (∑ n ∈ Finset.Icc 2 N,
            countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
              iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) +
          atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) -
          θ * rightCellQuadratureDefect
            (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
        (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) +
          2 * θ * sinhHalfMoment f ^ 2 ∧
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn f hf hfc) ≤
          primeBlindCounterterm lam (realWeilTestFn f hf hfc)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_odd_exists_counterterm_markov_nonneg fun f hf hfc hodd => ?_
  obtain ⟨lam, N, m, θ, hN1, hN, hdom, hle⟩ := h f hf hfc hodd
  exact ⟨lam,
    markovCountertermEnergy_nonneg_of_theta_slope_cesaro_le_coercive_of_cosh_zero
      m lam θ hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hN1 hN hdom,
    hle⟩

end RHTower

end
