import GaloisForLFunctions.RHTower.CCMFUSuzukiConnectedThirdTangentBridge
import GaloisForLFunctions.RHTower.RiemannSiegelThresholdLaw
import GaloisForLFunctions.HTGeometry.ShiftedEulerLogChord
import GaloisForLFunctions.HTGeometry.ObservationMomentBudget

open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

def ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox
    (ω : ℝ) (n : ℕ) : ℝ :=
  16 * shiftedEulerLogChordConnectedThirdExcess ω n /
    (Real.sqrt n * Real.log n ^ (5 : ℕ))

theorem ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox_nonneg
    {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    0 ≤ ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω n := by
  exact div_nonneg (mul_nonneg (by norm_num)
    (shiftedEulerLogChordConnectedThirdExcess_nonneg hω n))
    (by positivity)

theorem ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox_pos_iff
    {ω : ℝ} (hω : 0 < ω) {n : ℕ} (hn : 2 ≤ n) :
    0 < ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω n ↔
      IsPrimePow n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hden : 0 < Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (5 : ℕ) := by
    exact mul_pos (Real.sqrt_pos.2 hnR) (pow_pos hlog 5)
  rw [ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox]
  constructor
  · intro h
    have hnum : 0 < 16 * shiftedEulerLogChordConnectedThirdExcess ω n := by
      rcases (div_pos_iff.mp h) with hpos | hneg
      · exact hpos.1
      · exact ((not_lt_of_ge hden.le) hneg.2).elim
    apply (shiftedEulerLogChordConnectedThirdExcess_pos_iff hω n).mp
    nlinarith
  · intro hnpp
    exact div_pos (mul_pos (by norm_num)
      ((shiftedEulerLogChordConnectedThirdExcess_pos_iff hω n).mpr hnpp)) hden

theorem tendsto_ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox
    (n : ℕ) :
    Tendsto (fun ω : ℝ =>
      ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω (n + 2))
      (𝓝[>] 0) (𝓝 (ccmGuinandWeilPrimeEntryThirdJetScale (n + 2))) := by
  have hbase := tendsto_shiftedEulerLogChordConnectedThirdExcess (n + 2)
  have h := (hbase.const_mul (16 : ℝ)).div_const
    (Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) ^ (5 : ℕ))
  rw [ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent n]
  have hre :
      (shiftedEulerConnectedThirdTangentArithmetic (n + 2)).re =
        2 * ArithmeticFunction.vonMangoldt (n + 2) *
          Real.log ((n + 2 : ℕ) : ℝ) ^ (2 : ℕ) := by
    rw [shiftedEulerConnectedThirdTangentArithmetic_apply]
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    norm_num
    ring
  rw [hre]
  simpa only [ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox] using h

/-- Symmetric shifted increment of the two critical principal-pole exponentials. -/
def shiftedEulerLogPrincipalPolarIncrement (ω h : ℝ) : ℝ :=
  (Real.exp ((1 / 2 + ω) * h) - Real.exp ((1 / 2 - ω) * h)) +
    (Real.exp ((-1 / 2 + ω) * h) - Real.exp ((-1 / 2 - ω) * h))

def shiftedEulerLogPolarChordDensity (ω h : ℝ) : ℝ :=
  2 * Real.cosh (h / 2) * (Real.sinh (ω * h) / (ω * h))

/-- Exact principal-pole certification of the finite polar log chord. -/
theorem shiftedEulerLogPolarChordDensity_eq_principalPolarIncrement
    {ω h : ℝ} (hω : ω ≠ 0) (hh : h ≠ 0) :
    shiftedEulerLogPolarChordDensity ω h =
      shiftedEulerLogPrincipalPolarIncrement ω h / (2 * ω * h) := by
  rw [shiftedEulerLogPolarChordDensity,
    shiftedEulerLogPrincipalPolarIncrement, Real.cosh_eq, Real.sinh_eq]
  have h1 : (1 / 2 + ω) * h = h / 2 + ω * h := by ring
  have h2 : (1 / 2 - ω) * h = h / 2 - ω * h := by ring
  have h3 : (-1 / 2 + ω) * h = -(h / 2) + ω * h := by ring
  have h4 : (-1 / 2 - ω) * h = -(h / 2) - ω * h := by ring
  rw [h1, h2, h3, h4, Real.exp_add, Real.exp_sub,
    Real.exp_add, Real.exp_sub]
  have hinv : Real.exp (h * ω) * Real.exp (-(h * ω)) = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp [hω, hh]
  calc
    Real.exp (h * ω) *
        (Real.exp (h * ω) - Real.exp (-(h * ω))) =
      Real.exp (h * ω) ^ (2 : ℕ) -
        Real.exp (h * ω) * Real.exp (-(h * ω)) := by ring
    _ = Real.exp (h * ω) ^ (2 : ℕ) - 1 := by rw [hinv]

def shiftedEulerLogPolarConnectedThirdExcess (ω h : ℝ) : ℝ :=
  12 * (shiftedEulerLogPolarChordDensity ω h - 2 * Real.cosh (h / 2)) / ω ^ (2 : ℕ)

theorem shiftedEulerLogPolarConnectedThirdExcess_eq_principalPolarIncrement
    {ω h : ℝ} (hω : ω ≠ 0) (hh : h ≠ 0) :
    shiftedEulerLogPolarConnectedThirdExcess ω h =
      12 * (shiftedEulerLogPrincipalPolarIncrement ω h / (2 * ω * h) -
        2 * Real.cosh (h / 2)) / ω ^ (2 : ℕ) := by
  rw [shiftedEulerLogPolarConnectedThirdExcess,
    shiftedEulerLogPolarChordDensity_eq_principalPolarIncrement hω hh]

/-- Universal finite-clock connected third-jet multiplier. -/
def shiftedEulerLogConnectedThirdMultiplier (ω h : ℝ) : ℝ :=
  6 * (Real.sinh (ω * h) / (ω * h) - 1) / (ω * h) ^ (2 : ℕ)

theorem shiftedEulerLogConnectedThirdMultiplier_nonneg
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    0 ≤ shiftedEulerLogConnectedThirdMultiplier ω h := by
  have hy : 0 < ω * h := mul_pos hω hh
  have hratio : 1 ≤ Real.sinh (ω * h) / (ω * h) := by
    exact (le_div_iff₀ hy).2 (by
      simpa only [one_mul] using Real.self_le_sinh_iff.mpr hy.le)
  rw [shiftedEulerLogConnectedThirdMultiplier]
  positivity

/-- The connected Suzuki multiplier dominates its tangent value. -/
theorem one_le_shiftedEulerLogConnectedThirdMultiplier
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    1 ≤ shiftedEulerLogConnectedThirdMultiplier ω h := by
  have hy : 0 < ω * h := mul_pos hω hh
  have hjet := HTGeometry.self_add_cube_div_six_le_sinh hy.le
  rw [shiftedEulerLogConnectedThirdMultiplier]
  have hy0 : ω * h ≠ 0 := hy.ne'
  field_simp [hy0]
  nlinarith

/-- The connected Suzuki multiplier never exceeds its extremal symmetric Mellin shift. -/
theorem shiftedEulerLogConnectedThirdMultiplier_le_cosh
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    shiftedEulerLogConnectedThirdMultiplier ω h ≤ Real.cosh (ω * h) := by
  have hy : 0 < ω * h := mul_pos hω hh
  have hjet := sinh_sub_self_le hy.le
  rw [shiftedEulerLogConnectedThirdMultiplier]
  have hy0 : ω * h ≠ 0 := hy.ne'
  field_simp [hy0]
  nlinarith

theorem tendsto_shiftedEulerLogConnectedThirdMultiplier {h : ℝ} (hh : h ≠ 0) :
    Tendsto (fun ω : ℝ => shiftedEulerLogConnectedThirdMultiplier ω h)
      (𝓝[>] 0) (𝓝 1) := by
  have hscale : Tendsto (fun ω : ℝ => ω * h)
      (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun ω : ℝ => ω * h) (𝓝 0) (𝓝 0) := by
        simpa using
          ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).mul_const h).tendsto
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ω hω
      exact mul_ne_zero hω.ne' hh
  have hjet := tendsto_real_sinh_sub_self_div_cube_nhdsNE_zero.comp hscale
  convert hjet.const_mul 6 using 1
  · funext ω
    rw [shiftedEulerLogConnectedThirdMultiplier]
    by_cases hy : ω * h = 0
    · simp [hy]
    · simp only [Function.comp_apply]
      have hω : ω ≠ 0 := fun h0 => hy (by simp [h0])
      field_simp [hy, hω, hh]
  · norm_num

private def shiftedEulerLogConnectedThirdMultiplierPrimitive (y t : ℝ) : ℝ :=
  3 * (((1 - t) ^ (2 : ℕ) * Real.sinh (t * y)) / y +
    (2 * (1 - t) * Real.cosh (t * y)) / y ^ (2 : ℕ) +
    (2 * Real.sinh (t * y)) / y ^ (3 : ℕ))

private theorem hasDerivAt_shiftedEulerLogConnectedThirdMultiplierPrimitive
    {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (shiftedEulerLogConnectedThirdMultiplierPrimitive y)
      (3 * (1 - t) ^ (2 : ℕ) * Real.cosh (t * y)) t := by
  have harg : HasDerivAt (fun x : ℝ => x * y) y t := by
    simpa only [Function.id_def, one_mul] using
      (hasDerivAt_id t).mul_const y
  have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (x * y))
      (Real.cosh (t * y) * y) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sinh (t * y)).comp t harg
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (x * y))
      (Real.sinh (t * y) * y) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cosh (t * y)).comp t harg
  have honeSub : HasDerivAt (fun x : ℝ => 1 - x) (-1) t :=
    (hasDerivAt_id t).const_sub 1
  have hraw := ((honeSub.pow 2).mul hsinh).div_const y |>.add
    ((honeSub.const_mul 2).mul hcosh |>.div_const (y ^ (2 : ℕ))) |>.add
      (hsinh.const_mul 2 |>.div_const (y ^ (3 : ℕ))) |>.const_mul 3
  apply hraw.congr_deriv
  simp only [Pi.pow_apply]
  field_simp [hy]
  ring

/-- The finite-clock connected multiplier is a probability mixture of symmetric Mellin shifts.
The mixing density `3(1-t)²` is positive and has total mass one. -/
theorem shiftedEulerLogConnectedThirdMultiplier_eq_coshMixture
    {ω h : ℝ} (hω : ω ≠ 0) (hh : h ≠ 0) :
    shiftedEulerLogConnectedThirdMultiplier ω h =
      ∫ t in (0 : ℝ)..1, 3 * (1 - t) ^ (2 : ℕ) * Real.cosh (t * (ω * h)) := by
  have hy : ω * h ≠ 0 := mul_ne_zero hω hh
  have hcont : Continuous (fun t : ℝ =>
      3 * (1 - t) ^ (2 : ℕ) * Real.cosh (t * (ω * h))) := by
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ =>
      hasDerivAt_shiftedEulerLogConnectedThirdMultiplierPrimitive hy t)
    (hcont.intervalIntegrable 0 1)
  have hF1 : shiftedEulerLogConnectedThirdMultiplierPrimitive (ω * h) 1 =
      6 * Real.sinh (ω * h) / (ω * h) ^ (3 : ℕ) := by
    simp [shiftedEulerLogConnectedThirdMultiplierPrimitive]
    ring
  have hF0 : shiftedEulerLogConnectedThirdMultiplierPrimitive (ω * h) 0 =
      6 / (ω * h) ^ (2 : ℕ) := by
    simp [shiftedEulerLogConnectedThirdMultiplierPrimitive]
    ring
  rw [hFTC, hF1, hF0, shiftedEulerLogConnectedThirdMultiplier]
  field_simp [hy]

theorem integral_shiftedEulerLogConnectedThirdMultiplier_mixingDensity :
    (∫ t in (0 : ℝ)..1, 3 * (1 - t) ^ (2 : ℕ)) = 1 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun x : ℝ => -(1 - x) ^ (3 : ℕ)) (3 * (1 - t) ^ (2 : ℕ)) t := by
    intro t
    have hone : HasDerivAt (fun x : ℝ => 1 - x) (-1) t :=
      (hasDerivAt_id t).const_sub 1
    exact (hone.pow 3).neg.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t : ℝ => 3 * (1 - t) ^ (2 : ℕ))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => 3 * (1 - t) ^ (2 : ℕ))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint]
  norm_num

private theorem ccmGuinandWeilPrimeEntryThirdJetScale_eq_logSource_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    ccmGuinandWeilPrimeEntryThirdJetScale n =
      16 * (2 * ArithmeticFunction.vonMangoldt n * Real.log n ^ (2 : ℕ)) /
        (Real.sqrt n * Real.log n ^ (5 : ℕ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + m = m + 2 by omega,
    ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent m,
    shiftedEulerConnectedThirdTangentArithmetic_apply]
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  norm_num
  ring

/-- Exact common-multiplier law on every arithmetic atom. -/
theorem ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox_eq_multiplier
    {ω : ℝ} (hω : ω ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω n =
      ccmGuinandWeilPrimeEntryThirdJetScale n *
        shiftedEulerLogConnectedThirdMultiplier ω (Real.log n) := by
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox,
    shiftedEulerLogChordConnectedThirdExcess,
    shiftedEulerLogChordCoefficient,
    ccmGuinandWeilPrimeEntryThirdJetScale_eq_logSource_of_two_le hn,
    shiftedEulerLogConnectedThirdMultiplier]
  field_simp [hω, hlog]
  ring

theorem shiftedEulerLogPolarChordDensity_nonneg
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    0 ≤ shiftedEulerLogPolarChordDensity ω h := by
  have hy : 0 < ω * h := mul_pos hω hh
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.cosh_pos _).le)
    (div_nonneg (Real.sinh_nonneg_iff.mpr hy.le) hy.le)

theorem shiftedEulerLogPolarConnectedThirdExcess_nonneg
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    0 ≤ shiftedEulerLogPolarConnectedThirdExcess ω h := by
  have hy : 0 < ω * h := mul_pos hω hh
  have hratio : 1 ≤ Real.sinh (ω * h) / (ω * h) := by
    exact (le_div_iff₀ hy).2 (by
      simpa only [one_mul] using Real.self_le_sinh_iff.mpr hy.le)
  rw [shiftedEulerLogPolarConnectedThirdExcess,
    shiftedEulerLogPolarChordDensity]
  have hcosh : 0 < Real.cosh (h / 2) := Real.cosh_pos _
  have hdiff : 0 ≤ 2 * Real.cosh (h / 2) *
        (Real.sinh (ω * h) / (ω * h)) - 2 * Real.cosh (h / 2) := by
    nlinarith
  positivity

theorem shiftedEulerLogPolarConnectedThirdExcess_pos
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    0 < shiftedEulerLogPolarConnectedThirdExcess ω h := by
  have hy : 0 < ω * h := mul_pos hω hh
  have hratio : 1 < Real.sinh (ω * h) / (ω * h) := by
    exact (lt_div_iff₀ hy).2 (by
      simpa only [one_mul] using Real.self_lt_sinh_iff.mpr hy)
  rw [shiftedEulerLogPolarConnectedThirdExcess,
    shiftedEulerLogPolarChordDensity]
  have hcosh : 0 < Real.cosh (h / 2) := Real.cosh_pos _
  have hdiff : 0 < 2 * Real.cosh (h / 2) *
        (Real.sinh (ω * h) / (ω * h)) - 2 * Real.cosh (h / 2) := by
    nlinarith
  positivity

theorem tendsto_shiftedEulerLogPolarConnectedThirdExcess {h : ℝ} (hh : h ≠ 0) :
    Tendsto (fun ω : ℝ => shiftedEulerLogPolarConnectedThirdExcess ω h)
      (𝓝[>] 0) (𝓝 (4 * Real.cosh (h / 2) * h ^ (2 : ℕ))) := by
  have hscale : Tendsto (fun ω : ℝ => ω * h)
        (𝓝[>] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : Tendsto (fun ω : ℝ => ω * h) (𝓝 0) (𝓝 0) := by
          simpa using
            ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).mul_const h).tendsto
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ω hω
        exact mul_ne_zero hω.ne' hh
  have hjet := tendsto_real_sinh_sub_self_div_cube_nhdsNE_zero.comp hscale
  have hconst : Tendsto (fun _ : ℝ =>
        24 * Real.cosh (h / 2) * h ^ (2 : ℕ))
        (𝓝[>] 0) (𝓝 (24 * Real.cosh (h / 2) * h ^ (2 : ℕ))) :=
    tendsto_const_nhds
  have hprod := hjet.mul hconst
  convert hprod using 1
  · funext ω
    rw [shiftedEulerLogPolarConnectedThirdExcess,
      shiftedEulerLogPolarChordDensity]
    by_cases hω : ω = 0
    · simp [hω]
    · change
          12 * (2 * Real.cosh (h / 2) *
              (Real.sinh (ω * h) / (ω * h)) -
            2 * Real.cosh (h / 2)) / ω ^ (2 : ℕ) =
          ((Real.sinh (ω * h) - ω * h) / (ω * h) ^ (3 : ℕ)) *
            (24 * Real.cosh (h / 2) * h ^ (2 : ℕ))
      field_simp [hω, hh]
      <;> ring
  · ring

theorem shiftedEulerLogPolarConnectedThirdExcess_le
    {ω h H : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hh : 0 < h) (hhH : h ≤ H) :
    shiftedEulerLogPolarConnectedThirdExcess ω h ≤
      4 * Real.cosh (h / 2) * h ^ (2 : ℕ) * Real.cosh H := by
  have hy : 0 < ω * h := mul_pos hω hh
  have hyH : ω * h ≤ H := by
    calc
      ω * h ≤ 1 * h := mul_le_mul_of_nonneg_right hω1 hh.le
      _ = h := one_mul h
      _ ≤ H := hhH
  have hjet := sinh_sub_self_le hy.le
  have hcosh0 : 0 ≤ Real.cosh (h / 2) := (Real.cosh_pos _).le
  have hscaled :
      24 * Real.cosh (h / 2) * (Real.sinh (ω * h) - ω * h) ≤
        24 * Real.cosh (h / 2) *
          ((ω * h) ^ (3 : ℕ) / 6 * Real.cosh (ω * h)) :=
    mul_le_mul_of_nonneg_left hjet (by positivity)
  have hden : 0 < (ω * h) * ω ^ (2 : ℕ) := mul_pos hy (sq_pos_of_pos hω)
  have hdiv := div_le_div_of_nonneg_right hscaled hden.le
  have hcosh : Real.cosh (ω * h) ≤ Real.cosh H := by
    rw [Real.cosh_le_cosh]
    simpa only [abs_of_pos hy, abs_of_nonneg (hh.le.trans hhH)] using hyH
  have hlast :
      4 * Real.cosh (h / 2) * h ^ (2 : ℕ) * Real.cosh (ω * h) ≤
        4 * Real.cosh (h / 2) * h ^ (2 : ℕ) * Real.cosh H :=
    mul_le_mul_of_nonneg_left hcosh (by positivity)
  calc
    shiftedEulerLogPolarConnectedThirdExcess ω h =
        (24 * Real.cosh (h / 2) *
          (Real.sinh (ω * h) - ω * h)) / ((ω * h) * ω ^ (2 : ℕ)) := by
      rw [shiftedEulerLogPolarConnectedThirdExcess,
        shiftedEulerLogPolarChordDensity]
      field_simp [hω.ne', hh.ne']
      ring
    _ ≤ (24 * Real.cosh (h / 2) *
          ((ω * h) ^ (3 : ℕ) / 6 * Real.cosh (ω * h))) /
        ((ω * h) * ω ^ (2 : ℕ)) := hdiv
    _ = 4 * Real.cosh (h / 2) * h ^ (2 : ℕ) * Real.cosh (ω * h) := by
      field_simp [hω.ne', hh.ne']
      ring
    _ ≤ _ := hlast

def ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox
    (ω H h : ℝ) : ℝ :=
  16 * shiftedEulerLogPolarConnectedThirdExcess ω h / h ^ (5 : ℕ) *
    (1 - h / H)

/-- Exact common-multiplier law on the principal-polar continuum. -/
theorem ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox_eq_multiplier
    {ω H h : ℝ} (hω : ω ≠ 0) (hh : h ≠ 0) :
    ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h =
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
        (2 * Real.cosh (h / 2)) *
          shiftedEulerLogConnectedThirdMultiplier ω h := by
  rw [ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox,
    shiftedEulerLogPolarConnectedThirdExcess,
    shiftedEulerLogPolarChordDensity,
    ccmGuinandWeilThirdGradeCesaroTriangularWeight,
    ccmGuinandWeilThirdGradeWeight,
    shiftedEulerLogConnectedThirdMultiplier]
  field_simp [hω, hh]
  ring

theorem tendsto_ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox
    {H h : ℝ} (hh : h ≠ 0) :
    Tendsto (fun ω : ℝ =>
      ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h)
      (𝓝[>] 0)
      (𝓝 (ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
        (2 * Real.cosh (h / 2)))) := by
  have hbase := tendsto_shiftedEulerLogPolarConnectedThirdExcess hh
  have h := ((hbase.const_mul (16 : ℝ)).div_const (h ^ (5 : ℕ))).mul_const
    (1 - h / H)
  convert h using 1
  · funext ω
    rfl
  · rw [ccmGuinandWeilThirdGradeCesaroTriangularWeight,
      ccmGuinandWeilThirdGradeWeight]
    field_simp [hh]
    ring

theorem abs_ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox_le
    {ω b H h : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hb : 0 < b) (hbH : b ≤ H) (hh : b ≤ h) (hhH : h ≤ H) :
    |ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h| ≤
      64 * Real.cosh (H / 2) * Real.cosh H / b ^ (3 : ℕ) := by
  have hH : 0 < H := hb.trans_le hbH
  have hh0 : 0 < h := hb.trans_le hh
  have hexcess0 := shiftedEulerLogPolarConnectedThirdExcess_nonneg hω hh0
  have hexcess := shiftedEulerLogPolarConnectedThirdExcess_le hω hω1 hh0 hhH
  have hfactor0 : 0 ≤ 1 - h / H := by
    rw [sub_nonneg, div_le_one hH]
    exact hhH
  have hfactor1 : 1 - h / H ≤ 1 := by
    have : 0 ≤ h / H := div_nonneg hh0.le hH.le
    linarith
  have hbase0 : 0 ≤
      16 * shiftedEulerLogPolarConnectedThirdExcess ω h / h ^ (5 : ℕ) :=
    div_nonneg (mul_nonneg (by norm_num) hexcess0) (by positivity)
  have hfirst :
      ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h ≤
        16 * shiftedEulerLogPolarConnectedThirdExcess ω h / h ^ (5 : ℕ) := by
    rw [ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox]
    nlinarith
  have hsecond :
      16 * shiftedEulerLogPolarConnectedThirdExcess ω h / h ^ (5 : ℕ) ≤
        16 * (4 * Real.cosh (h / 2) * h ^ (2 : ℕ) * Real.cosh H) / h ^ (5 : ℕ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexcess (by norm_num)) (by positivity)
  have hcosh : Real.cosh (h / 2) ≤ Real.cosh (H / 2) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (by positivity : 0 ≤ h / 2),
      abs_of_nonneg (by positivity : 0 ≤ H / 2)]
    linarith
  have hpow : b ^ (3 : ℕ) ≤ h ^ (3 : ℕ) := pow_le_pow_left₀ hb.le hh 3
  have hinv : 1 / h ^ (3 : ℕ) ≤ 1 / b ^ (3 : ℕ) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hcoshH0 : 0 ≤ Real.cosh H := (Real.cosh_pos _).le
  have hthird :
      64 * Real.cosh (h / 2) * Real.cosh H / h ^ (3 : ℕ) ≤
        64 * Real.cosh (H / 2) * Real.cosh H / b ^ (3 : ℕ) := by
    have hcoef :
        64 * Real.cosh (h / 2) * Real.cosh H ≤
          64 * Real.cosh (H / 2) * Real.cosh H :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcosh (by norm_num)) hcoshH0
    calc
      64 * Real.cosh (h / 2) * Real.cosh H / h ^ (3 : ℕ) =
          (64 * Real.cosh (h / 2) * Real.cosh H) * (1 / h ^ (3 : ℕ)) := by ring
      _ ≤ (64 * Real.cosh (H / 2) * Real.cosh H) * (1 / h ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ (64 * Real.cosh (H / 2) * Real.cosh H) * (1 / b ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hnonneg : 0 ≤
      ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h := by
    rw [ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox]
    positivity
  rw [abs_of_nonneg hnonneg]
  calc
    ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h
        ≤ 16 * shiftedEulerLogPolarConnectedThirdExcess ω h / h ^ (5 : ℕ) := hfirst
    _ ≤ 16 * (4 * Real.cosh (h / 2) * h ^ (2 : ℕ) * Real.cosh H) / h ^ (5 : ℕ) := hsecond
    _ = 64 * Real.cosh (h / 2) * Real.cosh H / h ^ (3 : ℕ) := by
      field_simp [hh0.ne']
      ring
    _ ≤ _ := hthird

theorem tendsto_integral_ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    Tendsto (fun ω : ℝ => ∫ h in b..H,
        ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h)
      (𝓝[>] 0)
      (𝓝 (∫ h in b..H,
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          (2 * Real.cosh (h / 2)))) := by
  have hclock : ∀ᶠ ω : ℝ in 𝓝[>] 0, ω ∈ Set.Ioo 0 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ : ℝ =>
        64 * Real.cosh (H / 2) * Real.cosh H / b ^ (3 : ℕ))
  · filter_upwards [hclock] with ω hω
    apply ContinuousOn.aestronglyMeasurable
    · intro h hhmem
      have hmem : h ∈ Set.uIcc b H := Set.uIoc_subset_uIcc hhmem
      rw [Set.uIcc_of_le hbH] at hmem
      have hh0 : h ≠ 0 := (hb.trans_le hmem.1).ne'
      have hω0 : ω ≠ 0 := hω.1.ne'
      have hH0 : H ≠ 0 := (hb.trans_le hbH).ne'
      unfold ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox
        shiftedEulerLogPolarConnectedThirdExcess
        shiftedEulerLogPolarChordDensity
      have harg : ContinuousAt (fun x : ℝ => ω * x) h :=
        continuousAt_const.mul continuousAt_id
      have hsinh : ContinuousAt (fun x : ℝ => Real.sinh (ω * x)) h :=
        Real.continuous_sinh.continuousAt.comp harg
      have hratio : ContinuousAt
          (fun x : ℝ => Real.sinh (ω * x) / (ω * x)) h :=
        hsinh.div harg (mul_ne_zero hω0 hh0)
      have hcosh : ContinuousAt (fun x : ℝ => Real.cosh (x / 2)) h := by
        fun_prop
      have htwoC : ContinuousAt
          (fun x : ℝ => 2 * Real.cosh (x / 2)) h :=
        continuousAt_const.mul hcosh
      have hexcess : ContinuousAt
          (fun x : ℝ =>
            12 * (2 * Real.cosh (x / 2) *
              (Real.sinh (ω * x) / (ω * x)) -
                2 * Real.cosh (x / 2)) / ω ^ (2 : ℕ)) h :=
        (continuousAt_const.mul ((htwoC.mul hratio).sub htwoC)).div_const _
      have hnum : ContinuousAt
          (fun x : ℝ => 16 *
            (12 * (2 * Real.cosh (x / 2) *
              (Real.sinh (ω * x) / (ω * x)) -
                2 * Real.cosh (x / 2)) / ω ^ (2 : ℕ))) h :=
        continuousAt_const.mul hexcess
      have hpow : ContinuousAt (fun x : ℝ => x ^ (5 : ℕ)) h :=
        continuousAt_id.pow 5
      have hquot := hnum.div hpow (pow_ne_zero 5 hh0)
      have hfactor : ContinuousAt (fun x : ℝ => 1 - x / H) h := by
        fun_prop
      exact (hquot.mul hfactor).continuousWithinAt
    · exact measurableSet_uIoc
  · filter_upwards [hclock] with ω hω
    filter_upwards [] with h hhmem
    have hmem : h ∈ Set.uIcc b H := Set.uIoc_subset_uIcc hhmem
    rw [Set.uIcc_of_le hbH] at hmem
    exact abs_ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox_le
      hω.1 hω.2.le hb hbH hmem.1 hmem.2
  · exact intervalIntegrable_const
  · filter_upwards [] with h hhmem
    have hmem : h ∈ Set.uIcc b H := Set.uIoc_subset_uIcc hhmem
    rw [Set.uIcc_of_le hbH] at hmem
    exact tendsto_ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox
      (hb.trans_le hmem.1).ne'

private theorem tendsto_ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun ω : ℝ =>
      ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω n)
      (𝓝[>] 0) (𝓝 (ccmGuinandWeilPrimeEntryThirdJetScale n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_comm] using
    tendsto_ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox m

def ccmFUSuzukiPositiveConnectedLogChordTriangularPrimeApprox
    (b H ω : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then
      ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω k *
        (1 - Real.log k / H)
    else 0

theorem tendsto_ccmFUSuzukiPositiveConnectedLogChordTriangularPrimeApprox
    (b H : ℝ) :
    Tendsto (ccmFUSuzukiPositiveConnectedLogChordTriangularPrimeApprox b H)
      (𝓝[>] 0)
      (𝓝 (ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow b H)) := by
  have hsum : Tendsto (fun ω : ℝ =>
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω k *
            (1 - Real.log k / H)
        else 0)
      (𝓝[>] 0)
      (𝓝 (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          ccmGuinandWeilPrimeEntryThirdJetScale k *
            (1 - Real.log k / H)
        else 0)) := by
    apply tendsto_finsetSum
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      exact
        (tendsto_ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox_of_two_le
          (Finset.mem_Icc.mp hk).1).mul_const _
    · simp only [hbk, if_false]
      exact tendsto_const_nhds
  have htarget :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          ccmGuinandWeilPrimeEntryThirdJetScale k *
            (1 - Real.log k / H)
        else 0) =
      ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow b H := by
    rw [ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
      simpa only [Nat.add_comm] using congrArg
        (fun x : ℝ => x * (1 - Real.log ((m + 2 : ℕ) : ℝ) / H))
        (ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent m)
    · simp only [hbk, if_false]
  rw [htarget] at hsum
  change Tendsto (fun ω : ℝ =>
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox ω k *
            (1 - Real.log k / H)
        else 0) (𝓝[>] 0)
      (𝓝 (ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow b H))
  exact hsum

/-- Finite positive connected log-chord producer.  Prime and principal-polar carriers share the
same positive clock and remain coupled until the final signed readout. -/
def ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox
    (b H ω : ℝ) : ℝ :=
  ccmFUSuzukiPositiveConnectedLogChordTriangularPrimeApprox b H ω -
    ∫ h in b..H,
      ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h

/-- **Exact finite-clock cancellation law.**  The positive connected Suzuki log chord does not
deform prime and polar regions independently.  It applies one identical hyperbolic multiplier to
the literal signed prime--polar measure before scalarization. -/
theorem ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox_eq_weightedWindow
    {ω b H : ℝ} (hω : ω ≠ 0) (hb : 0 < b) (hbH : b ≤ H) :
    ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω =
      ccmGuinandWeilPrimePolarWeightedWindow b H
        (fun h => ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          shiftedEulerLogConnectedThirdMultiplier ω h) := by
  rw [ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox,
    ccmFUSuzukiPositiveConnectedLogChordTriangularPrimeApprox,
    ccmGuinandWeilPrimePolarWeightedWindow]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [ccmFUSuzukiPositiveConnectedLogChordPrimeEntryApprox_eq_multiplier
        hω hk2]
      rw [ccmGuinandWeilThirdGradeCesaroTriangularWeight,
        ← criticalMellinAtomWeight_mul_ccmGuinandWeilThirdGradeWeight_eq_scale]
      ring
    · simp only [hbk, if_false]
  · apply intervalIntegral.integral_congr
    intro h hhmem
    have hmem : h ∈ Set.uIcc b H := hhmem
    rw [Set.uIcc_of_le hbH] at hmem
    rw [ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox_eq_multiplier
      hω (hb.trans_le hmem.1).ne']
    ring

theorem tendsto_ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    Tendsto
      (ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H)
      (𝓝[>] 0)
      (𝓝 (ccmFUSuzukiConnectedThirdTangentTriangularCompletedWindow b H)) := by
  change Tendsto (fun ω : ℝ =>
      ccmFUSuzukiPositiveConnectedLogChordTriangularPrimeApprox b H ω -
        ∫ h in b..H,
          ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox ω H h)
    (𝓝[>] 0)
    (𝓝 (ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow b H -
      ∫ h in b..H,
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          (2 * Real.cosh (h / 2))))
  exact
    (tendsto_ccmFUSuzukiPositiveConnectedLogChordTriangularPrimeApprox b H).sub
      (tendsto_integral_ccmFUSuzukiPositiveConnectedLogChordPolarEntryApprox hb hbH)

/-- Fixed-window coefficient-faithful landing on the literal CCM prime--polar triangular source.
No positive/negative region is estimated separately. -/
theorem tendsto_ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox_literal
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    Tendsto
      (ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H)
      (𝓝[>] 0)
      (𝓝 (ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H))) := by
  rw [ccmGuinandWeilPrimePolarTriangularWindow_eq_connectedSuzukiProducer]
  exact
    tendsto_ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox hb hbH

end

end RHTower
