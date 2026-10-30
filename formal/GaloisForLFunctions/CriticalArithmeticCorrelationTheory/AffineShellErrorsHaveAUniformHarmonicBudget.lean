import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffineShellErrorsHavePolynomialHarmonicBounds
import GaloisForLFunctions.HTGeometry.HarmonicQuotientSquareBudget

/-!
# A horizon-independent budget for the actual affine shell errors

Integrating the inverse-logarithmic source envelope preserves its summable
square. The quotient cutoff has logarithm linear in the overlap, so the
global shell bound costs only the fifth power of the overlap.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

/-- Every actual shifted reciprocal shell family has a uniform harmonic budget. -/
theorem exists_shiftedReciprocalUpwardRowError_uniform_harmonic_budget {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) ≤ K * c ^ 5 := by
  obtain ⟨C, hC, hsource⟩ := exists_affineShellCorrection_polynomial_log_rate hm hφ hsupp hM
  obtain ⟨Ybase, hbase⟩ := eventually_atTop.mp (hsource 2)
  let Y₀ := max 1 Ybase
  have hY₀ : 1 ≤ Y₀ := le_max_left _ _
  have hY₀0 : 0 < Y₀ := zero_lt_one.trans_le hY₀
  let D : ℝ := 8 * (Real.log 4 + 4) * m.totient
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    positivity
  let J := |Real.log (4 * Y₀)| + 2
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  let H := 1 + 2 * Real.pi ^ 2
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨C ^ 2 * H + D ^ 2 * J + 1, by positivity, ?_⟩
  intro N hN c hc shift
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let T := 2 * c * Y₀ * Real.exp c
  have hexp : 1 ≤ Real.exp c := Real.one_le_exp_iff.mpr hc0.le
  have hTbase : 2 * c * Y₀ ≤ T := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
      (show 0 ≤ 2 * c * Y₀ by positivity)
  have hT : 1 ≤ T := by
    have hcy := mul_le_mul hc hY₀ zero_le_one hc0.le
    nlinarith only [hcy, hTbase]
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hglobal : ∀ n ∈ Icc 1 N,
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ D * c ^ 2 / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hquot : 1 ≤ (N : ℝ) / n := (le_div_iff₀ hn0).mpr
      (by simpa only [one_mul] using hnN)
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right
      (abs_affineShellCorrection_error_le_polynomial hm hφ hsupp hM n shift hc hquot)
      (Real.sqrt_nonneg _)
  have hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n →
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤
        (C * c ^ 2 / (1 + Real.log (((N : ℝ) / T) / n))) / Real.sqrt n := by
    intro n hn ht
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    let X := (N : ℝ) / n
    let Y := X / (2 * c)
    let t := Real.log (((N : ℝ) / T) / n)
    have hX0 : 0 < X := div_pos hN0 hn0
    have hY : Y₀ ≤ Y := (le_div_iff₀ (by positivity : 0 < 2 * c)).mpr
      (by have h := hTbase.trans ht; dsimp only [X] at *; nlinarith only [h])
    have hY0 : 0 < Y := hY₀0.trans_le hY
    have hYn : Ybase ≤ Y := (le_max_right _ _).trans hY
    have ht0 : 0 ≤ t := by
      apply Real.log_nonneg
      apply (one_le_div hn0).mpr
      apply (le_div_iff₀ hT0).mpr
      have h := (le_div_iff₀ hn0).mp ht
      simpa only [mul_comm] using h
    have hlogid : Real.log Y = Real.log Y₀ + c + t := by
      have hyid : Y = (Y₀ * Real.exp c) * (((N : ℝ) / T) / n) := by
        dsimp only [Y, X, T]
        field_simp
      rw [hyid, Real.log_mul (by positivity : Y₀ * Real.exp c ≠ 0)
        (by positivity : ((N : ℝ) / T) / n ≠ 0),
        Real.log_mul hY₀0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hloglower : c + t ≤ Real.log Y := by
      rw [hlogid]
      have h := Real.log_nonneg hY₀
      linarith only [h]
    have hct0 : 0 < c + t := by linarith only [hc0, ht0]
    have hlogY : 0 < Real.log Y := hct0.trans_le hloglower
    have hsq : c * (1 + t) ≤ Real.log Y ^ 2 := by
      have hs := mul_self_le_mul_self (add_nonneg hc0.le ht0) hloglower
      have hc2 := mul_le_mul_of_nonneg_left hc hc0.le
      have hct := mul_nonneg hc0.le ht0
      nlinarith only [hs, hc2, hct, sq_nonneg t]
    have hfrac : C * c ^ 3 / Real.log Y ^ 2 ≤ C * c ^ 2 / (1 + t) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hlogY) (by positivity : 0 < 1 + t)).mpr
      have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ C * c ^ 2 by positivity)
      nlinarith only [h]
    have hX : 2 * c * Y ≤ X := by
      have hid : 2 * c * Y = X := by
        dsimp only [Y]
        field_simp
      exact hid.le
    have hb := (hbase Y hYn).2 c X hc hX shift n
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right (hb.trans hfrac) (Real.sqrt_nonneg _)
  have hsum := HTGeometry.sum_sq_le_harmonic_log_envelope hN hT
    (shiftedReciprocalUpwardRowError φ c shift N m) hglobal hgood
  have hlogT : 1 + Real.log (2 * T) ≤ J * c := by
    have hid : 2 * T = (4 * Y₀) * c * Real.exp c := by dsimp only [T]; ring
    rw [hid, Real.log_mul (by positivity : (4 * Y₀) * c ≠ 0) (Real.exp_pos _).ne',
      Real.log_mul (by positivity : 4 * Y₀ ≠ 0) hc0.ne', Real.log_exp]
    have hl := Real.log_le_sub_one_of_pos hc0
    have ha := le_abs_self (Real.log (4 * Y₀))
    have hm := mul_le_mul_of_nonneg_left hc (abs_nonneg (Real.log (4 * Y₀)))
    dsimp only [J]
    linarith only [hl, ha, hm]
  have hc45 : c ^ 4 ≤ c ^ 5 := pow_le_pow_right₀ hc (by norm_num)
  have hhead : (C * c ^ 2) ^ 2 * H ≤ C ^ 2 * H * c ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hc45 (show 0 ≤ C ^ 2 * H by positivity)
    nlinarith only [h]
  have htail : (D * c ^ 2) ^ 2 * (1 + Real.log (2 * T)) ≤ D ^ 2 * J * c ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hlogT (sq_nonneg (D * c ^ 2))
    nlinarith only [h]
  have hc5 : 0 ≤ c ^ 5 := pow_nonneg hc0.le _
  change _ ≤ (C ^ 2 * H + D ^ 2 * J + 1) * c ^ 5
  change _ ≤ (C * c ^ 2) ^ 2 * H + (D * c ^ 2) ^ 2 * (1 + Real.log (2 * T)) at hsum
  nlinarith only [hsum, hhead, htail, hc5]

/-- The explicit tilted spline has a fifth-power overlap budget at every horizon. -/
theorem exists_tiltedUnitSpline_shiftedReciprocalUpwardRowError_uniform_harmonic_budget
    {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N,
        shiftedReciprocalUpwardRowError tiltedUnitSpline c shift N m n ^ 2) ≤ K * c ^ 5 :=
  exists_shiftedReciprocalUpwardRowError_uniform_harmonic_budget hm contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_shiftedReciprocalUpwardRowError_uniform_harmonic_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_shiftedReciprocalUpwardRowError_uniform_harmonic_budget
