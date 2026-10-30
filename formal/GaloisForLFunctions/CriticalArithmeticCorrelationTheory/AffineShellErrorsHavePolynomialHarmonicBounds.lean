import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffinePrimeShellsHavePolynomialGrowth
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingShellSourcesHaveLogarithmicRates
import GaloisForLFunctions.HTGeometry.HarmonicQuotientTailBound

/-!
# Polynomial harmonic bounds for the actual affine shell errors

Quantitative source control above a movable quotient cutoff combines with a
global polynomial shell bound. The harmonic mass below that cutoff yields
one uniform overlap estimate for every affine shift family.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

/-- Actual shifted reciprocal shell residuals have a polynomial overlap bound in harmonic norm. -/
theorem exists_shiftedReciprocalUpwardRowError_polynomial_harmonic_bound {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) / Real.log N ≤
        K * c ^ 6 / Real.sqrt (Real.log N) := by
  obtain ⟨C, hC, hsource⟩ := exists_affineShellCorrection_polynomial_log_rate hm hφ hsupp hM
  let D : ℝ := 8 * (Real.log 4 + 4) * m.totient
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    positivity
  let K := 2 * C ^ 2 + 5 * D ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYlim : Tendsto (fun N : ℕ => Real.exp (Real.sqrt (Real.log N))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.comp hloglim)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hYlim.eventually (hsource 2), hloglim.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with N hsourceN hL hN
  intro c hc shift
  let L := Real.log (N : ℝ)
  let Y := Real.exp (Real.sqrt L)
  let T := 2 * c * Y
  let A := C * c ^ 3 / L
  let B := D * c ^ 2
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hs1 : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
  have hs0 : 0 < Real.sqrt L := zero_lt_one.trans_le hs1
  have hY1 : 1 ≤ Y := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _)
  have hT : 1 ≤ T := by dsimp only [T]; nlinarith only [hc, hY1]
  have hglobal : ∀ n ∈ Icc 1 N,
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ B / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hquot : 1 ≤ (N : ℝ) / n := (le_div_iff₀ hn0).mpr (by simpa only [one_mul] using hnN)
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right
      (abs_affineShellCorrection_error_le_polynomial hm hφ hsupp hM n shift hc hquot)
      (Real.sqrt_nonneg _)
  have hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n →
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ A / Real.sqrt n := by
    intro n hn ht
    have hb := hsourceN.2 c ((N : ℝ) / n) hc ht shift n
    rw [Real.log_exp, Real.sq_sqrt (Real.log_natCast_nonneg N)] at hb
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)
  have hsum := HTGeometry.sum_sq_le_harmonic_quotient_tail hN hT
    (shiftedReciprocalUpwardRowError φ c shift N m) hglobal hgood
  have hhead : A ^ 2 * (1 + L) ≤ 2 * C ^ 2 * c ^ 6 * Real.sqrt L := by
    have hfrac : (1 + L) / L ^ 2 ≤ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hL0)).mpr
      nlinarith only [hL1]
    calc
      _ = C ^ 2 * c ^ 6 * ((1 + L) / L ^ 2) := by dsimp only [A]; ring
      _ ≤ C ^ 2 * c ^ 6 * 2 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ ≤ 2 * C ^ 2 * c ^ 6 * Real.sqrt L := by
        have h := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 2 * C ^ 2 * c ^ 6 by positivity)
        simpa only [mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hlogT : 1 + Real.log (2 * T) ≤ 4 * c + Real.sqrt L := by
    have hid : 2 * T = (4 * c) * Real.exp (Real.sqrt L) := by dsimp only [T, Y]; ring
    rw [hid, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have hb := Real.log_le_sub_one_of_pos (show 0 < 4 * c by positivity)
    linarith only [hb]
  have htail : B ^ 2 * (1 + Real.log (2 * T)) ≤ 5 * D ^ 2 * c ^ 6 * Real.sqrt L := by
    have hcs : 4 * c + Real.sqrt L ≤ 5 * c * Real.sqrt L := by
      have h1 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 4 * c by positivity)
      have h2 := mul_le_mul_of_nonneg_right hc hs0.le
      nlinarith only [h1, h2]
    have hc56 : c ^ 5 ≤ c ^ 6 := pow_le_pow_right₀ hc (by norm_num)
    calc
      _ ≤ B ^ 2 * (4 * c + Real.sqrt L) := mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
      _ ≤ B ^ 2 * (5 * c * Real.sqrt L) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = 5 * D ^ 2 * c ^ 5 * Real.sqrt L := by dsimp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc56 (by positivity)) hs0.le
  have hraw : (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) ≤
      K * c ^ 6 * Real.sqrt L := by
    have hb := hsum.trans (add_le_add hhead htail)
    dsimp only [K]
    nlinarith only [hb]
  change _ / L ≤ K * c ^ 6 / Real.sqrt L
  calc
    _ ≤ (K * c ^ 6 * Real.sqrt L) / L := div_le_div_of_nonneg_right hraw hL0.le
    _ = (K * c ^ 6 * Real.sqrt L) / (Real.sqrt L) ^ 2 := by
      rw [Real.sq_sqrt hL0.le]
    _ = _ := by field_simp

/-- The explicit tilted spline satisfies the same uniform quantitative source norm law. -/
theorem exists_tiltedUnitSpline_shiftedReciprocalUpwardRowError_polynomial_harmonic_bound
    {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError tiltedUnitSpline c shift N m n ^ 2) / Real.log N ≤
        K * c ^ 6 / Real.sqrt (Real.log N) :=
  exists_shiftedReciprocalUpwardRowError_polynomial_harmonic_bound hm contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_shiftedReciprocalUpwardRowError_polynomial_harmonic_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_shiftedReciprocalUpwardRowError_polynomial_harmonic_bound
