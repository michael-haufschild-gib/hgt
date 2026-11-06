import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve

/-!
# The physical prefix has small L¹ mass

The triangle inequality for the translated atoms and finite Cauchy–Schwarz
bound the prefix mass by its coefficient norm times the square root of its
relative length. The linear defect cutoff supplies the factor `c⁻¹/²`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticElectrostatics ArithmeticLorentzianGeometry SpacingScaleHarmonicAnalysis

private theorem integral_abs_atomicTest_le {g : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hs : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (M : ℕ) (x : ℕ → ℝ) :
    (∫ u, |atomicTest M x g u|) ≤ (∫ u, |g u|) * ∑ n ∈ Icc 1 M, |x n| := by
  have hga : Continuous (fun u => |g u|) := hg.abs
  have hsa : ∀ u, u ∉ Set.Icc 0 w → |g u| = 0 := by
    intro u hu
    rw [hs u hu, abs_zero]
  have hd : Continuous (atomicTest M x g) := by
    unfold atomicTest
    exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul (hg.comp (continuous_id.sub continuous_const))
  have hda : Continuous (atomicTest M (fun n => |x n|) (fun u => |g u|)) := by
    unfold atomicTest
    exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul (hga.comp (continuous_id.sub continuous_const))
  have hca : HasCompactSupport (fun u => |atomicTest M x g u|) := by
    simpa only [Real.norm_eq_abs] using (hasCompactSupport_atomicTest hs M x).norm
  have h := integral_mono (μ := volume)
    (hd.abs.integrable_of_hasCompactSupport hca)
    (hda.integrable_of_hasCompactSupport (hasCompactSupport_atomicTest hsa M _))
    (fun u => by
      unfold atomicTest
      simpa only [abs_mul] using abs_sum_le_sum_abs (fun n => x n * g (u - Real.log n)) (Icc 1 M))
  have he := integral_atomicTest_mul (φ := fun _ => (1 : ℝ)) continuous_const hga hsa M
    (fun n => |x n|)
  simp only [mul_one] at he
  simp_rw [integral_sub_right_eq_self (fun u => |g u|)] at he
  rw [he, ← sum_mul, mul_comm] at h
  exact h

/-- The squared L¹ mass of a centered prefix is bounded by its relative length. -/
theorem normalized_prefix_integral_abs_sq_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (x : ℕ → ℝ) :
    (∫ y, |Real.sqrt N / c *
      atomicTest M x (atomDilate φ (c / N)) (y + Real.log N)|) ^ 2 ≤
      (M : ℝ) / N * (∫ u, |φ u|) ^ 2 * ∑ n ∈ Icc 1 M, x n ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : Continuous (atomDilate φ (c / N)) := hφ.comp (continuous_id.div_const _)
  have hgs : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := by
    intro u hu
    apply hs
    intro hm
    apply hu
    refine ⟨?_, (div_le_one hw).mp hm.2⟩
    simpa only [zero_mul] using (le_div_iff₀ hw).mp hm.1
  have ha : (∫ u, |atomDilate φ (c / N) u|) = (c / N) * ∫ u, |φ u| := by
    simpa only [atomDilate, abs_of_pos hw, smul_eq_mul] using
      Measure.integral_comp_div (fun u => |φ u|) (c / N)
  have hb := mul_le_mul_of_nonneg_left (integral_abs_atomicTest_le hg hgs M x)
    (show 0 ≤ Real.sqrt N / c by positivity)
  rw [ha] at hb
  have he : (∫ y, |Real.sqrt N / c *
      atomicTest M x (atomDilate φ (c / N)) (y + Real.log N)|) =
      Real.sqrt N / c * ∫ u, |atomicTest M x (atomDilate φ (c / N)) u| := by
    simp_rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.sqrt N / c by positivity)]
    rw [integral_const_mul, integral_add_right_eq_self
      (fun u => |atomicTest M x (atomDilate φ (c / N)) u|) (Real.log N)]
  rw [he]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 M) (fun _ => (1 : ℝ)) (fun n => |x n|)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs,
    Nat.card_Icc, Nat.add_sub_cancel] at hcs
  have hsq := sq_le_sq₀ (show 0 ≤ Real.sqrt N / c *
    ∫ u, |atomicTest M x (atomDilate φ (c / N)) u| by positivity)
    (show 0 ≤ Real.sqrt N / c * ((c / N) * (∫ u, |φ u|) *
      ∑ n ∈ Icc 1 M, |x n|) by positivity) |>.mpr hb
  have hcoef : (Real.sqrt N / c * ((c / N) * (∫ u, |φ u|) *
      ∑ n ∈ Icc 1 M, |x n|)) ^ 2 =
      ((∫ u, |φ u|) ^ 2 / N) * (∑ n ∈ Icc 1 M, |x n|) ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hN0.le]
    field_simp
  rw [hcoef] at hsq
  exact hsq.trans ((mul_le_mul_of_nonneg_left hcs (by positivity)).trans_eq (by ring))

/-- The linear defect cutoff makes prefix L¹ mass at most a constant times `√(P/c)`. -/
theorem linear_prefix_integral_abs_sq_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (∫ y, |Real.sqrt N / c *
      atomicTest (N / linearDefectCutoff c) x (atomDilate φ (c / N))
        (y + Real.log N)|) ^ 2 ≤
      (∫ u, |φ u|) ^ 2 / (4 * c) *
        ∑ n ∈ Icc 1 (N / linearDefectCutoff c), x n ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨_, h4c, _, _⟩ := linearDefectCutoff_bounds hc
  have hdiv : ((N / linearDefectCutoff c : ℕ) : ℝ) * linearDefectCutoff c ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (linearDefectCutoff c)
  have hratio : ((N / linearDefectCutoff c : ℕ) : ℝ) / N ≤ 1 / (4 * c) := by
    apply (div_le_div_iff₀ hN0 (by positivity : 0 < 4 * c)).mpr
    nlinarith only [hdiv, mul_le_mul_of_nonneg_left h4c
      (Nat.cast_nonneg (N / linearDefectCutoff c))]
  have hb := normalized_prefix_integral_abs_sq_le hφ hs hc0 hN (N / linearDefectCutoff c) x
  exact hb.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hratio (sq_nonneg _))
    (sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring))

#print axioms normalized_prefix_integral_abs_sq_le
#print axioms linear_prefix_integral_abs_sq_le
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
