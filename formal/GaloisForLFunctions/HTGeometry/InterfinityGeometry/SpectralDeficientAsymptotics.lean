import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralGammaScaling
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralPrimitiveIdentity
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.HadamardDivision

/-!
# The deficient projective limit

Below the stability cut the transported finite part diverges, but after the projective
normalization `V^a` it converges to a fixed multiple of evaluation at the origin:

`V^a · η_a(e^{-V·} h) → c Γ(a) h(0)`,  `−1 < a < 0`.

Splitting the chart by Hadamard's lemma isolates the constant part, whose contribution is the
regularized cut integral, from the remainder, whose contribution is `O(1/V)` after normalization.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

variable {a V : ℝ}

/-- The transported finite part of a smooth chart at a deficient observer. -/
def transportedFinitePart (c a V : ℝ) (h : ℝ → ℝ) : ℝ :=
  c * ((∫ s in Ioo (0 : ℝ) 1, (Real.exp (-(V * s)) * h s - h 0) * s ^ (a - 1)) + h 0 / a)

/-- The Hadamard remainder contribution. -/
def remainderIntegral (a V : ℝ) (r : ℝ → ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) 1, Real.exp (-(V * s)) * r s * s ^ a

/-! ## The remainder -/

theorem integrableOn_remainder (ha : -1 < a) (hV : 0 ≤ V) {r : ℝ → ℝ} (hr : Continuous r) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    IntegrableOn (fun s : ℝ => Real.exp (-(V * s)) * r s * s ^ a) (Ioo 0 1) := by
  refine Integrable.mono' (g := fun s : ℝ => B * s ^ a)
    ((integrableOn_rpow_of_neg_one_lt ha).const_mul _) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.mul (ContinuousOn.mul ?_ hr.continuousOn) ?_
    · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hw : (0 : ℝ) < s ^ a := Real.rpow_pos_of_pos hs0 _
    have hexp0 : (0 : ℝ) < Real.exp (-(V * s)) := Real.exp_pos _
    have hexp1 : Real.exp (-(V * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw, abs_of_pos hexp0]
    have hrb : |r s| ≤ B := hB s hs
    have hstep : Real.exp (-(V * s)) * |r s| ≤ B := by
      nlinarith [abs_nonneg (r s)]
    exact mul_le_mul_of_nonneg_right hstep hw.le

/-- **The normalized remainder is `O(1/V)`.** -/
theorem abs_remainderIntegral_le (ha : -1 < a) (hV : 0 < V) {r : ℝ → ℝ} (hr : Continuous r)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    |remainderIntegral a V r| ≤ B * (V ^ (-(a + 1)) * Real.Gamma (a + 1)) := by
  have hint := integrableOn_remainder ha hV.le hr hB0 hB
  have hbound : |remainderIntegral a V r| ≤
      ∫ s in Ioo (0 : ℝ) 1, B * (Real.exp (-(V * s)) * s ^ a) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hint.norm ?_ measurableSet_Ioo fun s hs => ?_
    · exact ((integrableOn_expScaled ha hV).mono_set Ioo_subset_Ioi_self).const_mul B
    · have hs0 : (0 : ℝ) < s := hs.1
      have hw : (0 : ℝ) < s ^ a := Real.rpow_pos_of_pos hs0 _
      have hexp0 : (0 : ℝ) < Real.exp (-(V * s)) := Real.exp_pos _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw, abs_of_pos hexp0]
      have hrb : |r s| ≤ B := hB s hs
      nlinarith [abs_nonneg (r s), hw.le, hexp0.le]
  have hsub : (∫ s in Ioo (0 : ℝ) 1, B * (Real.exp (-(V * s)) * s ^ a)) ≤
      B * (V ^ (-(a + 1)) * Real.Gamma (a + 1)) := by
    rw [integral_const_mul, ← integral_expScaled ha hV]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    refine setIntegral_mono_set (integrableOn_expScaled ha hV) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0 : ℝ) < s := hs
      positivity
    · exact (Ioo_subset_Ioi_self : (Ioo (0 : ℝ) 1) ≤ Ioi 0).eventuallyLE
  linarith

end

end GaloisForLFunctions.HTGeometry.Interfinity
