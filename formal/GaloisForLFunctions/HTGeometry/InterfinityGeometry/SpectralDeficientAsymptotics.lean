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
    rw [remainderIntegral, ← Real.norm_eq_abs]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hint.norm ?_ measurableSet_Ioo fun s hs => ?_
    · exact ((integrableOn_expScaled ha hV).mono_set Ioo_subset_Ioi_self).const_mul B
    · have hs0 : (0 : ℝ) < s := hs.1
      have hw : (0 : ℝ) < s ^ a := Real.rpow_pos_of_pos hs0 _
      have hexp0 : (0 : ℝ) < Real.exp (-(V * s)) := Real.exp_pos _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw, abs_of_pos hexp0]
      have hrb : |r s| ≤ B := hB s hs
      calc Real.exp (-(V * s)) * |r s| * s ^ a
          ≤ Real.exp (-(V * s)) * B * s ^ a :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrb hexp0.le) hw.le
        _ = B * (Real.exp (-(V * s)) * s ^ a) := by ring
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

/-! ## The Hadamard split -/

theorem split_integrand {h r : ℝ → ℝ} (hr : ∀ s, h s = h 0 + s * r s) {s : ℝ} (hs : 0 < s)
    (V a : ℝ) :
    (Real.exp (-(V * s)) * h s - h 0) * s ^ (a - 1) =
      h 0 * (laplaceCochain V s * s ^ (a - 1)) + Real.exp (-(V * s)) * r s * s ^ a := by
  rw [hr s]
  simp only [laplaceCochain]
  rw [← rpow_succ_split hs a]
  ring

theorem transportedFinitePart_split (c : ℝ) (ha : -1 < a) (hV : 0 ≤ V) {h r : ℝ → ℝ}
    (hr : ∀ s, h s = h 0 + s * r s) (hrc : Continuous r) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    transportedFinitePart c a V h =
      c * (h 0 * (cutIntegral a V + 1 / a) + remainderIntegral a V r) := by
  have hint1 : IntegrableOn (fun s : ℝ => h 0 * (laplaceCochain V s * s ^ (a - 1))) (Ioo 0 1) :=
    (integrableOn_cutIntegrand ha hV).const_mul (h 0)
  have hint2 := integrableOn_remainder ha hV hrc hB0 hB
  have hsplit : (∫ s in Ioo (0 : ℝ) 1, (Real.exp (-(V * s)) * h s - h 0) * s ^ (a - 1)) =
      h 0 * cutIntegral a V + remainderIntegral a V r := by
    have hcongr : (∫ s in Ioo (0 : ℝ) 1, (Real.exp (-(V * s)) * h s - h 0) * s ^ (a - 1)) =
        ∫ s in Ioo (0 : ℝ) 1,
          (h 0 * (laplaceCochain V s * s ^ (a - 1)) + Real.exp (-(V * s)) * r s * s ^ a) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      exact split_integrand hr hs.1 V a
    rw [hcongr, integral_add hint1 hint2, integral_const_mul]
    rfl
  rw [transportedFinitePart, hsplit]
  ring

/-! ## The projective limit -/

theorem tendsto_normalized_remainder (ha : -1 < a) {r : ℝ → ℝ} (hrc : Continuous r) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    Tendsto (fun V : ℝ => V ^ a * remainderIntegral a V r) atTop (𝓝 0) := by
  have hlim : Tendsto (fun V : ℝ => B * Real.Gamma (a + 1) / V) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  have hVa : (0 : ℝ) < V ^ a := Real.rpow_pos_of_pos hV _
  have hbound := abs_remainderIntegral_le ha hV hrc hB0 hB
  have hcollapse : V ^ a * V ^ (-(a + 1)) = V⁻¹ := by
    rw [← Real.rpow_add hV, ← Real.rpow_neg_one V]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hVa]
  calc V ^ a * |remainderIntegral a V r| ≤ V ^ a * (B * (V ^ (-(a + 1)) * Real.Gamma (a + 1))) :=
        mul_le_mul_of_nonneg_left hbound hVa.le
    _ = B * Real.Gamma (a + 1) * (V ^ a * V ^ (-(a + 1))) := by ring
    _ = B * Real.Gamma (a + 1) / V := by rw [hcollapse]; ring

/-- **The deficient projective limit.**  After the normalization `V^a` the transported finite part
of a smooth chart converges to `c Γ(a) h(0)`. -/
theorem tendsto_transportedFinitePart (c : ℝ) (ha : -1 < a) (ha0 : a < 0) {h : ℝ → ℝ}
    (hh : IsSmoothReal h) :
    Tendsto (fun V : ℝ => V ^ a * transportedFinitePart c a V h) atTop
      (𝓝 (c * (Real.Gamma a * h 0))) := by
  set r : ℝ → ℝ := hadamardAvg 0 (deriv h) with hrdef
  have hrS : IsSmoothReal r := isSmoothReal_hadamardAvg 0 hh.derivSmooth
  have hrc : Continuous r := hrS.continuous
  have hr : ∀ s, h s = h 0 + s * r s := hadamard_eq hh
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hrc.continuousOn
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B := fun s hs =>
    le_trans (hB₀ s ⟨hs.1.le, hs.2.le⟩) (le_max_left _ _)
  have hmain : Tendsto (fun V : ℝ =>
      c * (h 0 * (V ^ a * (cutIntegral a V + 1 / a)) + V ^ a * remainderIntegral a V r)) atTop
      (𝓝 (c * (h 0 * Real.Gamma a + 0))) := by
    refine Tendsto.const_mul c ?_
    exact ((tendsto_regularizedCut ha ha0).const_mul (h 0)).add
      (tendsto_normalized_remainder ha hrc hB0 hB)
  rw [add_zero] at hmain
  have hval : c * (h 0 * Real.Gamma a) = c * (Real.Gamma a * h 0) := by ring
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
  rw [transportedFinitePart_split c ha hV hr hrc hB0 hB]
  ring

end

end GaloisForLFunctions.HTGeometry.Interfinity
