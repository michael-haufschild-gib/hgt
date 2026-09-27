import GaloisForLFunctions.HTGeometry.GramPairingCauchySchwarz
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A correlation-sensitive bound for continuous frames

The analysis energy of a bounded continuous Hilbert-space field is bounded
by the square root of its double Gram energy. The bound retains every
off-diagonal inner product and is no larger than the diagonal trace bound.
-/

open MeasureTheory Complex
open scoped InnerProduct BoundedContinuousFunction
noncomputable section

namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem bounded_integrable {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → F} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf (Filter.Eventually.of_forall hC)

omit [CompleteSpace E] in
private theorem pairing_sq_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ E) (f : E) :
    Integrable (fun x => ‖inner ℂ (v x) f‖ ^ 2) μ := by
  apply bounded_integrable
    ((v.continuous.inner continuous_const).norm.pow 2).aestronglyMeasurable
    (‖v‖ ^ 2 * ‖f‖ ^ 2)
  intro x
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := (norm_inner_le_norm (𝕜 := ℂ) (v x) f).trans
    (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg f))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

omit [CompleteSpace E] [InnerProductSpace ℂ E] in
private theorem vector_sq_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ E) : Integrable (fun x => ‖v x‖ ^ 2) μ := by
  apply bounded_integrable (v.continuous.norm.pow 2).aestronglyMeasurable (‖v‖ ^ 2)
  intro x
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (v.norm_coe_le_norm x) 2

/-- The entire off-diagonal Gram energy, without a rank truncation. -/
def continuousFrameGramEnergy (μ : Measure ℝ) (v : ℝ →ᵇ E) : ℝ :=
  ∫ x, ∫ y, ‖inner ℂ (v x) (v y)‖ ^ 2 ∂μ ∂μ

omit [CompleteSpace E] in
theorem continuousFrameGramEnergy_nonneg (μ : Measure ℝ) (v : ℝ →ᵇ E) :
    0 ≤ continuousFrameGramEnergy μ v :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

omit [CompleteSpace E] in
private theorem gram_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ E) :
    Integrable (fun z : ℝ × ℝ => ‖inner ℂ (v z.1) (v z.2)‖ ^ 2) (μ.prod μ) := by
  apply bounded_integrable
    (((v.continuous.comp continuous_fst).inner
      (v.continuous.comp continuous_snd)).norm.pow 2).aestronglyMeasurable (‖v‖ ^ 4)
  intro z
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := (norm_inner_le_norm (𝕜 := ℂ) (v z.1) (v z.2)).trans
    (mul_le_mul (v.norm_coe_le_norm z.1) (v.norm_coe_le_norm z.2)
      (norm_nonneg _) (norm_nonneg _))
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2]

/-- A source-uniform frame bound using correlations rather than only diagonal masses. -/
theorem continuousFrame_analysis_le_gram (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ E) (f : E) :
    (∫ x, ‖inner ℂ (v x) f‖ ^ 2 ∂μ) ≤
      Real.sqrt (continuousFrameGramEnergy μ v) * ‖f‖ ^ 2 := by
  let F : ℝ → ℂ := fun x => inner ℂ (v x) f
  let A : ℝ := ∫ x, ‖F x‖ ^ 2 ∂μ
  let g : E := ∫ x, F x • v x ∂μ
  have hF : Continuous F := v.continuous.inner continuous_const
  have hgi : Integrable (fun x => F x • v x) μ := by
    apply bounded_integrable (hF.smul v.continuous).aestronglyMeasurable
      (‖v‖ ^ 2 * ‖f‖)
    intro x
    change ‖F x • v x‖ ≤ _
    rw [norm_smul]
    have hFx := (norm_inner_le_norm (𝕜 := ℂ) (v x) f).trans
      (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg f))
    calc
      _ ≤ (‖v‖ * ‖f‖) * ‖v‖ :=
        mul_le_mul hFx (v.norm_coe_le_norm x) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hH := continuousFrameGramEnergy_nonneg μ v
  have hfg : inner ℂ f g = (A : ℂ) := by
    rw [← integral_inner hgi]
    calc
      _ = ∫ x, ((‖F x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [inner_smul_right, ← inner_conj_symm]
        change F x * (starRingEnd ℂ) (F x) = _
        rw [Complex.mul_conj, Complex.sq_norm]
      _ = _ := integral_complex_ofReal
  have hAcs : A ^ 2 ≤ ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) f g
    rw [hfg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA] at h
    simpa only [mul_pow] using pow_le_pow_left₀ hA h 2
  have hrow (x : ℝ) :
      ‖inner ℂ (v x) g‖ ^ 2 ≤
        A * (∫ y, ‖inner ℂ (v x) (v y)‖ ^ 2 ∂μ) := by
    rw [← integral_inner hgi]
    simp_rw [inner_smul_right]
    have h := GaloisForLFunctions.HTGeometry.norm_integral_mul_conj_sq_le
      (ν := μ) hF.norm.aestronglyMeasurable
      ((continuous_const.inner v.continuous).star.norm.aestronglyMeasurable)
      (pairing_sq_integrable μ v f)
      (show Integrable (fun y => ‖star (inner ℂ (v x) (v y))‖ ^ 2) μ by
        simpa only [norm_star, norm_inner_symm] using pairing_sq_integrable μ v (v x))
    simpa only [starRingEnd_apply, star_star, norm_star, A] using h
  have hEg : (∫ x, ‖inner ℂ (v x) g‖ ^ 2 ∂μ) ≤
      A * continuousFrameGramEnergy μ v := by
    rw [continuousFrameGramEnergy, ← integral_const_mul]
    exact integral_mono (pairing_sq_integrable μ v g)
      ((gram_integrable μ v).integral_prod_left.const_mul A) hrow
  have hgg : (‖g‖ ^ 2) ^ 2 ≤
      A * (∫ x, ‖inner ℂ (v x) g‖ ^ 2 ∂μ) := by
    have hid : (∫ x, (inner ℂ (v x) g) * (starRingEnd ℂ) (F x) ∂μ) =
        ((‖g‖ ^ 2 : ℝ) : ℂ) := by
      calc
        _ = (starRingEnd ℂ) (∫ x, inner ℂ g (F x • v x) ∂μ) := by
          rw [← integral_conj]
          apply integral_congr_ae
          filter_upwards with x
          simp only [inner_smul_right, map_mul, inner_conj_symm, mul_comm]
        _ = _ := by rw [integral_inner hgi, inner_self_eq_norm_sq_to_K]; simp
    have h := GaloisForLFunctions.HTGeometry.norm_integral_mul_conj_sq_le
      (ν := μ) (v.continuous.inner continuous_const).norm.aestronglyMeasurable
      hF.norm.aestronglyMeasurable (pairing_sq_integrable μ v g)
      (pairing_sq_integrable μ v f)
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    simpa only [A, mul_comm] using h
  have hgsq : ‖g‖ ^ 2 ≤ A * Real.sqrt (continuousFrameGramEnergy μ v) := by
    have h := hgg.trans (mul_le_mul_of_nonneg_left hEg hA)
    have he : (A * Real.sqrt (continuousFrameGramEnergy μ v)) ^ 2 =
        A * (A * continuousFrameGramEnergy μ v) := by
      rw [mul_pow, Real.sq_sqrt hH]
      ring
    rw [← he] at h
    exact (sq_le_sq₀ (sq_nonneg _) (mul_nonneg hA (Real.sqrt_nonneg _))).mp h
  change A ≤ _
  by_cases hAz : A = 0
  · rw [hAz]
    positivity
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have h := hAcs.trans (mul_le_mul_of_nonneg_left hgsq (sq_nonneg _))
    have h' : A * A ≤ A * (Real.sqrt (continuousFrameGramEnergy μ v) * ‖f‖ ^ 2) := by
      nlinarith only [h]
    exact le_of_mul_le_mul_left h' hAp

omit [CompleteSpace E] in
/-- Keeping the Gram correlations never weakens the diagonal trace ceiling. -/
theorem continuousFrame_gram_le_trace (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ E) :
    Real.sqrt (continuousFrameGramEnergy μ v) ≤ ∫ x, ‖v x‖ ^ 2 ∂μ := by
  have hv := vector_sq_integrable μ v
  have hrow (x : ℝ) : (∫ y, ‖inner ℂ (v x) (v y)‖ ^ 2 ∂μ) ≤
      ‖v x‖ ^ 2 * ∫ y, ‖v y‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono
      (by simpa only [norm_inner_symm] using pairing_sq_integrable μ v (v x))
      (hv.const_mul _) (fun y => ?_)
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_inner_le_norm (𝕜 := ℂ) (v x) (v y)) 2
  have h : continuousFrameGramEnergy μ v ≤ (∫ x, ‖v x‖ ^ 2 ∂μ) ^ 2 := by
    unfold continuousFrameGramEnergy
    calc
      _ ≤ ∫ x, ‖v x‖ ^ 2 * (∫ y, ‖v y‖ ^ 2 ∂μ) ∂μ :=
        integral_mono (gram_integrable μ v).integral_prod_left (hv.mul_const _) hrow
      _ = _ := by rw [integral_mul_const]; ring
  exact (Real.sqrt_le_left (integral_nonneg fun _ => sq_nonneg _)).mpr h

/-- Integrated two-vector Gram determinant, measuring the loss of collinearity. -/
def continuousFrameGramDefect (μ : Measure ℝ) (v : ℝ →ᵇ E) : ℝ :=
  ∫ x, ∫ y, (‖v x‖ ^ 2 * ‖v y‖ ^ 2 - ‖inner ℂ (v x) (v y)‖ ^ 2) ∂μ ∂μ

omit [CompleteSpace E] in
theorem continuousFrameGramDefect_nonneg (μ : Measure ℝ) (v : ℝ →ᵇ E) :
    0 ≤ continuousFrameGramDefect μ v := by
  apply integral_nonneg
  intro x
  apply integral_nonneg
  intro y
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℂ) (v x) (v y)) 2
  rw [mul_pow] at h
  exact sub_nonneg.mpr h

omit [CompleteSpace E] in
/-- The exact curvature discount from the diagonal trace, including every cross term. -/
theorem continuousFrame_gram_add_defect (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ →ᵇ E) :
    continuousFrameGramEnergy μ v + continuousFrameGramDefect μ v =
      (∫ x, ‖v x‖ ^ 2 ∂μ) ^ 2 := by
  have hv := vector_sq_integrable μ v
  have hrow (x : ℝ) :
      (∫ y, (‖v x‖ ^ 2 * ‖v y‖ ^ 2 - ‖inner ℂ (v x) (v y)‖ ^ 2) ∂μ) =
        ‖v x‖ ^ 2 * (∫ y, ‖v y‖ ^ 2 ∂μ) -
          (∫ y, ‖inner ℂ (v x) (v y)‖ ^ 2 ∂μ) := by
    rw [integral_sub (hv.const_mul _) (by
      simpa only [norm_inner_symm] using pairing_sq_integrable μ v (v x)), integral_const_mul]
  unfold continuousFrameGramDefect continuousFrameGramEnergy
  simp_rw [hrow]
  rw [integral_sub (hv.mul_const _) (gram_integrable μ v).integral_prod_left,
    integral_mul_const]
  ring

end HTGeometry
