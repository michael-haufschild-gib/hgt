import GaloisForLFunctions.RHTower.BurnolSoninContinuousEvaluation

/-!
# Aperture monotonicity of the extended Sonine space and of nonvanishing

Shrinking the aperture weakens the constant-head condition, so the extended Sonine spaces are
decreasing in the aperture:

`a ≤ b → L_b ≤ L_a`.

Consequently the completed Mellin evaluation vector vanishes at `a` only if it vanishes at every
larger aperture: a single Sonine witness at one aperture propagates nonvanishing to all smaller
apertures.  This reduces Burnol's nonvanishing statement to the existence of one vector of one
extended Sonine space on which the completed Mellin evaluation does not vanish.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem soninHeadConstant_mono {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : SoninHeadConstant b f) : SoninHeadConstant a f := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, ?_⟩
  refine Filter.Eventually.filter_mono ?_ hc
  refine MeasureTheory.ae_mono (Measure.restrict_mono ?_ le_rfl)
  exact Ioo_subset_Ioo le_rfl hab

/-- **The extended Sonine spaces decrease in the aperture.** -/
theorem soninExtendedSpace_mono {a b : ℝ} (hab : a ≤ b) :
    soninExtendedSpace b ≤ soninExtendedSpace a := by
  intro f hf
  rw [mem_soninExtendedSpace] at hf ⊢
  exact ⟨soninHeadConstant_mono hab hf.1, soninHeadConstant_mono hab hf.2⟩

/-- The evaluation vector vanishes exactly when the completed Mellin evaluation is identically zero
on the extended Sonine space. -/
theorem burnolExtendedSoninEvaluationVector_eq_zero_iff
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a : ℝ} (ha : 0 < a) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha = 0 ↔
      ∀ f : soninExtendedSpace a,
        soninMellinEvaluation w (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) = 0 := by
  constructor
  · intro h f
    rw [← inner_burnolExtendedSoninEvaluationVector w a hlo hhi ha f, h]
    simp
  · intro h
    set k := burnolExtendedSoninEvaluationVector w a hlo hhi ha with hk
    have hkk := h k
    rw [← inner_burnolExtendedSoninEvaluationVector w a hlo hhi ha] at hkk
    have hself : ‖(inner ℂ k k : ℂ)‖ = ‖k‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg k)]
    rw [hkk, norm_zero] at hself
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hself.symm)

/-- **Nonvanishing propagates to smaller apertures.**  A Sonine witness at aperture `b` is still a
witness at every aperture `a ≤ b`. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_le
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b)
    (h : burnolExtendedSoninEvaluationVector w b hlo hhi hb ≠ 0) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 := by
  intro hzero
  apply h
  rw [burnolExtendedSoninEvaluationVector_eq_zero_iff hlo hhi hb]
  intro g
  have hg : ((g : soninExtendedSpace b) : evenSubspace) ∈ soninExtendedSpace a :=
    soninExtendedSpace_mono hab g.property
  have := (burnolExtendedSoninEvaluationVector_eq_zero_iff hlo hhi ha).mp hzero
    ⟨((g : soninExtendedSpace b) : evenSubspace), hg⟩
  exact this

/-- **Reduction of Burnol's nonvanishing to one witness.**  If some vector of the extended Sonine
space at aperture `b` has nonzero completed Mellin evaluation, then the evaluation vector is nonzero
at every aperture `a ≤ b`, hence the aperture-type limit applies there. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_witness
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (g : soninExtendedSpace b)
    (hg : soninMellinEvaluation w (((g : soninExtendedSpace b) : evenSubspace) : SoninL2) ≠ 0) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 := by
  refine burnolExtendedSoninEvaluationVector_ne_zero_of_le hlo hhi ha hb hab ?_
  intro hzero
  exact hg ((burnolExtendedSoninEvaluationVector_eq_zero_iff hlo hhi hb).mp hzero g)

end RHTower
