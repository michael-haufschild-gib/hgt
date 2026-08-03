import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Infinite-horizon normalization law

Let `h` be a nowhere-zero weight on an infinite index set.  The inverse
weight normalization `z i / h i` sends the residual ray `c • h` to the
constant family `c`.  Hence the inverse-weight square-summability domain
meets that ray only at zero.

This elementary law is independent of a particular arithmetic model.  It is
the common functional-analytic core of rare-event whitening divergence and
inverse-horizon nonadmission of a nonzero residual source ray.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Square-summability after coefficientwise division by a horizon. -/
def InverseHorizonSquareSummable
    {I : Type*} (h z : I -> ℂ) : Prop :=
  Summable fun i => ‖z i / h i‖ ^ 2

/-- Weighted square-summability after coefficientwise division by a
horizon. -/
def WeightedInverseHorizonSquareSummable
    {I : Type*} (w : I -> ℝ) (h z : I -> ℂ) : Prop :=
  Summable fun i => w i * ‖z i / h i‖ ^ 2

/-- Inverse-horizon normalization sends a nowhere-zero weighted ray to the
corresponding constant family. -/
theorem inverseHorizon_normalizes_ray_to_constant
    {I : Type*} (h : I -> ℂ) (hzero : forall i, h i ≠ 0) (c : ℂ) :
    (fun i => ‖(c * h i) / h i‖ ^ 2) =
      (fun _ : I => ‖c‖ ^ 2) := by
  funext i
  rw [mul_div_cancel_right₀ c (hzero i)]

/-- **Infinite-horizon normalization law.**  On an infinite index set, the
inverse-horizon square-summability domain meets every nowhere-zero horizon
ray only at zero. -/
theorem inverseHorizonSquareSummable_ray_iff
    {I : Type*} [Infinite I]
    (h : I -> ℂ) (hzero : forall i, h i ≠ 0) (c : ℂ) :
    InverseHorizonSquareSummable h (fun i => c * h i) ↔ c = 0 := by
  rw [InverseHorizonSquareSummable,
    inverseHorizon_normalizes_ray_to_constant h hzero c,
    summable_const_iff]
  simp

/-- A nonzero scalar multiple of a nowhere-zero infinite horizon is never
inverse-horizon square-summable. -/
theorem not_inverseHorizonSquareSummable_ray_of_ne
    {I : Type*} [Infinite I]
    (h : I -> ℂ) (hzero : forall i, h i ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    ¬ InverseHorizonSquareSummable h (fun i => c * h i) := by
  rw [inverseHorizonSquareSummable_ray_iff h hzero c]
  exact hc

/-- **Complete diagonal-weight dichotomy.**  A diagonal inverse-horizon
domain admits a nonzero residual ray exactly when its weight is summable.
Consequently a summable weight admits the whole ray and selects nothing,
while a nonsummable weight admits only zero. -/
theorem weightedInverseHorizonSquareSummable_ray_iff
    {I : Type*} (w : I -> ℝ)
    (h : I -> ℂ) (hzero : forall i, h i ≠ 0) (c : ℂ) :
    WeightedInverseHorizonSquareSummable w h (fun i => c * h i) ↔
      c = 0 ∨ Summable w := by
  rw [WeightedInverseHorizonSquareSummable]
  have hfun :
      (fun i => w i * ‖(c * h i) / h i‖ ^ 2) =
        (fun i => w i * ‖c‖ ^ 2) := by
    funext i
    rw [mul_div_cancel_right₀ c (hzero i)]
  rw [hfun]
  constructor
  · intro hsum
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have hnorm : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
      have hdiv := hsum.div_const (‖c‖ ^ 2)
      simpa [mul_div_cancel_right₀ _ hnorm] using hdiv
  · rintro (rfl | hw)
    · simp
    · exact hw.mul_right _

/-- A nonsummable diagonal weight meets a nowhere-zero horizon ray only at
zero. -/
theorem weightedInverseHorizonSquareSummable_ray_iff_of_not_summable
    {I : Type*} {w : I -> ℝ} (hw : ¬ Summable w)
    (h : I -> ℂ) (hzero : forall i, h i ≠ 0) (c : ℂ) :
    WeightedInverseHorizonSquareSummable w h (fun i => c * h i) ↔
      c = 0 := by
  rw [weightedInverseHorizonSquareSummable_ray_iff w h hzero c,
    or_iff_left hw]

end

end GaloisForLFunctions.HTGeometry
