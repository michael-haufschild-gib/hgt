import GaloisForLFunctions.RHTower.SuzukiAffineResolventKreinDefect
import GaloisForLFunctions.RHTower.WeldPolarizationDirection

/-!
# Xi-real/functional-equation bipolarization completes the local Suzuki Krein debt

Two corpus-fixed operations act on the real weld-generator plane: the Xi-real quarter-turn `J`
and functional-equation coefficient reflection `R`.  Twisting the same weld area by `J` gives a
positive plane form, while twisting by `R` gives the split Krein block.  Their half-sum and
half-difference are the positive and negative light-cone squares.

This module proves that the negative half-difference is the unique minimal light-cone completion
of the Krein block.  At a negative Suzuki affine-resolvent coordinate, its coefficient is exactly
the already isolated global/local weld debt.  It also identifies both light-cone carriers with
the rank-one square-zero operators `(J + R) / 2` and `(J - R) / 2`.

No RH premise, estimate, or numerical calculation is used.  Remaining analytic problem is to
identify actual common-gauge Euler--Gamma/Neumann triangles with the negative square-zero channel.
-/

open GaloisForLFunctions GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Positive-light half-sum of Xi-real and functional-equation weld polarizations. -/
def suzukiWeldPositiveLightForm (theta : ℝ) :
    LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  (2 : ℝ)⁻¹ • (weldPlaneQ theta + weldFEKreinQ theta)

/-- Negative-light half-difference.  This is the forced local completion channel. -/
def suzukiWeldNegativeLightForm (theta : ℝ) :
    LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  (2 : ℝ)⁻¹ • (weldPlaneQ theta - weldFEKreinQ theta)

/-- The positive half-sum is a literal rank-one square. -/
theorem suzukiWeldPositiveLightForm_apply (theta : ℝ) (x y : ℝ × ℝ) :
    suzukiWeldPositiveLightForm theta x y =
      theta / 2 * (x.1 + x.2) * (y.1 + y.2) := by
  simp [suzukiWeldPositiveLightForm, weldPlaneQ_apply, weldFEKreinQ_apply]
  ring

/-- The negative half-difference is the opposite rank-one square. -/
theorem suzukiWeldNegativeLightForm_apply (theta : ℝ) (x y : ℝ × ℝ) :
    suzukiWeldNegativeLightForm theta x y =
      theta / 2 * (x.1 - x.2) * (y.1 - y.2) := by
  simp [suzukiWeldNegativeLightForm, weldPlaneQ_apply, weldFEKreinQ_apply]
  ring

/-- The positive-light form is positive semidefinite for a nonnegative rate. -/
theorem suzukiWeldPositiveLightForm_self_nonneg {theta : ℝ} (htheta : 0 ≤ theta) (x : ℝ × ℝ) :
    0 ≤ suzukiWeldPositiveLightForm theta x x := by
  rw [suzukiWeldPositiveLightForm_apply]
  have : theta / 2 * (x.1 + x.2) * (x.1 + x.2) = theta / 2 * (x.1 + x.2) ^ 2 := by ring
  rw [this]
  exact mul_nonneg (div_nonneg htheta (by norm_num)) (sq_nonneg _)

/-- The negative-light form is positive semidefinite for a nonnegative rate. -/
theorem suzukiWeldNegativeLightForm_self_nonneg {theta : ℝ} (htheta : 0 ≤ theta) (x : ℝ × ℝ) :
    0 ≤ suzukiWeldNegativeLightForm theta x x := by
  rw [suzukiWeldNegativeLightForm_apply]
  have : theta / 2 * (x.1 - x.2) * (x.1 - x.2) = theta / 2 * (x.1 - x.2) ^ 2 := by ring
  rw [this]
  exact mul_nonneg (div_nonneg htheta (by norm_num)) (sq_nonneg _)

/-- **Kernel of the positive-light square.**  At a strictly positive rate the positive-light form
degenerates exactly on the negative light line. -/
theorem suzukiWeldPositiveLightForm_self_eq_zero_iff {theta : ℝ} (htheta : 0 < theta)
    (x : ℝ × ℝ) :
    suzukiWeldPositiveLightForm theta x x = 0 ↔
      x ∈ Submodule.span ℝ {((1 : ℝ), (-1 : ℝ))} := by
  rw [suzukiWeldPositiveLightForm_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have hsum : x.1 + x.2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' (by positivity)
        · exact h''
      · exact h'
    exact ⟨x.1, Prod.ext (by simp) (by simp; linarith)⟩
  · rintro ⟨a, rfl⟩
    simp

/-- **Kernel of the negative-light square.**  At a strictly positive rate the negative-light form
degenerates exactly on the positive light line. -/
theorem suzukiWeldNegativeLightForm_self_eq_zero_iff {theta : ℝ} (htheta : 0 < theta)
    (x : ℝ × ℝ) :
    suzukiWeldNegativeLightForm theta x x = 0 ↔
      x ∈ Submodule.span ℝ {((1 : ℝ), (1 : ℝ))} := by
  rw [suzukiWeldNegativeLightForm_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have hdiff : x.1 - x.2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' (by positivity)
        · exact h''
      · exact h'
    exact ⟨x.1, Prod.ext (by simp) (by simp; linarith)⟩
  · rintro ⟨a, rfl⟩
    simp

/-- Xi-real plane metric is the sum of its two light-cone squares. -/
theorem weldPlaneQ_eq_positive_add_negative (theta : ℝ) :
    weldPlaneQ theta =
      suzukiWeldPositiveLightForm theta + suzukiWeldNegativeLightForm theta := by
  apply LinearMap.BilinForm.ext
  intro x y
  rw [weldPlaneQ_apply]
  change theta * (x.1 * y.1 + x.2 * y.2) =
    suzukiWeldPositiveLightForm theta x y + suzukiWeldNegativeLightForm theta x y
  rw [suzukiWeldPositiveLightForm_apply, suzukiWeldNegativeLightForm_apply]
  ring

/-- Functional-equation Krein form is positive light square minus negative light square. -/
theorem weldFEKreinQ_eq_positive_sub_negative (theta : ℝ) :
    weldFEKreinQ theta =
      suzukiWeldPositiveLightForm theta - suzukiWeldNegativeLightForm theta := by
  apply LinearMap.BilinForm.ext
  intro x y
  rw [weldFEKreinQ_apply]
  change theta * (x.1 * y.2 + x.2 * y.1) =
    suzukiWeldPositiveLightForm theta x y - suzukiWeldNegativeLightForm theta x y
  rw [suzukiWeldPositiveLightForm_apply, suzukiWeldNegativeLightForm_apply]
  ring

/-- Critical completion pays the entire negative square and leaves the positive square exactly. -/
theorem weldFEKreinQ_add_minimalCompletion (theta : ℝ) :
    weldFEKreinQ theta + suzukiWeldNegativeLightForm theta =
      suzukiWeldPositiveLightForm theta := by
  rw [weldFEKreinQ_eq_positive_sub_negative]
  abel

/-- Completed quadratic form at a variable completion rate.  This identity exposes both sharp
light-cone tests simultaneously. -/
theorem suzukiWeld_completedQuadratic_eq
    (theta kappa : ℝ) (x : ℝ × ℝ) :
    weldFEKreinQ theta x x + suzukiWeldNegativeLightForm kappa x x =
      theta / 2 * (x.1 + x.2) ^ 2 +
        (kappa - theta) / 2 * (x.1 - x.2) ^ 2 := by
  rw [weldFEKreinQ_apply, suzukiWeldNegativeLightForm_apply]
  ring

/-- Nonnegativity of a Krein block completed only in its forced negative-light direction. -/
def SuzukiWeldCompletedNonnegative (theta kappa : ℝ) : Prop :=
  ∀ x : ℝ × ℝ,
    0 ≤ weldFEKreinQ theta x x + suzukiWeldNegativeLightForm kappa x x

/-- **Sharp local completion law.**  Every direction is nonnegative exactly when the positive
rate is nonnegative and the completion coefficient pays at least the entire negative rate. -/
theorem suzukiWeldCompletedNonnegative_iff (theta kappa : ℝ) :
    SuzukiWeldCompletedNonnegative theta kappa ↔ 0 ≤ theta ∧ theta ≤ kappa := by
  constructor
  · intro h
    have hpos := h ((1 : ℝ), (1 : ℝ))
    have hneg := h ((1 : ℝ), (-1 : ℝ))
    rw [suzukiWeld_completedQuadratic_eq] at hpos hneg
    norm_num at hpos hneg
    constructor <;> linarith
  · rintro ⟨htheta, hkappa⟩ x
    rw [suzukiWeld_completedQuadratic_eq]
    have hplus : 0 ≤ theta / 2 * (x.1 + x.2) ^ 2 :=
      mul_nonneg (div_nonneg htheta (by norm_num)) (sq_nonneg _)
    have hminus : 0 ≤ (kappa - theta) / 2 * (x.1 - x.2) ^ 2 :=
      mul_nonneg (div_nonneg (sub_nonneg.mpr hkappa) (by norm_num)) (sq_nonneg _)
    exact add_nonneg hplus hminus

/-- **Unique minimal completion rate.**  For a nonnegative positive-light rate, that same rate is
the least admissible completion coefficient, not merely a sufficient one. -/
theorem suzukiWeldCompletedNonnegative_isLeast {theta : ℝ} (htheta : 0 ≤ theta) :
    IsLeast {kappa : ℝ | SuzukiWeldCompletedNonnegative theta kappa} theta :=
  ⟨(suzukiWeldCompletedNonnegative_iff theta theta).mpr ⟨htheta, le_rfl⟩,
    fun _ hk => ((suzukiWeldCompletedNonnegative_iff theta _).mp hk).2⟩

/-- Positive-light square-zero triangle direction `(J + R) / 2`. -/
def suzukiWeldPositiveTriangleLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (2 : ℝ)⁻¹ • (planeJ + weldFEReflectionLinear)

/-- Negative-light square-zero triangle direction `(J - R) / 2`. -/
def suzukiWeldNegativeTriangleLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (2 : ℝ)⁻¹ • (planeJ - weldFEReflectionLinear)

/-- Xi-real quarter-turn and functional-equation reflection anticommute. -/
theorem planeJ_comp_weldFEReflectionLinear_eq_neg :
    planeJ.comp weldFEReflectionLinear =
      -(weldFEReflectionLinear.comp planeJ) := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x₁, x₂⟩
  ext <;> simp [planeJ, weldFEReflectionLinear, LinearMap.comp_apply]

/-- Positive-light triangle direction is square-zero. -/
theorem suzukiWeldPositiveTriangleLinear_sq :
    suzukiWeldPositiveTriangleLinear.comp suzukiWeldPositiveTriangleLinear = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x₁, x₂⟩
  ext <;>
    simp [suzukiWeldPositiveTriangleLinear, planeJ, weldFEReflectionLinear,
      LinearMap.comp_apply] <;>
    ring

/-- Negative-light triangle direction is square-zero. -/
theorem suzukiWeldNegativeTriangleLinear_sq :
    suzukiWeldNegativeTriangleLinear.comp suzukiWeldNegativeTriangleLinear = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x₁, x₂⟩
  ext <;>
    simp [suzukiWeldNegativeTriangleLinear, planeJ, weldFEReflectionLinear,
      LinearMap.comp_apply] <;>
    ring

/-- Positive light square is the area twist by the positive square-zero triangle. -/
theorem suzukiWeldPositiveLightForm_eq_triangleTwist (theta : ℝ) :
    suzukiWeldPositiveLightForm theta =
      (weldAreaForm theta).compl₂ suzukiWeldPositiveTriangleLinear := by
  apply LinearMap.BilinForm.ext
  intro x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [suzukiWeldPositiveLightForm_apply, suzukiWeldPositiveTriangleLinear,
    weldAreaForm, planeJ, weldFEReflectionLinear, LinearMap.compl₂_apply]
  ring

/-- Negative completion square is the area twist by the negative square-zero triangle. -/
theorem suzukiWeldNegativeLightForm_eq_triangleTwist (theta : ℝ) :
    suzukiWeldNegativeLightForm theta =
      (weldAreaForm theta).compl₂ suzukiWeldNegativeTriangleLinear := by
  apply LinearMap.BilinForm.ext
  intro x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [suzukiWeldNegativeLightForm_apply, suzukiWeldNegativeTriangleLinear,
    weldAreaForm, planeJ, weldFEReflectionLinear, LinearMap.compl₂_apply]
  ring

/-- Exact positive debt rate forced by a negative affine-resolvent spectral coordinate. -/
def suzukiNegativeNodeWeldRate (alpha beta t : ℝ) : ℝ :=
  -suzukiAffineResolventKreinDefect alpha beta t

/-- Source-relevant negative coordinate gives a strictly positive weld completion rate. -/
theorem suzukiNegativeNodeWeldRate_pos
    {alpha beta t : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (htneg : t < 0) :
    0 < suzukiNegativeNodeWeldRate alpha beta t := by
  exact suzukiNegativeSpectralNode_compensationDeficit_pos hab hb0 hbt htneg

/-- At a negative Suzuki spectral node, every-direction completion is equivalent to paying at
least the exact affine-resolvent debt. -/
theorem suzukiNegativeNodeWeldCompletion_iff
    {alpha beta t kappa : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (htneg : t < 0) :
    SuzukiWeldCompletedNonnegative (suzukiNegativeNodeWeldRate alpha beta t) kappa ↔
      suzukiNegativeNodeWeldRate alpha beta t ≤ kappa := by
  rw [suzukiWeldCompletedNonnegative_iff]
  simp [le_of_lt (suzukiNegativeNodeWeldRate_pos hab hb0 hbt htneg)]

/-- The exact affine-resolvent debt is sufficient; the preceding iff proves it is also minimal. -/
theorem suzukiNegativeNodeWeldCompletion_minimal
    {alpha beta t : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (htneg : t < 0) :
    SuzukiWeldCompletedNonnegative
      (suzukiNegativeNodeWeldRate alpha beta t)
      (suzukiNegativeNodeWeldRate alpha beta t) := by
  rw [suzukiNegativeNodeWeldCompletion_iff hab hb0 hbt htneg]

end

end RHTower
