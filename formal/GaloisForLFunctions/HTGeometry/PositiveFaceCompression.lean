import Mathlib

/-!
# Positive-face compression of divergent Gram pencils

A positive Gram pencil `t B*B + D*D` can remain finite under a fixed carrier `J` without
normalization or subtraction.  This happens exactly when the carrier lies in the kernel of the
leading feature map.  On that face the complete subleading Gram survives unchanged.

This module formalizes the positive survivor of the failed regularization-trilemma conjecture.  No
Riemann-hypothesis premise or divisor specialization occurs.
-/

namespace GaloisForLFunctions.HTGeometry

section PositiveFaceCompression

variable {H Y U : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Observed energy of the positive Gram pencil with leading feature `B`, subleading feature `D`,
and fixed carrier `J`. -/
def positiveFacePencilEnergy (B D : H →L[ℝ] U) (J : Y →L[ℝ] H)
    (t : ℝ) (y : Y) : ℝ :=
  t * ‖B (J y)‖ ^ 2 + ‖D (J y)‖ ^ 2

/-- Pointwise finiteness of every nonnegative ray of the compressed positive pencil. -/
def PositiveFacePencilPointwiseBounded (B D : H →L[ℝ] U) (J : Y →L[ℝ] H) : Prop :=
  ∀ y, ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → positiveFacePencilEnergy B D J t y ≤ M

/-- **Positive-face compression classification.**  A fixed carrier makes every observed positive
pencil ray finite exactly when the leading feature vanishes on that carrier. -/
theorem positiveFacePencil_pointwiseBounded_iff_comp_eq_zero
    (B D : H →L[ℝ] U) (J : Y →L[ℝ] H) :
    PositiveFacePencilPointwiseBounded B D J ↔ B.comp J = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.comp_apply, zero_apply]
    by_contra hne
    have ha : 0 < ‖B (J y)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    obtain ⟨M, hM⟩ := h y
    let t : ℝ := (|M| + 1) / ‖B (J y)‖ ^ 2
    have ht : 0 ≤ t := div_nonneg (by positivity) ha.le
    have hta : t * ‖B (J y)‖ ^ 2 = |M| + 1 := by
      dsimp [t]
      field_simp [ne_of_gt ha]
    have hb := hM t ht
    rw [positiveFacePencilEnergy, hta] at hb
    nlinarith [le_abs_self M, sq_nonneg ‖D (J y)‖]
  · intro hcomp y
    refine ⟨‖D (J y)‖ ^ 2, ?_⟩
    intro t ht
    have hzero : B (J y) = 0 := by
      change (B.comp J) y = 0
      rw [hcomp]
      rfl
    simp [positiveFacePencilEnergy, hzero]

/-- On an admitted positive face, the full subleading energy survives unchanged at every scale. -/
theorem positiveFacePencilEnergy_eq_subleading_of_comp_eq_zero
    (B D : H →L[ℝ] U) (J : Y →L[ℝ] H)
    (h : B.comp J = 0) (t : ℝ) (y : Y) :
    positiveFacePencilEnergy B D J t y = ‖D (J y)‖ ^ 2 := by
  have hzero : B (J y) = 0 := by
    change (B.comp J) y = 0
    rw [h]
    rfl
  simp [positiveFacePencilEnergy, hzero]

/-- Simultaneous finiteness is exactly simultaneous membership in every leading kernel. -/
theorem positiveFacePencil_family_pointwiseBounded_iff
    {I : Type*} (B D : I → H →L[ℝ] U) (J : Y →L[ℝ] H) :
    (∀ i, PositiveFacePencilPointwiseBounded (B i) (D i) J) ↔
      ∀ i, (B i).comp J = 0 := by
  simp only [positiveFacePencil_pointwiseBounded_iff_comp_eq_zero]

/-- If the leading feature is injective, no nonzero fixed carrier can make the pencil finite. -/
theorem positiveFacePencil_injective_leading_forces_zero_carrier
    (B D : H →L[ℝ] U) (J : Y →L[ℝ] H)
    (hB : Function.Injective B) (h : PositiveFacePencilPointwiseBounded B D J) :
    J = 0 := by
  have hcomp : B.comp J = 0 :=
    (positiveFacePencil_pointwiseBounded_iff_comp_eq_zero B D J).mp h
  apply ContinuousLinearMap.ext
  intro y
  apply hB
  have hzero : B (J y) = 0 := by
    change (B.comp J) y = 0
    rw [hcomp]
    rfl
  simpa using hzero

/-- The concrete diagonal positive pencil used to falsify the three-branch regularization law. -/
def diagonalPositivePencilEnergy (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  t * x.1 ^ 2 + x.2 ^ 2

/-- Compression to the second coordinate retains its full subleading energy at every scale. -/
theorem diagonalPositivePencil_secondFace (t y : ℝ) :
    diagonalPositivePencilEnergy t (0, y) = y ^ 2 := by
  simp [diagonalPositivePencilEnergy]

/-- The same positive pencil diverges along its leading first-coordinate ray. -/
theorem diagonalPositivePencil_firstRay_unbounded (M : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ M < diagonalPositivePencilEnergy t (1, 0) := by
  refine ⟨|M| + 1, by positivity, ?_⟩
  have hM : M < |M| + 1 := by linarith [le_abs_self M]
  simpa [diagonalPositivePencilEnergy] using hM

/-- Capstone: the diagonal source diverges in one positive direction while a proper positive face
retains a nonzero subleading datum exactly. -/
theorem positiveFaceCompression_fourthBranch :
    (∀ t : ℝ, diagonalPositivePencilEnergy t (0, 1) = 1) ∧
      (∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < diagonalPositivePencilEnergy t (1, 0)) := by
  constructor
  · intro t
    simpa using diagonalPositivePencil_secondFace t 1
  · exact diagonalPositivePencil_firstRay_unbounded

end PositiveFaceCompression

end GaloisForLFunctions.HTGeometry
