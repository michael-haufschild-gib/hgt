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

variable {𝕜 H Y U : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- Observed energy of the positive Gram pencil with leading feature `B`, subleading feature `D`,
and fixed carrier `J`. -/
def positiveFacePencilEnergy (B D : H →L[𝕜] U) (J : Y →L[𝕜] H)
    (t : ℝ) (y : Y) : ℝ :=
  t * ‖B (J y)‖ ^ (2 : ℕ) + ‖D (J y)‖ ^ (2 : ℕ)

/-- Pointwise finiteness of every nonnegative ray of the compressed positive pencil. -/
def PositiveFacePencilPointwiseBounded (B D : H →L[𝕜] U) (J : Y →L[𝕜] H) : Prop :=
  ∀ y, ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → positiveFacePencilEnergy B D J t y ≤ M

/-- **Positive-face compression classification.**  A fixed carrier makes every observed positive
pencil ray finite exactly when the leading feature vanishes on that carrier. -/
theorem positiveFacePencil_pointwiseBounded_iff_comp_eq_zero
    (B D : H →L[𝕜] U) (J : Y →L[𝕜] H) :
    PositiveFacePencilPointwiseBounded B D J ↔ B.comp J = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.comp_apply, zero_apply]
    by_contra hne
    have ha : 0 < ‖B (J y)‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hne)
    obtain ⟨M, hM⟩ := h y
    let t : ℝ := (|M| + 1) / ‖B (J y)‖ ^ (2 : ℕ)
    have ht : 0 ≤ t := div_nonneg (by positivity) ha.le
    have hta : t * ‖B (J y)‖ ^ (2 : ℕ) = |M| + 1 := by
      dsimp [t]
      field_simp [ne_of_gt ha]
    have hb := hM t ht
    rw [positiveFacePencilEnergy, hta] at hb
    nlinarith [le_abs_self M, sq_nonneg ‖D (J y)‖]
  · intro hcomp y
    refine ⟨‖D (J y)‖ ^ (2 : ℕ), ?_⟩
    intro t ht
    have hzero : B (J y) = 0 := by
      change (B.comp J) y = 0
      rw [hcomp]
      rfl
    simp [positiveFacePencilEnergy, hzero]

/-- On an admitted positive face, the full subleading energy survives unchanged at every scale. -/
theorem positiveFacePencilEnergy_eq_subleading_of_comp_eq_zero
    (B D : H →L[𝕜] U) (J : Y →L[𝕜] H)
    (h : B.comp J = 0) (t : ℝ) (y : Y) :
    positiveFacePencilEnergy B D J t y = ‖D (J y)‖ ^ (2 : ℕ) := by
  have hzero : B (J y) = 0 := by
    change (B.comp J) y = 0
    rw [h]
    rfl
  simp [positiveFacePencilEnergy, hzero]

/-- Vanishing of the leading composite is exactly containment of the carrier range in the
leading kernel. -/
theorem positiveFacePencil_comp_eq_zero_iff_range_le_ker
    (B : H →L[𝕜] U) (J : Y →L[𝕜] H) :
    B.comp J = 0 ↔
      LinearMap.range (J : Y →ₗ[𝕜] H) ≤ LinearMap.ker (B : H →ₗ[𝕜] U) := by
  constructor
  · intro h _ hx
    obtain ⟨y, rfl⟩ := hx
    change B (J y) = 0
    have hy := congrArg (fun T : Y →L[𝕜] U => T y) h
    simpa using hy
  · intro h
    apply ContinuousLinearMap.ext
    intro y
    exact h ⟨y, rfl⟩

/-- Fixed positive-face boundedness is exactly containment of the carrier range in the leading
kernel. -/
theorem positiveFacePencil_pointwiseBounded_iff_range_le_ker
    (B D : H →L[𝕜] U) (J : Y →L[𝕜] H) :
    PositiveFacePencilPointwiseBounded B D J ↔
      LinearMap.range (J : Y →ₗ[𝕜] H) ≤ LinearMap.ker (B : H →ₗ[𝕜] U) := by
  rw [positiveFacePencil_pointwiseBounded_iff_comp_eq_zero,
    positiveFacePencil_comp_eq_zero_iff_range_le_ker]

/-- On the leading null face the retained energy is nonzero exactly when the complete subleading
composite is nonzero. -/
theorem positiveFacePencilEnergy_nonzero_iff_subleading_comp_ne_zero
    (B D : H →L[𝕜] U) (J : Y →L[𝕜] H) (h : B.comp J = 0) (t : ℝ) :
    (fun y => positiveFacePencilEnergy B D J t y) ≠ 0 ↔ D.comp J ≠ 0 := by
  apply not_congr
  constructor
  · intro henergy
    apply ContinuousLinearMap.ext
    intro y
    have hy := congrFun henergy y
    rw [positiveFacePencilEnergy_eq_subleading_of_comp_eq_zero B D J h t y] at hy
    simpa using hy
  · intro hcomp
    funext y
    rw [positiveFacePencilEnergy_eq_subleading_of_comp_eq_zero B D J h t y]
    have hy := congrArg (fun T : Y →L[𝕜] U => T y) hcomp
    simpa using hy

/-- Simultaneous finiteness is exactly simultaneous membership in every leading kernel. -/
theorem positiveFacePencil_family_pointwiseBounded_iff
    {I : Type*} (B D : I → H →L[𝕜] U) (J : Y →L[𝕜] H) :
    (∀ i, PositiveFacePencilPointwiseBounded (B i) (D i) J) ↔
      ∀ i, (B i).comp J = 0 := by
  simp only [positiveFacePencil_pointwiseBounded_iff_comp_eq_zero]

/-- If the leading feature is injective, no nonzero fixed carrier can make the pencil finite. -/
theorem positiveFacePencil_injective_leading_forces_zero_carrier
    (B D : H →L[𝕜] U) (J : Y →L[𝕜] H)
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
  t * x.1 ^ (2 : ℕ) + x.2 ^ (2 : ℕ)

/-- Compression to the second coordinate retains its full subleading energy at every scale. -/
theorem diagonalPositivePencil_secondFace (t y : ℝ) :
    diagonalPositivePencilEnergy t (0, y) = y ^ (2 : ℕ) := by
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

section PositiveFaceFormationLaplacian

variable {𝕜 H Y : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {I : Type*} [Fintype I]
variable {U : I → Type*}
variable [∀ i, NormedAddCommGroup (U i)] [∀ i, InnerProductSpace 𝕜 (U i)]
variable [∀ i, CompleteSpace (U i)]

/-- Heterogeneous finite analysis map into the Hilbert direct sum of leading feature spaces. -/
noncomputable def positiveFaceAnalysisMapL2 (B : ∀ i, H →L[𝕜] U i) :
    H →L[𝕜] PiLp 2 U :=
  (PiLp.continuousLinearEquiv 2 𝕜 U).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi B

omit [CompleteSpace H] [Fintype I] [∀ i, CompleteSpace (U i)] in
@[simp] theorem positiveFaceAnalysisMapL2_apply
    (B : ∀ i, H →L[𝕜] U i) (x : H) (i : I) :
    positiveFaceAnalysisMapL2 B x i = B i x := rfl

omit [CompleteSpace H] [Fintype I] [∀ i, CompleteSpace (U i)] in
/-- Kernel of the analysis map is the common leading null face. -/
theorem ker_positiveFaceAnalysisMapL2 (B : ∀ i, H →L[𝕜] U i) :
    LinearMap.ker (positiveFaceAnalysisMapL2 B : H →ₗ[𝕜] PiLp 2 U) =
      ⨅ i, LinearMap.ker (B i : H →ₗ[𝕜] U i) := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_iInf]
    intro i
    rw [LinearMap.mem_ker] at hx ⊢
    have hi := congrArg (fun z : PiLp 2 U => z i) hx
    simpa using hi
  · intro hx
    rw [Submodule.mem_iInf] at hx
    rw [LinearMap.mem_ker]
    ext i
    exact hx i

omit [CompleteSpace H] [Fintype I] [∀ i, CompleteSpace (U i)] in
/-- Simultaneous boundedness for heterogeneous leading spaces is exactly containment in the
kernel of their joint analysis map. -/
theorem positiveFacePencil_heterogeneous_family_pointwiseBounded_iff
    (B D : ∀ i, H →L[𝕜] U i) (J : Y →L[𝕜] H) :
    (∀ i, PositiveFacePencilPointwiseBounded (B i) (D i) J) ↔
      LinearMap.range (J : Y →ₗ[𝕜] H) ≤
        LinearMap.ker (positiveFaceAnalysisMapL2 B : H →ₗ[𝕜] PiLp 2 U) := by
  rw [ker_positiveFaceAnalysisMapL2]
  constructor
  · intro h x hx
    rw [Submodule.mem_iInf]
    intro i
    exact (positiveFacePencil_pointwiseBounded_iff_range_le_ker (B i) (D i) J).mp (h i) hx
  · intro h i
    rw [positiveFacePencil_pointwiseBounded_iff_range_le_ker]
    intro x hx
    exact (Submodule.mem_iInf _).mp (h hx) i

omit [CompleteSpace H] [Fintype I] [∀ i, CompleteSpace (U i)] in
/-- On the common leading face every heterogeneous subleading Gram energy survives unchanged. -/
theorem positiveFacePencil_heterogeneous_family_energy_eq_subleading
    (B D : ∀ i, H →L[𝕜] U i) (J : Y →L[𝕜] H)
    (h : LinearMap.range (J : Y →ₗ[𝕜] H) ≤
      LinearMap.ker (positiveFaceAnalysisMapL2 B : H →ₗ[𝕜] PiLp 2 U))
    (i : I) (t : ℝ) (y : Y) :
    positiveFacePencilEnergy (B i) (D i) J t y = ‖D i (J y)‖ ^ (2 : ℕ) := by
  apply positiveFacePencilEnergy_eq_subleading_of_comp_eq_zero
  rw [positiveFacePencil_comp_eq_zero_iff_range_le_ker]
  intro x hx
  rw [ker_positiveFaceAnalysisMapL2] at h
  exact (Submodule.mem_iInf _).mp (h hx) i

/-- Positive formation Laplacian of a heterogeneous finite feature family. -/
noncomputable def positiveFaceFormationLaplacian (B : ∀ i, H →L[𝕜] U i) : H →L[𝕜] H :=
  ∑ i, (B i).adjoint ∘L B i

theorem positiveFaceFormationLaplacian_apply
    (B : ∀ i, H →L[𝕜] U i) (x : H) :
    positiveFaceFormationLaplacian B x = ∑ i, (B i).adjoint (B i x) := by
  simp [positiveFaceFormationLaplacian, sum_apply]

/-- Formation Laplacian is the Gram square of the joint analysis map. -/
theorem positiveFaceFormationLaplacian_eq_adjoint_comp_analysis
    (B : ∀ i, H →L[𝕜] U i) :
    positiveFaceFormationLaplacian B =
      (positiveFaceAnalysisMapL2 B).adjoint ∘L positiveFaceAnalysisMapL2 B := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right (𝕜 := 𝕜)
  intro y
  rw [positiveFaceFormationLaplacian_apply, sum_inner,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left (positiveFaceAnalysisMapL2 B) y
      (positiveFaceAnalysisMapL2 B x),
    PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ =>
    ContinuousLinearMap.adjoint_inner_left (B i) y (B i x)

/-- Exact radical identity: the formation Laplacian, analysis map, and common leading face have
the same kernel. -/
theorem ker_positiveFaceFormationLaplacian (B : ∀ i, H →L[𝕜] U i) :
    LinearMap.ker (positiveFaceFormationLaplacian B : H →ₗ[𝕜] H) =
      ⨅ i, LinearMap.ker (B i : H →ₗ[𝕜] U i) := by
  rw [positiveFaceFormationLaplacian_eq_adjoint_comp_analysis,
    ContinuousLinearMap.ker_adjoint_comp_self, ker_positiveFaceAnalysisMapL2]

end PositiveFaceFormationLaplacian

end GaloisForLFunctions.HTGeometry
