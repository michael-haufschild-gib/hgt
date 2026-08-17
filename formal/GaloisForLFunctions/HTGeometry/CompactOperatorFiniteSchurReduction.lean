import Mathlib

/-!
# Finite Schur reduction for compact perturbations of the identity

A compact operator on a complex Hilbert space admits one finite observation space whose invisible
kernel is a strict contraction sector.  The kernel is closed, its orthogonal complement is
finite-dimensional, and the contraction margin can be fixed at one half.

This supplies a source-independent finite Schur reduction without invoking an enumerated spectral
basis: a finite metric net of the compact image replaces spectral projection machinery.
-/

open Complex Set
open scoped ENNReal InnerProduct

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A compact endomorphism has a closed finite-codimensional sector on which its norm is strictly
less than one half of the input norm. -/
theorem exists_finiteCodimensional_strictContractionKernel_of_isCompactOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    ∃ M : Submodule ℂ E,
      IsClosed (M : Set E) ∧ FiniteDimensional ℂ Mᗮ ∧
        ∀ x ∈ M, x ≠ 0 → ‖K x‖ < (1 / 2 : ℝ) * ‖x‖ := by
  have htbClosure : TotallyBounded
      (closure (K '' Metric.closedBall (0 : E) 1)) :=
    (hK.isCompact_closure_image_closedBall 1).totallyBounded
  have htb : TotallyBounded (K '' Metric.closedBall (0 : E) 1) :=
    htbClosure.subset subset_closure
  obtain ⟨t, htfinite, hcover⟩ :=
    Metric.totallyBounded_iff.mp htb (1 / 2 : ℝ) (by norm_num)
  let V : Submodule ℂ E := Submodule.span ℂ t
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ htfinite
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let A : E →L[ℂ] V := V.orthogonalProjectionOnto ∘L K
  let M : Submodule ℂ E := A.ker
  have hMclosed : IsClosed (M : Set E) := A.isClosed_ker
  have hMperpFinite : FiniteDimensional ℂ Mᗮ := by
    have hrangeFinite : FiniteDimensional ℂ A.adjoint.range := by
      exact FiniteDimensional.of_surjective
        (A.adjoint : V →ₗ[ℂ] E).rangeRestrict
        (A.adjoint : V →ₗ[ℂ] E).surjective_rangeRestrict
    letI : FiniteDimensional ℂ A.adjoint.range := hrangeFinite
    change FiniteDimensional ℂ A.kerᗮ
    rw [A.orthogonal_ker,
      A.adjoint.range.closed_of_finiteDimensional.submodule_topologicalClosure_eq]
    exact hrangeFinite
  refine ⟨M, hMclosed, hMperpFinite, ?_⟩
  intro x hxM hxne
  have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  let y : E := ((‖x‖ : ℂ)⁻¹) • x
  have hynorm : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul]
    simp [hrpos.ne']
  have hyball : y ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hynorm]
  have hKycover := hcover
    (show K y ∈ K '' Metric.closedBall (0 : E) 1 from ⟨y, hyball, rfl⟩)
  obtain ⟨z, hzt, hKyz⟩ := Set.mem_iUnion₂.mp hKycover
  have hzV : z ∈ V := Submodule.subset_span hzt
  have hxA : A x = 0 := hxM
  have hyA : A y = 0 := by
    dsimp [y]
    rw [map_smul A ((‖x‖ : ℂ)⁻¹) x, hxA, smul_zero]
  have hproj : V.orthogonalProjectionOnto (K y) = 0 := hyA
  have hKyorth : K y ∈ Vᗮ :=
    V.orthogonalProjectionOnto_eq_zero_iff.mp hproj
  have hinner : inner ℂ (K y) z = 0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal V (K y)).mp hKyorth z hzV)
  have hpyth : ‖K y - z‖ ^ 2 = ‖K y‖ ^ 2 + ‖z‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (K y) (-z) (by simpa using hinner)
    simpa [sub_eq_add_neg, pow_two] using h
  have hnormle : ‖K y‖ ≤ ‖K y - z‖ := by
    nlinarith [sq_nonneg ‖z‖, norm_nonneg (K y), norm_nonneg (K y - z)]
  have hdist : ‖K y - z‖ < 1 / 2 := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hKyz
  have hKylt : ‖K y‖ < 1 / 2 := hnormle.trans_lt hdist
  have hscale : ‖K y‖ = ‖K x‖ / ‖x‖ := by
    dsimp [y]
    rw [map_smul K ((‖x‖ : ℂ)⁻¹) x, norm_smul]
    simp [div_eq_mul_inv, mul_comm]
  have hratio : ‖K x‖ / ‖x‖ < 1 / 2 := by
    rw [← hscale]
    exact hKylt
  exact (div_lt_iff₀ hrpos).mp hratio

end GaloisForLFunctions.HTGeometry
