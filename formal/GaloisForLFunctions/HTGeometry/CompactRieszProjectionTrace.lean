import GaloisForLFunctions.HTGeometry.CompactOperatorGeneralSpectrum
import GaloisForLFunctions.HTGeometry.RieszProjectionFiniteSection
import GaloisForLFunctions.HTGeometry.RieszProjectionSpectral
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite-rank Riesz blocks of compact operators

Every nonzero spectral point of a compact complex operator admits a circular Riesz projection
whose range is finite dimensional and equals the full maximal generalized eigenspace.  This file
supplies the compact-idempotent argument needed to remove the finite-rank premise from the local
Riesz theory.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- A compact idempotent continuous operator has finite-dimensional range. -/
theorem finiteDimensional_range_of_isCompactOperator_of_isIdempotentElem
    {P : H →L[ℂ] H} (hPcompact : IsCompactOperator P) (hP : IsIdempotentElem P) :
    FiniteDimensional ℂ (LinearMap.range (P : H →ₗ[ℂ] H)) := by
  let W : Submodule ℂ H := LinearMap.range (P : H →ₗ[ℂ] H)
  have hWclosed : IsClosed (W : Set H) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hP
  letI : CompleteSpace W := hWclosed.completeSpace_coe
  have hmaps : ∀ x ∈ W, (P : H →ₗ[ℂ] H) x ∈ W := by
    intro x hx
    exact ⟨x, rfl⟩
  have hrestrictCompact : IsCompactOperator ((P : H →ₗ[ℂ] H).restrict hmaps) :=
    hPcompact.restrict hmaps hWclosed
  have hrestrict : (P : H →ₗ[ℂ] H).restrict hmaps = LinearMap.id := by
    ext x
    obtain ⟨y, hy⟩ := x.2
    have hmul : P (P y) = P y := by
      have := congrArg (fun Q : H →L[ℂ] H => Q y) hP
      simpa only [mul_apply_eq_comp] using this
    change P (x : H) = x
    rw [← hy]
    exact hmul
  apply FiniteDimensional.of_isCompactOperator_id
  simpa [hrestrict] using hrestrictCompact

/-- Every nonzero spectral point of a compact operator has a finite-rank circular Riesz
projection whose range is exactly its maximal generalized eigenspace. -/
theorem exists_rieszProjection_range_eq_maxGenEigenspace_of_isCompactOperator
    {T : H →L[ℂ] H} (hT : IsCompactOperator T) {mu : ℂ}
    (hmu : mu ∈ spectrum ℂ T) (hmu0 : mu ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < ‖mu‖ ∧
      (∀ lam ∈ sphere mu r, lam ∈ resolventSet ℂ T) ∧
      rieszProjection T mu r * rieszProjection T mu r = rieszProjection T mu r ∧
      FiniteDimensional ℂ
        (LinearMap.range ((rieszProjection T mu r : H →L[ℂ] H) : H →ₗ[ℂ] H)) ∧
      LinearMap.range ((rieszProjection T mu r : H →L[ℂ] H) : H →ₗ[ℂ] H) =
        Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) mu := by
  obtain ⟨R, hR, hRmu, hIso⟩ :=
    exists_isolating_closedBall_nonzero_spectrum_general hT hmu hmu0
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hrmu : r < ‖mu‖ := lt_trans hrR hRmu
  have hres : ∀ lam ∈ sphere mu r, lam ∈ resolventSet ℂ T := by
    intro lam hlam
    apply hIso lam (closedBall_subset_closedBall hrR.le (sphere_subset_closedBall hlam))
    intro hlamMu
    subst lam
    exact hr.ne' (by simpa using hlam.symm)
  have hannulus : ∀ lam ∈ closedBall mu R \ ball mu r,
      lam ∈ resolventSet ℂ T := by
    intro lam hlam
    apply hIso lam hlam.1
    intro hlamMu
    subst lam
    exact hlam.2 (mem_ball_self hr)
  have hIdem : rieszProjection T mu r * rieszProjection T mu r =
      rieszProjection T mu r := rieszProjection_mul_self T hr hrR hannulus
  have hzero : (0 : ℂ) ∉ closedBall mu r := by
    intro hzeroMem
    have hd := mem_closedBall.mp hzeroMem
    rw [Complex.dist_eq, zero_sub, norm_neg] at hd
    exact (not_le_of_gt hrmu) hd
  have hfactor := rieszProjection_eq_mul T hr.le hres hzero
  have hPcompact : IsCompactOperator (rieszProjection T mu r : H →L[ℂ] H) := by
    rw [hfactor]
    exact hT.comp_clm _
  have hfin : FiniteDimensional ℂ
      (LinearMap.range ((rieszProjection T mu r : H →L[ℂ] H) : H →ₗ[ℂ] H)) :=
    finiteDimensional_range_of_isCompactOperator_of_isIdempotentElem hPcompact
      (by rw [isIdempotentElem_iff]; exact hIdem)
  have hsep : ∀ nu : ℂ, nu ≠ mu →
      (∃ v : H, v ≠ 0 ∧ T v = nu • v) → nu ∉ closedBall mu r := by
    intro nu hnumu hnuEig hnuBall
    have hnuRes := hIso nu (closedBall_subset_closedBall hrR.le hnuBall) hnumu
    obtain ⟨v, hv, hTv⟩ := hnuEig
    exact not_mem_resolventSet_of_eigenvector hv hTv hnuRes
  have hrange := range_rieszProjection_eq_maxGenEigenspace hr.le hres
    (mem_ball_self hr) hIdem hsep hfin
  exact ⟨r, hr, hrmu, hres, hIdem, hfin, hrange⟩

end

end GaloisForLFunctions.HTGeometry
