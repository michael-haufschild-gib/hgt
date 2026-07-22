import GaloisForLFunctions.RHTower.HardyTitchmarshSourceTransport
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# Exact unitary rigidity of symmetric Sonin aperture

The exact Sonin projection correction has squared Hilbert--Schmidt norm `8 a^2`.  This module
proves the required general unitary-invariance bridge and obtains a complete classification:
positive symmetric Sonin corrections are unitarily equivalent exactly when their apertures are
equal.  Thus aperture is not a removable unitary gauge.
-/

noncomputable section

set_option maxHeartbeats 3000000

open scoped InnerProduct InnerProductSpace

namespace RHTower

open ContinuousLinearMap

section UnitaryHilbertSchmidt

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Unitary conjugacy preserves the Hilbert--Schmidt class. -/
theorem unitaryPush_isHilbertSchmidt
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (u : H ≃ₗᵢ[ℂ] K) :
    IsHilbertSchmidt (unitaryPush u T) := by
  unfold RHTower.unitaryPush
  exact (hT.comp_right (u.symm : K →L[ℂ] H)).comp_left
    (u : H →L[ℂ] K)

/-- Right composition by the inverse of a unitary preserves squared Hilbert--Schmidt norm. -/
theorem hsNormSq_comp_right_linearIsometryEquiv_symm
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (u : H ≃ₗᵢ[ℂ] K) :
    hsNormSq (T ∘L (u.symm : K →L[ℂ] H)) = hsNormSq T := by
  let S : K →L[ℂ] H := T ∘L (u.symm : K →L[ℂ] H)
  have hS : IsHilbertSchmidt S := hT.comp_right (u.symm : K →L[ℂ] H)
  calc
    hsNormSq (T ∘L (u.symm : K →L[ℂ] H)) =
        hsNormSq (ContinuousLinearMap.adjoint S) := hS.hsNormSq_adjoint.symm
    _ = hsNormSq ((u : H →L[ℂ] K) ∘L ContinuousLinearMap.adjoint T) := by
      congr 1
      dsimp [S]
      rw [ContinuousLinearMap.adjoint_comp]
      change ContinuousLinearMap.adjoint (u.symm : K →L[ℂ] H) ∘L
          ContinuousLinearMap.adjoint T =
        (u : H →L[ℂ] K) ∘L ContinuousLinearMap.adjoint T
      have huadj : ContinuousLinearMap.adjoint (u.symm : K →L[ℂ] H) =
          (u : H →L[ℂ] K) := by
        simpa using LinearIsometryEquiv.adjoint_eq_symm u.symm
      rw [huadj]
    _ = hsNormSq (ContinuousLinearMap.adjoint T) := by
      exact hsNormSq_comp_left_eq_of_norm_map hT.adjoint
        (u : H →L[ℂ] K) (fun x => u.norm_map x)
    _ = hsNormSq T := hT.hsNormSq_adjoint

/-- Squared Hilbert--Schmidt norm is invariant under unitary conjugacy. -/
theorem hsNormSq_unitaryPush
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (u : H ≃ₗᵢ[ℂ] K) :
    hsNormSq (unitaryPush u T) = hsNormSq T := by
  unfold RHTower.unitaryPush
  rw [hsNormSq_comp_left_eq_of_norm_map
    (hT.comp_right (u.symm : K →L[ℂ] H))
    (u : H →L[ℂ] K) (fun x => u.norm_map x)]
  exact hsNormSq_comp_right_linearIsometryEquiv_symm hT u

end UnitaryHilbertSchmidt

/-- Distinct positive symmetric Sonin apertures have unitarily inequivalent exact projection
corrections. -/
theorem eq_of_unitaryPush_centralSoninProjectionCorrection_eq
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (u : SoninL2 ≃ₗᵢ[ℂ] SoninL2)
    (htransport : unitaryPush u (centralSoninProjectionCorrection a) =
      centralSoninProjectionCorrection b) :
    a = b := by
  have hHS := centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have henergy := hsNormSq_unitaryPush hHS u
  rw [htransport,
    hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq b hb,
    hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq a ha] at henergy
  nlinarith

/-- **Exact aperture classification.**  Positive Sonin projection corrections are unitarily
equivalent if and only if their apertures are equal. -/
theorem exists_unitaryPush_centralSoninProjectionCorrection_eq_iff
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃ u : SoninL2 ≃ₗᵢ[ℂ] SoninL2,
      unitaryPush u (centralSoninProjectionCorrection a) =
        centralSoninProjectionCorrection b) ↔ a = b := by
  constructor
  · rintro ⟨u, hu⟩
    exact eq_of_unitaryPush_centralSoninProjectionCorrection_eq a b ha hb u hu
  · intro hab
    subst b
    refine ⟨LinearIsometryEquiv.refl ℂ SoninL2, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    simp [unitaryPush]

end RHTower
