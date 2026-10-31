import GaloisForLFunctions.AdelicKreinGeometry.Haar.IndexPreservation

/-!
# Uniqueness of the positive Haar and slope parts

The exact slope-index law makes the difference of two slope parts positive definite. Haar normalization makes its identity value zero, forcing the difference to vanish.
-/

open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A decomposition into a positive Haar carrier and a Hermitian slope kernel is unique.
The index law makes the difference of the slope parts positive; its zero value at identity then
forces it to vanish. -/
theorem positive_haar_slope_split_unique {p q : AffineGroupQ → ℂ} {ψ χ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hq : IsPosDefKernel q)
    (hps : HasIntegerSuccessor p) (hqs : HasIntegerSuccessor q)
    (hψ : IsHermKernel ψ) (hχ : IsHermKernel χ)
    (heq : ∀ g, p g + ψ (slopeUnit g) = q g + χ (slopeUnit g)) : p = q ∧ ψ = χ := by
  let τ : ℚˣ → ℂ := fun u => ψ u - χ u
  have hτ : IsHermKernel τ := by
    intro u
    change ψ u⁻¹ - χ u⁻¹ = (starRingEnd ℂ) (ψ u - χ u)
    rw [hψ, hχ, map_sub]
  have he : (fun g => p g + τ (slopeUnit g)) = q := by
    funext g
    dsimp only [τ]
    linear_combination heq g
  have hi := negIndex_add_slope_of_integer_successor hp hps τ hτ
  rw [he, hq.negIndex_eq_zero] at hi
  have hpos : IsPosDefKernel τ := (isPosDefKernel_iff hτ).mpr hi.symm
  have hzero : τ 1 = 0 := by
    have h := heq 1
    rw [map_one, hasIntegerSuccessor_one hps, hasIntegerSuccessor_one hqs] at h
    exact sub_eq_zero.mpr (add_left_cancel h)
  have hslope : ψ = χ := by
    funext u
    have hb := hpos.norm_le u
    rw [hzero, Complex.zero_re] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  refine ⟨?_, hslope⟩
  funext g
  have h := heq g
  rw [hslope] at h
  exact add_right_cancel h

#print axioms positive_haar_slope_split_unique
end GaloisForLFunctions.AdelicKreinGeometry
