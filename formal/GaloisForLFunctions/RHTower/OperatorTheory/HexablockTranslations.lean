import GaloisForLFunctions.HTGeometry.OperatorTheory.TetrablockAlgebra
import GaloisForLFunctions.HTGeometry.OperatorTheory.HexablockAlgebra
import GaloisForLFunctions.RHTower.PrimeTranslationKoszulOffLine

/-!
# Hexablock coordinates of real and logarithmic translations

Real translations supply commuting unitaries without additional assumptions.
Their polynomial coordinates satisfy both hexablock energy partitions and
the cross relation. On the one-translation slice, Brown–Halmos invariance is
exactly commutation with translation; logarithmic prime translations are
included by substituting their real translation lengths.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.Hexablock ContinuousLinearMap
open MeasureTheory

private theorem unitaryOp_star_mul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (U : H ≃ₗᵢ[ℂ] H) :
    star (unitaryOp U) * unitaryOp U = 1 := by
  rw [_root_.ContinuousLinearMap.star_eq_adjoint]
  exact U.toLinearIsometry.adjoint_comp_self

private theorem unitaryOp_mul_star {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (U : H ≃ₗᵢ[ℂ] H) :
    unitaryOp U * star (unitaryOp U) = 1 := by
  have hs : star (unitaryOp U) = unitaryOp U.symm := by
    calc
      star (unitaryOp U) = star (unitaryOp U) * (unitaryOp U * unitaryOp U.symm) := by
        rw [unitaryOp_mul_symm, mul_one]
      _ = unitaryOp U.symm := by rw [← mul_assoc, unitaryOp_star_mul, one_mul]
  rw [hs, unitaryOp_mul_symm]

/-- Four arbitrary real translations satisfy the hexablock coordinate identities. -/
theorem hexablock_translation_relations (b c d e : ℝ) :
    let u := unitaryOp (additiveTranslationUnitary b)
    let v := unitaryOp (additiveTranslationUnitary c)
    let w := unitaryOp (additiveTranslationUnitary d)
    let z := unitaryOp (additiveTranslationUnitary e)
    (star (a u w) * a u w + star (x₁ u v) * x₁ u v = 1) ∧
    (star (a u w) * a u w + star (x₂ u w z) * x₂ u w z = 1) ∧
    star (x₃ u v w z) * x₃ u v w z = 1 ∧
    star (x₁ u v) * x₃ u v w z = x₂ u w z := by
  dsimp only
  have h (t : ℝ) := unitaryOp_star_mul (additiveTranslationUnitary t)
  obtain ⟨h₁, h₂, h₃⟩ := energy _ _ _ _ (h b) (h c) (h d) (h e)
  exact ⟨h₁, h₂, h₃, cross _ _ _ _ (h b) (h c)
    (commute_additiveTranslationUnitary b c) (commute_additiveTranslationUnitary b d)
    (commute_additiveTranslationUnitary b e)⟩

/-- On a translation slice Brown–Halmos invariance is exactly translation commutation. -/
theorem hexablock_translation_brownHalmos_iff (b : ℝ)
    (T : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2) :
    let u := unitaryOp (additiveTranslationUnitary b)
    BrownHalmos (halfDiff u 1) (halfSum u 1) (halfSum u 1) u T ↔ Commute T u := by
  dsimp only
  rw [slice_brownHalmos_iff]
  constructor
  · intro h
    change T * unitaryOp (additiveTranslationUnitary b) =
      unitaryOp (additiveTranslationUnitary b) * T
    calc
      T * unitaryOp (additiveTranslationUnitary b) =
          unitaryOp (additiveTranslationUnitary b) *
            (star (unitaryOp (additiveTranslationUnitary b)) * T *
              unitaryOp (additiveTranslationUnitary b)) := by
        rw [← mul_assoc, ← mul_assoc, unitaryOp_mul_star, one_mul]
      _ = unitaryOp (additiveTranslationUnitary b) * T := by rw [h]
  · intro h
    rw [mul_assoc, h.eq, ← mul_assoc, unitaryOp_star_mul, one_mul]

/-- Three real translations give the tetrablock coordinate identities. -/
theorem tetrablock_translation_relations (b c d : ℝ) :
    let u := unitaryOp (additiveTranslationUnitary b)
    let v := unitaryOp (additiveTranslationUnitary c)
    let z := unitaryOp (additiveTranslationUnitary d)
    (star (halfDiff u v) * halfDiff u v +
      star (Tetrablock.x₂ u v) * Tetrablock.x₂ u v = 1) ∧
    (star (Tetrablock.x₂ u v) * Tetrablock.x₃ u v z = Tetrablock.x₁ u v z) ∧
    star (Tetrablock.x₃ u v z) * Tetrablock.x₃ u v z = 1 := by
  dsimp only
  have h (t : ℝ) := unitaryOp_star_mul (additiveTranslationUnitary t)
  exact ⟨Tetrablock.energy _ _ (h b) (h c),
    Tetrablock.cross _ _ _ (h b) (h c) (commute_additiveTranslationUnitary b c)
      (commute_additiveTranslationUnitary b d) (commute_additiveTranslationUnitary c d),
    Tetrablock.last_isometry _ _ _ (h b) (h c) (h d)⟩

end RHTower

#print axioms RHTower.hexablock_translation_relations
#print axioms RHTower.hexablock_translation_brownHalmos_iff

#print axioms RHTower.tetrablock_translation_relations
