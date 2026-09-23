import GaloisForLFunctions.HTGeometry.RightInverseMonoidGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Finite determinant kernel implies finite matrix group

For a matrix submonoid with internal right inverses and determinant square one, the determinant-one
fiber has index at most two.  Hence finiteness of that fiber forces finiteness of the submonoid.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- A matrix group whose determinant has order at most two is finite when its determinant-one
fiber is finite. -/
theorem finite_submonoid_of_finite_detOne
    {C : Type u} [Field C]
    (S : Submonoid (Matrix (Fin 2) (Fin 2) C))
    (hright : ∀ x : S, ∃ y : S, x * y = 1)
    (hdetSq : ∀ x : S, x.1.det ^ (2 : ℕ) = 1)
    (hdetOne : ({x : S | x.1.det = 1} : Set S).Finite) :
    Finite S := by
  classical
  letI : Group S := groupOfRightInverses hright
  let H : Set S := {x | x.1.det = 1}
  letI : Finite H := by
    apply Set.Finite.to_subtype
    simpa [H] using hdetOne
  by_cases hall : ∀ x : S, x.1.det = 1
  · exact Finite.of_injective (fun x : S => (⟨x, hall x⟩ : H))
      (fun _ _ h => congrArg Subtype.val h)
  · push Not at hall
    obtain ⟨z, hz⟩ := hall
    have hzneg : z.1.det = -1 := ((sq_eq_one_iff).mp (hdetSq z)).resolve_left hz
    have hzinvProd : z.1.det * (z⁻¹).1.det = 1 := by
      rw [← Matrix.det_mul]
      change ((z * z⁻¹ : S) : Matrix (Fin 2) (Fin 2) C).det = 1
      rw [mul_inv_cancel]
      exact Matrix.det_one
    have hzinvNeg : (z⁻¹).1.det = -1 := by
      rw [hzneg] at hzinvProd
      simpa using congrArg Neg.neg hzinvProd
    let normalize : (x : S) → x.1.det ≠ 1 → H := fun x hx =>
      ⟨x * z⁻¹, by
        change (x * z⁻¹ : S).1.det = 1
        rw [Submonoid.coe_mul, Matrix.det_mul,
          ((sq_eq_one_iff).mp (hdetSq x)).resolve_left hx, hzinvNeg]
        simp⟩
    let f : S → Bool × H := fun x =>
      if hx : x.1.det = 1 then (false, ⟨x, hx⟩) else (true, normalize x hx)
    apply Finite.of_injective f
    intro a b hab
    by_cases ha : a.1.det = 1
    · by_cases hb : b.1.det = 1
      · have hval : (⟨a, ha⟩ : H) = ⟨b, hb⟩ := by
          simpa only [f, dif_pos ha, dif_pos hb] using
            congrArg (fun p : Bool × H => p.2) hab
        exact congrArg Subtype.val hval
      · exfalso
        have htag : false = true := by
          simpa only [f, dif_pos ha, dif_neg hb] using
            congrArg (fun p : Bool × H => p.1) hab
        cases htag
    · by_cases hb : b.1.det = 1
      · exfalso
        have htag : true = false := by
          simpa only [f, dif_neg ha, dif_pos hb] using
            congrArg (fun p : Bool × H => p.1) hab
        cases htag
      · have hnorm : normalize a ha = normalize b hb := by
          simpa only [f, dif_neg ha, dif_neg hb] using
            congrArg (fun p : Bool × H => p.2) hab
        have hmul : a * z⁻¹ = b * z⁻¹ := congrArg Subtype.val hnorm
        exact mul_right_cancel hmul

end

end GaloisForLFunctions.HTGeometry
