import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedDomain
import GaloisForLFunctions.HTGeometry.FiniteRightFactorSpecialization

/-!
# Tensor products of arbitrary fields over an algebraically closed field

Each pair of tensors uses only a finitely generated subalgebra of one factor.  Its inclusion into
the full tensor product is injective by flatness over the base field.  The finite-type tensor-domain
theorem therefore detects zero divisors without a finite-generation assumption on either field.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Over an algebraically closed field, the tensor product of arbitrary field extensions is a
domain. -/
theorem isDomain_tensorProduct_of_fields
    {k A B : Type*} [Field k] [IsAlgClosed k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] : IsDomain (A ⊗[k] B) := by
  let hnozero : ∀ z w : A ⊗[k] B, z * w = 0 → z = 0 ∨ w = 0 := by
    intro z w hzw
    obtain ⟨R, hR, zR, wR, hzR, hwR⟩ :=
      GaloisForLFunctions.exists_fg_right_subalgebra_lifts_pair k A B z w
    letI : Algebra.FiniteType k R :=
      GaloisForLFunctions.finiteTypeOfSubalgebraFG R hR
    letI : NoZeroDivisors R := ⟨by
      intro a b hab
      have habB : (a : B) * (b : B) = 0 := congrArg Subtype.val hab
      rcases eq_zero_or_eq_zero_of_mul_eq_zero habB with ha | hb
      · exact Or.inl (Subtype.ext ha)
      · exact Or.inr (Subtype.ext hb)⟩
    letI : IsDomain R := NoZeroDivisors.to_isDomain R
    letI : IsDomain (R ⊗[k] A) := isDomain_tensorProduct_of_finiteType
    have hprod : zR * wR = 0 := by
      apply GaloisForLFunctions.tensorRightSubalgebraMap_injective k A B R
      rw [map_mul, hzR, hwR, hzw, map_zero]
    have hcommprod :
        Algebra.TensorProduct.comm k A R zR *
            Algebra.TensorProduct.comm k A R wR = 0 := by
      rw [← map_mul, hprod, map_zero]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hcommprod with hz | hw
    · exact Or.inl (by
        rw [← hzR]
        have hzR0 : zR = 0 :=
          (Algebra.TensorProduct.comm k A R).injective (by simpa using hz)
        rw [hzR0, map_zero])
    · exact Or.inr (by
        rw [← hwR]
        have hwR0 : wR = 0 :=
          (Algebra.TensorProduct.comm k A R).injective (by simpa using hw)
        rw [hwR0, map_zero])
  letI : NoZeroDivisors (A ⊗[k] B) := ⟨fun {z w} h => hnozero z w h⟩
  exact NoZeroDivisors.to_isDomain (A ⊗[k] B)

end

end GaloisForLFunctions.HTGeometry
