import GaloisForLFunctions.HTGeometry.TailCoefficientFixedField
import GaloisForLFunctions.HTGeometry.KummerDegreeBound
import Mathlib.FieldTheory.Tower

/-!
# The degree of the parameter field over the coefficient field

The parameter field is generated over the coefficient field by the first parameter alone, whose
`n`-th power is the first tail coefficient.  So its degree over the coefficient field is at most
`n`.

The deck transformations give the opposite bound, since the coefficient field sits inside their
fixed field and the function field has degree exactly the order of the group over that fixed field.
The two bounds force the degree to be `n` and the coefficient field to be exactly the fixed field.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

open scoped IntermediateField

set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
theorem tailCoeff_mem_tailCoeffField (j : Fin n) :
    algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
      (tailCoeff K n j) ∈ tailCoeffField K n :=
  IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩

/-- **The first parameter generates the parameter field over the coefficient field.** -/
theorem tailCoeffField_adjoin_eq_top (hn : 0 < n) :
    (tailCoeffField K n)⟮algebraMap (MvPolynomial (Fin n) K)
        (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X (⟨0, hn⟩ : Fin n))⟯ = ⊤ := by
  refine IntermediateField.restrictScalars_injective K ?_
  rw [IntermediateField.restrictScalars_top]
  refine le_antisymm le_top ?_
  rw [← tailParamField_eq_top (K := K) (n := n), tailParamField, IntermediateField.adjoin_le_iff]
  rintro z (⟨j, rfl⟩ | ⟨j, hj0, rfl⟩)
  · exact IntermediateField.algebraMap_mem
      ((tailCoeffField K n)⟮algebraMap (MvPolynomial (Fin n) K)
        (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X (⟨0, hn⟩ : Fin n))⟯)
      (⟨_, tailCoeff_mem_tailCoeffField j⟩ : tailCoeffField K n)
  · have hj : j = (⟨0, hn⟩ : Fin n) := Fin.ext hj0
    subst hj
    exact IntermediateField.mem_adjoin_simple_self (tailCoeffField K n)
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (MvPolynomial.X (⟨0, hn⟩ : Fin n)))

omit [CharZero K] in
theorem pow_algebraMap_X_zero (hn : 0 < n) :
    (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (MvPolynomial.X (⟨0, hn⟩ : Fin n))) ^ n =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (tailCoeff K n (⟨0, hn⟩ : Fin n)) := by
  rw [← map_pow, tailCoeff_zero hn]

/-- **The parameter field has degree at most `n` over the coefficient field.** -/
theorem finrank_tailCoeffField_le (hn : 0 < n) :
    Module.finrank (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) ≤ n := by
  set L := FractionRing (MvPolynomial (Fin n) K)
  set p₁ := algebraMap (MvPolynomial (Fin n) K) L (MvPolynomial.X (⟨0, hn⟩ : Fin n)) with hp₁
  have hc : p₁ ^ n =
      algebraMap (tailCoeffField K n) L
        (⟨algebraMap (MvPolynomial (Fin n) K) L (tailCoeff K n (⟨0, hn⟩ : Fin n)),
          tailCoeff_mem_tailCoeffField _⟩ : tailCoeffField K n) := by
    rw [hp₁, pow_algebraMap_X_zero hn]
    rfl
  have hle := finrank_adjoin_le_of_pow_mem (F := tailCoeffField K n) (L := L) hn hc
  rw [tailCoeffField_adjoin_eq_top hn] at hle
  have htop : Module.finrank (tailCoeffField K n)
      (⊤ : IntermediateField (tailCoeffField K n) L) =
      Module.finrank (tailCoeffField K n) L :=
    (IntermediateField.topEquiv (F := tailCoeffField K n) (E := L)).toLinearEquiv.finrank_eq
  rwa [htop] at hle

theorem finiteDimensional_tailCoeffField (hn : 0 < n) :
    FiniteDimensional (tailCoeffField K n) (FractionRing (MvPolynomial (Fin n) K)) := by
  set L := FractionRing (MvPolynomial (Fin n) K)
  set p₁ := algebraMap (MvPolynomial (Fin n) K) L (MvPolynomial.X (⟨0, hn⟩ : Fin n)) with hp₁
  have hc : p₁ ^ n =
      algebraMap (tailCoeffField K n) L
        (⟨algebraMap (MvPolynomial (Fin n) K) L (tailCoeff K n (⟨0, hn⟩ : Fin n)),
          tailCoeff_mem_tailCoeffField _⟩ : tailCoeffField K n) := by
    rw [hp₁, pow_algebraMap_X_zero hn]
    rfl
  have hint : IsIntegral (tailCoeffField K n) p₁ := isIntegral_of_pow_mem hn hc
  have hfd : FiniteDimensional (tailCoeffField K n) (tailCoeffField K n)⟮p₁⟯ :=
    IntermediateField.adjoin.finiteDimensional hint
  rw [tailCoeffField_adjoin_eq_top hn] at hfd
  exact Module.Finite.equiv
    (IntermediateField.topEquiv (F := tailCoeffField K n) (E := L)).toLinearEquiv

end GaloisForLFunctions.HTGeometry
