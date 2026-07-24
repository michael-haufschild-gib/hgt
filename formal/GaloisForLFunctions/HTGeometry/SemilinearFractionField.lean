import GaloisForLFunctions.HTGeometry.FractionRingDerivation

/-!
# Semilinearity propagates from a domain to its fraction field

A clock dilation is built on a differential domain `A` and must act on the fraction field
`F = Frac(A)` (the field `C⟨y⟩`).  Semilinearity `E(D z) = λ · D(E z)` is a defining property that
need only be checked on the domain: this file shows it propagates to all of `F`.

The mechanism is derivation conjugation.  If `E` is semilinear on the image of `A`, then the two
derivations `D` and `λ · (E⁻¹ ∘ D ∘ E)` agree on `A`, hence agree on `F`
(`fractionRing_derivation_ext`), which is exactly semilinearity of `E` on `F`.
-/

namespace GaloisForLFunctions

noncomputable section

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- Conjugation of a derivation by a `C`-algebra automorphism: `z ↦ E⁻¹(D(E z))`. -/
def conjDerivation (E : F ≃ₐ[C] F) (D : Derivation C F F) : Derivation C F F :=
  Derivation.mk'
    (E.symm.toLinearMap.comp (D.toLinearMap.comp E.toLinearMap))
    (by
      intro a b
      show E.symm (D (E (a * b))) = a • E.symm (D (E b)) + b • E.symm (D (E a))
      rw [map_mul, Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.symm_apply_apply])

@[simp] theorem conjDerivation_apply (E : F ≃ₐ[C] F) (D : Derivation C F F) (z : F) :
    conjDerivation E D z = E.symm (D (E z)) := rfl

/-- **Semilinearity propagates to the fraction field.**  A `C`-algebra automorphism `E` of a fraction
field `F = Frac(A)` that is semilinear on the image of `A` (with factor `λ`, for the extended
derivation) is semilinear on all of `F`. -/
theorem algEquiv_semilinear_of_semilinear_algebraMap
    {A : Type*} [CommRing A] [IsDomain A]
    [Algebra C A] [Algebra A F] [IsScalarTower C A F] [IsFractionRing A F]
    (D : Derivation C A F) (E : F ≃ₐ[C] F) (lam : C)
    (hED : ∀ a : A, E (fractionRingDerivation D (algebraMap A F a))
        = algebraMap C F lam * fractionRingDerivation D (E (algebraMap A F a))) :
    ∀ z : F, E (fractionRingDerivation D z)
      = algebraMap C F lam * fractionRingDerivation D (E z) := by
  set DF := fractionRingDerivation D with hDF
  have hderiv_eq : DF = (algebraMap C F lam) • conjDerivation E DF := by
    refine fractionRing_derivation_ext (A := A) _ _ (fun a => ?_)
    rw [Derivation.smul_apply, conjDerivation_apply, smul_eq_mul]
    conv_lhs => rw [← E.symm_apply_apply (DF (algebraMap A F a)), hED a, map_mul,
      AlgEquiv.commutes]
  intro z
  have hz := DFunLike.congr_fun hderiv_eq z
  rw [Derivation.smul_apply, conjDerivation_apply, smul_eq_mul] at hz
  rw [hz, map_mul, AlgEquiv.commutes, AlgEquiv.apply_symm_apply]

end

end GaloisForLFunctions
