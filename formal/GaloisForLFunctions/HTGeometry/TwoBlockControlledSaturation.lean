import GaloisForLFunctions.HTGeometry.FactorControlledSaturation
import GaloisForLFunctions.HTGeometry.JetFractionDerivationTransport

/-!
# The two-block saturation certificate with a controlled multiplier

The two-block splitting turns a differential polynomial in two blocks of jets into a differential
polynomial in the right block over the ring of the left block.  Under that splitting the differential
principal ideal of a two-block polynomial is the differential principal ideal of its image, so a
certificate proved over the coefficient ring transports back to the two-block ring unchanged.

Combining this with the multiplier exchange gives a two-block saturation certificate whose
multiplier is a product of powers of the initial and the separant of the polynomial itself.  Unlike
a multiplier obtained by clearing denominators, its coefficients are coefficients of the polynomial,
so its order in the left block is bounded by that of the polynomial -- the hypothesis the
divisibility bridge needs.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

variable {F : Type*} [Field F] [Differential F]

/-- The two-block splitting identifies the two differential principal ideals. -/
theorem mem_familyIterateIdeal_of_twoBlockEquiv_mem
    {A Q : DifferentialPolynomial (Unit ⊕ Unit) F} :
    letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
    differentialPolynomialTwoBlockEquiv F Q ∈
        diffPolyIterateIdeal (differentialPolynomialTwoBlockEquiv F A) →
      Q ∈ differentialPolynomialFamilyIterateIdeal A := by
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  intro hQ
  have hgen : ∀ x ∈ diffPolyIterateIdeal (differentialPolynomialTwoBlockEquiv F A),
      (differentialPolynomialTwoBlockEquiv F).symm x ∈
        differentialPolynomialFamilyIterateIdeal A := by
    intro x hx
    rw [diffPolyIterateIdeal] at hx
    refine Submodule.span_induction (hx := hx) ?_ ?_ ?_ ?_
    · rintro _ ⟨n, rfl⟩
      have hiter : (differentialPolynomialTwoBlockEquiv F).symm
          (diffPolyIterate n (differentialPolynomialTwoBlockEquiv F A)) = diffPolyIterate n A := by
        rw [← differentialPolynomialTwoBlockEquiv_diffPolyIterate, AlgEquiv.symm_apply_apply]
      rw [hiter, diffPolyIterate_eq_familyIterateOver]
      exact differentialPolynomialFamilyIterateOver_mem_iterateIdeal A n
    · simp
    · intro u v _ _ hu hv
      simpa using (differentialPolynomialFamilyIterateIdeal A).add_mem hu hv
    · intro r u _ hu
      rw [smul_eq_mul, map_mul]
      exact (differentialPolynomialFamilyIterateIdeal A).mul_mem_left _ hu
  have hsymm := hgen _ hQ
  rwa [AlgEquiv.symm_apply_apply] at hsymm

variable {E : Type*} [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
variable [CharZero F]

/-- **The two-block saturation certificate with a controlled multiplier.**

Input: a certificate saturating the image of `D` into the differential ideal of the image of `A` by
powers of the initial and the separant of a squarefree polynomial having that image as an
irreducible factor of the same order.

Output: a two-block certificate for `D` itself whose multiplier is a product of powers of the
initial and the separant of `A` in the right-block splitting.  Every coefficient of the multiplier
is a coefficient of `A`, so the multiplier introduces no left-block jet beyond those of `A`. -/
theorem exists_twoBlock_controlled_certificate {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {A D : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hAvars : (differentialPolynomialTwoBlockEquiv F A).vars.Nonempty)
    {B : DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F))}
    (hAirr : Irreducible (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F A)))
    (hsquarefree : Squarefree (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A) * B))
    (horder : scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A)) =
      scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A) * B))
    {a b : ℕ}
    (hsat :
      letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
      letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
        differentialIndependentJetFractionDifferential y hy
      scalarDifferentialPolynomialInitial (MvPolynomial.map
            (algebraMap (DifferentialPolynomial Unit F)
              (FractionRing (DifferentialPolynomial Unit F)))
            (differentialPolynomialTwoBlockEquiv F A) * B) ^ a *
          (scalarDifferentialPolynomialSeparant (MvPolynomial.map
              (algebraMap (DifferentialPolynomial Unit F)
                (FractionRing (DifferentialPolynomial Unit F)))
              (differentialPolynomialTwoBlockEquiv F A) * B) ^ b *
            MvPolynomial.map
              (algebraMap (DifferentialPolynomial Unit F)
                (FractionRing (DifferentialPolynomial Unit F)))
              (differentialPolynomialTwoBlockEquiv F D)) ∈
        differentialPolynomialIterateIdeal (MvPolynomial.map
          (algebraMap (DifferentialPolynomial Unit F)
            (FractionRing (DifferentialPolynomial Unit F)))
          (differentialPolynomialTwoBlockEquiv F A))) :
    letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
    ∃ a' b' : ℕ,
      (differentialPolynomialTwoBlockEquiv F).symm
            (scalarDifferentialPolynomialInitial (differentialPolynomialTwoBlockEquiv F A) ^ a' *
              scalarDifferentialPolynomialSeparant
                (differentialPolynomialTwoBlockEquiv F A) ^ b') * D ∈
        differentialPolynomialFamilyIterateIdeal A := by
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  obtain ⟨a', b', hmem⟩ := exists_factor_initial_separant_powers_mem_diffPolyIterateIdeal
    (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)))
    (IsFractionRing.injective (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)))
    (algebraMap_jetFraction_deriv hy) hAvars hAirr hsquarefree horder hsat
  refine ⟨a', b', mem_familyIterateIdeal_of_twoBlockEquiv_mem ?_⟩
  rw [map_mul, AlgEquiv.apply_symm_apply, mul_assoc]
  exact hmem

end

end GaloisForLFunctions
