import GaloisForLFunctions.HTGeometry.CriticalSourceChartLocalization

/-!
# The source field is the fraction field of the source chart ring

The raw coordinates are algebraically independent, so the polynomial ring on them has the actual
critical source field as its fraction field; inverting one nonzero polynomial does not change that.
Together with `criticalSourceChartRing_isIntegrallyClosed` this makes the source chart the integral
closure of the observation chart in the source field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable (K : Type*) [Field K] (m n : ℕ)

/-- The raw polynomial ring acts on the actual critical source field by evaluation. -/
noncomputable instance criticalSourcePolynomialAlgebra :
    Algebra (MvPolynomial (Fin (m + n)) K) (criticalSourceField K m n) :=
  (MvPolynomial.aeval (criticalSourceRaw K m n) :
    MvPolynomial (Fin (m + n)) K →ₐ[K] criticalSourceField K m n).toRingHom.toAlgebra

theorem algebraMap_criticalSourcePolynomial (p : MvPolynomial (Fin (m + n)) K) :
    algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceField K m n) p =
      MvPolynomial.aeval (criticalSourceRaw K m n) p := rfl

/-- The rational presentation of the source field, as an equivalence of polynomial algebras. -/
noncomputable def criticalSourceFracEquiv :
    FractionRing (MvPolynomial (Fin (m + n)) K) ≃ₐ[MvPolynomial (Fin (m + n)) K]
      criticalSourceField K m n :=
  { criticalSourceFieldEquiv K m n with
    commutes' := fun p => by
      apply Subtype.ext
      have h := (algebraicIndependent_criticalAmbientRaw K m n).aevalEquivField_algebraMap_apply_coe
        p
      have h2 : ((MvPolynomial.aeval (criticalSourceRaw K m n) p : criticalSourceField K m n) :
          genericJetField K (m + n))
          = MvPolynomial.aeval (fun j : Fin (m + n) => criticalAmbientRaw K m n (j : ℕ)) p :=
        coe_aeval_criticalSourceRaw K m n p
      rw [algebraMap_criticalSourcePolynomial, h2]
      exact h }

instance criticalSourcePolynomial_isFractionRing :
    IsFractionRing (MvPolynomial (Fin (m + n)) K) (criticalSourceField K m n) :=
  IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (MvPolynomial (Fin (m + n)) K))
    (criticalSourceFracEquiv K m n)

variable [Fact (0 < m)] [Fact (0 < n)]

instance criticalSourceChartRingPolynomialTower :
    IsScalarTower (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (algebraMap_criticalSourceChartRing_apply K m n p).symm

/-- **The actual critical source field is the fraction field of the source chart ring.** -/
instance criticalSourceChartRing_isFractionRing :
    IsFractionRing (criticalSourceChartRing K m n) (criticalSourceField K m n) :=
  IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers (criticalSourceChartPoly K m n)) _ _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (criticalSourceChartPoly_ne_zero K m n))

end

end GaloisForLFunctions.HTGeometry
