import GaloisForLFunctions.HTGeometry.LocalizationDerivation

/-!
# The difference action on the differential coordinate ring, as an automorphism

Packaging `sigmaJetCoordHom_comp_eq_id` into a ring equivalence.  The inverse composition is the
same theorem applied to the inverse system: the construction for `σ⁻¹` and the `σ⁻¹`-image of `A⁻¹`
has, as its own inverse datum, the construction for `σ` and `A` again.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K : Type*} [CommRing K] [Differential K] {n : ℕ}

omit [Differential K] in
theorem map_symm_map_self (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) :
    (A.map (σ.symm : K →+* K)).map (σ : K →+* K) = A := by
  refine Matrix.ext fun i j => ?_
  simp [Matrix.map_apply]

/-- **The difference action on the differential coordinate ring is a ring automorphism.** -/
def sigmaJetCoordEquiv (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    DifferentialPolynomial (Fin n × Fin n) K ≃+* DifferentialPolynomial (Fin n × Fin n) K :=
  RingEquiv.ofRingHom (sigmaJetCoordHom σ A)
    (sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K)))
    (by
      have hprod : (A'.map (σ.symm : K →+* K)) * (A.map (σ.symm : K →+* K))
          = (1 : Matrix (Fin n) (Fin n) K) := by
        rw [← Matrix.map_mul, hA'A]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have h := sigmaJetCoordHom_comp_eq_id σ.symm (commutesDeriv_symm hσ)
        (A'.map (σ.symm : K →+* K)) (A.map (σ.symm : K →+* K)) hprod
      rw [RingEquiv.symm_symm, map_symm_map_self σ A] at h
      exact h)
    (sigmaJetCoordHom_comp_eq_id σ hσ A A' hAA')

@[simp] theorem sigmaJetCoordEquiv_apply (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (f : DifferentialPolynomial (Fin n × Fin n) K) :
    sigmaJetCoordEquiv σ hσ A A' hAA' hA'A f = sigmaJetCoordHom σ A f := rfl

/-- The automorphism commutes with the total derivation. -/
theorem sigmaJetCoordEquiv_commutes (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (f : DifferentialPolynomial (Fin n × Fin n) K) :
    sigmaJetCoordEquiv σ hσ A A' hAA' hA'A (jetCoordDeriv K n f)
      = jetCoordDeriv K n (sigmaJetCoordEquiv σ hσ A A' hAA' hA'A f) :=
  sigmaJetCoordHom_commutes σ hσ A f

end

end GaloisForLFunctions.HTGeometry
