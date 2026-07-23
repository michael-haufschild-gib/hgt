import GaloisForLFunctions.RHTower.GammaQuarterLatticeBlackHoleSpectralRefinementUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeArchUniversalStrictHankelRayAdjoiningUniversalityLaw

/-!
# Gamma-quarter refined prime--archimedean Hankel-cone universality law

The three Gamma/Bose residue sectors complementary to the central quarter-lattice connection form
an unconditional strict Hankel ray.  The universal adjoining theorem therefore makes their
addition to the prime--archimedean/black-hole/reciprocal cone an exact RH classifier.  This ties
the quarter-lattice refinement identity to the cone criterion: the very ray that completes the
central Gamma jet into the four-dilated black-hole clock can be adjoined without weakening or
strengthening the classifier.
-/

namespace RHTower

noncomputable section

/-- The three complementary quarter-lattice Gamma/Bose sectors form a strict Hankel ray at every
finite depth. -/
theorem gammaQuarterLatticeComplementMoment_hankel_posDef (n : ℕ) :
    (HTGeometry.momentHankelMatrix gammaQuarterLatticeComplementMoment n).PosDef := by
  have hhalf := HTGeometry.gammaBoseHankel_posDef (a := 1 / 2) (by norm_num) n
  have hthree := HTGeometry.gammaBoseHankel_posDef (a := 3 / 4) (by norm_num) n
  have hone := HTGeometry.gammaBoseHankel_posDef (a := 1) (by norm_num) n
  have hmatrix :
      HTGeometry.momentHankelMatrix gammaQuarterLatticeComplementMoment n =
        HTGeometry.momentHankelMatrix (HTGeometry.gammaBoseMoment (1 / 2)) n +
          (HTGeometry.momentHankelMatrix (HTGeometry.gammaBoseMoment (3 / 4)) n +
            HTGeometry.momentHankelMatrix (HTGeometry.gammaBoseMoment 1) n) := by
    ext i j
    simp [HTGeometry.momentHankelMatrix, gammaQuarterLatticeComplementMoment, add_assoc]
  rw [hmatrix]
  exact hhalf.add (hthree.add hone)

/-- **Gamma-quarter refined prime--archimedean Hankel-cone universality law.**  RH is equivalent
to strict positivity of every nonzero nonnegative mixture after adjoining the exact complementary
ray from the central-Gamma/black-hole quarter-lattice refinement. -/
theorem riemannHypothesis_iff_primeArch_adjoin_gammaQuarterLatticeComplement :
    RiemannHypothesis ↔
      ∀ (scaleLog : ℂ) (alpha beta gamma delta : ℝ),
        0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → 0 ≤ delta →
          0 < alpha + beta + gamma + delta →
            ∀ n : ℕ,
              (HTGeometry.momentHankelMatrix
                (primeArchAdjoinedStrictHankelMixedClock
                  gammaQuarterLatticeComplementMoment
                  scaleLog alpha beta gamma delta) n).PosDef :=
  riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay
    gammaQuarterLatticeComplementMoment
    gammaQuarterLatticeComplementMoment_hankel_posDef

/-- The adjoined strict ray is exactly the complement completing the normalized central Gamma
connection into the four-dilated black-hole clock. -/
theorem gammaQuarterRefinedPrimeArchHankelCone_completion_and_classifier :
    (∀ (scaleLog : ℂ) (m : ℕ),
      normalizedGammaRealConnectionJet m + gammaQuarterLatticeComplementMoment m =
        (4 : ℝ) ^ (m + 2) * HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m) ∧
    (RiemannHypothesis ↔
      ∀ (scaleLog : ℂ) (alpha beta gamma delta : ℝ),
        0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → 0 ≤ delta →
          0 < alpha + beta + gamma + delta →
            ∀ n : ℕ,
              (HTGeometry.momentHankelMatrix
                (primeArchAdjoinedStrictHankelMixedClock
                  gammaQuarterLatticeComplementMoment
                  scaleLog alpha beta gamma delta) n).PosDef) := by
  exact ⟨gammaRealConnection_add_quarterComplement_eq_dilatedBlackHoleClock,
    riemannHypothesis_iff_primeArch_adjoin_gammaQuarterLatticeComplement⟩

end

end RHTower
