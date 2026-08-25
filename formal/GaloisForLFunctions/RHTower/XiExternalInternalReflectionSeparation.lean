import GaloisForLFunctions.RHTower.XiJointAncestrySuperselection
import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapPhaseGeometry

/-!
# External/internal reflection separation on the Xi divisor

Functional-equation reflection and the coefficient-faithful fixed-circle source phase orbit are
unconditional.  Neither detects horizontal placement.  The arithmetic discriminator is the
upgrade from that unitary source phase to the physical half-density character: at one prime this
upgrade is equivalent both to zero modular transfer charge and to a nonzero closed untwisted
source-linear correspondence between the reflected prime-Poisson sectors.

Thus a hypothetical off-line Xi divisor would still retain reflected multiplicity and a nonzero
moderate unitary phase orbit.  What fails is not external reflection or phase coherence, but
internal implementability in one arithmetic source representation.
-/

open Complex

namespace RHTower

noncomputable section

/-- Closed untwisted prime-source sewing is exactly neutral modular transfer charge. -/
theorem xiPrimePoissonReflectionSewing_iff_modularCharge_zero
    (rho : XiDivisorSupport) :
    XiPrimePoissonReflectionSewing rho ↔
      shellTransferEntropy (rho : ℂ) = 0 := by
  rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
    xiDivisorSyndromeIsInternalOnly_iff_re_eq_half,
    shellTransferEntropy_eq_zero_iff]

/-- At any one prime, internal source correspondence is equivalent to upgrading the canonical
unitary source-phase orbit to the physical half-density sewing law. -/
theorem xiPrimePoissonReflectionSewing_iff_sourcePhaseOrbit_physicalSewing
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    XiPrimePoissonReflectionSewing rho ↔
      ∀ e : ℤ,
        ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho (e - 1) =
          bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) *
            ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho e := by
  rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
    xiDivisorSyndromeIsInternalOnly_iff_re_eq_half,
    ccmRationalAdelicPrimeXiSourcePhaseOrbit_physicalSewing_iff_singularStokesFlat,
    ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- **External/internal separation.**  An off-line Xi divisor retains multiplicity-preserving
functional-equation reflection and a nonzero moderate unitary source-phase sewing.  The physical
phase upgrade fails, its reflected prime-source sectors are disjoint, and no nonzero closed
untwisted source-linear sewing exists. -/
theorem xiOffLine_externalPhase_without_internalSewing
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    (MeromorphicOn.divisor xi Set.univ) (1 - (rho : ℂ)) =
        (MeromorphicOn.divisor xi Set.univ) (rho : ℂ) ∧
      ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho ≠ 0 ∧
      bilateralModerate (ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho) ∧
      (∀ e : ℤ,
        ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho (e - 1) =
          ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho *
            ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho e) ∧
      (¬ ∀ e : ℤ,
        ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho (e - 1) =
          bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) *
            ccmRationalAdelicPrimeXiSourcePhaseOrbit p rho e) ∧
      XiPrimePoissonReflectionDisjoint rho ∧
      ¬ XiPrimePoissonReflectionSewing rho := by
  have hnoInternal : ¬ XiPrimePoissonReflectionSewing rho := by
    rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
      xiDivisorSyndromeIsInternalOnly_iff_re_eq_half]
    exact hoff
  refine ⟨xi_divisor_one_sub (rho : ℂ),
    ccmRationalAdelicPrimeXiSourcePhaseOrbit_ne_zero p rho,
    ccmRationalAdelicPrimeXiSourcePhaseOrbit_moderate p rho,
    ccmRationalAdelicPrimeXiSourcePhaseOrbit_sewing p rho, ?_,
    xiPrimePoissonReflectionDisjoint_of_offLine rho hoff, hnoInternal⟩
  intro hphysical
  exact hnoInternal
    ((xiPrimePoissonReflectionSewing_iff_sourcePhaseOrbit_physicalSewing p rho).2 hphysical)

end

end RHTower
