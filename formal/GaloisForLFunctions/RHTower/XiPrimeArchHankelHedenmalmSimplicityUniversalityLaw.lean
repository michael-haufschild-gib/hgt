import GaloisForLFunctions.RHTower.PrimeArchExactReconstructionStrictHankelRayUniversalityLaw
import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw

/-!
# Xi prime--arch Hankel/Hedenmalm simplicity universality

Exact prescribed dual reconstruction for every finite prime--archimedean source Hankel packet is
already an exact RH classifier.  Combining it with the existing Hedenmalm simplicity classifier
replaces the abstract RH conjunct by a concrete Hilbert reconstruction phase.

The universal strict-ray closure theorem strengthens this replacement: the full Hedenmalm
RH-and-simplicity certificate is also exactly simultaneous closure under every strict
`HTGeometry` Hankel ray together with Xi simplicity.  In the negative phase, failure is
synchronized across every strict auxiliary ray.
-/

namespace RHTower

noncomputable section

/-- **Prime--arch exact-reconstruction/Hedenmalm universality law.** Exact source Hankel
reconstruction together with simple Xi zeros is exactly the full Hedenmalm RH-and-simplicity
certificate. -/
theorem
    primeArchSourceMomentHankelExactReconstructionPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate :
    (PrimeArchSourceMomentHankelExactReconstructionPhase ∧ XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr
    primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis
    Iff.rfl).trans
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Certificate-only positive form: exact prescribed source reconstruction and the eight-chart
Hedenmalm simplicity phase are exactly the enlarged RH-and-simplicity certificate. -/
theorem
    primeArchSourceMomentHankelExactReconstructionPhase_and_hendenmalmSimplicity_iff_rhSimplicityCertificate :
    (PrimeArchSourceMomentHankelExactReconstructionPhase ∧
        XiHedenmalmSimplicityUniversalCertificate) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr Iff.rfl
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm).trans
      primeArchSourceMomentHankelExactReconstructionPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- **Prime--arch reconstruction/Hedenmalm failure classification.** Failure of the enlarged
certificate is exactly failure of exact source Hankel reconstruction or failure of Xi
simplicity. -/
theorem
    not_primeArchSourceMomentHankelExactReconstructionPhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate :
    (¬PrimeArchSourceMomentHankelExactReconstructionPhase ∨ ¬XiZerosSimple) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro hfailure hcertificate
    have hphase :=
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.2
        hcertificate
    rcases hfailure with hnotReconstruction | hnotSimple
    · exact hnotReconstruction
        (primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis.2
          hphase.1)
    · exact hnotSimple hphase.2
  · intro hnotCertificate
    by_cases hreconstruction : PrimeArchSourceMomentHankelExactReconstructionPhase
    · right
      intro hsimple
      exact hnotCertificate
        (primeArchSourceMomentHankelExactReconstructionPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.1
          ⟨hreconstruction, hsimple⟩)
    · exact Or.inl hreconstruction

/-- Certificate-only negative form: failure of the enlarged Hedenmalm certificate is exactly
failure of exact source reconstruction or failure of the eight-chart simplicity certificate. -/
theorem
    not_primeArchSourceMomentHankelExactReconstructionPhase_or_not_hendenmalmSimplicity_iff_not_rhSimplicityCertificate :
    (¬PrimeArchSourceMomentHankelExactReconstructionPhase ∨
        ¬XiHedenmalmSimplicityUniversalCertificate) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate :=
  (or_congr Iff.rfl
    (not_congr xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate).symm).trans
      not_primeArchSourceMomentHankelExactReconstructionPhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate

/-! ### All-strict-ray strengthening -/

/-- **All-strict-ray/Hedenmalm universality law.**  Closure under every strict `HTGeometry`
Hankel ray together with simple Xi zeros is exactly the full Hedenmalm RH-and-simplicity
certificate. -/
theorem
    primeArchAllStrictHankelRayAdjoiningPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate :
    (PrimeArchAllStrictHankelRayAdjoiningPhase ∧ XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr
    primeArchAllStrictHankelRayAdjoiningPhase_iff_riemannHypothesis
    Iff.rfl).trans
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Certificate-only all-ray form: simultaneous strict-ray closure and the eight-chart
simplicity phase are exactly the enlarged RH-and-simplicity certificate. -/
theorem
    primeArchAllStrictHankelRayAdjoiningPhase_and_hendenmalmSimplicity_iff_rhSimplicityCertificate :
    (PrimeArchAllStrictHankelRayAdjoiningPhase ∧
        XiHedenmalmSimplicityUniversalCertificate) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr Iff.rfl
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm).trans
      primeArchAllStrictHankelRayAdjoiningPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Once closure under every strict Hankel ray is known, Xi simplicity alone is equivalent to the
full Hedenmalm RH-and-simplicity certificate. -/
theorem xiZerosSimple_iff_hendenmalmUniversalCertificate_of_allStrictHankelRayAdjoiningPhase
    (hall : PrimeArchAllStrictHankelRayAdjoiningPhase) :
    XiZerosSimple ↔ XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro hsimple
    exact
      primeArchAllStrictHankelRayAdjoiningPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.1
        ⟨hall, hsimple⟩
  · intro hcertificate
    exact
      (riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.2
        hcertificate).2

/-- Under the all-strict-ray phase, the eight-chart Hedenmalm simplicity certificate is already
the full RH-and-simplicity certificate. -/
theorem
    hendenmalmSimplicity_iff_rhSimplicityCertificate_of_allStrictHankelRayAdjoiningPhase
    (hall : PrimeArchAllStrictHankelRayAdjoiningPhase) :
    XiHedenmalmSimplicityUniversalCertificate ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm.trans
    (xiZerosSimple_iff_hendenmalmUniversalCertificate_of_allStrictHankelRayAdjoiningPhase
      hall)

/-- **Synchronized all-ray/Hedenmalm failure law.**  The enlarged certificate fails exactly when
every strict auxiliary Hankel ray fails to repair the prime--arch cone, or Xi has a multiple
zero. -/
theorem
    primeArchAllStrictHankelRayAdjoiningFailurePhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate :
    (PrimeArchAllStrictHankelRayAdjoiningFailurePhase ∨ ¬XiZerosSimple) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate :=
  (or_congr
    not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allStrictHankelRayAdjoiningFailurePhase.symm
    Iff.rfl).trans
      not_primeArchSourceMomentHankelExactReconstructionPhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate

/-- Certificate-only synchronized failure form. -/
theorem
    primeArchAllStrictHankelRayAdjoiningFailurePhase_or_not_hendenmalmSimplicity_iff_not_rhSimplicityCertificate :
    (PrimeArchAllStrictHankelRayAdjoiningFailurePhase ∨
        ¬XiHedenmalmSimplicityUniversalCertificate) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate :=
  (or_congr Iff.rfl
    (not_congr xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate).symm).trans
      primeArchAllStrictHankelRayAdjoiningFailurePhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate

end

end RHTower
