import GaloisForLFunctions.RHTower.CCMRestrictedWeilSourceAlignedArbitraryAccuracy

/-!
# Finite literal source obstruction from a physical null vector

The arbitrary-accuracy Gamma--Slepian reduction does not merely localize a negative direction.
It turns every nonzero physical vector of zero completed source energy into a finite actual source
head on which the literal von Mangoldt compression almost compensates the full norm, scalar Gamma,
and rank-two polar terms.  The loss is arbitrarily prescribed; no spectral or RH premise enters.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

namespace RHTower

/-- Every nonzero physical null vector of the literal completed source has, at every positive
accuracy, a finite peripheral Gamma--Slepian source head with literal prime overcompensation.
The statement retains the coupled prime, polar, and scalar Gamma terms exactly. -/
theorem exists_ccmRestrictedWeil_finitePrimeOvercompensation_of_physical_sourceNull
    (a : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain a)
    (hphysical : ccmArchimedeanFormToAperture a q ≠ 0)
    (hnull : ccmRestrictedWeilSourceQuadratic a q = 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : CCMRestrictedWeilSourceApproximationCertificate a delta,
      let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection q
      h ≠ 0 ∧
        (1 - delta) * ‖h‖ ^ 2 +
            (inner ℂ
              ((ccmArchimedeanRemainderScalar •
                ccmArchimedeanGammaSlepianGram a) h) h).re +
            (inner ℂ (ccmRestrictedWeilFormPolarCompression a h) h).re ≤
          (inner ℂ (ccmRestrictedWeilFormPrimeCompression a h) h).re := by
  obtain ⟨C⟩ := exists_ccmRestrictedWeil_sourceApproximationCertificate a hdelta
  refine ⟨C, ?_⟩
  have hqne : q ≠ 0 := by
    intro hq
    apply hphysical
    rw [hq, map_zero]
  have hqnonpos : (ccmRestrictedWeilForm a q q).re ≤ 0 := by
    rw [ccmRestrictedWeilForm_self_re_eq_source, hnull]
  exact C.sourceHead_prime_overcompensation_of_nonpositive hdelta q hqne hqnonpos

end RHTower
