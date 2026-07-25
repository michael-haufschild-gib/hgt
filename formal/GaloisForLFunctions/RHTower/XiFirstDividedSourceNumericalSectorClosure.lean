import GaloisForLFunctions.RHTower.XiFirstDividedSourceNumericalSector

/-!
# First-divided numerical-sector closure

Under RH every centered Xi spectral point is real.  The exact first-divided numerical-value
identity therefore puts every Xi-annihilating Hilbert quotient in the upper numerical sector.
For a quotient which also retains every first divided source, the sector condition is thus
equivalent to RH.  The canonical two-point quotient supplies both structural conditions
unconditionally.
-/

open Complex

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Under RH, source annihilation alone puts every first-divided numerical value on the boundary
of the upper sector.  No faithfulness or simplicity hypothesis is needed in this direction. -/
theorem firstDividedSourceUpperNumericalSector_of_riemannHypothesis
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (hsource : J XiC = 0)
    (hRH : RiemannHypothesis) :
    XiFirstDividedSourceUpperNumericalSector J := by
  intro rho
  rw [xiFirstDividedSourceNumericalValue_im_eq J hsource rho]
  let q : XiZeroCopy :=
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have hs : xiSpectralPointSupport rho = (t : ℂ) := by
    simpa only [q, xiSpectralPoint_eq_support] using ht
  rw [hs]
  simp

/-- For every Xi-annihilating quotient which retains all first divided sources, the upper
numerical-sector condition is exactly RH. -/
theorem firstDividedSourceUpperNumericalSector_iff_riemannHypothesis
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (hsource : J XiC = 0)
    (hfaithful : ∀ rho : XiDivisorSupport,
      J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0) :
    XiFirstDividedSourceUpperNumericalSector J ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_firstDividedSourceUpperNumericalSector
      J hsource hfaithful,
    firstDividedSourceUpperNumericalSector_of_riemannHypothesis J hsource⟩

/-- For any two distinct regular source points, the two-point first-divided numerical sector is
exactly RH; annihilation and fiberwise faithfulness are consequences of the source formula. -/
theorem twoPointFirstDividedSourceUpperNumericalSector_iff_riemannHypothesis
    (u v : XiCRegularPoint) (huv : (u : ℂ) ≠ v) :
    XiFirstDividedSourceUpperNumericalSector
        (xiTwoPointSourceQuotient u v) ↔
      RiemannHypothesis :=
  firstDividedSourceUpperNumericalSector_iff_riemannHypothesis
    (xiTwoPointSourceQuotient u v)
    (xiTwoPointSourceQuotient_XiC u v)
    (xiTwoPointSourceQuotient_firstDivided_ne_zero u v huv)

/-- The fixed prime-source two-point numerical-sector interface has no independent hypothesis:
it is an exact RH criterion. -/
theorem canonicalTwoPointFirstDividedSourceUpperNumericalSector_iff_riemannHypothesis :
    XiFirstDividedSourceUpperNumericalSector
        (xiTwoPointSourceQuotient
          xiPrimeSourceRegularPointOne xiPrimeSourceRegularPointTwo) ↔
      RiemannHypothesis :=
  twoPointFirstDividedSourceUpperNumericalSector_iff_riemannHypothesis
    xiPrimeSourceRegularPointOne xiPrimeSourceRegularPointTwo
    xiPrimeSourceRegularPointOne_ne_two

end RHTower
