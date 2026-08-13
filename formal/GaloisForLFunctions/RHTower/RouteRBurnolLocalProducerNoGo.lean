import GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux
import GaloisForLFunctions.RHTower.BurnolReflectedCoShiftCartierContinuation

/-!
# Route R Burnol local-producer no-go

The proposed Burnol source laws are pointwise impossible at every right-half
Xi divisor candidate.  This is not merely a clash of scalar signs:

* the fixed divided-shift Herglotz port has strictly positive real part;
* the reflected Cartier source lift is exactly its negative;
* Cartier zero-transfer strictly amplifies the fixed two-head energy; and
* the explicit oriented head current is strictly positive.

Consequently reflected sewing, physical dissipativity, two-head
non-amplification, and head-current dissipativity are each globally equivalent
to the Riemann hypothesis: under RH their right-half quantifiers are empty,
while any instance off the line contradicts the already constructed source
operators.  Thus none is an independent local Euler--Gamma--Stokes producer.
-/

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## Pointwise incompatibilities on the actual operators -/

/-- The constructed physical Herglotz port cannot be dissipative at a
right-half divisor candidate. -/
theorem not_xiDivisor_burnolDividedShiftPhysicalPort_re_nonpos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    ¬ (burnolDividedShiftPhysicalPort (rho : ℂ)).re ≤ 0 :=
  not_le.mpr (re_burnolDividedShiftPhysicalPort_pos h)

/-- The explicit oriented two-head current cannot be nonpositive at a
right-half divisor candidate. -/
theorem not_xiDivisor_burnolOrientedGammaHeadFlux_nonpos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    ¬ burnolSoninOrientedGammaHeadFlux (1 / 2)
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) ≤ 0 :=
  not_le.mpr
    (xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift_pos rho h)

/-- The constructed Cartier transfer cannot be non-amplifying on the fixed
two-head polarization at a right-half divisor candidate. -/
theorem not_xiDivisor_burnolCartierZeroTransferGammaHeadEnergy_nonamplifying
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    ¬ burnolSoninGammaHeadEnergy (1 / 2)
          (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) ≤
        burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom :=
  not_le.mpr
    (xiDivisor_burnolCartierZeroTransfer_strictly_amplifies_gammaHeadEnergy rho h)

/-- **Concrete sewing no-go.**  At a right-half divisor candidate the fixed
forward port cannot equal the constructed reflected zero-divided source
reading.  Their real parts have strict opposite signs. -/
theorem not_xiDivisor_burnolForwardReflectedCartierStokesSewing
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    ¬ burnolDividedShiftPhysicalPort (rho : ℂ) =
        inner ℂ burnolFixedSubWindowSourceAtom
          (burnolXiReflectedCoShiftCartierSourceLift rho h : evenSubspace) := by
  intro hsew
  have hpos : 0 < (burnolDividedShiftPhysicalPort (rho : ℂ)).re :=
    re_burnolDividedShiftPhysicalPort_pos h
  have hneg :
      (inner ℂ burnolFixedSubWindowSourceAtom
        (burnolXiReflectedCoShiftCartierSourceLift rho h : evenSubspace)).re < 0 := by
    rw [coe_burnolXiReflectedCoShiftCartierSourceLift]
    exact re_inner_burnolReflectedCoShiftContinuation_neg
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      burnolFixedSubWindowSourceAtom_ne_zero
  rw [hsew] at hpos
  linarith

/-! ## Exact global classification -/

/-- Physical-port dissipativity is exactly RH, not a weaker source lemma. -/
theorem burnolXiDividedShiftPhysicalDissipativity_iff_riemannHypothesis :
    BurnolXiDividedShiftPhysicalDissipativity ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_burnolXiDividedShiftPhysicalDissipativity
  · intro hRH rho h
    have hline := xi_divisor_support_re_eq_half_of_rh hRH rho
    exfalso
    linarith

/-- Oriented-head dissipativity is exactly RH, not a weaker source lemma. -/
theorem burnolXiCartierDividedShiftHeadFluxDissipativity_iff_riemannHypothesis :
    BurnolXiCartierDividedShiftHeadFluxDissipativity ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_burnolXiCartierDividedShiftHeadFluxDissipativity
  · intro hRH rho h
    have hline := xi_divisor_support_re_eq_half_of_rh hRH rho
    exfalso
    linarith

/-- Fixed two-head non-amplification is exactly RH, not a weaker source
contraction. -/
theorem burnolXiCartierZeroTransferGammaHeadEnergyNonamplification_iff_riemannHypothesis :
    BurnolXiCartierZeroTransferGammaHeadEnergyNonamplification ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_burnolXiCartierZeroTransferGammaHeadEnergyNonamplification
  · intro hRH rho h
    have hline := xi_divisor_support_re_eq_half_of_rh hRH rho
    exfalso
    linarith

/-- Forward/reflected Cartier sewing is exactly RH.  Pointwise it is
incompatible with the constructed Herglotz source operators; under RH the
right-half quantifier is empty. -/
theorem burnolXiForwardReflectedCartierStokesSewing_iff_riemannHypothesis :
    BurnolXiForwardReflectedCartierStokesSewing ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_burnolXiForwardReflectedCartierStokesSewing
  · intro hRH rho h
    have hline := xi_divisor_support_re_eq_half_of_rh hRH rho
    exfalso
    linarith

/-- The four alleged local producers are one RH-equivalent endpoint. -/
theorem burnolRouteRLocalProducer_equivalences :
    BurnolXiForwardReflectedCartierStokesSewing ↔
      BurnolXiDividedShiftPhysicalDissipativity ∧
      BurnolXiCartierDividedShiftHeadFluxDissipativity ∧
      BurnolXiCartierZeroTransferGammaHeadEnergyNonamplification := by
  rw [burnolXiForwardReflectedCartierStokesSewing_iff_riemannHypothesis,
    burnolXiDividedShiftPhysicalDissipativity_iff_riemannHypothesis,
    burnolXiCartierDividedShiftHeadFluxDissipativity_iff_riemannHypothesis,
    burnolXiCartierZeroTransferGammaHeadEnergyNonamplification_iff_riemannHypothesis]
  tauto

end

end RHTower
