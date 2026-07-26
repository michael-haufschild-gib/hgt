import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.MobiusLiouvilleSquareDilationWall
import GaloisForLFunctions.RHTower.MobiusMertensSelfConvolutionCriterion

/-!
# Möbius energy/analytic-unit wall universality law

The Mellin--Plancherel route turns strict-right logarithmic energy into the canonical Möbius
continuation wall.  Independently, multiplication by any analytic nowhere-zero target factor was
shown to preserve that wall.  Their composition yields a source theorem for every analytic-unit
twist at once, including the Liouville square-dilation channel.  Under the classical decay
converse, energy, every analytic-unit wall, the Liouville wall, and RH are identical predicates.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Every strict-right Möbius logarithmic-energy certificate constructs the continuation wall
twisted by an arbitrary analytic unit. -/
theorem mobiusLaplaceUnitTwistedMellinContinuationWall_of_strictRightEnergyFinite
    {U : ℂ → ℂ} (hU : AnalyticOnNhd ℂ U rightHalf)
    (hUne : ∀ s ∈ rightHalf, U s ≠ 0)
    (henergy : MobiusLaplaceStrictRightEnergyFinite) :
    MobiusLaplaceUnitTwistedMellinContinuationWall U :=
  (mobiusLaplaceUnitTwistedMellinContinuationWall_iff hU hUne).2
    (mobiusLaplaceMellinContinuationWall_of_strictRightEnergyFinite henergy)

/-- Under the standard RH-to-decay converse, strict-right energy is exactly every analytic-unit
twisted continuation wall. -/
theorem mobiusLaplaceStrictRightEnergyFinite_iff_unitTwistedWall_of_decay
    {U : ℂ → ℂ} (hU : AnalyticOnNhd ℂ U rightHalf)
    (hUne : ∀ s ∈ rightHalf, U s ≠ 0)
    (hLittlewood : RiemannHypothesis → MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    MobiusLaplaceStrictRightEnergyFinite ↔
      MobiusLaplaceUnitTwistedMellinContinuationWall U :=
  (mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_decay hLittlewood).trans
    (((mobiusLaplaceUnitTwistedMellinContinuationWall_iff hU hUne).trans
      mobiusLaplaceMellinContinuationWall_iff_riemannHypothesis).symm)

/-- One classical RH-to-Mertens premise supplies the decay converse and identifies strict-right
energy with RH. -/
theorem mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_mertens
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusLaplaceStrictRightEnergyFinite ↔ RiemannHypothesis :=
  mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_decay
    (fun hRH =>
      mobiusMertensAllStrictHalfPowerBound_implies_allStrictHalfPowerDecay
        (hLittlewood hRH))

/-- The same Mertens premise identifies cofinal strict-right energy with RH. -/
theorem mobiusLaplaceCofinalStrictRightEnergyFinite_iff_riemannHypothesis_of_mertens
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusLaplaceCofinalStrictRightEnergyFinite ↔ RiemannHypothesis :=
  mobiusLaplaceCofinalStrictRightEnergyFinite_iff_riemannHypothesis_of_decay
    (fun hRH =>
      mobiusMertensAllStrictHalfPowerBound_implies_allStrictHalfPowerDecay
        (hLittlewood hRH))

/-- Under the single classical RH-to-Mertens premise, strict-right energy is exactly every
analytic-unit twisted continuation wall. -/
theorem mobiusLaplaceStrictRightEnergyFinite_iff_unitTwistedWall_of_mertens
    {U : ℂ → ℂ} (hU : AnalyticOnNhd ℂ U rightHalf)
    (hUne : ∀ s ∈ rightHalf, U s ≠ 0)
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusLaplaceStrictRightEnergyFinite ↔
      MobiusLaplaceUnitTwistedMellinContinuationWall U :=
  (mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_mertens
      hLittlewood).trans
    (((mobiusLaplaceUnitTwistedMellinContinuationWall_iff hU hUne).trans
      mobiusLaplaceMellinContinuationWall_iff_riemannHypothesis).symm)

/-- The Liouville square-dilation wall is constructed directly from strict-right Möbius energy. -/
theorem mobiusLiouvilleSquareDilationMellinContinuationWall_of_strictRightEnergyFinite
    (henergy : MobiusLaplaceStrictRightEnergyFinite) :
    MobiusLiouvilleSquareDilationMellinContinuationWall :=
  mobiusLaplaceUnitTwistedMellinContinuationWall_of_strictRightEnergyFinite
    mobiusLiouvilleSquareDilationUnit_analyticOnNhd
    (fun _ hs => mobiusLiouvilleSquareDilationUnit_ne_zero hs) henergy

/-- Cofinal strict-right energy already constructs the Liouville wall. -/
theorem mobiusLiouvilleSquareDilationMellinContinuationWall_of_cofinalEnergyFinite
    (henergy : MobiusLaplaceCofinalStrictRightEnergyFinite) :
    MobiusLiouvilleSquareDilationMellinContinuationWall :=
  mobiusLiouvilleSquareDilationMellinContinuationWall_of_strictRightEnergyFinite
    (mobiusLaplaceStrictRightEnergyFinite_of_cofinalStrictRightEnergyFinite henergy)

/-- **Möbius energy/Liouville-wall universality law.**  Under the classical decay converse, the
Möbius logarithmic-energy source is exactly the Liouville square-dilation continuation wall. -/
theorem mobiusLaplaceStrictRightEnergyFinite_iff_liouvilleSquareDilationWall_of_decay
    (hLittlewood : RiemannHypothesis → MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    MobiusLaplaceStrictRightEnergyFinite ↔
      MobiusLiouvilleSquareDilationMellinContinuationWall :=
  mobiusLaplaceStrictRightEnergyFinite_iff_unitTwistedWall_of_decay
    mobiusLiouvilleSquareDilationUnit_analyticOnNhd
    (fun _ hs => mobiusLiouvilleSquareDilationUnit_ne_zero hs) hLittlewood

/-- The single classical RH-to-Mertens premise also identifies Möbius logarithmic energy with the
Liouville square-dilation wall. -/
theorem mobiusLaplaceStrictRightEnergyFinite_iff_liouvilleSquareDilationWall_of_mertens
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusLaplaceStrictRightEnergyFinite ↔
      MobiusLiouvilleSquareDilationMellinContinuationWall :=
  mobiusLaplaceStrictRightEnergyFinite_iff_unitTwistedWall_of_mertens
    mobiusLiouvilleSquareDilationUnit_analyticOnNhd
    (fun _ hs => mobiusLiouvilleSquareDilationUnit_ne_zero hs) hLittlewood

end

end RHTower
