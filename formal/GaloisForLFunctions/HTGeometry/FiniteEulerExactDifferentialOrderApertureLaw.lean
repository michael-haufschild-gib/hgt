import GaloisForLFunctions.HTGeometry.RationalPhaseCharacterRankAperture
import GaloisForLFunctions.HTGeometry.FiniteEulerGammaMeroAperture
import GaloisForLFunctions.HTGeometry.ZetaHypertranscendence
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import Mathlib.NumberTheory.PrimeCounting

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Canonical finite packet of primes at most `N`. -/
def finitePrimePacketLE (N : ℕ) : Finset Nat.Primes :=
  (((Finset.Iic N).filter Nat.Prime).attach).map
    (⟨fun p => ⟨p.1, (Finset.mem_filter.mp p.2).2⟩,
      fun _ _ h =>
        Subtype.ext (congrArg (fun q : Nat.Primes => (q : ℕ)) h)⟩ :
      {p // p ∈ (Finset.Iic N).filter Nat.Prime} ↪ Nat.Primes)

/-- The canonical packet has exactly `π(N)` primes. -/
theorem card_finitePrimePacketLE (N : ℕ) :
    (finitePrimePacketLE N).card = Nat.primeCounting N := by
  rw [finitePrimePacketLE, Finset.card_map, Finset.card_attach]
  change ((Finset.Iic N).filter Nat.Prime).card = Nat.count Nat.Prime (N + 1)
  rw [Nat.count_eq_card_filter_range, Nat.range_succ_eq_Iic]

/-- All constant- and Gamma-coefficient differential orders asserted by the
finite Euler aperture law, packaged without auxiliary premises. -/
def FiniteEulerExactDifferentialOrderLaw (S : Finset Nat.Primes) : Prop :=
  autonomousMinimalOrder
      (phaseFunction (finitePrimeFrequency S)
        (polynomialPhaseObservable
          (eulerInverseAnchorPolynomial (finitePrimeDamping S)))) =
      Fintype.card ↥S ∧
  autonomousMinimalOrder (finiteEulerProductPhase S) = Fintype.card ↥S ∧
  autonomousMinimalOrder (finiteEulerFluxPhase S) = Fintype.card ↥S ∧
  autonomousMinimalOrder (finiteEulerCharacteristicDet S) = Fintype.card ↥S ∧
  gammaMeroMinimalOrder (finiteEulerAnchorMero S) = Fintype.card ↥S ∧
  gammaMeroMinimalOrder (finiteEulerProductMero S) = Fintype.card ↥S ∧
  gammaMeroMinimalOrder (finiteEulerFluxMero S) = Fintype.card ↥S

/-- Exact finite-Euler aperture law for every finite prime packet. -/
theorem finiteEulerExactDifferentialOrderLaw (S : Finset Nat.Primes) :
    FiniteEulerExactDifferentialOrderLaw S := by
  refine ⟨autonomousMinimalOrder_finiteEulerInverseAnchor_eq S,
    autonomousMinimalOrder_finiteEulerProductPhase_eq S,
    autonomousMinimalOrder_finiteEulerFluxPhase_eq S,
    autonomousMinimalOrder_finiteEulerCharacteristicDet_eq S,
    gammaMeroMinimalOrder_finiteEulerAnchor_eq S,
    gammaMeroMinimalOrder_finiteEulerProduct_eq S,
    gammaMeroMinimalOrder_finiteEulerFlux_eq S⟩

/-- Canonical cutoff form: every displayed order is exactly `π(N)`. -/
theorem finiteEulerExactDifferentialOrderLaw_below (N : ℕ) :
    autonomousMinimalOrder
        (finiteEulerCharacteristicDet (finitePrimePacketLE N)) =
        Nat.primeCounting N ∧
    autonomousMinimalOrder
        (finiteEulerProductPhase (finitePrimePacketLE N)) =
        Nat.primeCounting N ∧
    autonomousMinimalOrder
        (finiteEulerFluxPhase (finitePrimePacketLE N)) =
        Nat.primeCounting N ∧
    gammaMeroMinimalOrder
        (finiteEulerAnchorMero (finitePrimePacketLE N)) =
        Nat.primeCounting N ∧
    gammaMeroMinimalOrder
        (finiteEulerProductMero (finitePrimePacketLE N)) =
        Nat.primeCounting N ∧
    gammaMeroMinimalOrder
        (finiteEulerFluxMero (finitePrimePacketLE N)) =
        Nat.primeCounting N := by
  simp only [autonomousMinimalOrder_finiteEulerCharacteristicDet_eq,
    autonomousMinimalOrder_finiteEulerProductPhase_eq,
    autonomousMinimalOrder_finiteEulerFluxPhase_eq,
    gammaMeroMinimalOrder_finiteEulerAnchor_eq,
    gammaMeroMinimalOrder_finiteEulerProduct_eq,
    gammaMeroMinimalOrder_finiteEulerFlux_eq,
    Fintype.card_coe, card_finitePrimePacketLE, and_self]

/-- Gamma-relative finite Euler order recedes to infinity along canonical
prime cutoffs. -/
theorem tendsto_gammaMeroMinimalOrder_finiteEulerFlux_below :
    Tendsto
      (fun N => gammaMeroMinimalOrder
        (finiteEulerFluxMero (finitePrimePacketLE N))) atTop atTop := by
  simpa [gammaMeroMinimalOrder_finiteEulerFlux_eq, Fintype.card_coe,
    card_finitePrimePacketLE] using Nat.tendsto_primeCounting

local instance finiteEulerLawDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance finiteEulerLawIntAlgebra : Algebra ℤ upperEndMeroField :=
  Ring.toIntAlgebra _

local instance finiteEulerLawDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance finiteEulerLawComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance finiteEulerLawRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance finiteEulerLawRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance finiteEulerLawRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

local instance finiteEulerLawGammaFieldDifferentialAlgebra :
    DifferentialAlgebra ↥gammaCoefficientField upperEndMeroField where
  deriv_algebraMap _ := rfl

local instance finiteEulerLawCharZero : CharZero upperEndMeroField where
  cast_injective := by
    intro m n h
    apply Nat.cast_injective (R := ℂ)
    apply upperEndComplexToMero.injective
    simpa using h

/-- Meromorphic infinite Euler logarithmic source `-ζ'/ζ` in the upper-end
carrier. -/
def infiniteEulerLogarithmicSourceMero : upperEndMeroField :=
  -((algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic)′ /
    algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic)

/-- The infinite Euler logarithmic source is hypertranscendental over the
Euler--Gamma coefficient field. -/
theorem infiniteEulerLogarithmicSourceMero_hypertranscendentalOver_gammaCoefficientField
    {σ : ℝ} (hσ : 1 < σ) :
    HypertranscendentalOver ↥gammaCoefficientField
      infiniteEulerLogarithmicSourceMero := by
  let zetaMero :=
    algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic
  have hlog : HypertranscendentalOver ↥gammaCoefficientField
      (zetaMero′ / zetaMero) :=
    (hypertranscendentalOver_deriv_div_self_iff zetaMero).2
      (zeta_hypertranscendentalOver_gammaCoefficientField hσ)
  intro hsource
  apply hlog
  have hneg := differentialAlgebraicOver_neg hsource
  simpa [infiniteEulerLogarithmicSourceMero, zetaMero] using hneg

end

end GaloisForLFunctions.HTGeometry

