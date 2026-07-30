import GaloisForLFunctions.HTGeometry.AnalyticOrderRigidityLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalBirthValuationLaw
import GaloisForLFunctions.HTGeometry.WeightedObserverTemporalSteinerLaw

/-!
# Exact weighted birth of observer-temporal sectors

Weighted locality gives an asymptotic lower bound.  Analytic order rigidity
turns that bound into an exact statement about the first nonzero Taylor
coefficient of every active temporal sector.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

/-- **Exact weighted packet birth law.**  If a weighted interaction-packet
ray is active, its exact analytic birth order is at least the sum of the
positive interaction weights in the packet. -/
theorem interactionPacketWeight_le_analyticBirthOrder
    {E : Type*} [Fintype E] [DecidableEq E]
    {branch : (E → ℂ) → ℂ}
    (hbranch : AnalyticAt ℂ branch 0)
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e ∈ packet, 0 < weight e)
    (z : E → ℂ)
    {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hseries :
      HasFPowerSeriesAt
        (fun g : ℂ =>
          spectralPacketResponse branch packet
            (fun e => g ^ weight e * z e))
        series 0)
    (hactive :
      AnalyticSectorActive
        (fun g : ℂ =>
          spectralPacketResponse branch packet
            (fun e => g ^ weight e * z e))) :
    (∑ e ∈ packet, weight e) ≤ analyticBirthOrder series := by
  apply le_fpowerSeries_order_of_isBigO_norm_pow
    hseries
    (series_ne_zero_of_analyticSectorActive hseries hactive)
  exact spectralPacketResponse_globalWeightedMonomialRay_isBigO
    branch hbranch packet weight hpos z

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- Observer response along a positive integer-weighted interaction
switch-on schedule. -/
noncomputable def weightedSpectralObserverRay
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (z : E → ℂ) (g : ℂ) : ℂ :=
  L.productSpectralInteractionShiftSiteContrast onsite hinj
    x alternative sites
      (fun e => g ^ weight e * z e)

/-- Every weighted local observer ray is analytic at zero. -/
theorem weightedSpectralObserverRay_analyticAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℂ) :
    AnalyticAt ℂ
      (L.weightedSpectralObserverRay onsite hinj
        x alternative sites weight z) 0 := by
  let coupling : ℂ → (E → ℂ) :=
    fun g e => g ^ weight e * z e
  have hcoupling : AnalyticAt ℂ coupling 0 := by
    dsimp [coupling]
    apply AnalyticAt.pi
    intro e
    fun_prop
  have hcoupling0 : coupling 0 = 0 := by
    funext e
    simp [coupling, Nat.ne_of_gt (hpos e)]
  unfold weightedSpectralObserverRay
  unfold productSpectralInteractionShiftSiteContrast
  unfold dependentHigherCoordinateContrast finsetMobiusResponse
  apply Finset.analyticAt_fun_sum
  intro d hd
  unfold productSpectralInteractionShift
  let config :=
    dependentUpdateOnFinset x alternative (sites \ d)
  have hbranch :=
    (L.productEigenvalueBranch_spec onsite hinj config).1
  have hcomp :
      AnalyticAt ℂ
        (fun g : ℂ =>
          L.productEigenvalueBranch onsite hinj config
            (coupling g)) 0 := by
    simpa [Function.comp_def] using
      hbranch.comp_of_eq hcoupling hcoupling0
  exact analyticAt_const.mul (hcomp.sub analyticAt_const)

/-- Canonical Taylor series of a weighted local observer ray. -/
noncomputable def weightedSpectralObserverRaySeries
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  Classical.choose
    (L.weightedSpectralObserverRay_analyticAt onsite hinj
      x alternative sites weight hpos z)

/-- Canonical weighted observer series represents its ray. -/
theorem weightedSpectralObserverRaySeries_spec
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℂ) :
    HasFPowerSeriesAt
      (L.weightedSpectralObserverRay onsite hinj
        x alternative sites weight z)
      (L.weightedSpectralObserverRaySeries onsite hinj
        x alternative sites weight hpos z) 0 :=
  Classical.choose_spec
    (L.weightedSpectralObserverRay_analyticAt onsite hinj
      x alternative sites weight hpos z)

/-- **Exact weighted observer-Steiner birth law.** If a local observer
contrast is active along an inhomogeneous switch-on schedule, its exact
analytic birth order is at least every certified weighted connected-spanning
cost. -/
theorem weightedObserverSteinerLowerBound_le_analyticBirthOrder
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (r : ℕ)
    (hr : WeightedObserverSteinerLowerBound L sites weight r)
    (z : E → ℂ)
    {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hseries :
      HasFPowerSeriesAt
        (fun g : ℂ =>
          L.productSpectralInteractionShiftSiteContrast onsite hinj
            x alternative sites
              (fun e => g ^ weight e * z e))
        series 0)
    (hactive :
      AnalyticSectorActive
        (fun g : ℂ =>
          L.productSpectralInteractionShiftSiteContrast onsite hinj
            x alternative sites
              (fun e => g ^ weight e * z e))) :
    r ≤ analyticBirthOrder series := by
  apply le_fpowerSeries_order_of_isBigO_norm_pow
    hseries
    (series_ne_zero_of_analyticSectorActive hseries hactive)
  exact
    L.productSpectralInteractionShiftSiteContrast_weightedMonomialRay_isBigO
      onsite hinj x alternative sites weight hpos r hr z

/-- Unconditional canonical-series form of exact weighted observer birth. -/
theorem weightedObserverSteinerLowerBound_le_weightedObserverSeries_order
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℂ)
    (hactive :
      AnalyticSectorActive
        (L.weightedSpectralObserverRay onsite hinj
          x alternative sites weight z))
    (r : ℕ)
    (hr : WeightedObserverSteinerLowerBound L sites weight r) :
    r ≤
      (L.weightedSpectralObserverRaySeries onsite hinj
        x alternative sites weight hpos z).order := by
  have hseries :=
    L.weightedSpectralObserverRaySeries_spec onsite hinj
      x alternative sites weight hpos z
  exact L.weightedObserverSteinerLowerBound_le_analyticBirthOrder
    onsite hinj x alternative sites weight hpos r hr z
      hseries hactive

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
