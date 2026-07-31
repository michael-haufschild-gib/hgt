import GaloisForLFunctions.HTGeometry.LocalSpectralObserverSteinerLaw
import GaloisForLFunctions.HTGeometry.AnalyticOrderRigidityLaw

/-!
# Locality bounds the birth order of observer time

The local spectral observer law supplies a geometric Big-O onset.  Analytic
order rigidity turns that asymptotic statement into an intrinsic statement
about the first nonzero Taylor layer.  Thus every active observer clock is
born no earlier than the smallest connected interaction packet spanning all
sites queried by that observer.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

noncomputable section

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- Scalar coupling-ray response of a site-Möbius spectral observer. -/
def spectralObserverCouplingRay
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ) (g : ℂ) : ℂ :=
  L.productSpectralInteractionShiftSiteContrast
    onsite hinj x alternative sites (g • z)

omit [∀ (v : V), Nonempty (A v)] in
/-- Every local spectral-observer coupling ray is analytic at zero. -/
theorem spectralObserverCouplingRay_analyticAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ) :
    AnalyticAt ℂ
      (spectralObserverCouplingRay
        L onsite hinj x alternative sites z) 0 := by
  unfold spectralObserverCouplingRay
  unfold productSpectralInteractionShiftSiteContrast
  unfold dependentHigherCoordinateContrast finsetMobiusResponse
  apply Finset.analyticAt_fun_sum
  intro d hd
  unfold productSpectralInteractionShift
  let config :=
    dependentUpdateOnFinset x alternative (sites \ d)
  have hray :
      AnalyticAt ℂ (fun g : ℂ => g • z) 0 := by
    fun_prop
  have hbranch :=
    (L.productEigenvalueBranch_spec onsite hinj config).1
  have hcomp :
      AnalyticAt ℂ
        (fun g : ℂ =>
          L.productEigenvalueBranch onsite hinj config
            (g • z)) 0 := by
    have hc := hbranch.comp_of_eq hray (by simp)
    simpa [Function.comp_def] using hc
  exact analyticAt_const.mul (hcomp.sub analyticAt_const)

/-- Canonical scalar Taylor series of a local spectral-observer ray. -/
def spectralObserverCouplingRaySeries
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n =>
      iteratedDeriv n
        (spectralObserverCouplingRay
          L onsite hinj x alternative sites z) 0 /
          n.factorial)

omit [∀ (v : V), Nonempty (A v)] in
theorem spectralObserverCouplingRay_hasFPowerSeriesAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ) :
    HasFPowerSeriesAt
      (spectralObserverCouplingRay
        L onsite hinj x alternative sites z)
      (spectralObserverCouplingRaySeries
        L onsite hinj x alternative sites z) 0 := by
  exact
    (spectralObserverCouplingRay_analyticAt
      L onsite hinj x alternative sites z).hasFPowerSeriesAt

/-- **Local spectral temporal-birth law.** If an observer response is an
active analytic germ and every connected packet spanning that observer has
at least `r` interactions, then its exact birth order is at least `r`. -/
theorem observerSteinerLowerBound_le_spectralObserverCouplingRaySeries_order
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (z : E → ℂ)
    (hactive :
      ¬spectralObserverCouplingRay L onsite hinj
          x alternative sites z
        =ᶠ[𝓝 0] fun _ => 0)
    (r : ℕ) (hr : ObserverSteinerLowerBound L sites r) :
    r ≤
      (spectralObserverCouplingRaySeries L onsite hinj
        x alternative sites z).order := by
  have hf :=
    spectralObserverCouplingRay_hasFPowerSeriesAt
      L onsite hinj x alternative sites z
  have hseries :
      spectralObserverCouplingRaySeries L onsite hinj
        x alternative sites z ≠ 0 := by
    intro hzero
    apply hactive
    exact HasFPowerSeriesAt.eventually_eq_zero
      (by simpa [hzero] using hf)
  apply le_fpowerSeries_order_of_isBigO_norm_pow hf hseries r
  exact
    L.productSpectralInteractionShiftSiteContrast_couplingRay_isBigO
      onsite hinj x alternative sites r hr z

end

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
