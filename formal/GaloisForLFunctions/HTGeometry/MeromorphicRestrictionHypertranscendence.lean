import GaloisForLFunctions.HTGeometry.MeromorphicDifferentialField
import GaloisForLFunctions.HTGeometry.DifferentialClockEmbeddingCovariance

/-!
# Hypertranscendence descends to nonempty open meromorphic subdomains

Restriction from a connected meromorphic domain to a nonempty open connected subdomain is an
injective differential embedding over the rational coordinate field.  Consequently every
hypertranscendental meromorphic source on the ambient domain remains hypertranscendental after
restriction.

This is the missing local-observability bridge for physical response laws.  Global Gamma,
elliptic-Gamma, and Dirichlet sources can be restricted to a regular experimental or clock chart
without losing their complete differential resolution.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- The canonical meromorphic restriction as an algebra hom over the rational coordinate field. -/
def restrictMeroAlgHomRatFunc
    {U V : Set ℂ} (hVU : V ⊆ U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    letI : Algebra (RatFunc ℂ) (meroField V) :=
      (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    meroField U →ₐ[RatFunc ℂ] meroField V := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Algebra (RatFunc ℂ) (meroField V) :=
    (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  exact
    { Bottcher.restrictMeroHom hVU hUo hUc hUne hVo hVc hVne with
      commutes' := fun r => by
        exact RingHom.congr_fun
          (Bottcher.restrictMeroHom_ratfuncToMero
            hVU hUo hUc hUne hUinf hVo hVc hVne hVinf) r }

/-- Restriction is a differential algebra embedding over `C(z)`. -/
theorem restrictMeroAlgHomRatFunc_deriv
    {U V : Set ℂ} (hVU : V ⊆ U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (x : meroField U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    letI : Algebra (RatFunc ℂ) (meroField V) :=
      (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    letI := meroFieldDifferential hUo hUc hUne
    letI := meroFieldDifferential hVo hVc hVne
    restrictMeroAlgHomRatFunc hVU hUo hUc hUne hUinf
        hVo hVc hVne hVinf x′ =
      (restrictMeroAlgHomRatFunc hVU hUo hUc hUne hUinf
        hVo hVc hVne hVinf x)′ := by
  exact restrictMeroHom_deriv hVU hUo hUc hUne hVo hVc hVne x

/-- **Local HT persistence.**  A global meromorphic HT source remains HT on every nonempty open
connected subdomain. -/
theorem hypertranscendentalOver_restrictMeroAlgHomRatFunc
    {U V : Set ℂ} (hVU : V ⊆ U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (x : meroField U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    letI : Algebra (RatFunc ℂ) (meroField V) :=
      (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    letI := meroFieldDifferential hUo hUc hUne
    letI := meroFieldDifferential hVo hVc hVne
    HypertranscendentalOver (RatFunc ℂ) x →
      HypertranscendentalOver (RatFunc ℂ)
        (restrictMeroAlgHomRatFunc hVU hUo hUc hUne hUinf
          hVo hVc hVne hVinf x) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Algebra (RatFunc ℂ) (meroField V) :=
    (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  letI := meroFieldDifferential hUo hUc hUne
  letI := meroFieldDifferential hVo hVc hVne
  intro hx
  let e := restrictMeroAlgHomRatFunc hVU hUo hUc hUne hUinf
    hVo hVc hVne hVinf
  have hederiv : ∀ z : meroField U, e z′ = (e z)′ := by
    intro z
    exact restrictMeroAlgHomRatFunc_deriv
      hVU hUo hUc hUne hUinf hVo hVc hVne hVinf z
  apply (hypertranscendentalOver_algHom_iff e hederiv x).2
  exact hx

set_option synthInstance.maxHeartbeats 20000

end

end GaloisForLFunctions.HTGeometry
