import GaloisForLFunctions.HTGeometry.MeromorphicRestrictionHypertranscendence

/-!
# Hasse reflection of hypertranscendence on meromorphic charts

Restriction from a connected meromorphic domain to a nonempty connected open subdomain is a
derivation-preserving field embedding.  It therefore reflects as well as preserves
hypertranscendence over the rational coordinate field.  One regular local chart contains the
complete algebraic-differential obstruction.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- Meromorphic hypertranscendence is equivalent to hypertranscendence on any nonempty connected
open subchart. -/
theorem hypertranscendentalOver_restrictMeroAlgHomRatFunc_hasse_iff
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
    HypertranscendentalOver (RatFunc ℂ) x ↔
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
  let e := restrictMeroAlgHomRatFunc hVU hUo hUc hUne hUinf
    hVo hVc hVne hVinf
  have hederiv : ∀ z : meroField U, e z′ = (e z)′ := by
    intro z
    exact restrictMeroAlgHomRatFunc_deriv
      hVU hUo hUc hUne hUinf hVo hVc hVne hVinf z
  exact (hypertranscendentalOver_algHom_iff e hederiv x).symm

end


end GaloisForLFunctions.HTGeometry
