import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.MeromorphicRestrictionHypertranscendence

/-!
# Local analytic exponential clocks in meromorphic differential fields

An analytic latent clock on a nonempty connected open chart defines an element of the chart's
meromorphic function field.  Its pointwise exponential is a nonzero element whose logarithmic
derivative is exactly the derivative of the latent clock.  Consequently an analytic
hypertranscendental clock remains hypertranscendental after exponentiation.

The construction is local: it applies on any pole-free observation chart, not only to entire
functions.  The file also proves that the canonical `C(z)` embedding into every such chart
intertwines the rational-coordinate derivation with meromorphic differentiation.  This supplies
the differential-algebra instance needed to apply the general observability theorems locally.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- An analytic function on `U`, represented as an element of the analytic germ domain. -/
def analyticFunctionElement {U : Set ℂ} (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) : analyticSubring U :=
  ⟨(f : Germ (𝒷 U) ℂ), ⟨f, hf, rfl⟩⟩

/-- The pointwise exponential of a local analytic function, as an analytic germ. -/
def analyticExponentialElement {U : Set ℂ} (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) : analyticSubring U :=
  analyticFunctionElement (fun z ↦ Complex.exp (f z)) hf.cexp

/-- The local exponential phase differentiates as `exp(f) * f'` inside the analytic-germ
domain. -/
theorem analyticSubringDeriv_analyticExponentialElement
    {U : Set ℂ} (hUo : IsOpen U) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) :
    analyticSubringDeriv hUo (analyticExponentialElement f hf) =
      analyticExponentialElement f hf *
        analyticSubringDeriv hUo (analyticFunctionElement f hf) := by
  apply Subtype.ext
  change (deriv (fun z ↦ Complex.exp (f z)) : Germ (𝒷 U) ℂ) =
    (↑(fun z ↦ Complex.exp (f z)) : Germ (𝒷 U) ℂ) *
      (↑(deriv f) : Germ (𝒷 U) ℂ)
  rw [← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr fun z hz ↦
    (hf z hz).differentiableAt.hasDerivAt.cexp.deriv

/-- A pointwise complex exponential is nonzero as an analytic germ on every nonempty chart. -/
theorem analyticExponentialElement_ne_zero
    {U : Set ℂ} (hUne : U.Nonempty) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) :
    analyticExponentialElement f hf ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ := hUne
  have hgerm := congrArg Subtype.val hzero
  change (↑(fun w ↦ Complex.exp (f w)) : Germ (𝒷 U) ℂ) = 0 at hgerm
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  exact Complex.exp_ne_zero (f z) (eventually_principal.mp hgerm z hz)

/-- The analytic exponential phase remains nonzero after embedding in the local meromorphic
fraction field. -/
theorem analyticExponentialMero_ne_zero
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    algebraMap (analyticSubring U) (meroField U)
        (analyticExponentialElement f hf) ≠ 0 := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  exact (map_ne_zero (algebraMap (analyticSubring U) (meroField U))).2
    (analyticExponentialElement_ne_zero hUne f hf)

/-- **Local analytic logarithmic-derivative identity.**  In the genuine meromorphic field of a
chart, the exponential observation has logarithmic derivative equal to the derivative of its
latent analytic clock. -/
theorem analyticExponentialMero_logDeriv
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroFieldDifferential hUo hUc hUne
    (algebraMap (analyticSubring U) (meroField U)
          (analyticExponentialElement f hf))′ /
        algebraMap (analyticSubring U) (meroField U)
          (analyticExponentialElement f hf) =
      (algebraMap (analyticSubring U) (meroField U)
          (analyticFunctionElement f hf))′ := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroFieldDifferential hUo hUc hUne
  rw [meroFieldDifferential_algebraMap,
    analyticSubringDeriv_analyticExponentialElement, map_mul,
    meroFieldDifferential_algebraMap]
  field_simp [analyticExponentialMero_ne_zero hUo hUc hUne f hf]

set_option synthInstance.maxHeartbeats 100000

/-- The rational-coordinate embedding into the meromorphic field of an arbitrary nonempty
connected open chart commutes with differentiation.  The previously available compatibility law
was global (`U = C`); restriction makes it local without changing the rational coordinate. -/
theorem meroField_deriv_ratfuncToMero_on
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (r : RatFunc ℂ) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroFieldDifferential hUo hUc hUne
    (ratfuncToMero U hUo hUc hUne hUinf r)′ =
      ratfuncToMero U hUo hUc hUne hUinf
        (GaloisForLFunctions.HTGeometry.ratFuncCoordinateDerivation ℂ r) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroFieldDifferential hUo hUc hUne
  letI : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
    Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
      isPreconnected_univ Set.univ_nonempty
  letI : Differential (meroField (Set.univ : Set ℂ)) :=
    meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  let ρ : meroField Set.univ →+* meroField U :=
    Bottcher.restrictMeroHom (Set.subset_univ U)
      isOpen_univ isPreconnected_univ Set.univ_nonempty
      hUo hUc hUne
  have hfix := Bottcher.restrictMeroHom_ratfuncToMero
    (Set.subset_univ U)
    isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ
    hUo hUc hUne hUinf
  have hr : ρ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ r) =
      ratfuncToMero U hUo hUc hUne hUinf r :=
    RingHom.congr_fun hfix r
  have hdr : ρ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ
        (GaloisForLFunctions.HTGeometry.ratFuncCoordinateDerivation ℂ r)) =
      ratfuncToMero U hUo hUc hUne hUinf
        (GaloisForLFunctions.HTGeometry.ratFuncCoordinateDerivation ℂ r) :=
    RingHom.congr_fun hfix _
  calc
    (ratfuncToMero U hUo hUc hUne hUinf r)′ =
        (ρ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r))′ := by rw [hr]
    _ = ρ ((ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r)′) := by
      rw [restrictMeroHom_deriv]
    _ = ρ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ
            (GaloisForLFunctions.HTGeometry.ratFuncCoordinateDerivation ℂ r)) := by
      rw [GaloisForLFunctions.meroField_deriv_ratfuncToMero]
    _ = ratfuncToMero U hUo hUc hUne hUinf
          (GaloisForLFunctions.HTGeometry.ratFuncCoordinateDerivation ℂ r) := hdr

/-- The canonical `C(z)`-algebra structure on a local meromorphic chart is differential. -/
@[reducible] def meroFieldRatFuncDifferentialAlgebra
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    letI : Differential (RatFunc ℂ) :=
      GaloisForLFunctions.ratFuncCoordinateDifferential
    letI := meroFieldDifferential hUo hUc hUne
    DifferentialAlgebra (RatFunc ℂ) (meroField U) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Differential (RatFunc ℂ) :=
    GaloisForLFunctions.ratFuncCoordinateDifferential
  letI := meroFieldDifferential hUo hUc hUne
  exact ⟨fun r ↦ meroField_deriv_ratfuncToMero_on hUo hUc hUne hUinf r⟩

/-- **Concrete local exponential-clock transfer.**  If an analytic clock is
hypertranscendental in the meromorphic differential field of a chart, its actual pointwise
exponential is hypertranscendental on the same chart.  The logarithmic-derivative hypothesis of
the abstract observation theorem is discharged by complex analysis. -/
theorem hypertranscendentalOver_analyticExponentialMero
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    letI : Differential (RatFunc ℂ) :=
      GaloisForLFunctions.ratFuncCoordinateDifferential
    letI := meroFieldDifferential hUo hUc hUne
    letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
      meroFieldRatFuncDifferentialAlgebra hUo hUc hUne hUinf
    HypertranscendentalOver (RatFunc ℂ)
        (algebraMap (analyticSubring U) (meroField U)
          (analyticFunctionElement f hf)) →
      HypertranscendentalOver (RatFunc ℂ)
        (algebraMap (analyticSubring U) (meroField U)
          (analyticExponentialElement f hf)) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Differential (RatFunc ℂ) :=
    GaloisForLFunctions.ratFuncCoordinateDifferential
  letI := meroFieldDifferential hUo hUc hUne
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
    meroFieldRatFuncDifferentialAlgebra hUo hUc hUne hUinf
  intro hsource
  exact hypertranscendentalOver_phase_of_logDeriv_eq_deriv hsource
    (analyticExponentialMero_logDeriv hUo hUc hUne f hf)

set_option synthInstance.maxHeartbeats 20000

end

end GaloisForLFunctions.HTGeometry
