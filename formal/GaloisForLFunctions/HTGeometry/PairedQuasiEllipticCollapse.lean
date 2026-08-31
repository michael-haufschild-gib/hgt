import GaloisForLFunctions.HTGeometry.MeroRealizationTransport
import GaloisForLFunctions.HTGeometry.ThetaSourceOnePole

/-!
# The paired quasi-elliptic collapse

A one-pole quasi-elliptic increment is the theta logarithmic derivative up to an additive constant,
and its quasiperiod is forced to be `-2πi`.  A primitive whose two structural increments agree with
those of a reference primitive up to constants, and which has period one, therefore equals that
reference up to a single additive constant, and the two constants vanish.  In particular the paired
constraint system determines its solution up to one complex constant.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- A meromorphic function whose canonical normal form is constant agrees with that constant off
its poles. -/
theorem eventually_eq_const_of_constant_toMeromorphicNFOn {d : ℂ → ℂ}
    (hd : MeromorphicOn d Set.univ)
    (hconst : ∀ x y, toMeromorphicNFOn d Set.univ x = toMeromorphicNFOn d Set.univ y) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, d w = toMeromorphicNFOn d Set.univ 0 := by
  filter_upwards [hd.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)] with w hw
  rw [← hw]
  exact hconst w 0

/-- **A one-pole quasi-elliptic increment is the theta logarithmic derivative up to a constant**,
and its quasiperiod is `-2πi`. -/
theorem eq_thetaLogDerivMero_add_const_of_matching_principal_parts
    {τ : ℂ} (hτ : 0 < τ.im) {U : meroField (Set.univ : Set ℂ)} {u : ℂ → ℂ}
    (hU : RealizesMero U u)
    (huan : ∀ z ∉ thetaDivisor τ, AnalyticAt ℂ u z)
    (hup : ∀ q ∈ thetaDivisor τ, HasPrincipalPart u q 1)
    (huper : ∀ z, ∀ᶠ w in 𝓝[≠] z, u (w + 1) = u w)
    {k : ℂ} (huinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, u (w + τ) = u w + k) :
    (∃ c : ℂ, U = thetaLogDerivMero τ hτ + algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)
      ∧ k = -(2 * (Real.pi : ℂ) * Complex.I) := by
  obtain ⟨hconst, hk⟩ :=
    const_sub_thetaSource_of_matching_principal_parts hτ huan hup huper huinc
  have hdm : MeromorphicOn (fun w => u w - thetaSource τ w) Set.univ := by
    intro z hz
    exact ((meromorphicOn_of_principal_parts huan hup) z hz).sub
      ((meromorphicOn_thetaSource hτ) z hz)
  have hev := eventually_eq_const_of_constant_toMeromorphicNFOn hdm hconst
  have hsub : RealizesMero (U - thetaLogDerivMero τ hτ) (fun w => u w - thetaSource τ w) :=
    realizesMero_sub hU (realizesMero_thetaLogDerivMero τ hτ)
  have heq : U - thetaLogDerivMero τ hτ
      = algebraMap ℂ (meroField (Set.univ : Set ℂ))
        (toMeromorphicNFOn (fun w => u w - thetaSource τ w) Set.univ 0) :=
    realizesMero_eq_of_eventuallyEq hsub
      (realizesMero_algebraMap_complex _) hev
  exact ⟨⟨_, by linear_combination heq⟩, hk⟩

/-! ### The collapse and the uniqueness of the paired constraint system -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The paired collapse.**  If the two structural increments of `F` are those of a reference
primitive `P` up to constants, and both have period one, then `F` equals `P` up to one complex
constant and the two constants vanish. -/
theorem exists_complex_sub_of_structural_increments
    {σ τ : ℂ} (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {F P : meroField (Set.univ : Set ℂ)} {a b : ℂ}
    (hFone : addTranslationMeroEquiv 1 F = F) (hPone : addTranslationMeroEquiv 1 P = P)
    (hσ : addTranslationMeroEquiv σ F - F
      = (addTranslationMeroEquiv σ P - P) + algebraMap ℂ (meroField (Set.univ : Set ℂ)) a)
    (hτ : addTranslationMeroEquiv τ F - F
      = (addTranslationMeroEquiv τ P - P) + algebraMap ℂ (meroField (Set.univ : Set ℂ)) b) :
    (∃ c : ℂ, F - P = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) ∧ a = 0 ∧ b = 0 := by
  refine exists_complex_of_unit_period_of_constIncrements hv ?_ ?_ ?_
  · rw [map_sub, hFone, hPone]
  · rw [map_sub]
    linear_combination hσ
  · rw [map_sub]
    linear_combination hτ

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Constraint uniqueness.**  Two primitives with period one and the same two structural
increments differ by a complex constant. -/
theorem exists_complex_sub_of_same_increments
    {σ τ : ℂ} (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {F P : meroField (Set.univ : Set ℂ)}
    (hFone : addTranslationMeroEquiv 1 F = F) (hPone : addTranslationMeroEquiv 1 P = P)
    (hσ : addTranslationMeroEquiv σ F - F = addTranslationMeroEquiv σ P - P)
    (hτ : addTranslationMeroEquiv τ F - F = addTranslationMeroEquiv τ P - P) :
    ∃ c : ℂ, F - P = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  refine (exists_complex_sub_of_structural_increments (a := 0) (b := 0) hv hFone hPone ?_ ?_).1
  · rw [map_zero, add_zero]
    exact hσ
  · rw [map_zero, add_zero]
    exact hτ

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Translation defects do not see an additive constant.**  If two primitives differ by a complex
constant, their translation defects coincide at every shift.  Every statement about the defect
family of one — in particular the elliptic-gamma period-coset matroid and the differential-algebraic
shift spectrum — therefore holds verbatim for the other. -/
theorem defect_eq_of_sub_algebraMap {F P : meroField (Set.univ : Set ℂ)} {c : ℂ}
    (h : F - P = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) (k : ℂ) :
    addTranslationMeroEquiv k F - F = addTranslationMeroEquiv k P - P := by
  have hF : F = P + algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
    linear_combination h
  rw [hF, map_add, addTranslationMeroEquiv_complexConst]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The paired constraint system has the elliptic-gamma defect family.**  A primitive with period
one whose two structural increments are those of a reference primitive up to constants has exactly
the same translation defects as that reference. -/
theorem defect_eq_of_structural_increments
    {σ τ : ℂ} (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {F P : meroField (Set.univ : Set ℂ)} {a b : ℂ}
    (hFone : addTranslationMeroEquiv 1 F = F) (hPone : addTranslationMeroEquiv 1 P = P)
    (hσ : addTranslationMeroEquiv σ F - F
      = (addTranslationMeroEquiv σ P - P) + algebraMap ℂ (meroField (Set.univ : Set ℂ)) a)
    (hτ : addTranslationMeroEquiv τ F - F
      = (addTranslationMeroEquiv τ P - P) + algebraMap ℂ (meroField (Set.univ : Set ℂ)) b)
    (k : ℂ) :
    addTranslationMeroEquiv k F - F = addTranslationMeroEquiv k P - P := by
  obtain ⟨⟨c, hc⟩, _, _⟩ :=
    exists_complex_sub_of_structural_increments hv hFone hPone hσ hτ
  exact defect_eq_of_sub_algebraMap hc k

end

end GaloisForLFunctions.HTGeometry
