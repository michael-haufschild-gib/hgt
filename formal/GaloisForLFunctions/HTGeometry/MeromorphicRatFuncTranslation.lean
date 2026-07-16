import GaloisForLFunctions.HTGeometry.MeromorphicTranslation
import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# The rational coordinate inside the global meromorphic field

The canonical embedding `ℂ(X) → meroField univ` intertwines unit translation with
`X ↦ X + 1` and intertwines the meromorphic derivation with the rational coordinate
derivation.  These are the base-field compatibility laws needed by rational-shift
hypertranscendence arguments in the genuine meromorphic carrier.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance meromorphicRatFuncDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicRatFuncIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance meromorphicRatFuncIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance meromorphicRatFuncDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Translating a polynomial evaluation germ is polynomial composition with `X + q`. -/
theorem addTranslationAnalyticEquiv_polyToAnalytic (q : ℂ) (p : Polynomial ℂ) :
    addTranslationAnalyticEquiv q (polyToAnalytic Set.univ p) =
      polyToAnalytic Set.univ (p.comp (Polynomial.X + Polynomial.C q)) := by
  apply Subtype.ext
  rw [show ((addTranslationAnalyticEquiv q (polyToAnalytic Set.univ p) :
      analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ) =
        ((polyToAnalytic Set.univ p : analyticSubring Set.univ) :
          Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation q)
            (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) from rfl]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z => p.eval (z + q)) =
    Germ.ofFun (l := 𝓟 Set.univ)
      (fun z => (p.comp (Polynomial.X + Polynomial.C q)).eval z)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    simp [Polynomial.eval_comp]

/-- Translation of the global meromorphic field restricts to `ratShift` on `ℂ(X)`. -/
theorem addTranslationMeroEquiv_ratfuncToMero (r : RatFunc ℂ) :
    addTranslationMeroEquiv 1
        (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r) =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (ratShift r) := by
  let ρ := ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ
  have hhom : (addTranslationMeroEquiv 1).toRingHom.comp ρ = ρ.comp ratShift := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply,
      ratfuncToMero_algebraMap_polynomial, ratShift_algebraMap,
      ratfuncToMero_algebraMap_polynomial]
    simp only [polyToMero, RingHom.comp_apply]
    change addTranslationMeroEquiv 1
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ p)) = _
    rw [addTranslationMeroEquiv_algebraMap,
      addTranslationAnalyticEquiv_polyToAnalytic]
  exact RingHom.congr_fun hhom r

/-- Differentiating a polynomial evaluation germ gives the formal derivative germ. -/
theorem analyticSubringDeriv_polyToAnalytic (p : Polynomial ℂ) :
    analyticSubringDeriv isOpen_univ (polyToAnalytic Set.univ p) =
      polyToAnalytic Set.univ p.derivative := by
  apply Subtype.ext
  change Germ.ofFun (l := 𝓟 Set.univ) (deriv (fun z : ℂ => p.eval z)) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun z : ℂ => p.derivative.eval z)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => Polynomial.deriv p

/-- The global meromorphic derivation differentiates polynomial evaluation germs formally. -/
theorem meroField_deriv_polyToMero (p : Polynomial ℂ) :
    (polyToMero Set.univ p)′ = polyToMero Set.univ p.derivative := by
  change (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (polyToAnalytic Set.univ p))′ = _
  rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
    Set.univ_nonempty, analyticSubringDeriv_polyToAnalytic]
  rfl

/-- The meromorphic derivation restricts to the rational coordinate derivation on `ℂ(X)`. -/
theorem meroField_deriv_ratfuncToMero (r : RatFunc ℂ) :
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ r)′ =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ
        (HTGeometry.ratFuncCoordinateDerivation ℂ r) := by
  let ρ := ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ
  induction r using RatFunc.induction_on with
  | f p q hq =>
      let pR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      let qR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) q
      change (ρ (pR / qR))′ =
        ρ (HTGeometry.ratFuncCoordinateDerivation ℂ (pR / qR))
      rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div]
      simp only [map_mul, map_sub, map_pow, map_inv₀, smul_eq_mul]
      rw [show ρ pR = polyToMero Set.univ p by
          exact ratfuncToMero_algebraMap_polynomial Set.univ
            isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ p,
        show ρ qR = polyToMero Set.univ q by
          exact ratfuncToMero_algebraMap_polynomial Set.univ
            isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ q]
      rw [meroField_deriv_polyToMero, meroField_deriv_polyToMero]
      rw [show HTGeometry.ratFuncCoordinateDerivation ℂ pR =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative by
          simp [pR],
        show HTGeometry.ratFuncCoordinateDerivation ℂ qR =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative by
          simp [qR]]
      rw [show ρ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative) =
            polyToMero Set.univ p.derivative by
          exact ratfuncToMero_algebraMap_polynomial Set.univ
            isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ p.derivative,
        show ρ (algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative) =
            polyToMero Set.univ q.derivative by
          exact ratfuncToMero_algebraMap_polynomial Set.univ
            isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ q.derivative]

end

end GaloisForLFunctions
