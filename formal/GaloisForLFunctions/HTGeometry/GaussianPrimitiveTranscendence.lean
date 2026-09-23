import GaloisForLFunctions.HTGeometry.GaussianExponentialField
import GaloisForLFunctions.HTGeometry.HyperexponentialTranscendence
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The Gaussian primitive is transcendental over the Gaussian exponential field

The Gaussian exponential is transcendental over the rational functions, and a primitive of it is
transcendental over the field the rational functions and the exponential generate.

The first statement is the hyperexponential transcendence criterion, whose hypothesis is that
`w′ = -2k·z·w` has no nonzero rational solution.  The second is the Liouville obstruction: an
algebraic primitive would lie in the field itself by the algebraic descent along the derivation,
and no element of that field has derivative the exponential because `w′ - 2z·w = 1` has no rational
solution.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

theorem algebraMap_ratFunc_injective :
    Function.Injective (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) :=
  (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective

/-- The logarithmic derivative of the Gaussian exponential, as an element of the rational field. -/
def gaussLogDerivElem : ↥ratField :=
  ⟨algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) gaussLogDeriv, gaussLogDeriv_mem⟩

@[simp]
theorem gaussLogDerivElem_coe :
    ((gaussLogDerivElem : ↥ratField) : meroField (Set.univ : Set ℂ))
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) gaussLogDeriv := rfl

theorem derivationClosed_ratField' :
    ∀ v ∈ ratField, meroComplexDerivation v ∈ ratField := fun _v hv => derivationClosed_ratField hv

/-- The scaled logarithmic derivative, as a rational function. -/
theorem natCast_mul_gaussLogDeriv (k : ℕ) :
    (k : RatFunc ℂ) * gaussLogDeriv
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C ((-2 : ℂ) * (k : ℂ)) * Polynomial.X) := by
  rw [gaussLogDeriv, ← map_natCast (algebraMap (Polynomial ℂ) (RatFunc ℂ)) k, ← map_mul]
  congr 1
  have hk : ((k : ℕ) : Polynomial ℂ) = Polynomial.C ((k : ℕ) : ℂ) := by
    simp
  rw [hk, ← mul_assoc, ← Polynomial.C_mul, mul_comm ((k : ℕ) : ℂ) (-2 : ℂ)]

/-- **No nonzero rational function solves the scaled Gaussian equation.** -/
theorem hker_ratField (k : ℕ) (hk : 1 ≤ k) (w : meroField (Set.univ : Set ℂ)) (hw : w ∈ ratField)
    (h : meroComplexDerivation w
      = (k : meroField (Set.univ : Set ℂ))
        * ((gaussLogDerivElem : ↥ratField) : meroField (Set.univ : Set ℂ)) * w) :
    w = 0 := by
  obtain ⟨r, rfl⟩ := hw
  have hk0 : ((-2 : ℂ) * (k : ℂ)) ≠ 0 := by
    have hkc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero (by norm_num) hkc
  have hnat : (k : meroField (Set.univ : Set ℂ))
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (k : RatFunc ℂ) :=
    (map_natCast _ k).symm
  have hleft : meroComplexDerivation (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r)
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r′ := deriv_algebraMap r
  rw [hleft, gaussLogDerivElem_coe, hnat, ← map_mul, ← map_mul] at h
  have hr : r′ = (k : RatFunc ℂ) * gaussLogDeriv * r := algebraMap_ratFunc_injective h
  have hzero : r = 0 := by
    refine GaloisForLFunctions.RationalShadow.eq_zero_of_deriv_eq_linear_mul hk0 ?_
    have hd : ratFuncCoordinateDerivation ℂ r = r′ := rfl
    rw [hd, hr, natCast_mul_gaussLogDeriv k]
  rw [hzero, map_zero]

/-- **The Gaussian exponential is transcendental over the rational functions.** -/
theorem transcendental_gaussElem : Transcendental ↥ratField gaussElem := by
  refine transcendental_of_hyperexponential meroComplexDerivation ratField
    derivationClosed_ratField' gaussElem_ne_zero gaussLogDeriv_mem ?_ ?_
  · simpa using deriv_gaussElem
  · intro k hk w hw hrel
    exact hker_ratField k hk w hw (by simpa using hrel)

/-! ### The Gaussian primitive -/

theorem differentiable_gaussianExp : Differentiable ℂ (fun z : ℂ => Complex.exp (-z ^ (2 : ℕ))) := by
  intro z
  have h2 : HasDerivAt (fun w : ℂ => -(w ^ (2 : ℕ))) (-((2 : ℕ) * z ^ (2 - 1))) z :=
    (hasDerivAt_pow 2 z).neg
  exact (h2.cexp).differentiableAt

/-- A primitive of the Gaussian exponential, produced by Morera's theorem for the plane. -/
def gaussPrimitive : ℂ → ℂ := Classical.choose differentiable_gaussianExp.isExactOn_univ

theorem hasDerivAt_gaussPrimitive (z : ℂ) :
    HasDerivAt gaussPrimitive (Complex.exp (-z ^ (2 : ℕ))) z :=
  Classical.choose_spec differentiable_gaussianExp.isExactOn_univ z (Set.mem_univ z)

theorem differentiable_gaussPrimitive : Differentiable ℂ gaussPrimitive :=
  fun z => (hasDerivAt_gaussPrimitive z).differentiableAt

theorem deriv_gaussPrimitive : deriv gaussPrimitive = fun z : ℂ => Complex.exp (-z ^ (2 : ℕ)) := by
  funext z
  exact (hasDerivAt_gaussPrimitive z).deriv

theorem analyticOnNhd_gaussPrimitive :
    AnalyticOnNhd ℂ gaussPrimitive (Set.univ : Set ℂ) :=
  differentiable_gaussPrimitive.differentiableOn.analyticOnNhd isOpen_univ

/-- The Gaussian primitive as an element of the meromorphic field. -/
def gaussPrimElem : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement gaussPrimitive analyticOnNhd_gaussPrimitive

theorem deriv_gaussPrimElem : gaussPrimElem′ = gaussElem := by
  rw [gaussPrimElem, deriv_analyticMeroElement', gaussElem]
  refine analyticMeroElement_congr _ _ ?_
  rw [deriv_gaussPrimitive]

/-! ### The exponential field and the Liouville obstruction -/

/-- The field generated by the rational functions and the Gaussian exponential. -/
def gaussField : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  (IntermediateField.adjoin ↥ratField ({gaussElem} : Set (meroField (Set.univ : Set ℂ)))).restrictScalars ℂ

theorem gaussElem_mem_gaussField : gaussElem ∈ gaussField :=
  IntermediateField.subset_adjoin ↥ratField
    ({gaussElem} : Set (meroField (Set.univ : Set ℂ))) (Set.mem_singleton _)

theorem ratField_le_gaussField : ratField ≤ gaussField := by
  intro x hx
  exact IntermediateField.algebraMap_mem
    (IntermediateField.adjoin ↥ratField ({gaussElem} : Set (meroField (Set.univ : Set ℂ))))
    (⟨x, hx⟩ : ↥ratField)

theorem derivationClosed_gaussField : DerivationClosed gaussField := by
  have hmem : gaussElem′ ∈ IntermediateField.adjoin ↥ratField
      ({gaussElem} : Set (meroField (Set.univ : Set ℂ))) := by
    rw [deriv_gaussElem]
    refine IntermediateField.mul_mem _ ?_ (IntermediateField.subset_adjoin ↥ratField
      ({gaussElem} : Set (meroField (Set.univ : Set ℂ))) (Set.mem_singleton _))
    exact IntermediateField.algebraMap_mem _ (⟨_, gaussLogDeriv_mem⟩ : ↥ratField)
  exact derivationClosed_adjoin_singleton gaussElem hmem

/-- **The inhomogeneous Gaussian equation has no rational solution.** -/
theorem hinhom_ratField (w : ↥ratField) :
    restrictDerivation meroComplexDerivation ratField derivationClosed_ratField' w
      + gaussLogDerivElem * w ≠ 1 := by
  intro h
  obtain ⟨r, hr⟩ := w.2
  have hcoe := congrArg (fun v : ↥ratField => (v : meroField (Set.univ : Set ℂ))) h
  simp only [AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
    restrictDerivation_coe, meroComplexDerivation_apply, gaussLogDerivElem_coe] at hcoe
  rw [← hr, deriv_algebraMap, ← map_mul, ← map_add, ← map_one
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))] at hcoe
  have hrel : r′ + gaussLogDeriv * r = 1 := algebraMap_ratFunc_injective hcoe
  refine GaloisForLFunctions.RationalShadow.not_deriv_eq_linear_mul_add_one
    (c := (2 : ℂ)) (by norm_num) r ?_
  have hg : gaussLogDeriv = algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C (-2 : ℂ) * Polynomial.X) := rfl
  have hswap : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (2 : ℂ) * Polynomial.X)
      = -gaussLogDeriv := by
    rw [hg, ← map_neg]
    congr 1
    rw [← neg_mul, ← Polynomial.C_neg]
    norm_num
  show ratFuncCoordinateDerivation ℂ r
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (2 : ℂ) * Polynomial.X) * r + 1
  have hd : ratFuncCoordinateDerivation ℂ r = r′ := rfl
  rw [hd, hswap]
  linear_combination hrel

/-- **No element of the Gaussian exponential field is a primitive of the exponential.** -/
theorem not_deriv_eq_gaussElem {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ gaussField) :
    y′ ≠ gaussElem := by
  have h := not_deriv_eq_of_hyperexponential meroComplexDerivation ratField
    derivationClosed_ratField' (t := gaussElem) (u := gaussLogDerivElem)
    transcendental_gaussElem (by simpa using deriv_gaussElem)
    (fun k hk w hrel => by
      have := hker_ratField k hk (w : meroField (Set.univ : Set ℂ)) w.2 (by
        have hcoe := congrArg (fun v : ↥ratField => (v : meroField (Set.univ : Set ℂ))) hrel
        simpa using hcoe)
      exact Subtype.ext (by simpa using this))
    hinhom_ratField hy
  simpa using h

/-- **The Gaussian primitive is transcendental over the Gaussian exponential field.** -/
theorem not_isAlgebraic_gaussPrimElem : ¬ IsAlgebraic ↥gaussField gaussPrimElem := by
  intro halg
  have hconst : ∀ z ∈ (⊤ : IntermediateField ℂ (meroField (Set.univ : Set ℂ))),
      meroComplexDerivation z = 0 → z ∈ gaussField := by
    intro z _ hz
    obtain ⟨c, hc⟩ := exists_complex_of_deriv_eq_zero (by simpa using hz)
    rw [← hc]
    exact IntermediateField.algebraMap_mem _ c
  have hmem := mem_of_isAlgebraic_of_derivation_mem meroComplexDerivation gaussField ⊤ le_top
    (fun v hv => derivationClosed_gaussField hv) hconst
    (T := gaussPrimElem) (by trivial) halg
    (by simpa [deriv_gaussPrimElem] using gaussElem_mem_gaussField)
  exact not_deriv_eq_gaussElem hmem deriv_gaussPrimElem

end

end GaloisForLFunctions.HTGeometry
