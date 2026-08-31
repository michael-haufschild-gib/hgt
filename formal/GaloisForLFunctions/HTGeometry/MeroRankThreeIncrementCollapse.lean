import GaloisForLFunctions.HTGeometry.MeroFieldConstants
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.GaussianOrderLedger

/-!
# Rank-three increment collapse in the meromorphic field of the plane

An element of the global meromorphic differential field whose translation increments along three
rationally independent steps are constants, one of them zero, is itself a constant.  Its derivative
is fixed by the whole rank-three translation group, hence constant; subtracting that multiple of
the coordinate leaves an element with vanishing derivative, hence a constant; and the exact period
kills the coordinate coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The coordinate germ translates by the step. -/
theorem addTranslationMeroEquiv_coordElem (q : ℂ) :
    addTranslationMeroEquiv q coordElem
      = coordElem + algebraMap ℂ (meroField (Set.univ : Set ℂ)) q := by
  rw [coordElem, addTranslationMeroEquiv_analyticMeroElement,
    algebraMap_complex_eq_analyticMeroElement, ← analyticMeroElement_add]

/-- The complex constants of the meromorphic field are the constant analytic germs. -/
theorem algebraMap_complex_eq_constToAnalytic (c : ℂ) :
    algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (constToAnalytic Set.univ c)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  rw [algebraMap_complex_eq_analyticMeroElement, analyticMeroElement]
  rfl

/-- Translations fix the complex constants. -/
theorem addTranslationMeroEquiv_complexConst (q c : ℂ) :
    addTranslationMeroEquiv q (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  rw [← algebraMap_complex_eq_constToAnalytic, addTranslationMeroEquiv_const]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Rank-three increment collapse.**  A meromorphic element with constant increments along three
rationally independent steps, one of which is an exact period, is a complex constant. -/
theorem exists_complex_of_rankThree_constIncrements
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) (hv0 : v 0 ≠ 0)
    {W : meroField (Set.univ : Set ℂ)} {c : Fin 3 → ℂ}
    (hW : ∀ i, addTranslationMeroEquiv (v i) W
      = W + algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i))
    (hc0 : c 0 = 0) :
    ∃ b : ℂ, W = algebraMap ℂ (meroField (Set.univ : Set ℂ)) b := by
  -- the derivative is fixed by every generator
  have hfix : ∀ i, addTranslationMeroEquiv (v i) (W′) = W′ := by
    intro i
    have h1 : addTranslationMeroEquiv (v i) (W′) = ((addTranslationMeroEquiv (v i)) W)′ :=
      addTranslationMeroEquiv_deriv (v i) W
    rw [h1, hW i]
    have h2 : (W + algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i))′
        = W′ + (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i))′ := by
      simp only [map_add]
    rw [h2, deriv_complexConst, add_zero]
  have hspan : ∀ q ∈ Submodule.span ℤ (Set.range v),
      addTranslationMeroEquiv q (W′) = W′ :=
    rankThree_span_fixed_of_generator_fixed v (W′) hfix
  obtain ⟨k, hk⟩ := exists_constant_of_rankThree_translation_fixed v hv (W′) hspan
  have hconv := algebraMap_complex_eq_constToAnalytic k
  have hkm : algebraMap ℂ (meroField (Set.univ : Set ℂ)) k = W′ := by
    rw [← hconv]
    exact hk
  have hderiv : (W - algebraMap ℂ (meroField (Set.univ : Set ℂ)) k * coordElem)′ = 0 := by
    have hsub : (W - algebraMap ℂ (meroField (Set.univ : Set ℂ)) k * coordElem)′
        = W′ - (algebraMap ℂ (meroField (Set.univ : Set ℂ)) k * coordElem)′ := by
      simp only [map_sub]
    have hmul : (algebraMap ℂ (meroField (Set.univ : Set ℂ)) k * coordElem)′
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) k * coordElem′
          + coordElem * (algebraMap ℂ (meroField (Set.univ : Set ℂ)) k)′ := by
      simp only [Derivation.leibniz, smul_eq_mul]
    rw [hsub, hmul, deriv_coordElem, deriv_complexConst, mul_one, mul_zero, add_zero, ← hkm,
      sub_self]
  obtain ⟨b, hb⟩ := exists_complex_of_deriv_eq_zero hderiv
  have hWform : W = algebraMap ℂ (meroField (Set.univ : Set ℂ)) k * coordElem
      + algebraMap ℂ (meroField (Set.univ : Set ℂ)) b := by
    linear_combination -hb
  -- the exact period kills the slope
  have hzero : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (k * v 0) = 0 := by
    have h0 := hW 0
    rw [hc0, map_zero, add_zero, hWform, map_add, map_mul,
      addTranslationMeroEquiv_coordElem, addTranslationMeroEquiv_complexConst,
      addTranslationMeroEquiv_complexConst] at h0
    rw [map_mul]
    linear_combination h0
  have hk0 : k = 0 := by
    have hinj : Function.Injective (algebraMap ℂ (meroField (Set.univ : Set ℂ))) :=
      (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective
    have : k * v 0 = 0 := by
      have := hinj (by rw [hzero, map_zero] :
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (k * v 0)
          = algebraMap ℂ (meroField (Set.univ : Set ℂ)) 0)
      exact this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hv0
  refine ⟨b, ?_⟩
  rw [hWform, hk0, map_zero, zero_mul, zero_add]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Paired quasi-elliptic collapse in the meromorphic field.**  An element with exact period one
and constant increments along two further steps, the three rationally independent, is a complex
constant and both increments vanish. -/
theorem exists_complex_of_unit_period_of_constIncrements
    {σ τ : ℂ} (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {W : meroField (Set.univ : Set ℂ)} {a b : ℂ}
    (hone : addTranslationMeroEquiv 1 W = W)
    (hσ : addTranslationMeroEquiv σ W = W + algebraMap ℂ (meroField (Set.univ : Set ℂ)) a)
    (hτ : addTranslationMeroEquiv τ W = W + algebraMap ℂ (meroField (Set.univ : Set ℂ)) b) :
    (∃ c : ℂ, W = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) ∧ a = 0 ∧ b = 0 := by
  have hinj : Function.Injective (algebraMap ℂ (meroField (Set.univ : Set ℂ))) :=
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective
  have hW : ∀ i : Fin 3, addTranslationMeroEquiv (![(1 : ℂ), σ, τ] i) W
      = W + algebraMap ℂ (meroField (Set.univ : Set ℂ)) (![(0 : ℂ), a, b] i) := by
    intro i
    fin_cases i
    · show addTranslationMeroEquiv 1 W = W + algebraMap ℂ (meroField (Set.univ : Set ℂ)) 0
      rw [map_zero, add_zero]
      exact hone
    · exact hσ
    · exact hτ
  obtain ⟨c, hc⟩ := exists_complex_of_rankThree_constIncrements ![(1 : ℂ), σ, τ] hv
    (by show (1 : ℂ) ≠ 0; exact one_ne_zero) hW (by rfl)
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · have h := hσ
    rw [hc, addTranslationMeroEquiv_complexConst] at h
    have : algebraMap ℂ (meroField (Set.univ : Set ℂ)) a = 0 := by linear_combination -h
    have h0 : algebraMap ℂ (meroField (Set.univ : Set ℂ)) a
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) 0 := by rw [this, map_zero]
    exact hinj h0
  · have h := hτ
    rw [hc, addTranslationMeroEquiv_complexConst] at h
    have : algebraMap ℂ (meroField (Set.univ : Set ℂ)) b = 0 := by linear_combination -h
    have h0 : algebraMap ℂ (meroField (Set.univ : Set ℂ)) b
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) 0 := by rw [this, map_zero]
    exact hinj h0

end

end GaloisForLFunctions.HTGeometry
