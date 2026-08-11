import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative
import GaloisForLFunctions.HTGeometry.MeromorphicTranslation

/-!
# Realization is compatible with quotients, logarithmic derivatives and translation

Multiplying out the two fractions realizes a quotient; combining that with the derivative rule
realizes a logarithmic derivative; and precomposition with a translation acts on a fraction by
translating both entire representatives.

* `realizesMero_div`, `realizesMero_logDeriv`;
* `realizesMero_translate`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

/-- **Realization is compatible with quotients.** -/
theorem realizesMero_div {x y : meroField (Set.univ : Set ℂ)} {f g : ℂ → ℂ}
    (hx : RealizesMero x f) (hy : RealizesMero y g) (hy0 : y ≠ 0) :
    RealizesMero (x / y) (fun z ↦ f z / g z) := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := hx
  obtain ⟨c, d, C, D, hd0, hC, hD, hCc, hDd, hycd, hgCD⟩ := hy
  have ha : a = entireElem A hA := Subtype.ext hAa.symm
  have hb : b = entireElem B hB := Subtype.ext hBb.symm
  have hc : c = entireElem C hC := Subtype.ext hCc.symm
  have hd : d = entireElem D hD := Subtype.ext hDd.symm
  subst ha; subst hb; subst hc; subst hd
  have hc0 : entireElem C hC ≠ 0 := by
    intro hzero
    apply hy0
    rw [hycd, hzero, map_zero, zero_div]
  have hnum : AnalyticOnNhd ℂ (fun z ↦ A z * D z * D z) (Set.univ : Set ℂ) := (hA.mul hD).mul hD
  have hden : AnalyticOnNhd ℂ (fun z ↦ B z * C z * D z) (Set.univ : Set ℂ) := (hB.mul hC).mul hD
  have hden0 : entireElem (fun z ↦ B z * C z * D z) hden ≠ 0 := by
    intro hzero
    have hmul : entireElem (fun z ↦ B z * C z * D z) hden
        = entireElem B hB * entireElem C hC * entireElem D hD := rfl
    rw [hmul] at hzero
    rcases mul_eq_zero.mp hzero with hz | hz
    · rcases mul_eq_zero.mp hz with hz' | hz'
      · exact hb0 hz'
      · exact hc0 hz'
    · exact hd0 hz
  have hxy : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem A hA) /
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem B hB) /
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem C hC) /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem D hD))
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ A z * D z * D z) hnum) /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ B z * C z * D z) hden) := by
    have hnumeq : entireElem (fun z ↦ A z * D z * D z) hnum
        = entireElem A hA * entireElem D hD * entireElem D hD := rfl
    have hdeneq : entireElem (fun z ↦ B z * C z * D z) hden
        = entireElem B hB * entireElem C hC * entireElem D hD := rfl
    rw [hnumeq, hdeneq, map_mul, map_mul, map_mul, map_mul]
    have hB' : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem B hB) ≠ 0 := algebraMap_analyticSubring_ne_zero hb0
    have hC' : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem C hC) ≠ 0 := algebraMap_analyticSubring_ne_zero hc0
    have hD' : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem D hD) ≠ 0 := algebraMap_analyticSubring_ne_zero hd0
    field_simp
  rw [hxab, hycd, hxy]
  refine realizesMero_fraction hnum hden hden0 fun z hz ↦ ?_
  have hBz : B z ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  have hCz : C z ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  have hDz : D z ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  rw [hfAB z hBz, hgCD z hDz]
  field_simp

/-- **Realization is compatible with logarithmic derivatives.** -/
theorem realizesMero_logDeriv {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (h : RealizesMero x f) (hx0 : x ≠ 0) : RealizesMero (x′ / x) (logDeriv f) := by
  have hfun : logDeriv f = fun z ↦ deriv f z / f z := by
    funext z
    rw [logDeriv_apply]
  rw [hfun]
  exact realizesMero_div (realizesMero_deriv h) h hx0

theorem addTranslationAnalyticEquiv_entireElem (q : ℂ) (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ)) :
    addTranslationAnalyticEquiv q (entireElem A hA)
      = entireElem (fun z ↦ A (z + q)) (fun z _ ↦
        AnalyticAt.comp (g := A) (f := fun w : ℂ ↦ w + q) (hA (z + q) (Set.mem_univ _))
          (by fun_prop)) := rfl

/-- **Realization is compatible with translation.** -/
theorem realizesMero_translate {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (h : RealizesMero x f) (q : ℂ) :
    RealizesMero (addTranslationMeroEquiv q x) (fun z ↦ f (z + q)) := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := h
  have ha : a = entireElem A hA := Subtype.ext hAa.symm
  have hb : b = entireElem B hB := Subtype.ext hBb.symm
  subst ha; subst hb
  have hAq : AnalyticOnNhd ℂ (fun z ↦ A (z + q)) (Set.univ : Set ℂ) := fun z _ ↦
    AnalyticAt.comp (g := A) (f := fun w : ℂ ↦ w + q) (hA (z + q) (Set.mem_univ _)) (by fun_prop)
  have hBq : AnalyticOnNhd ℂ (fun z ↦ B (z + q)) (Set.univ : Set ℂ) := fun z _ ↦
    AnalyticAt.comp (g := B) (f := fun w : ℂ ↦ w + q) (hB (z + q) (Set.mem_univ _)) (by fun_prop)
  have hBq0 : entireElem (fun z ↦ B (z + q)) hBq ≠ 0 := by
    intro hzero
    apply hb0
    have hmap : addTranslationAnalyticEquiv q (entireElem B hB)
        = entireElem (fun z ↦ B (z + q)) hBq := rfl
    have := congrArg (addTranslationAnalyticEquiv q).symm (hmap.trans hzero)
    simpa using this
  have hxq : addTranslationMeroEquiv q
        (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem A hA) /
          algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem B hB))
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ A (z + q)) hAq) /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ B (z + q)) hBq) := by
    rw [map_div₀, addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap]
    rfl
  rw [hxab, hxq]
  refine realizesMero_fraction hAq hBq hBq0 fun z hz ↦ ?_
  exact hfAB (z + q) hz

end

end GaloisForLFunctions.HTGeometry
