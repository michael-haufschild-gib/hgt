import GaloisForLFunctions.HTGeometry.EntireTranslationDefectCountability
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import GaloisForLFunctions.HTGeometry.MeroExponentialGauge

/-!
# Entire multiplicative translation-defect countability

This module transfers additive translation-spectrum countability through the logarithmic
derivative.  The transfer is exact: for a nowhere-zero entire function, differential algebraicity
is preserved and reflected by its logarithmic derivative.  Consequently a hypertranscendental
nowhere-zero entire function has only countably many differentially algebraic multiplicative
translation defects.
-/

open Set
open scoped Differential UnivMeroFieldInstances

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Global logarithmic-derivative equivalence.**  A nowhere-zero entire function is
differentially algebraic exactly when its logarithmic derivative is. -/
theorem differentiallyAlgebraic_logDeriv_iff {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (hGne : ∀ z, G z ≠ 0) :
    DifferentiallyAlgebraic (fun z => deriv G z / G z) ↔
      DifferentiallyAlgebraic G := by
  let L : ℂ → ℂ := fun z => deriv G z / G z
  have hL : AnalyticOnNhd ℂ L Set.univ :=
    hG.deriv.div hG (fun z _ => hGne z)
  have hGmero_ne : analyticMeroElement G hG ≠ 0 := by
    rw [Ne, analyticMeroElement_eq_zero_iff hG]
    intro hzero
    exact hGne 0 (hzero 0 (Set.mem_univ 0))
  have hprod : analyticMeroElement L hL * analyticMeroElement G hG =
      (analyticMeroElement G hG)′ := by
    rw [← analyticMeroElement_mul hL hG, deriv_analyticMeroElement]
    apply analyticMeroElement_congr
    funext z
    simp only [L]
    exact div_mul_cancel₀ (deriv G z) (hGne z)
  have hmero : analyticMeroElement L hL =
      (analyticMeroElement G hG)′ / analyticMeroElement G hG :=
    (eq_div_iff hGmero_ne).2 hprod
  constructor
  · intro hLDA
    have hLmDA :=
      differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hL hLDA
    rw [hmero] at hLmDA
    exact differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hG
      ((GaloisForLFunctions.differentialAlgebraicOver_deriv_div_self_iff
        (analyticMeroElement G hG)).1 hLmDA)
  · intro hGDA
    apply differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hL
    rw [hmero]
    exact (GaloisForLFunctions.differentialAlgebraicOver_deriv_div_self_iff
      (analyticMeroElement G hG)).2
        (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hG hGDA)

/-- **Entire multiplicative translation-spectrum countability.**  A hypertranscendental
nowhere-zero entire function has at most countably many differentially algebraic quotients
`z ↦ G (z + h) / G z`. -/
theorem countable_differentiallyAlgebraic_multiplicativeTranslationDefect
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGne : ∀ z, G z ≠ 0)
    (hGht : ¬ DifferentiallyAlgebraic G) :
    {h : ℂ | DifferentiallyAlgebraic fun z => G (z + h) / G z}.Countable := by
  have hGan : AnalyticOnNhd ℂ G Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 hG
  let L : ℂ → ℂ := fun z => deriv G z / G z
  have hLan : AnalyticOnNhd ℂ L Set.univ :=
    hGan.deriv.div hGan (fun z _ => hGne z)
  have hLht : ¬ DifferentiallyAlgebraic L := by
    intro hLDA
    exact hGht ((differentiallyAlgebraic_logDeriv_iff hGan hGne).1 hLDA)
  refine (countable_differentiallyAlgebraic_translationDefect
    (Complex.analyticOnNhd_univ_iff_differentiable.1 hLan) hLht).mono ?_
  intro h hh
  let Q : ℂ → ℂ := fun z => G (z + h) / G z
  have hGshift : AnalyticOnNhd ℂ (fun z => G (z + h)) Set.univ :=
    hGan.comp (analyticOnNhd_id.add analyticOnNhd_const) (Set.mapsTo_univ _ _)
  have hQan : AnalyticOnNhd ℂ Q Set.univ :=
    hGshift.div hGan (fun z _ => hGne z)
  have hQne : ∀ z, Q z ≠ 0 := fun z => div_ne_zero (hGne (z + h)) (hGne z)
  have hlogQDA : DifferentiallyAlgebraic (fun z => deriv Q z / Q z) :=
    (differentiallyAlgebraic_logDeriv_iff hQan hQne).2 hh
  have hlog : (fun z => deriv Q z / Q z) = fun z => L (z + h) - L z := by
    funext z
    have hGz : DifferentiableAt ℂ G z := hG.differentiableAt
    have hGzh : DifferentiableAt ℂ G (z + h) := hG.differentiableAt
    have hQderiv := deriv_div
      (hGzh.comp z (differentiableAt_id.add_const h)) hGz (hGne z)
    change deriv (fun u => G (u + h) / G u) z =
      (deriv (fun u => G (u + h)) z * G z - G (z + h) * deriv G z) / G z ^ 2
        at hQderiv
    change deriv (fun u => G (u + h) / G u) z / (G (z + h) / G z) =
      deriv G (z + h) / G (z + h) - deriv G z / G z
    rw [hQderiv, deriv_comp_add_const]
    field_simp [hGne z, hGne (z + h)]
  change DifferentiallyAlgebraic (fun z => L (z + h) - L z)
  rw [← hlog]
  exact hlogQDA

end

end GaloisForLFunctions.HTGeometry
