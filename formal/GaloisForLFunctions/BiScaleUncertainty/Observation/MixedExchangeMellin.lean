import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerBoundaryEulerSource

/-!
# Mixed-exchange differential operators on Meyer sources

Negative Euler differentiation acts on the actual Meyer cap. The radial operator
`z²∂² - 2z∂ + z² + 9/4 + ν²` becomes a second log derivative plus an exponential
potential. Its entire Mellin transform is a shift by two plus a quadratic multiplier.
-/

open Complex MeasureTheory
open RHTower
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

/-- The constant-coefficient part of the mixed-exchange operator stays inside the cap. -/
def mixedExchangeCap (ν : ℝ) (f : DeningerMeyerCap) : DeningerMeyerCap :=
  deningerMeyerNegativeEuler (deningerMeyerNegativeEuler f) +
    (3 : ℂ) • deningerMeyerNegativeEuler f + ((9 / 4 : ℂ) + (ν : ℂ) ^ 2) • f

theorem mixedExchangeCap_mellin (ν : ℝ) (f : DeningerMeyerCap) (s : ℂ) :
    deningerMeyerBoundaryMellin (mixedExchangeCap ν f) s =
      ((s + 3 / 2) ^ 2 + (ν : ℂ) ^ 2) * deningerMeyerBoundaryMellin f s := by
  change deningerMeyerBoundaryMellinLM s (mixedExchangeCap ν f) = _
  simp only [mixedExchangeCap, map_add, map_smul, smul_eq_mul]
  change deningerMeyerBoundaryMellin (deningerMeyerNegativeEuler (deningerMeyerNegativeEuler f)) s +
    3 * deningerMeyerBoundaryMellin (deningerMeyerNegativeEuler f) s +
      (9 / 4 + (ν : ℂ) ^ 2) * deningerMeyerBoundaryMellin f s = _
  rw [deningerMeyerBoundaryMellin_negativeEuler, deningerMeyerBoundaryMellin_negativeEuler]
  ring

theorem mixedExchangeCap_log_value (ν : ℝ) (f : DeningerMeyerCap) (t : ℝ) :
    (deningerMeyerStrongLogSumLM (mixedExchangeCap ν f) : ℝ → ℂ) t =
      deriv (deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ)) t -
        3 * deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t +
        (9 / 4 + (ν : ℂ) ^ 2) * (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t := by
  have hA := deningerMeyerNegativeEuler_boundary f
  have hAA := deningerMeyerNegativeEuler_boundary (deningerMeyerNegativeEuler f)
  rw [hA] at hAA
  simp only [mixedExchangeCap, map_add, map_smul]
  change (deningerMeyerStrongLogSumLM (deningerMeyerNegativeEuler (deningerMeyerNegativeEuler f)) : ℝ → ℂ) t +
    3 * (deningerMeyerStrongLogSumLM (deningerMeyerNegativeEuler f) : ℝ → ℂ) t +
      (9 / 4 + (ν : ℂ) ^ 2) * (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t = _
  rw [congrFun hA t, congrFun hAA t]
  simp only [Pi.neg_apply, deriv.neg, neg_neg]
  ring

/-- Add the radial quadratic potential in logarithmic coordinates. -/
def mixedExchangeLogSource (ν : ℝ) (f : DeningerMeyerCap) (t : ℝ) : ℂ :=
  (deningerMeyerStrongLogSumLM (mixedExchangeCap ν f) : ℝ → ℂ) t +
    Complex.exp (2 * (t : ℂ)) * (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t

theorem mixedExchangeLogSource_value (ν : ℝ) (f : DeningerMeyerCap) (t : ℝ) :
    mixedExchangeLogSource ν f t =
      deriv (deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ)) t -
        3 * deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t +
        (Complex.exp (2 * (t : ℂ)) + 9 / 4 + (ν : ℂ) ^ 2) *
          (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t := by
  rw [mixedExchangeLogSource, mixedExchangeCap_log_value]
  ring

theorem mixedExchangeLogSource_mellin (ν : ℝ) (f : DeningerMeyerCap) (s : ℂ) :
    deningerMeyerStrongLogMellin (mixedExchangeLogSource ν f) s =
      deningerMeyerBoundaryMellin f (s + 2) +
        ((s + 3 / 2) ^ 2 + (ν : ℂ) ^ 2) * deningerMeyerBoundaryMellin f s := by
  have hi (g : DeningerMeyerCap) (z : ℂ) :
      Integrable (fun t : ℝ => Complex.exp (z * t) * (deningerMeyerStrongLogSumLM g : ℝ → ℂ) t) := by
    apply (integrable_deningerMeyerStrongLogMellinJet (deningerMeyerStrongLogSumLM g).property 0 z).congr
    filter_upwards with t
    simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]
  have hs (t : ℝ) : Complex.exp (s * t) *
      (Complex.exp (2 * (t : ℂ)) * (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t) =
      Complex.exp ((s + 2) * t) * (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t := by
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hishift : Integrable (fun t : ℝ => Complex.exp (s * t) *
      (Complex.exp (2 * (t : ℂ)) * (deningerMeyerStrongLogSumLM f : ℝ → ℂ) t)) := by
    simpa only [hs] using hi f (s + 2)
  simp only [deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet,
    pow_zero, one_mul, mixedExchangeLogSource, mul_add]
  rw [integral_add (hi (mixedExchangeCap ν f) s) hishift]
  simp only [hs]
  have hm := mixedExchangeCap_mellin ν f s
  simp only [deningerMeyerBoundaryMellin, deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJet, pow_zero, one_mul] at hm ⊢
  rw [hm, add_comm]

#print axioms mixedExchangeCap_mellin
#print axioms mixedExchangeCap_log_value
#print axioms mixedExchangeLogSource_value
#print axioms mixedExchangeLogSource_mellin

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
