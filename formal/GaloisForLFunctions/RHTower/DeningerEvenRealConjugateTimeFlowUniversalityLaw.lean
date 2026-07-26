import GaloisForLFunctions.RHTower.DeningerArithmeticFlow
import GaloisForLFunctions.RHTower.DeningerArithmeticRealStructure

/-!
# Deninger even-Real conjugate-time flow universality

The functional-equation Real involution sends the complex Frobenius flow at time `t` to the same
flow at conjugate time.  On the real-time subgroup it therefore commutes with the full
source-defined flow.
-/

open Complex

namespace RHTower

noncomputable section

/-- Functional-equation reflection sends the source exponential at `t` to the source exponential
at conjugate time. -/
theorem deningerEntireFunctionalEquationSigma_flowSource (t : ℂ) :
    deningerEntireFunctionalEquationSigma (deningerEntireFlowSource t) =
      deningerEntireFlowSource ((starRingEnd ℂ) t) := by
  apply DeningerEntire.ext
  intro z
  change
    (starRingEnd ℂ)
        (Complex.exp
          (t * (1 / 2 + I * (-(starRingEnd ℂ) z)))) =
      Complex.exp ((starRingEnd ℂ) t * (1 / 2 + I * z))
  rw [← Complex.exp_conj]
  congr 1
  simp [map_ofNat]

/-- The descended even-Real structure intertwines complex Frobenius time with conjugate time. -/
theorem deningerArithmeticH1EvenKReal_sigma_flow
    (t : ℂ) (x : DeningerArithmeticH1) :
    deningerArithmeticH1EvenKReal.sigma (deningerArithmeticFlow t x) =
      deningerArithmeticFlow ((starRingEnd ℂ) t)
        (deningerArithmeticH1EvenKReal.sigma x) := by
  obtain ⟨F, rfl⟩ := Quotient.exists_rep x
  rw [deningerArithmeticFlow_apply, deningerArithmeticFlowClass]
  change
    deningerArithmeticH1EvenKReal.sigma
        (deningerEntireH1Class (deningerEntireFlowSource t) *
          deningerEntireH1Class F) =
      deningerEntireH1Class
          (deningerEntireFlowSource ((starRingEnd ℂ) t)) *
        deningerArithmeticH1EvenKReal.sigma (deningerEntireH1Class F)
  rw [← map_mul, deningerArithmeticH1EvenKReal_sigma_class,
    deningerEntireFunctionalEquationSigma_mul,
    deningerEntireFunctionalEquationSigma_flowSource, map_mul,
    deningerArithmeticH1EvenKReal_sigma_class]

/-- Real time is fixed, so the even-Real structure commutes with the real Frobenius flow. -/
theorem deningerArithmeticH1EvenKReal_sigma_flow_ofReal
    (t : ℝ) (x : DeningerArithmeticH1) :
    deningerArithmeticH1EvenKReal.sigma
        (deningerArithmeticFlow (t : ℂ) x) =
      deningerArithmeticFlow (t : ℂ)
        (deningerArithmeticH1EvenKReal.sigma x) := by
  convert deningerArithmeticH1EvenKReal_sigma_flow (t : ℂ) x using 1
  simp

/-- **Deninger even-Real conjugate-time flow universality law.**  The Real involution intertwines
all complex times, commutes with every real time, and respects the additive flow composition. -/
theorem deninger_evenReal_conjugateTimeFlowUniversality :
    (∀ (t : ℂ) (x : DeningerArithmeticH1),
      deningerArithmeticH1EvenKReal.sigma (deningerArithmeticFlow t x) =
        deningerArithmeticFlow ((starRingEnd ℂ) t)
          (deningerArithmeticH1EvenKReal.sigma x)) ∧
    (∀ (t : ℝ) (x : DeningerArithmeticH1),
      deningerArithmeticH1EvenKReal.sigma
          (deningerArithmeticFlow (t : ℂ) x) =
        deningerArithmeticFlow (t : ℂ)
          (deningerArithmeticH1EvenKReal.sigma x)) ∧
    ∀ (t u : ℂ) (x : DeningerArithmeticH1),
      deningerArithmeticH1EvenKReal.sigma
          (deningerArithmeticFlow (t + u) x) =
        deningerArithmeticFlow ((starRingEnd ℂ) t)
          (deningerArithmeticFlow ((starRingEnd ℂ) u)
            (deningerArithmeticH1EvenKReal.sigma x)) := by
  refine ⟨deningerArithmeticH1EvenKReal_sigma_flow,
    deningerArithmeticH1EvenKReal_sigma_flow_ofReal, ?_⟩
  intro t u x
  rw [deningerArithmeticH1EvenKReal_sigma_flow, map_add,
    deningerArithmeticFlow_add, LinearMap.comp_apply]

end

end RHTower
