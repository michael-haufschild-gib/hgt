import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Duhamel formula of a driven oscillator with a variable frequency

For a constant frequency the propagator is the sine, and the addition formula separates the two time
variables of the Duhamel integral. For a *variable* frequency there is no addition formula, but the
same separation is available: the propagator from `s` to `t` of the equation `u'' = -ω(t)²u` is

`S(t)C(s) - C(t)S(s)`

for any fundamental pair `C, S` of the homogeneous equation, and that expression is already
separated. The Wronskian `CS' - SC'` is constant along the equation, and it is exactly the factor
that makes the source appear once in the second derivative.

Nothing here depends on how `C` and `S` were obtained, so the file is purely the calculus of the
Duhamel formula: two integrals with `t`-independent integrands, differentiated by the fundamental
theorem of calculus.
-/

namespace GaloisForLFunctions.HTGeometry

open intervalIntegral

section Duhamel

variable {C dC ddC S dS ddS ω : ℝ → ℝ} {α β : ℂ} {h : ℝ → ℂ}

/-! ## The two moments of the source -/

/-- The moment of the source against the first member of the pair. -/
noncomputable def duhamelPairFirstPart (C : ℝ → ℝ) (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, ((C s : ℝ) : ℂ) * h s

/-- The moment of the source against the second member of the pair. -/
noncomputable def duhamelPairSecondPart (S : ℝ → ℝ) (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, ((S s : ℝ) : ℂ) * h s

theorem hasDerivAt_duhamelPairFirstPart (hC : Continuous C) (hh : Continuous h) (t : ℝ) :
    HasDerivAt (duhamelPairFirstPart C h) (((C t : ℝ) : ℂ) * h t) t :=
  (((Complex.continuous_ofReal.comp hC).mul hh).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem hasDerivAt_duhamelPairSecondPart (hS : Continuous S) (hh : Continuous h) (t : ℝ) :
    HasDerivAt (duhamelPairSecondPart S h) (((S t : ℝ) : ℂ) * h t) t :=
  (((Complex.continuous_ofReal.comp hS).mul hh).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem duhamelPairFirstPart_zero (C : ℝ → ℝ) (h : ℝ → ℂ) :
    duhamelPairFirstPart C h 0 = 0 := by
  rw [duhamelPairFirstPart, intervalIntegral.integral_same]

theorem duhamelPairSecondPart_zero (S : ℝ → ℝ) (h : ℝ → ℂ) :
    duhamelPairSecondPart S h 0 = 0 := by
  rw [duhamelPairSecondPart, intervalIntegral.integral_same]

/-! ## The Duhamel solution and its derivative -/

/-- The Duhamel solution of the driven oscillator, written with a fundamental pair: the free
solution with data `(α, β)` plus the two separated moments of the source. -/
noncomputable def duhamelPair (C S : ℝ → ℝ) (α β : ℂ) (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((C t : ℝ) : ℂ) * (α - duhamelPairSecondPart S h t) +
    ((S t : ℝ) : ℂ) * (β + duhamelPairFirstPart C h t)

/-- Its time derivative: the two source terms cancel, so only the derivatives of the pair
survive. -/
noncomputable def duhamelPairDeriv (C dC S dS : ℝ → ℝ) (α β : ℂ) (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((dC t : ℝ) : ℂ) * (α - duhamelPairSecondPart S h t) +
    ((dS t : ℝ) : ℂ) * (β + duhamelPairFirstPart C h t)

theorem duhamelPair_zero (C S : ℝ → ℝ) (α β : ℂ) (h : ℝ → ℂ) :
    duhamelPair C S α β h 0 = ((C 0 : ℝ) : ℂ) * α + ((S 0 : ℝ) : ℂ) * β := by
  rw [duhamelPair, duhamelPairFirstPart_zero, duhamelPairSecondPart_zero]
  ring

theorem duhamelPairDeriv_zero (C dC S dS : ℝ → ℝ) (α β : ℂ) (h : ℝ → ℂ) :
    duhamelPairDeriv C dC S dS α β h 0 = ((dC 0 : ℝ) : ℂ) * α + ((dS 0 : ℝ) : ℂ) * β := by
  rw [duhamelPairDeriv, duhamelPairFirstPart_zero, duhamelPairSecondPart_zero]
  ring

/-- **The first derivative of the Duhamel solution.** -/
theorem hasDerivAt_duhamelPair (hCd : ∀ r, HasDerivAt C (dC r) r)
    (hSd : ∀ r, HasDerivAt S (dS r) r) (hC : Continuous C) (hS : Continuous S)
    (hh : Continuous h) (t : ℝ) :
    HasDerivAt (duhamelPair C S α β h) (duhamelPairDeriv C dC S dS α β h t) t := by
  have hP : HasDerivAt (fun r : ℝ => α - duhamelPairSecondPart S h r)
      (-(((S t : ℝ) : ℂ) * h t)) t := by
    simpa using (hasDerivAt_duhamelPairSecondPart hS hh t).const_sub α
  have hQ : HasDerivAt (fun r : ℝ => β + duhamelPairFirstPart C h r)
      (((C t : ℝ) : ℂ) * h t) t := by
    simpa using (hasDerivAt_duhamelPairFirstPart hC hh t).const_add β
  have hCc : HasDerivAt (fun r : ℝ => ((C r : ℝ) : ℂ)) ((dC t : ℝ) : ℂ) t := HasDerivAt.ofReal_comp (hCd t)
  have hSc : HasDerivAt (fun r : ℝ => ((S r : ℝ) : ℂ)) ((dS t : ℝ) : ℂ) t := HasDerivAt.ofReal_comp (hSd t)
  have hmain := (hCc.mul hP).add (hSc.mul hQ)
  refine hmain.congr_deriv ?_
  rw [duhamelPairDeriv]
  ring

/-- **The second derivative: the equation.** The Wronskian of the pair is the factor with which the
source reappears, so a pair normalized to Wronskian one solves the driven equation. -/
theorem hasDerivAt_duhamelPairDeriv (hCd2 : ∀ r, HasDerivAt dC (ddC r) r)
    (hSd2 : ∀ r, HasDerivAt dS (ddS r) r) (hC : Continuous C) (hS : Continuous S)
    (hh : Continuous h) (heqC : ∀ r, ddC r = -(ω r ^ 2 * C r))
    (heqS : ∀ r, ddS r = -(ω r ^ 2 * S r)) (hW : ∀ r, C r * dS r - S r * dC r = 1) (t : ℝ) :
    HasDerivAt (duhamelPairDeriv C dC S dS α β h)
      (-(((ω t ^ 2 : ℝ) : ℂ)) * duhamelPair C S α β h t + h t) t := by
  have hP : HasDerivAt (fun r : ℝ => α - duhamelPairSecondPart S h r)
      (-(((S t : ℝ) : ℂ) * h t)) t := by
    simpa using (hasDerivAt_duhamelPairSecondPart hS hh t).const_sub α
  have hQ : HasDerivAt (fun r : ℝ => β + duhamelPairFirstPart C h r)
      (((C t : ℝ) : ℂ) * h t) t := by
    simpa using (hasDerivAt_duhamelPairFirstPart hC hh t).const_add β
  have hCc : HasDerivAt (fun r : ℝ => ((dC r : ℝ) : ℂ)) ((ddC t : ℝ) : ℂ) t := HasDerivAt.ofReal_comp (hCd2 t)
  have hSc : HasDerivAt (fun r : ℝ => ((dS r : ℝ) : ℂ)) ((ddS t : ℝ) : ℂ) t := HasDerivAt.ofReal_comp (hSd2 t)
  have hmain := (hCc.mul hP).add (hSc.mul hQ)
  refine hmain.congr_deriv ?_
  have hWt : ((C t : ℝ) : ℂ) * ((dS t : ℝ) : ℂ) - ((S t : ℝ) : ℂ) * ((dC t : ℝ) : ℂ) = 1 := by
    have hc : (((C t * dS t - S t * dC t : ℝ)) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hW t]
    push_cast at hc
    exact hc
  have hCeq : ((ddC t : ℝ) : ℂ) = -(((ω t ^ 2 : ℝ) : ℂ) * ((C t : ℝ) : ℂ)) := by
    rw [heqC t]
    push_cast
    ring
  have hSeq : ((ddS t : ℝ) : ℂ) = -(((ω t ^ 2 : ℝ) : ℂ) * ((S t : ℝ) : ℂ)) := by
    rw [heqS t]
    push_cast
    ring
  rw [duhamelPair, hCeq, hSeq]
  linear_combination (h t) * hWt

end Duhamel

end GaloisForLFunctions.HTGeometry
