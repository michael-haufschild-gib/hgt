import Mathlib

/-!
# Testing a translation-invariant operator against a weight

A jump operator built from translations can always be moved onto the test weight, because Lebesgue
measure is translation invariant:

`∫ f(L+s) w(L) dL = ∫ f(L) w(L−s) dL`.

Consequently the first difference satisfies

`∫ [f(L) − f(L+s)] w(L) dL = ∫ f(L) [w(L) − w(L−s)] dL`,

so a hypothesis stated by testing the operator against weights is equivalent to one stated by
testing the *adjoint* differences against the profile.  This is the bridge that lets an equation
assumed in the tested sense be used against concrete weights, with no distribution theory: the
pairing is an ordinary integral throughout, and only translation invariance is needed.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- A continuous compactly supported factor makes any continuous product integrable. -/
theorem integrable_mul_of_compactSupport {u v : ℝ → ℝ} (hu : Continuous u)
    (hcu : HasCompactSupport u) (hv : Continuous v) : Integrable fun L => u L * v L :=
  (hu.mul hv).integrable_of_hasCompactSupport hcu.mul_right

/-- Translating a compactly supported function keeps compact support. -/
theorem hasCompactSupport_shift {u : ℝ → ℝ} (hcu : HasCompactSupport u) (s : ℝ) :
    HasCompactSupport fun L => u (L + s) :=
  hcu.comp_homeomorph (Homeomorph.addRight s)

/-- The same for a backward translation. -/
theorem hasCompactSupport_shift' {u : ℝ → ℝ} (hcu : HasCompactSupport u) (s : ℝ) :
    HasCompactSupport fun L => u (L - s) := by
  have h := hcu.comp_homeomorph (Homeomorph.addRight (-s))
  have hEq : (fun L => u (L + -s)) = fun L => u (L - s) := by
    funext L
    rw [← sub_eq_add_neg]
  exact hEq ▸ h

/-- **Translation adjointness.**  Shifting the profile is the same as shifting the weight the other
way.  Unconditional: it is translation invariance of Lebesgue measure. -/
theorem integral_translate_pairing (f w : ℝ → ℝ) (s : ℝ) :
    (∫ L, f (L + s) * w L) = ∫ L, f L * w (L - s) := by
  have h := integral_add_right_eq_self (μ := volume) (fun x : ℝ => f x * w (x - s)) s
  simpa using h

/-- **The first difference moves onto the weight.**  Testing `f − f(·+s)` against `w` equals
testing `f` against `w − w(·−s)`. -/
theorem integral_firstDifference_pairing {f w : ℝ → ℝ} (hf : Continuous f)
    (hcf : HasCompactSupport f) (hw : Continuous w) (s : ℝ) :
    (∫ L, (f L - f (L + s)) * w L) = ∫ L, f L * (w L - w (L - s)) := by
  have h1 : Integrable fun L => f L * w L := integrable_mul_of_compactSupport hf hcf hw
  have h2 : Integrable fun L => f (L + s) * w L :=
    integrable_mul_of_compactSupport (hf.comp (continuous_id.add continuous_const))
      (hasCompactSupport_shift hcf s) hw
  have h3 : Integrable fun L => f L * w (L - s) :=
    integrable_mul_of_compactSupport hf hcf (hw.comp (continuous_id.sub continuous_const))
  have hL : (∫ L, (f L - f (L + s)) * w L)
      = (∫ L, f L * w L) - ∫ L, f (L + s) * w L := by
    rw [← MeasureTheory.integral_sub h1 h2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun L => by ring)
  have hR : (∫ L, f L * (w L - w (L - s)))
      = (∫ L, f L * w L) - ∫ L, f L * w (L - s) := by
    rw [← MeasureTheory.integral_sub h1 h3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun L => by ring)
  rw [hL, hR, integral_translate_pairing f w s]

/-- **The symmetric second difference moves onto the weight.**  This is the tested form of the
transport operator: the second difference of the profile against `w` equals the profile against the
second difference of `w`. -/
theorem integral_secondDifference_pairing {f w : ℝ → ℝ} (hf : Continuous f)
    (hcf : HasCompactSupport f) (hw : Continuous w) (s : ℝ) :
    (∫ L, (2 * f L - f (L + s) - f (L - s)) * w L)
      = ∫ L, f L * (2 * w L - w (L - s) - w (L + s)) := by
  have h1 : Integrable fun L => f L * w L := integrable_mul_of_compactSupport hf hcf hw
  have h2 : Integrable fun L => f (L + s) * w L :=
    integrable_mul_of_compactSupport (hf.comp (continuous_id.add continuous_const))
      (hasCompactSupport_shift hcf s) hw
  have h3 : Integrable fun L => f (L - s) * w L :=
    integrable_mul_of_compactSupport (hf.comp (continuous_id.sub continuous_const))
      (hasCompactSupport_shift' hcf s) hw
  have h4 : Integrable fun L => f L * w (L - s) :=
    integrable_mul_of_compactSupport hf hcf (hw.comp (continuous_id.sub continuous_const))
  have h5 : Integrable fun L => f L * w (L + s) :=
    integrable_mul_of_compactSupport hf hcf (hw.comp (continuous_id.add continuous_const))
  have hswap : (∫ L, f (L - s) * w L) = ∫ L, f L * w (L + s) := by
    have h := integral_add_right_eq_self (μ := volume) (fun x : ℝ => f (x - s) * w x) s
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun L => by simp)
  have hL : (∫ L, (2 * f L - f (L + s) - f (L - s)) * w L)
      = 2 * (∫ L, f L * w L) - (∫ L, f (L + s) * w L) - ∫ L, f (L - s) * w L := by
    have e1 : Integrable fun L => 2 * (f L * w L) - f (L + s) * w L := (h1.const_mul 2).sub h2
    have step1 : (∫ L, (2 * f L - f (L + s) - f (L - s)) * w L)
        = ∫ L, ((2 * (f L * w L) - f (L + s) * w L) - f (L - s) * w L) :=
      integral_congr_ae (Filter.Eventually.of_forall fun L => by ring)
    rw [step1, MeasureTheory.integral_sub e1 h3,
      MeasureTheory.integral_sub (h1.const_mul 2) h2, MeasureTheory.integral_const_mul]
  have hR : (∫ L, f L * (2 * w L - w (L - s) - w (L + s)))
      = 2 * (∫ L, f L * w L) - (∫ L, f L * w (L - s)) - ∫ L, f L * w (L + s) := by
    have e1 : Integrable fun L => 2 * (f L * w L) - f L * w (L - s) := (h1.const_mul 2).sub h4
    have step1 : (∫ L, f L * (2 * w L - w (L - s) - w (L + s)))
        = ∫ L, ((2 * (f L * w L) - f L * w (L - s)) - f L * w (L + s)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun L => by ring)
    rw [step1, MeasureTheory.integral_sub e1 h5,
      MeasureTheory.integral_sub (h1.const_mul 2) h4, MeasureTheory.integral_const_mul]
  rw [hL, hR, integral_translate_pairing f w s, hswap]

end GaloisForLFunctions.HTGeometry
