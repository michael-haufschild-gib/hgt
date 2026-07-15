import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic
import GaloisForLFunctions.RHTower.GaussComponentVerticalMagnitude
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Vertical phase of an archimedean Gauss component

The magnitude asymptotic of a Gauss component is not enough for the paired-channel
Hankel calculation: the moving Fourier phase is load-bearing.  This file supplies the
missing complex vertical asymptotic of the lower Gamma factor and combines the two
digamma phases into the exact logarithmic clock of the Gauss component.
-/

namespace RHTower

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

/-- The lower-half-plane vertical digamma asymptotic, obtained by conjugating the
upper-half-plane theorem. -/
theorem digamma_lower_vertical_sub_log_I_tendsto_zero (σ : ℝ) (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) - (t : ℂ) * Complex.I) -
        ((Real.log t : ℂ) - (Real.pi / 2 : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hupper := digamma_vertical_sub_log_I_tendsto_zero σ hσ
  have hconj := (Complex.continuous_conj.continuousAt.tendsto.comp hupper)
  have hconj' : Tendsto (fun t : ℝ => conj
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) -
        ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I)))
      atTop (nhds 0) := by simpa using hconj
  refine hconj'.congr' ?_
  filter_upwards with t
  rw [map_sub]
  rw [show conj ((σ : ℂ) + (t : ℂ) * Complex.I) =
      (σ : ℂ) - (t : ℂ) * Complex.I by apply Complex.ext <;> simp]
  rw [ReflectedDigammaAnomaly.digamma_conj]
  apply congrArg₂ (· - ·) rfl
  apply Complex.ext <;> simp

/-- Logarithmic derivative of the vertical `m`-fold Gauss component. -/
def gaussComponentVerticalLogDeriv {m : ℕ} (k : Fin m) (t : ℝ) : ℂ :=
  -(Complex.I / (m : ℂ)) * (Real.log (Real.pi / (m : ℝ)) : ℂ) +
    Complex.I / (2 * (m : ℂ)) *
      (Complex.digamma
          ((gaussComponentOffset k : ℂ) +
            (t / (2 * (m : ℝ)) : ℂ) * Complex.I) +
        Complex.digamma
          (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
            (t / (2 * (m : ℝ)) : ℂ) * Complex.I))

/-- The phase clock of a Gauss component is universal: its logarithmic derivative is
asymptotic to `i/m * log (t/(2π))`, independently of the component label `k`. -/
theorem gaussComponentVerticalLogDeriv_sub_clock_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    Tendsto (fun t : ℝ =>
      gaussComponentVerticalLogDeriv k t -
        Complex.I / (m : ℂ) * (Real.log (t / (2 * Real.pi)) : ℂ))
      atTop (nhds 0) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hc : (0 : ℝ) < 2 * (m : ℝ) := mul_pos (by norm_num) hmR
  have ha : 0 ≤ gaussComponentOffset k := by
    rw [gaussComponentOffset]
    positivity
  have hδ : 0 ≤ gaussComponentDelta m := by
    rw [gaussComponentDelta]
    positivity
  have hu := (digamma_vertical_sub_log_I_tendsto_zero
    (gaussComponentOffset k) ha).comp (tendsto_id.atTop_div_const hc)
  have hl := (digamma_lower_vertical_sub_log_I_tendsto_zero
    (gaussComponentOffset k + gaussComponentDelta m) (add_nonneg ha hδ)).comp
      (tendsto_id.atTop_div_const hc)
  have hsum := hu.add hl
  have hscaled := hsum.const_mul (Complex.I / (2 * (m : ℂ)))
  refine hscaled.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htau : 0 < t / (2 * (m : ℝ)) := div_pos ht hc
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlogscale :
      Real.log (t / (2 * (m : ℝ))) - Real.log (Real.pi / (m : ℝ)) =
        Real.log (t / (2 * Real.pi)) := by
    rw [← Real.log_div (div_ne_zero (by positivity) hmR.ne')]
    congr 1
    field_simp
  simp only [gaussComponentVerticalLogDeriv]
  push_cast
  rw [Real.log_div ht.ne' (mul_ne_zero (by norm_num) hmR.ne'),
    Real.log_div hpi.ne' hmR.ne',
    Real.log_div ht.ne' (mul_ne_zero (by norm_num) hpi.ne')]
  ring

end

end RHTower
