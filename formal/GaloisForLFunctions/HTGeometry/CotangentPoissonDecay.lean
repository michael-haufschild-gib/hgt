import GaloisForLFunctions.HTGeometry.ExteriorEulerPoissonBridge
import GaloisForLFunctions.HTGeometry.CylinderCoordinateEulerBridge

set_option autoImplicit false

/-!
# Cotangent decay after its nonzero half-plane limit is removed

The cylinder coordinate identifies upper-half-plane cotangent with a
Herglotz kernel.  Its imaginary part is negative Poisson mass.  The quantity
that decays is `cot z + i`, which also bounds the real part; cotangent itself
does not decay.  A logarithmic exterior-radius coordinate covers the whole
upper half-plane without input hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter
open scoped Topology

noncomputable section

/-- Global upper-half-plane coordinates adapted to the cotangent cylinder. -/
def cotangentPoissonPoint (x θ : ℝ) : ℂ :=
  ((θ : ℂ) + (Real.log (exteriorEulerRadius x) : ℂ) * I) / 2

/-- The contracted cylinder phase. -/
def cotangentPoissonPhase (x θ : ℝ) : ℂ :=
  ((exteriorEulerRadius x)⁻¹ : ℂ) * Complex.exp (θ * I)

theorem norm_cotangentPoissonPhase (x θ : ℝ) :
    ‖cotangentPoissonPhase x θ‖ = (exteriorEulerRadius x)⁻¹ := by
  have hr := exteriorEulerRadius_gt_one x
  rw [cotangentPoissonPhase, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (show 0 < exteriorEulerRadius x by linarith),
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_cotangentPoissonPhase_lt_one (x θ : ℝ) :
    ‖cotangentPoissonPhase x θ‖ < 1 := by
  rw [norm_cotangentPoissonPhase]
  have hr := exteriorEulerRadius_gt_one x
  exact (inv_lt_one₀ (by linarith)).mpr hr

theorem cotangentPoissonPhase_ne_one (x θ : ℝ) :
    cotangentPoissonPhase x θ ≠ 1 := by
  intro h
  have hn := norm_cotangentPoissonPhase_lt_one x θ
  rw [h, norm_one] at hn
  exact (lt_irrefl 1 hn).elim

theorem exp_cotangentPoissonPoint (x θ : ℝ) :
    Complex.exp (2 * I * cotangentPoissonPoint x θ) =
      cotangentPoissonPhase x θ := by
  have hr := exteriorEulerRadius_gt_one x
  have harg : 2 * I * cotangentPoissonPoint x θ =
      -(Real.log (exteriorEulerRadius x) : ℂ) + (θ : ℂ) * I := by
    unfold cotangentPoissonPoint
    ring_nf
    rw [I_sq]
    ring
  rw [harg, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp,
    Real.exp_log (show 0 < exteriorEulerRadius x by linarith)]
  rfl

/-- Exact cylinder representation, with its denominator exclusion proved
from the radius coordinate. -/
theorem cot_cotangentPoissonPoint (x θ : ℝ) :
    Complex.cot (cotangentPoissonPoint x θ) =
      I * ((cotangentPoissonPhase x θ + 1) / (cotangentPoissonPhase x θ - 1)) := by
  rw [Complex.cot_eq_cos_div_sin, cos_div_sin_eq_cylinder _
    (by rw [exp_cotangentPoissonPoint]; exact cotangentPoissonPhase_ne_one x θ),
    exp_cotangentPoissonPoint]

/-- The imaginary component is exactly negative Poisson mass. -/
theorem cot_cotangentPoissonPoint_im (x θ : ℝ) :
    (Complex.cot (cotangentPoissonPoint x θ)).im =
      -poissonKernel 0 (cotangentPoissonPhase x θ) 1 := by
  rw [cot_cotangentPoissonPoint]
  have halg : (cotangentPoissonPhase x θ + 1) / (cotangentPoissonPhase x θ - 1) =
      -herglotzRieszKernel 0 (cotangentPoissonPhase x θ) 1 := by
    unfold herglotzRieszKernel
    simp only [sub_zero]
    rw [show cotangentPoissonPhase x θ - 1 = -(1 - cotangentPoissonPhase x θ) by ring]
    simp only [div_neg, add_comm]
  rw [halg, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, neg_re]
  rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply]

theorem cot_cotangentPoissonPoint_im_neg (x θ : ℝ) :
    (Complex.cot (cotangentPoissonPoint x θ)).im < 0 := by
  rw [cot_cotangentPoissonPoint_im]
  exact neg_neg_of_pos (poissonKernel_zero_pos_of_norm_lt_one
    (norm_cotangentPoissonPhase_lt_one x θ) (norm_one : ‖(1 : ℂ)‖ = 1))

/-- Removing the limiting value exposes one decaying resolvent. -/
theorem cot_cotangentPoissonPoint_add_I (x θ : ℝ) :
    Complex.cot (cotangentPoissonPoint x θ) + I =
      2 * I * cotangentPoissonPhase x θ / (cotangentPoissonPhase x θ - 1) := by
  rw [cot_cotangentPoissonPoint]
  field_simp [sub_ne_zero.mpr (cotangentPoissonPhase_ne_one x θ)]
  ring

/-- Uniform decay of the corrected cotangent, with an explicit radius
bound and no numerical verification. -/
theorem norm_cot_cotangentPoissonPoint_add_I_le (x θ : ℝ) :
    ‖Complex.cot (cotangentPoissonPoint x θ) + I‖ ≤
      2 / (exteriorEulerRadius x - 1) := by
  have hr := exteriorEulerRadius_gt_one x
  have hr0 : 0 < exteriorEulerRadius x := by linarith
  have hq := norm_cotangentPoissonPhase_lt_one x θ
  have hden : 1 - (exteriorEulerRadius x)⁻¹ ≤ ‖cotangentPoissonPhase x θ - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (cotangentPoissonPhase x θ)
    rw [norm_one, norm_cotangentPoissonPhase, norm_sub_rev] at h
    exact h
  have hpos : 0 < 1 - (exteriorEulerRadius x)⁻¹ := by
    rw [norm_cotangentPoissonPhase] at hq
    linarith
  rw [cot_cotangentPoissonPoint_add_I, norm_div, norm_mul, norm_mul,
    norm_I, norm_ofNat, mul_one, norm_cotangentPoissonPhase]
  calc
    2 * (exteriorEulerRadius x)⁻¹ / ‖cotangentPoissonPhase x θ - 1‖ ≤
        2 * (exteriorEulerRadius x)⁻¹ / (1 - (exteriorEulerRadius x)⁻¹) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = 2 / (exteriorEulerRadius x - 1) := by field_simp

/-- The real part inherits the corrected cotangent's decay bound. -/
theorem abs_re_cot_cotangentPoissonPoint_le (x θ : ℝ) :
    |(Complex.cot (cotangentPoissonPoint x θ)).re| ≤
      2 / (exteriorEulerRadius x - 1) := by
  calc
    |(Complex.cot (cotangentPoissonPoint x θ)).re| =
        |(Complex.cot (cotangentPoissonPoint x θ) + I).re| := by simp
    _ ≤ ‖Complex.cot (cotangentPoissonPoint x θ) + I‖ := Complex.abs_re_le_norm _
    _ ≤ _ := norm_cot_cotangentPoissonPoint_add_I_le x θ

/-- The correction decays exponentially in the global radius coordinate. -/
theorem norm_cot_cotangentPoissonPoint_add_I_le_exp (x θ : ℝ) :
    ‖Complex.cot (cotangentPoissonPoint x θ) + I‖ ≤ 2 * Real.exp (-x) := by
  simpa only [exteriorEulerRadius, add_sub_cancel_left, Real.exp_neg, div_eq_mul_inv]
    using norm_cot_cotangentPoissonPoint_add_I_le x θ

/-- Even an arbitrarily varying horizontal phase has the same nonzero
upper-half-plane cotangent limit. -/
theorem tendsto_cot_cotangentPoissonPoint (θ : ℝ → ℝ) :
    Tendsto (fun x => Complex.cot (cotangentPoissonPoint x (θ x)))
      atTop (nhds (-I)) := by
  have hb : Tendsto (fun x : ℝ => 2 * Real.exp (-x)) atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
  have hz : Tendsto (fun x => Complex.cot (cotangentPoissonPoint x (θ x)) + I)
      atTop (nhds (0 : ℂ)) :=
    squeeze_zero_norm (fun x => norm_cot_cotangentPoissonPoint_add_I_le_exp x (θ x)) hb
  simpa using hz.sub_const I

end

end GaloisForLFunctions.HTGeometry
