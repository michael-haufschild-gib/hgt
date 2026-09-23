/-
Copyright (c) 2026 Michael L. Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael L. Walker
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Suzuki Gamma-skew frequency flux and homogeneous L² Liouville law

This module isolates the exact Hilbert-space frequency ODE obtained from the differentiated
whole-line logarithmic Suzuki seam equation. With Fourier convention
`f(η) = ∫ F(L) exp(-iηL) dL`, its homogeneous equation is

`f'(η) = -f(η)/(2η) + (i/2) (r(η)I - T) f(η)`,

where the exact logarithmic remainder multiplier `r` is real and the prime coupling `T` is
self-adjoint. The second term is therefore skew for real norm flux. The exact conserved current is

`η ‖f(η)‖²`.

Constancy makes every nonzero current equal to a nonzero multiple of `1 / |η|` in norm square,
contradicting L²-integrability. Consequently every homogeneous solution with integrable norm-square
tails vanishes at every nonzero frequency.

The theorem is unconditional. It does **not** assert that the full Connes/CCM valuation seam has
already been realized by a single bounded self-adjoint `T`; that source-identification connector
remains separate.
-/

open Complex RealInnerProductSpace MeasureTheory Set

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance suzukiGammaSkewFrequencyFluxLocalInst1 : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- Multiplication by `i/2` turns a real scalar shift minus a self-adjoint operator into a
real-inner-product skew direction. -/
lemma suzukiGammaSkew_frequency_inner_zero
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ) (v : H) :
    inner ℝ v (((Complex.I / 2 : ℂ) • (((r : ℂ) • v) - T v))) = 0 := by
  rw [real_inner_eq_re_inner]
  have him :
      Complex.im (inner ℂ v (((r : ℂ) • v) - T v)) = 0 := by
    let S : H →ₗ[ℂ] H := (r : ℂ) • LinearMap.id - (T : H →ₗ[ℂ] H)
    have hS : S.IsSymmetric := by
      apply LinearMap.IsSymmetric.sub
      · apply LinearMap.IsSymmetric.smul
        · simp
        · exact LinearMap.IsSymmetric.id
      · exact hT.isSymmetric
    simpa [S] using hS.im_inner_self_apply v
  rw [inner_smul_right]
  change Complex.re ((Complex.I / 2) *
    inner ℂ v (((r : ℂ) • v) - T v)) = 0
  rw [Complex.mul_re]
  have hIre : (Complex.I / 2 : ℂ).re = 0 := by norm_num
  have hIim : (Complex.I / 2 : ℂ).im = 1 / 2 := by norm_num
  rw [hIre, hIim, him]
  ring

omit [CompleteSpace H] in
/-- Hilbert-space derivative of squared norm along a real parameter. -/
lemma suzukiGammaSkew_sqNorm_hasDerivAt
    {f : ℝ → H} {f' : H} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => ‖f t‖ ^ (2 : ℕ)) (2 * inner ℝ (f x) f') x := by
  have hi := HasDerivAt.inner ℝ h h
  have heq : (fun t => inner ℝ (f t) (f t)) = (fun t => ‖f t‖ ^ (2 : ℕ)) := by
    funext t
    exact real_inner_self_eq_norm_sq (f t)
  rw [heq] at hi
  have hsymm : inner ℝ (f x) f' + inner ℝ f' (f x) = 2 * inner ℝ (f x) f' := by
    rw [real_inner_comm f' (f x)]
    ring
  rwa [hsymm] at hi

/-- Exact real-frequency vector field after Fourier transforming the differentiated homogeneous
Suzuki logarithmic seam equation. -/
def suzukiGammaSkewFrequencyField
    (T : H →L[ℂ] H) (r : ℝ → ℝ) (η : ℝ) (v : H) : H :=
  (-1 / (2 * η) : ℝ) • v +
    (Complex.I / 2 : ℂ) • (((r η : ℂ) • v) - T v)

/-- Self-adjoint part of exact frequency field contributes no radial norm flux. -/
lemma real_inner_suzukiGammaSkewFrequencyField
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ → ℝ)
    {η : ℝ} (v : H) :
    inner ℝ v (suzukiGammaSkewFrequencyField T r η v) =
      (-1 / (2 * η) : ℝ) * ‖v‖ ^ (2 : ℕ) := by
  rw [suzukiGammaSkewFrequencyField, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, suzukiGammaSkew_frequency_inner_zero T hT (r η) v, add_zero]

/-- Exact conserved current: `η ‖f(η)‖²` has derivative zero on either frequency half-line. -/
theorem suzukiGammaSkew_weightedCurrent_hasDerivAt_zero
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ → ℝ)
    (f : ℝ → H) {η : ℝ} (hη : η ≠ 0)
    (hf : HasDerivAt f (suzukiGammaSkewFrequencyField T r η (f η)) η) :
    HasDerivAt (fun x => x * ‖f x‖ ^ (2 : ℕ)) 0 η := by
  have hsq := suzukiGammaSkew_sqNorm_hasDerivAt hf
  have hprod := (hasDerivAt_id η).mul hsq
  have hz :
      1 * ‖f η‖ ^ (2 : ℕ) +
          η * (2 * inner ℝ (f η) (suzukiGammaSkewFrequencyField T r η (f η))) = 0 := by
    rw [one_mul, real_inner_suzukiGammaSkewFrequencyField T hT r]
    field_simp [hη]
    ring
  have hprod0 : HasDerivAt
      (id * fun x => ‖f x‖ ^ (2 : ℕ)) 0 η :=
    hprod.congr_deriv (by simpa only [id_eq] using hz)
  apply hprod0.congr_of_eventuallyEq
  filter_upwards with x
  rfl

/-- Current values agree everywhere on positive frequency half-line. -/
theorem suzukiGammaSkew_weightedCurrent_eq_of_pos
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ → ℝ)
    (f : ℝ → H)
    (hf : ∀ η, η ≠ 0 →
      HasDerivAt f (suzukiGammaSkewFrequencyField T r η (f η)) η)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * ‖f x‖ ^ (2 : ℕ) = y * ‖f y‖ ^ (2 : ℕ) := by
  let J : ℝ → ℝ := fun η => η * ‖f η‖ ^ (2 : ℕ)
  have hJ : ∀ η ∈ Ioi (0 : ℝ), HasDerivAt J 0 η := by
    intro η hη
    exact suzukiGammaSkew_weightedCurrent_hasDerivAt_zero
      T hT r f hη.ne' (hf η hη.ne')
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun η hη => (hJ η hη).differentiableAt.differentiableWithinAt)
    (fun η hη => (hJ η hη).deriv) hx hy

/-- Positive-frequency L² Liouville theorem. Exact seam ODE plus integrable norm square forces
every positive-frequency value to vanish. -/
theorem suzukiGammaSkew_eq_zero_of_pos_of_integrableOn_normSq
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ → ℝ)
    (f : ℝ → H)
    (hf : ∀ η, η ≠ 0 →
      HasDerivAt f (suzukiGammaSkewFrequencyField T r η (f η)) η)
    (hL2 : IntegrableOn (fun η => ‖f η‖ ^ (2 : ℕ)) (Ioi (1 : ℝ))) :
    ∀ η, 0 < η → f η = 0 := by
  have hcurrent (η : ℝ) (hη : 0 < η) :
      η * ‖f η‖ ^ (2 : ℕ) = ‖f 1‖ ^ (2 : ℕ) := by
    simpa using suzukiGammaSkew_weightedCurrent_eq_of_pos
      T hT r f hf hη zero_lt_one
  have hC : ‖f 1‖ ^ (2 : ℕ) = 0 := by
    by_contra hCne
    have hscaled : IntegrableOn (fun η : ℝ => ‖f 1‖ ^ (2 : ℕ) * η⁻¹) (Ioi (1 : ℝ)) := by
      refine hL2.congr_fun ?_ measurableSet_Ioi
      intro η hη
      have hη0 : η ≠ 0 := ne_of_gt (lt_trans zero_lt_one hη)
      have hc := hcurrent η (lt_trans zero_lt_one hη)
      calc
        ‖f η‖ ^ (2 : ℕ) = η⁻¹ * ‖f 1‖ ^ (2 : ℕ) := by
          apply (eq_inv_mul_iff_mul_eq₀ hη0).2
          simpa [mul_comm] using hc
        _ = ‖f 1‖ ^ (2 : ℕ) * η⁻¹ := by ring
    have hinv : IntegrableOn (fun η : ℝ => η⁻¹) (Ioi (1 : ℝ)) := by
      have hi : IntegrableOn
          (fun η : ℝ => (‖f 1‖ ^ (2 : ℕ))⁻¹ * (‖f 1‖ ^ (2 : ℕ) * η⁻¹))
          (Ioi (1 : ℝ)) :=
        Integrable.const_mul hscaled (‖f 1‖ ^ (2 : ℕ))⁻¹
      refine hi.congr_fun ?_ measurableSet_Ioi
      intro η _
      calc
        (‖f 1‖ ^ (2 : ℕ))⁻¹ * (‖f 1‖ ^ (2 : ℕ) * η⁻¹) =
            ((‖f 1‖ ^ (2 : ℕ))⁻¹ * ‖f 1‖ ^ (2 : ℕ)) * η⁻¹ := by ring
        _ = η⁻¹ := by rw [inv_mul_cancel₀ hCne, one_mul]
    exact not_integrableOn_Ioi_inv hinv
  intro η hη
  have hz : ‖f η‖ ^ (2 : ℕ) = 0 := by
    have hc := hcurrent η hη
    rw [hC, mul_eq_zero] at hc
    exact hc.resolve_left hη.ne'
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- Current values agree everywhere on negative frequency half-line. -/
theorem suzukiGammaSkew_weightedCurrent_eq_of_neg
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ → ℝ)
    (f : ℝ → H)
    (hf : ∀ η, η ≠ 0 →
      HasDerivAt f (suzukiGammaSkewFrequencyField T r η (f η)) η)
    {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    x * ‖f x‖ ^ (2 : ℕ) = y * ‖f y‖ ^ (2 : ℕ) := by
  let J : ℝ → ℝ := fun η => η * ‖f η‖ ^ (2 : ℕ)
  have hJ : ∀ η ∈ Iio (0 : ℝ), HasDerivAt J 0 η := by
    intro η hη
    exact suzukiGammaSkew_weightedCurrent_hasDerivAt_zero
      T hT r f hη.ne (hf η hη.ne)
  apply isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
    (fun η hη => (hJ η hη).differentiableAt.differentiableWithinAt)
    (fun η hη => (hJ η hη).deriv) hx hy

/-- Reciprocal frequency is nonintegrable on every left half-line as well. -/
lemma suzukiGammaSkew_not_integrableOn_Iio_inv {a : ℝ} :
    ¬ IntegrableOn (fun η : ℝ => η⁻¹) (Iio a) := by
  intro h
  have h' : IntegrableOn (fun η : ℝ => η⁻¹) (Iio (-(-a))) := by
    simpa only [neg_neg] using h
  have hn := h'.comp_neg_Ioi (c := -a)
  have hinv : IntegrableOn (fun η : ℝ => η⁻¹) (Ioi (-a)) := by
    have hneg := hn.neg
    refine hneg.congr_fun ?_ measurableSet_Ioi
    intro η _
    simp
  exact not_integrableOn_Ioi_inv hinv

/-- Negative-frequency L² Liouville theorem. -/
theorem suzukiGammaSkew_eq_zero_of_neg_of_integrableOn_normSq
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ → ℝ)
    (f : ℝ → H)
    (hf : ∀ η, η ≠ 0 →
      HasDerivAt f (suzukiGammaSkewFrequencyField T r η (f η)) η)
    (hL2 : IntegrableOn (fun η => ‖f η‖ ^ (2 : ℕ)) (Iio (-1 : ℝ))) :
    ∀ η, η < 0 → f η = 0 := by
  have hcurrent (η : ℝ) (hη : η < 0) :
      η * ‖f η‖ ^ (2 : ℕ) = -‖f (-1)‖ ^ (2 : ℕ) := by
    simpa using suzukiGammaSkew_weightedCurrent_eq_of_neg T hT r f hf
      (x := η) (y := (-1 : ℝ)) hη (by norm_num)
  have hC : ‖f (-1)‖ ^ (2 : ℕ) = 0 := by
    by_contra hCne
    have hKne : -‖f (-1)‖ ^ (2 : ℕ) ≠ 0 := neg_ne_zero.mpr hCne
    have hscaled :
        IntegrableOn (fun η : ℝ => (-‖f (-1)‖ ^ (2 : ℕ)) * η⁻¹) (Iio (-1 : ℝ)) := by
      refine hL2.congr_fun ?_ measurableSet_Iio
      intro η hη
      have hη0 : η ≠ 0 := ne_of_lt (lt_trans hη (by norm_num))
      have hc := hcurrent η (lt_trans hη (by norm_num))
      calc
        ‖f η‖ ^ (2 : ℕ) = η⁻¹ * (-‖f (-1)‖ ^ (2 : ℕ)) := by
          apply (eq_inv_mul_iff_mul_eq₀ hη0).2
          simpa [mul_comm] using hc
        _ = (-‖f (-1)‖ ^ (2 : ℕ)) * η⁻¹ := by ring
    have hinv : IntegrableOn (fun η : ℝ => η⁻¹) (Iio (-1 : ℝ)) := by
      have hi : IntegrableOn
          (fun η : ℝ => (-‖f (-1)‖ ^ (2 : ℕ))⁻¹ *
            ((-‖f (-1)‖ ^ (2 : ℕ)) * η⁻¹))
          (Iio (-1 : ℝ)) :=
        Integrable.const_mul hscaled (-‖f (-1)‖ ^ (2 : ℕ))⁻¹
      refine hi.congr_fun ?_ measurableSet_Iio
      intro η _
      calc
        (-‖f (-1)‖ ^ (2 : ℕ))⁻¹ * ((-‖f (-1)‖ ^ (2 : ℕ)) * η⁻¹) =
            ((-‖f (-1)‖ ^ (2 : ℕ))⁻¹ * (-‖f (-1)‖ ^ (2 : ℕ))) * η⁻¹ := by ring
        _ = η⁻¹ := by rw [inv_mul_cancel₀ hKne, one_mul]
    exact suzukiGammaSkew_not_integrableOn_Iio_inv hinv
  intro η hη
  have hz : ‖f η‖ ^ (2 : ℕ) = 0 := by
    have hc := hcurrent η hη
    rw [hC, neg_zero, mul_eq_zero] at hc
    exact hc.resolve_left hη.ne
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- Whole homogeneous seam Liouville classification, pointwise away from the measure-zero
frequency origin. -/
theorem suzukiGammaSkew_eq_zero_of_integrableTails_normSq
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (r : ℝ → ℝ)
    (f : ℝ → H)
    (hf : ∀ η, η ≠ 0 →
      HasDerivAt f (suzukiGammaSkewFrequencyField T r η (f η)) η)
    (hpos : IntegrableOn (fun η => ‖f η‖ ^ (2 : ℕ)) (Ioi (1 : ℝ)))
    (hneg : IntegrableOn (fun η => ‖f η‖ ^ (2 : ℕ)) (Iio (-1 : ℝ))) :
    ∀ η, η ≠ 0 → f η = 0 := by
  intro η hη
  rcases lt_or_gt_of_ne hη with hηneg | hηpos
  · exact suzukiGammaSkew_eq_zero_of_neg_of_integrableOn_normSq
      T hT r f hf hneg η hηneg
  · exact suzukiGammaSkew_eq_zero_of_pos_of_integrableOn_normSq
      T hT r f hf hpos η hηpos

end RHTower
