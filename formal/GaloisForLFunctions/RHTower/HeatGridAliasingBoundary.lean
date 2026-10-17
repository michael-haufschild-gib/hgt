import GaloisForLFunctions.RHTower.XiGaussianHeatTwoPrimeSampling

/-!
# A single heat grid can hide a nonreal parabolic frequency

For every positive step, a conjugate pair strictly inside the right spectral
parabola has exactly the sampled heat trace of a positive real atom. Every
sampled Hankel section is nonnegative, even after arbitrary odd prefixes,
while the trace at half a step is strictly negative. Two incommensurate
prime grids remove this aliasing for the actual Xi source.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- A nonreal frequency inside `Im(w)^2 < Re(w)` with one full turn per grid step. -/
def heatGridAliasedFrequency (h : ℝ) : ℂ :=
  ((1 + (2 * Real.pi / h) ^ 2 : ℝ) : ℂ) + ((2 * Real.pi / h : ℝ) : ℂ) * I

/-- The real trace of the conjugation-closed two-frequency packet. -/
def heatGridAliasedTrace (h t : ℝ) : ℝ :=
  (Complex.exp (-(t : ℂ) * heatGridAliasedFrequency h) +
    Complex.exp (-(t : ℂ) * (starRingEnd ℂ) (heatGridAliasedFrequency h))).re

theorem heatGridAliasedFrequency_re (h : ℝ) :
    (heatGridAliasedFrequency h).re = 1 + (2 * Real.pi / h) ^ 2 := by
  simp only [heatGridAliasedFrequency, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem heatGridAliasedFrequency_im (h : ℝ) :
    (heatGridAliasedFrequency h).im = 2 * Real.pi / h := by
  simp only [heatGridAliasedFrequency, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]
  ring

theorem heatGridAliasedTrace_eq (h t : ℝ) :
    heatGridAliasedTrace h t =
      2 * Real.exp (-t * (1 + (2 * Real.pi / h) ^ 2)) *
        Real.cos (t * (2 * Real.pi / h)) := by
  simp only [heatGridAliasedTrace, Complex.add_re, Complex.exp_re,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, add_zero,
    Complex.conj_re, Complex.conj_im, heatGridAliasedFrequency_re,
    heatGridAliasedFrequency_im]
  ring_nf
  rw [Real.cos_neg]
  ring

/-- On the entire grid the nonreal packet is indistinguishable from one positive real atom. -/
theorem heatGridAliasedTrace_nat {h : ℝ} (hh : 0 < h) (n : ℕ) :
    heatGridAliasedTrace h ((n : ℝ) * h) =
      2 * Real.exp (-h * (1 + (2 * Real.pi / h) ^ 2)) ^ n := by
  rw [heatGridAliasedTrace_eq]
  have hphase : ((n : ℝ) * h) * (2 * Real.pi / h) = (n : ℝ) * (2 * Real.pi) := by
    field_simp [ne_of_gt hh]
  rw [hphase, Real.cos_nat_mul_two_pi, mul_one, ← Real.exp_nat_mul]
  congr 2
  ring

/-- The hidden negative sign already occurs halfway between consecutive samples. -/
theorem heatGridAliasedTrace_half_neg {h : ℝ} (hh : 0 < h) :
    heatGridAliasedTrace h (h / 2) < 0 := by
  rw [heatGridAliasedTrace_eq]
  have hphase : h / 2 * (2 * Real.pi / h) = Real.pi := by
    field_simp [ne_of_gt hh]
  rw [hphase, Real.cos_pi]
  have := Real.exp_pos (-(h / 2) * (1 + (2 * Real.pi / h) ^ 2))
  linarith

/-- Every shifted sampled Hankel form is nonnegative for this nonreal packet. -/
theorem completeHankelCone_heatGridAliasedTrace {h : ℝ} (hh : 0 < h) (K : ℕ) :
    CompleteHankelCone
      (fun n : ℕ => heatGridAliasedTrace h ((2 * K + 1 + n : ℕ) * h)) := by
  rw [completeHankelCone_iff_momentFunctional_square_nonnegative]
  intro p
  let r := Real.exp (-h * (1 + (2 * Real.pi / h) ^ 2))
  have hfunctional (P : ℝ[X]) :
      HTGeometry.momentFunctional
        (fun n : ℕ => heatGridAliasedTrace h ((2 * K + 1 + n : ℕ) * h)) P =
      2 * r ^ (2 * K + 1) * P.eval r := by
    rw [HTGeometry.momentFunctional_eq_support_sum, Polynomial.eval_eq_sum,
      Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [heatGridAliasedTrace_nat hh, pow_add]
    dsimp [r]
    ring
  rw [hfunctional, Polynomial.eval_pow]
  exact mul_nonneg (by dsimp [r]; positivity) (sq_nonneg _)

/-- Exact one-grid obstruction inside the natural parabolic frequency region. -/
theorem heatGrid_single_grid_aliasing (h : {t : ℝ // 0 < t}) :
    (heatGridAliasedFrequency h).im ≠ 0 ∧
    (heatGridAliasedFrequency h).im ^ 2 < (heatGridAliasedFrequency h).re ∧
    (∀ K : ℕ, CompleteHankelCone
      (fun n : ℕ => heatGridAliasedTrace h ((2 * K + 1 + n : ℕ) * (h : ℝ)))) ∧
    heatGridAliasedTrace h ((h : ℝ) / 2) < 0 := by
  refine ⟨?_, ?_, completeHankelCone_heatGridAliasedTrace h.property,
    heatGridAliasedTrace_half_neg h.property⟩
  · rw [heatGridAliasedFrequency_im]
    exact ne_of_gt (div_pos (mul_pos (by norm_num) Real.pi_pos) h.property)
  · rw [heatGridAliasedFrequency_re, heatGridAliasedFrequency_im]
    linarith

end

end RHTower
