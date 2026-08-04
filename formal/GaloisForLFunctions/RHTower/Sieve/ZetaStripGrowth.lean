import GaloisForLFunctions.RHTower.FractionalPartZeta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Growth of zeta in the strip

The corpus's fractional-part continuation gives, for `re s > 0` and `s ≠ 1`,

`∫₁^∞ fract(t)·t^{-(s+1)} dt = 1/(s−1) − ζ(s)/s`.

Since `0 ≤ fract t < 1`, the integral is bounded by `∫₁^∞ t^{-σ-1} dt = 1/σ`, so

`‖ζ(s)‖ ≤ ‖s‖/‖s−1‖ + ‖s‖/σ`.

This is the growth estimate the three-four-one inequality needs on the left of the abscissa of
convergence: linear in `|s|`, which is what the classical zero-free region argument consumes.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

/-- The fractional-part integral is bounded by `1/σ`. -/
theorem norm_integral_fract_cpow_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖
      ≤ 1 / s.re := by
  have hintegrable : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hpt : ∀ t ∈ Set.Ioi (1 : ℝ),
      ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-s.re - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
      exact le_of_lt (Int.fract_lt_one t)
    have hpow : ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      ring
    rw [norm_mul, hpow]
    have hnn : (0 : ℝ) ≤ t ^ (-s.re - 1) := Real.rpow_nonneg ht0.le _
    nlinarith [hfract, hnn, norm_nonneg (((Int.fract t : ℝ) : ℂ))]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hae : ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (1 : ℝ))),
      ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-s.re - 1) :=
    Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) hpt
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
    hintegrable hae) ?_
  rw [integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) (by norm_num : (0:ℝ) < 1)]
  have hexp : -s.re - 1 + 1 = -s.re := by ring
  rw [hexp, Real.one_rpow]
  rw [neg_div_neg_eq]

/-- **Growth of zeta in the strip.**  From the fractional-part continuation: for `re s > 0` and
`s ≠ 1`, the size of `ζ` is linear in `‖s‖`. -/
theorem norm_riemannZeta_strip_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have hkey := RHTower.integral_Ioi_one_fract_cpow_of_re_pos hs hs1
  have hsne : s ≠ 0 := by
    intro hcon
    rw [hcon] at hs
    simp at hs
  have hzeta : riemannZeta s = s * (1 / (s - 1)) - s *
      (∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [hkey]
    field_simp
    ring
  rw [hzeta]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖s * (1 / (s - 1))‖ = ‖s‖ / ‖s - 1‖ := by
    rw [norm_mul, norm_div, norm_one]
    ring
  have h2 : ‖s * (∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))‖
      ≤ ‖s‖ / s.re := by
    rw [norm_mul]
    have hb := norm_integral_fract_cpow_le hs
    have hsn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖
        ≤ ‖s‖ * (1 / s.re) := mul_le_mul_of_nonneg_left hb hsn
      _ = ‖s‖ / s.re := by ring
  linarith [h1.le, h1.ge, h2]

end RHTower.Sieve
