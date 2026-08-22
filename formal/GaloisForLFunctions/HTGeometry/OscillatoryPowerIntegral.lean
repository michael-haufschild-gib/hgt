import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The oscillatory power integral and its uniform decay

For `0 < a ≤ T`, `Re s > 0` and a nonzero frequency `l`, one integration by parts gives

`∫_a^T e^{ilt} t^{-s} dt
   = e^{ilT}T^{-s}/(il) − e^{ila}a^{-s}/(il) + (s/(il)) ∫_a^T e^{ilt} t^{-s-1} dt`,

hence the bound

`‖∫_a^T e^{ilt} t^{-s} dt‖ ≤ (2 a^{-Re s} + ‖s‖ a^{-Re s}/Re s) / |l|`,

**uniform in the truncation `T`**.  This is the estimate Burnol uses (arXiv:math/0203120, proof of
Thm. 4.8, quoting his C. R. note) to control the cosine transform `C_a(u, 1-s)` of a truncated
power, and it is what makes the truncated Mellin transforms of a Sonine function converge locally
uniformly across the critical line.

## Main results

* `oscPowerIntegral_ibp` — the integration-by-parts identity.
* `norm_oscPowerIntegral_le` — the `1/|l|` bound, uniform in `T`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set intervalIntegral

noncomputable section

/-- The oscillatory power integral `∫_a^T e^{i l t} t^{-s} dt`. -/
def oscPowerIntegral (a T : ℝ) (s : ℂ) (l : ℝ) : ℂ :=
  ∫ t in a..T, Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) * (t : ℂ) ^ (-s)

private theorem hasDerivAt_oscPhase (l t : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (((l * x : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) * ((l : ℂ) * Complex.I)) t := by
  have h0 : HasDerivAt (fun x : ℝ => ((l * x : ℝ) : ℂ)) (l : ℂ) t := by
    simpa using ((hasDerivAt_id t).const_mul l).ofReal_comp
  have h1 : HasDerivAt (fun x : ℝ => ((l * x : ℝ) : ℂ) * Complex.I) ((l : ℂ) * Complex.I) t := by
    simpa using h0.mul_const Complex.I
  exact h1.cexp

private theorem norm_oscPhase (l t : ℝ) :
    ‖Complex.exp (((l * t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  simpa using Complex.norm_exp_ofReal_mul_I (l * t)

/-- **Integration by parts for the oscillatory power integral.** -/
theorem oscPowerIntegral_ibp {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : -s - 1 ≠ 0) {l : ℝ} (hl : l ≠ 0) :
    oscPowerIntegral a T s l =
      (T : ℂ) ^ (-s) * (Complex.exp (((l * T : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)) -
        (a : ℂ) ^ (-s) * (Complex.exp (((l * a : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)) -
        ∫ t in a..T, (-s * (t : ℂ) ^ (-s - 1)) *
          (Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)) := by
  have hlI : ((l : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hl) Complex.I_ne_zero
  have hnegs : (-s) ≠ 0 := neg_ne_zero.2 hs0
  set u : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hu
  set u' : ℝ → ℂ := fun t => -s * (t : ℂ) ^ (-s - 1) with hu'
  set v : ℝ → ℂ :=
    fun t => Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I) with hv
  set v' : ℝ → ℂ := fun t => Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) with hv'
  have hpos : ∀ t ∈ Set.uIcc a T, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le haT] at ht
    exact lt_of_lt_of_le ha ht.1
  have hposOoo : ∀ t ∈ Set.Ioo (min a T) (max a T), 0 < t := by
    intro t ht
    rw [min_eq_left haT, max_eq_right haT] at ht
    exact lt_trans ha ht.1
  have hderivU : ∀ t : ℝ, 0 < t → HasDerivAt u (u' t) t := by
    intro t ht
    have h := hasDerivAt_ofReal_cpow_const (x := t) ht.ne' (r := -s) hnegs
    exact h
  have hucont : ContinuousOn u (Set.uIcc a T) :=
    fun t ht => ((hderivU t (hpos t ht)).continuousAt).continuousWithinAt
  have hvcont : ContinuousOn v (Set.uIcc a T) :=
    fun t _ => (((hasDerivAt_oscPhase l t).continuousAt).div_const _).continuousWithinAt
  have huu' : ∀ t ∈ Set.Ioo (min a T) (max a T), HasDerivAt u (u' t) t :=
    fun t ht => hderivU t (hposOoo t ht)
  have hvv' : ∀ t ∈ Set.Ioo (min a T) (max a T), HasDerivAt v (v' t) t := by
    intro t _
    have h := (hasDerivAt_oscPhase l t).div_const ((l : ℂ) * Complex.I)
    refine h.congr_deriv ?_
    rw [hv', mul_div_assoc, div_self hlI, mul_one]
  have hu'int : IntervalIntegrable u' volume a T := by
    refine ContinuousOn.intervalIntegrable ?_
    intro t ht
    have htpos : 0 < t := hpos t ht
    have h := hasDerivAt_ofReal_cpow_const (x := t) htpos.ne' (r := -s - 1) hs1
    exact ((h.continuousAt).const_mul (-s)).continuousWithinAt
  have hv'int : IntervalIntegrable v' volume a T :=
    ContinuousOn.intervalIntegrable fun t _ =>
      ((hasDerivAt_oscPhase l t).continuousAt).continuousWithinAt
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := u) (u' := u') (v := v)
    (v' := v') hucont hvcont huu' hvv' hu'int hv'int
  have hcomm : oscPowerIntegral a T s l = ∫ t in a..T, u t * v' t := by
    rw [oscPowerIntegral]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hu, hv']
    ring
  rw [hcomm, hIBP]

/-- **The oscillatory power integral decays like `1/|l|`, uniformly in the truncation.** -/
theorem norm_oscPowerIntegral_le {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) {s : ℂ} (hs : 0 < s.re)
    {l : ℝ} (hl : l ≠ 0) :
    ‖oscPowerIntegral a T s l‖ ≤
      (2 * a ^ (-s.re) + ‖s‖ * a ^ (-s.re) / s.re) / |l| := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1 : -s - 1 ≠ 0 := by
    intro h
    have : s = -1 := by linear_combination -h
    rw [this] at hs
    simp at hs
    linarith
  have hlI : ((l : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hl) Complex.I_ne_zero
  have hlInorm : ‖((l : ℂ) * Complex.I)‖ = |l| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hlabs : 0 < |l| := abs_pos.2 hl
  have hTpos : 0 < T := lt_of_lt_of_le ha haT
  have hpos : ∀ t ∈ Set.uIcc a T, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le haT] at ht
    exact lt_of_lt_of_le ha ht.1
  have hbT : ‖(T : ℂ) ^ (-s) *
      (Complex.exp (((l * T : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I))‖
        = T ^ (-s.re) / |l| := by
    rw [norm_mul, norm_div, hlInorm, norm_oscPhase,
      Complex.norm_cpow_eq_rpow_re_of_pos hTpos, Complex.neg_re]
    ring
  have hba : ‖(a : ℂ) ^ (-s) *
      (Complex.exp (((l * a : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I))‖
        = a ^ (-s.re) / |l| := by
    rw [norm_mul, norm_div, hlInorm, norm_oscPhase,
      Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    ring
  have hTle : T ^ (-s.re) ≤ a ^ (-s.re) := by
    rw [Real.rpow_def_of_pos hTpos, Real.rpow_def_of_pos ha]
    refine Real.exp_le_exp.2 ?_
    have h1 : 0 ≤ Real.log T - Real.log a := by
      have := Real.log_le_log ha haT
      linarith
    nlinarith [mul_nonneg h1 hs.le]
  have hTnn : 0 ≤ T ^ (-s.re) := Real.rpow_nonneg hTpos.le _
  -- the integral term
  have hint : ‖∫ t in a..T, (-s * (t : ℂ) ^ (-s - 1)) *
      (Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I))‖
        ≤ ‖s‖ * a ^ (-s.re) / s.re / |l| := by
    have hle := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun t : ℝ => (-s * (t : ℂ) ^ (-s - 1)) *
        (Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I))) haT
    refine hle.trans ?_
    have hcong : (∫ t in a..T, ‖(-s * (t : ℂ) ^ (-s - 1)) *
        (Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I))‖)
          = ∫ t in a..T, (‖s‖ / |l|) * t ^ (-s.re - 1) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have htpos : 0 < t := hpos t ht
      rw [norm_mul, norm_mul, norm_neg, norm_div, hlInorm, norm_oscPhase,
        Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      ring
    rw [hcong, intervalIntegral.integral_const_mul]
    have hzero : (0 : ℝ) ∉ Set.uIcc a T := by
      rw [Set.uIcc_of_le haT]
      intro hmem
      exact absurd hmem.1 (not_le.2 ha)
    have hrne : (-s.re - 1) ≠ -1 := by
      intro h
      have : s.re = 0 := by linarith
      linarith
    rw [integral_rpow (Or.inr ⟨hrne, hzero⟩)]
    have hexp : -s.re - 1 + 1 = -s.re := by ring
    rw [hexp]
    have hstep : (T ^ (-s.re) - a ^ (-s.re)) / (-s.re) ≤ a ^ (-s.re) / s.re := by
      have hrw : (T ^ (-s.re) - a ^ (-s.re)) / (-s.re)
          = (a ^ (-s.re) - T ^ (-s.re)) / s.re := by
        field_simp
        ring
      rw [hrw]
      gcongr
      linarith
    have hcoef : 0 ≤ ‖s‖ / |l| := by positivity
    calc ‖s‖ / |l| * ((T ^ (-s.re) - a ^ (-s.re)) / (-s.re))
        ≤ ‖s‖ / |l| * (a ^ (-s.re) / s.re) := by
          exact mul_le_mul_of_nonneg_left hstep hcoef
      _ = ‖s‖ * a ^ (-s.re) / s.re / |l| := by ring
  rw [oscPowerIntegral_ibp ha haT hs0 hs1 hl]
  have hsplit := norm_sub_le
    ((T : ℂ) ^ (-s) * (Complex.exp (((l * T : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)) -
      (a : ℂ) ^ (-s) * (Complex.exp (((l * a : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)))
    (∫ t in a..T, (-s * (t : ℂ) ^ (-s - 1)) *
      (Complex.exp (((l * t : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)))
  have hsplit2 := norm_sub_le
    ((T : ℂ) ^ (-s) * (Complex.exp (((l * T : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)))
    ((a : ℂ) ^ (-s) * (Complex.exp (((l * a : ℝ) : ℂ) * Complex.I) / ((l : ℂ) * Complex.I)))
  rw [hbT, hba] at hsplit2
  have hfin : T ^ (-s.re) / |l| + a ^ (-s.re) / |l| + ‖s‖ * a ^ (-s.re) / s.re / |l|
      ≤ (2 * a ^ (-s.re) + ‖s‖ * a ^ (-s.re) / s.re) / |l| := by
    rw [← add_div, ← add_div]
    gcongr
    linarith
  linarith [hsplit, hsplit2, hint, hfin]

end

end GaloisForLFunctions.HTGeometry
