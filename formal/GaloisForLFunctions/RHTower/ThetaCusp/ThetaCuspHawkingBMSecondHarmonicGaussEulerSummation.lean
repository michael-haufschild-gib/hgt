import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussCoefficientAsymptotics
import GaloisForLFunctions.HTGeometry.GammaNatShift
import Mathlib.Analysis.Analytic.Binomial

/-!
# Euler-integral proof of Gauss summation in a positive chamber

This file proves the exact Gamma quotient for the ordinary hypergeometric coefficient sum when
Euler's integral is dominated by an explicit real binomial majorant.  Subsequent contiguous
transport removes this auxiliary chamber while preserving the convergence half-plane.
-/

open Complex Nat Polynomial Filter Topology Set MeasureTheory


namespace RHTower
noncomputable section

theorem inv_factorial_mul_ascPochhammer_eq_choose (a : ℂ) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a =
      Ring.choose (a + n - 1) n := by
  rw [← Ring.multichoose_eq a n, ← Polynomial.ascPochhammer_smeval_eq_eval,
    Polynomial.ascPochhammer_smeval_cast]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  simp only [nsmul_eq_mul] at h
  rw [← h]
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

theorem inv_factorial_mul_ascPochhammer_real_eq_choose (a : ℝ) (n : ℕ) :
    (n.factorial : ℝ)⁻¹ * (ascPochhammer ℝ n).eval a =
      Ring.choose (a + n - 1) n := by
  rw [← Ring.multichoose_eq a n, ← Polynomial.ascPochhammer_smeval_eq_eval,
    Polynomial.ascPochhammer_smeval_cast]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  simp only [nsmul_eq_mul] at h
  rw [← h]
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

theorem ascPochhammer_eval_real_eq_prod_range (s : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval s = ∏ j ∈ Finset.range n, (s + (j : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

theorem norm_ascPochhammer_eval_le_real_norm (a : ℂ) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a‖ ≤ (ascPochhammer ℝ n).eval ‖a‖ := by
  rw [ascPochhammer_eval_eq_prod_range, ascPochhammer_eval_real_eq_prod_range, norm_prod]
  apply Finset.prod_le_prod
  · intro j hj
    positivity
  · intro j hj
    calc
      ‖a + (j : ℂ)‖ ≤ ‖a‖ + ‖(j : ℂ)‖ := norm_add_le a (j : ℂ)
      _ = ‖a‖ + (j : ℝ) := by rw [Complex.norm_natCast]

theorem norm_inv_factorial_mul_ascPochhammer_le_choose_norm
    (a : ℂ) (n : ℕ) :
    ‖(n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a‖ ≤
      Ring.choose ((‖a‖ : ℝ) + n - 1) n := by
  rw [norm_mul, norm_inv, norm_natCast,
    ← inv_factorial_mul_ascPochhammer_real_eq_choose]
  gcongr
  exact norm_ascPochhammer_eval_le_real_norm a n

theorem hasSum_ascPochhammer_div_factorial_mul_pow
    (a : ℂ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum
      (fun n : ℕ => (n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a * (x : ℂ) ^ n)
      (1 / (1 - (x : ℂ)) ^ a) := by
  have hxball : (x : ℂ) ∈ Metric.eball 0 1 := by
    rw [Metric.mem_eball, edist_dist, Complex.dist_eq, sub_zero,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, ENNReal.ofReal_lt_one]
    exact hx1
  have hs := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum hxball
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    inv_factorial_mul_ascPochhammer_eq_choose, zero_add] using hs

theorem hasSum_choose_mul_pow_real
    (A : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum
      (fun n : ℕ => Ring.choose (A + n - 1) n * x ^ n)
      (1 / (1 - x) ^ A) := by
  have hxball : x ∈ Metric.eball 0 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg hx0,
      ENNReal.ofReal_lt_one]
    exact hx1
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero A).hasSum hxball
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hs

def gaussEulerTerm (a b c : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) *
    (x : ℂ) ^ (b + n - 1) * (1 - (x : ℂ)) ^ (c - b - 1)

def gaussEulerMajorant (a b c : ℂ) (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - 1) *
    (Ring.choose ((‖a‖ : ℝ) + n - 1) n * x ^ n)

theorem hasSum_gaussEulerTerm
    (a b c : ℂ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => gaussEulerTerm a b c n x)
      ((x : ℂ) ^ (b - 1) * (1 - (x : ℂ)) ^ (c - a - b - 1)) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hy : (0 : ℝ) < 1 - x := sub_pos.mpr hx1
  have hyc : (1 - (x : ℂ)) ≠ 0 := by
    norm_cast
    exact hy.ne'
  have hs := hasSum_ascPochhammer_div_factorial_mul_pow a hx0.le hx1
  have hmul := hs.mul_left
    ((x : ℂ) ^ (b - 1) * (1 - (x : ℂ)) ^ (c - b - 1))
  have hterm (n : ℕ) :
      gaussEulerTerm a b c n x =
        ((x : ℂ) ^ (b - 1) * (1 - (x : ℂ)) ^ (c - b - 1)) *
          ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a * (x : ℂ) ^ n) := by
    simp only [gaussEulerTerm]
    rw [show b + (n : ℂ) - 1 = (b - 1) + n by ring,
      Complex.cpow_add _ _ hxc, Complex.cpow_natCast]
    ring
  have hseries : HasSum (fun n : ℕ => gaussEulerTerm a b c n x)
      ((x : ℂ) ^ (b - 1) * (1 - (x : ℂ)) ^ (c - b - 1) *
        (1 / (1 - (x : ℂ)) ^ a)) := by
    exact HasSum.congr_fun hmul hterm
  convert hseries using 1
  rw [show c - a - b - 1 = (c - b - 1) + (-a) by ring,
    Complex.cpow_add _ _ hyc, Complex.cpow_neg]
  ring

theorem gaussEulerTerm_norm_le_majorant
    (a b c : ℂ) (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖gaussEulerTerm a b c n x‖ ≤ gaussEulerMajorant a b c n x := by
  have hy : (0 : ℝ) < 1 - x := sub_pos.mpr hx1
  have hnormy : ‖(1 - (x : ℂ)) ^ (c - b - 1)‖ =
      (1 - x) ^ (c - b - 1).re := by
    have heq : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hxpow : x ^ (b + n - 1).re = x ^ (b.re - 1) * x ^ n := by
    rw [show (b + (n : ℂ) - 1).re = (b.re - 1) + n by simp; ring,
      Real.rpow_add hx0, Real.rpow_natCast]
  rw [gaussEulerTerm, gaussEulerMajorant, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0,
    hnormy, hxpow]
  have hcoeff := norm_inv_factorial_mul_ascPochhammer_le_choose_norm a n
  calc
    ‖(n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a‖ *
          (x ^ (b.re - 1) * x ^ n) * (1 - x) ^ (c - b - 1).re ≤
        Ring.choose (‖a‖ + (n : ℝ) - 1) n *
          (x ^ (b.re - 1) * x ^ n) * (1 - x) ^ (c - b - 1).re := by
      gcongr
    _ = x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - 1) *
          (Ring.choose (‖a‖ + (n : ℝ) - 1) n * x ^ n) := by
      simp only [Complex.sub_re, Complex.one_re]
      ring

theorem hasSum_gaussEulerMajorant
    (a b c : ℂ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => gaussEulerMajorant a b c n x)
      (x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - ‖a‖ - 1)) := by
  have hy : (0 : ℝ) < 1 - x := sub_pos.mpr hx1
  have hs := hasSum_choose_mul_pow_real ‖a‖ hx0.le hx1
  have hmul := hs.mul_left (x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - 1))
  have hterm (n : ℕ) :
      gaussEulerMajorant a b c n x =
        (x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - 1)) *
          (Ring.choose (‖a‖ + (n : ℝ) - 1) n * x ^ n) := by
    rfl
  have hseries : HasSum (fun n : ℕ => gaussEulerMajorant a b c n x)
      ((x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - 1)) *
        (1 / (1 - x) ^ ‖a‖)) := HasSum.congr_fun hmul hterm
  convert hseries using 1
  rw [show (c - b).re - ‖a‖ - 1 = ((c - b).re - 1) + (-‖a‖) by ring,
    Real.rpow_add hy, Real.rpow_neg hy.le]
  ring

theorem intervalIntegrable_tsum_gaussEulerMajorant
    (a b c : ℂ) (hb : 0 < b.re) (hmargin : ‖a‖ < (c - b).re) :
    IntervalIntegrable (fun x : ℝ => ∑' n : ℕ, gaussEulerMajorant a b c n x)
      volume 0 1 := by
  have hright : 0 < (c - b).re - ‖a‖ := sub_pos.mpr hmargin
  have hbeta := Complex.betaIntegral_convergent
    (u := (b.re : ℂ)) (v := (((c - b).re - ‖a‖ : ℝ) : ℂ))
    (by simpa using hb) (by simpa using hright)
  have htarget : IntervalIntegrable
      (fun x : ℝ => x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - ‖a‖ - 1))
      volume 0 1 := by
    apply hbeta.norm.congr_uIoo
    intro x hx
    have hx0 : 0 < x := by simpa using hx.1
    have hx1 : x < 1 := by simpa using hx.2
    have hy : 0 < 1 - x := sub_pos.mpr hx1
    have hnormy : ‖(1 - (x : ℂ)) ^ ((((c - b).re - ‖a‖ : ℝ) : ℂ) - 1)‖ =
        (1 - x) ^ (((((c - b).re - ‖a‖ : ℝ) : ℂ) - 1).re) := by
      have heq : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
      rw [heq, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    change ‖(x : ℂ) ^ ((b.re : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((((c - b).re - ‖a‖ : ℝ) : ℂ) - 1)‖ =
      x ^ (b.re - 1) * (1 - x) ^ ((c - b).re - ‖a‖ - 1)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hnormy]
    simp only [Complex.ofReal_sub, Complex.ofReal_re,
      Complex.sub_re, Complex.one_re]
  apply htarget.congr_uIoo
  intro x hx
  have hx0 : 0 < x := by simpa using hx.1
  have hx1 : x < 1 := by simpa using hx.2
  exact (hasSum_gaussEulerMajorant a b c hx0 hx1).tsum_eq.symm

theorem gaussEulerTerm_intervalIntegrable
    (a b c : ℂ) (n : ℕ) (hb : 0 < b.re) (hcb : 0 < (c - b).re) :
    IntervalIntegrable (gaussEulerTerm a b c n) volume 0 1 := by
  have hbn : 0 < (b + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  have hbeta := (Complex.betaIntegral_convergent hbn hcb).const_mul
    ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a)
  change IntervalIntegrable (fun x : ℝ =>
    ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) *
      (x : ℂ) ^ (b + n - 1) * (1 - (x : ℂ)) ^ (c - b - 1)) volume 0 1
  simpa only [mul_assoc] using hbeta

theorem hasSum_intervalIntegral_gaussEulerTerm
    (a b c : ℂ) (hb : 0 < b.re) (hmargin : ‖a‖ < (c - b).re) :
    HasSum
      (fun n : ℕ => ∫ x : ℝ in 0..1, gaussEulerTerm a b c n x)
      (Complex.betaIntegral b (c - a - b)) := by
  have hcb : 0 < (c - b).re := lt_of_le_of_lt (norm_nonneg a) hmargin
  have hgap : 0 < (c - a - b).re := by
    have hre : (c - a - b).re = (c - b).re - a.re := by
      simp only [Complex.sub_re]
      ring
    rw [hre]
    exact sub_pos.mpr (lt_of_le_of_lt (Complex.re_le_norm a) hmargin)
  have htermInt (n : ℕ) := gaussEulerTerm_intervalIntegrable a b c n hb hcb
  have hDCT := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (F := gaussEulerTerm a b c)
    (f := fun x : ℝ => (x : ℂ) ^ (b - 1) *
      (1 - (x : ℂ)) ^ (c - a - b - 1))
    (gaussEulerMajorant a b c)
    (fun n => (intervalIntegrable_iff.mp (htermInt n)).1)
    (by
      intro n
      filter_upwards [(volume : Measure ℝ).ae_ne 1] with x hxne hxmem
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at hxmem
      exact gaussEulerTerm_norm_le_majorant a b c n hxmem.1
        (lt_of_le_of_ne hxmem.2 hxne))
    (by
      filter_upwards [(volume : Measure ℝ).ae_ne 1] with x hxne hxmem
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at hxmem
      exact (hasSum_gaussEulerMajorant a b c hxmem.1
        (lt_of_le_of_ne hxmem.2 hxne)).summable)
    (intervalIntegrable_tsum_gaussEulerMajorant a b c hb hmargin)
    (by
      filter_upwards [(volume : Measure ℝ).ae_ne 1] with x hxne hxmem
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at hxmem
      exact hasSum_gaussEulerTerm a b c hxmem.1 (lt_of_le_of_ne hxmem.2 hxne))
  simpa only [Complex.betaIntegral] using hDCT

theorem betaIntegral_mul_ordinaryHypergeometricCoefficient_eq_shift
    (a b c : ℂ) (n : ℕ) (hb : 0 < b.re) (hcb : 0 < (c - b).re) :
    Complex.betaIntegral b (c - b) * ordinaryHypergeometricCoefficient a b c n =
      ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a) *
        Complex.betaIntegral (b + n) (c - b) := by
  have hc : 0 < c.re := by
    have hre : c.re = b.re + (c - b).re := by
      simp only [Complex.sub_re]
      ring
    rw [hre]
    positivity
  have hbn : 0 < (b + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  have hcn : 0 < (c + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  have hGb := HTGeometry.Gamma_add_nat_of_re_pos b hb n
  have hGc := HTGeometry.Gamma_add_nat_of_re_pos c hc n
  rw [← ascPochhammer_eval_eq_prod_range] at hGb hGc
  have hGbn0 : Complex.Gamma (b + (n : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) k]
  have hGcn0 : Complex.Gamma (c + (n : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) k]
  have hGc0 : Complex.Gamma c ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hPc : (ascPochhammer ℂ n).eval c ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hGc
    exact hGcn0 hGc
  rw [Complex.betaIntegral_eq_Gamma_mul_div b (c - b) hb hcb,
    Complex.betaIntegral_eq_Gamma_mul_div (b + n) (c - b) hbn hcb]
  rw [show b + (c - b) = c by ring,
    show b + (n : ℂ) + (c - b) = c + n by ring,
    hGb, hGc]
  simp only [ordinaryHypergeometricCoefficient]
  field_simp [hGc0, hGcn0, hPc]

theorem intervalIntegral_gaussEulerTerm_eq
    (a b c : ℂ) (n : ℕ) (hb : 0 < b.re) (hcb : 0 < (c - b).re) :
    (∫ x : ℝ in 0..1, gaussEulerTerm a b c n x) =
      Complex.betaIntegral b (c - b) * ordinaryHypergeometricCoefficient a b c n := by
  rw [betaIntegral_mul_ordinaryHypergeometricCoefficient_eq_shift a b c n hb hcb]
  rw [Complex.betaIntegral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [gaussEulerTerm]
  ring

theorem Complex.Gamma_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro k hk
  have := congrArg Complex.re hk
  simp only [Complex.neg_re, Complex.natCast_re] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem tsum_ordinaryHypergeometricCoefficient_eq_beta_ratio_of_euler_chamber
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : 0 < b.re) (hmargin : ‖a‖ < (c - b).re) :
    ∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n =
      Complex.betaIntegral b (c - a - b) / Complex.betaIntegral b (c - b) := by
  have hcb : 0 < (c - b).re := lt_of_le_of_lt (norm_nonneg a) hmargin
  have hc : 0 < c.re := by
    have hre : c.re = b.re + (c - b).re := by
      simp only [Complex.sub_re]
      ring
    rw [hre]
    positivity
  have hgap : 0 < (c - a - b).re := by
    have hre : (c - a - b).re = (c - b).re - a.re := by
      simp only [Complex.sub_re]
      ring
    rw [hre]
    exact sub_pos.mpr (lt_of_le_of_lt (Complex.re_le_norm a) hmargin)
  have hbavoid : ∀ k : ℕ, (k : ℂ) ≠ -b := by
    intro k hk
    have := congrArg Complex.re hk
    simp only [Complex.natCast_re, Complex.neg_re] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hcavoid : ∀ k : ℕ, (k : ℂ) ≠ -c := by
    intro k hk
    have := congrArg Complex.re hk
    simp only [Complex.natCast_re, Complex.neg_re] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hsum := summable_ordinaryHypergeometricCoefficient_of_re_gap_pos
    a b c ha hbavoid hcavoid hgap
  have hintegral := hasSum_intervalIntegral_gaussEulerTerm a b c hb hmargin
  have hscaled : HasSum
      (fun n : ℕ => Complex.betaIntegral b (c - b) *
        ordinaryHypergeometricCoefficient a b c n)
      (Complex.betaIntegral b (c - a - b)) := by
    exact HasSum.congr_fun hintegral fun n =>
      (intervalIntegral_gaussEulerTerm_eq a b c n hb hcb).symm
  have hscaled' := hsum.hasSum.mul_left (Complex.betaIntegral b (c - b))
  have heq : Complex.betaIntegral b (c - b) *
      (∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n) =
        Complex.betaIntegral b (c - a - b) := hscaled'.unique hscaled
  have hbeta0 : Complex.betaIntegral b (c - b) ≠ 0 := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div b (c - b) hb hcb,
      show b + (c - b) = c by ring]
    exact div_ne_zero
      (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hb)
        (Complex.Gamma_ne_zero_of_re_pos hcb))
      (Complex.Gamma_ne_zero_of_re_pos hc)
  exact (eq_div_iff hbeta0).2 (by simpa only [mul_comm] using heq)

theorem gaussSummation_of_euler_chamber
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : 0 < b.re) (hmargin : ‖a‖ < (c - b).re) :
    ∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n =
      Complex.Gamma c * Complex.Gamma (c - a - b) /
        (Complex.Gamma (c - a) * Complex.Gamma (c - b)) := by
  rw [tsum_ordinaryHypergeometricCoefficient_eq_beta_ratio_of_euler_chamber
    a b c ha hb hmargin]
  have hcb : 0 < (c - b).re := lt_of_le_of_lt (norm_nonneg a) hmargin
  have hgap : 0 < (c - a - b).re := by
    have hre : (c - a - b).re = (c - b).re - a.re := by
      simp only [Complex.sub_re]
      ring
    rw [hre]
    exact sub_pos.mpr (lt_of_le_of_lt (Complex.re_le_norm a) hmargin)
  have hca : 0 < (c - a).re := by
    have hre : (c - a).re = b.re + (c - a - b).re := by
      simp only [Complex.sub_re]
      ring
    rw [hre]
    positivity
  have hc : 0 < c.re := by
    have hre : c.re = b.re + (c - b).re := by
      simp only [Complex.sub_re]
      ring
    rw [hre]
    positivity
  rw [Complex.betaIntegral_eq_Gamma_mul_div b (c - a - b) hb hgap,
    Complex.betaIntegral_eq_Gamma_mul_div b (c - b) hb hcb,
    show b + (c - a - b) = c - a by ring,
    show b + (c - b) = c by ring]
  field_simp [Complex.Gamma_ne_zero_of_re_pos hb,
    Complex.Gamma_ne_zero_of_re_pos hgap,
    Complex.Gamma_ne_zero_of_re_pos hca,
    Complex.Gamma_ne_zero_of_re_pos hcb,
    Complex.Gamma_ne_zero_of_re_pos hc]

end
end RHTower
