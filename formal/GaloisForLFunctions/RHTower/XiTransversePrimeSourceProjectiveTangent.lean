import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Projective tangent geometry of the transverse Xi prime-source aperture

Every finite transverse shift--jet packet has full Hilbert rank, but its zeroth-order prime
columns have a common projective cofinite limit.  This module identifies the first nonzero defect:
two positive apertures `a,b` meet to exact grade `min a b`, with sign determined by their order.
Prime-power valuation layer `e` multiplies the grade by `e+1`.

This is the positive boundary statement left by the failure of an unrenormalized cofinite-prime
Hilbert completion to supply an RH amplifier.  It does not constrain Xi zeros.
-/

namespace RHTower

open Filter Topology

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Projective ratio of two zeroth-order transverse prime-source aperture columns.  The common
prime-logarithm factor has already been cancelled. -/
def xiTransversePrimeApertureRatio (a b : ℕ) (p : Nat.Primes) : ℂ :=
  (1 - primeShiftFactor (a : ℂ) p) / (1 - primeShiftFactor (b : ℂ) p)

/-- A positive integral prime shift factor tends to zero on the cofinite prime filter. -/
theorem tendsto_primeShiftFactor_nat_cofinite_zero (a : ℕ) (ha : 0 < a) :
    Tendsto (fun p : Nat.Primes => primeShiftFactor (a : ℂ) p) cofinite (𝓝 0) := by
  have hare : (0 : ℂ).re < ((a : ℂ).re) := by
    simp only [Complex.zero_re, Complex.natCast_re]
    exact_mod_cast ha
  simpa [primeShiftFactor] using
    (tendsto_primeShiftLog_ratio_of_re_lt
      (α := (a : ℂ)) (β := 0) hare 0 0)

/-- The transverse defect factor is nonzero at every prime for a positive aperture. -/
theorem one_sub_primeShiftFactor_nat_ne_zero
    (a : ℕ) (ha : 0 < a) (p : Nat.Primes) :
    1 - primeShiftFactor (a : ℂ) p ≠ 0 := by
  have hsource := xiTransverseShiftArithmetic_primePow_ne_zero a ha p 0
  rw [pow_one, xiTransverseShiftArithmetic_apply_prime] at hsource
  intro hzero
  apply hsource
  rw [hzero, mul_zero]

/-- The factor ratio in the projective aperture is exactly the ratio of the actual prime-source
columns. -/
theorem xiTransversePrimeApertureRatio_eq_source_ratio
    (a b : ℕ) (hb : 0 < b) (p : Nat.Primes) :
    xiTransversePrimeApertureRatio a b p =
      xiTransverseShiftArithmetic a p / xiTransverseShiftArithmetic b p := by
  rw [xiTransverseShiftArithmetic_apply_prime,
    xiTransverseShiftArithmetic_apply_prime]
  have hp : (Real.log (p : ℕ) : ℂ) ≠ 0 := by
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    exact_mod_cast (Real.log_pos hp1).ne'
  have hb0 := one_sub_primeShiftFactor_nat_ne_zero b hb p
  simp only [xiTransversePrimeApertureRatio]
  field_simp

/-- All positive zeroth-order aperture columns collapse to one projective ray at the cofinite
prime boundary. -/
theorem tendsto_xiTransversePrimeApertureRatio_cofinite_one
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (xiTransversePrimeApertureRatio a b) cofinite (𝓝 1) := by
  have ha0 := tendsto_primeShiftFactor_nat_cofinite_zero a ha
  have hb0 := tendsto_primeShiftFactor_nat_cofinite_zero b hb
  have hnum : Tendsto (fun p : Nat.Primes =>
      (1 : ℂ) - primeShiftFactor (a : ℂ) p) cofinite (𝓝 ((1 : ℂ) - 0)) :=
    tendsto_const_nhds.sub ha0
  have hden : Tendsto (fun p : Nat.Primes =>
      (1 : ℂ) - primeShiftFactor (b : ℂ) p) cofinite (𝓝 ((1 : ℂ) - 0)) :=
    tendsto_const_nhds.sub hb0
  have h := hnum.div hden (by norm_num : (1 : ℂ) - 0 ≠ 0)
  simpa [xiTransversePrimeApertureRatio] using! h

/-- If `a<b`, the first projective defect occurs at the smaller shift grade `a` and has
orientation `-1`. -/
theorem tendsto_xiTransversePrimeApertureRatio_firstDefect_of_lt
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun p : Nat.Primes =>
      (xiTransversePrimeApertureRatio a b p - 1) /
        primeShiftFactor (a : ℂ) p) cofinite (𝓝 (-1)) := by
  have hb : 0 < b := ha.trans hab
  have habre : ((a : ℂ).re) < ((b : ℂ).re) := by
    simpa only [Complex.natCast_re] using (show (a : ℝ) < b by exact_mod_cast hab)
  have hratio : Tendsto (fun p : Nat.Primes =>
      primeShiftFactor (b : ℂ) p / primeShiftFactor (a : ℂ) p) cofinite (𝓝 0) := by
    simpa using
      (tendsto_primeShiftLog_ratio_of_re_lt
        (α := (b : ℂ)) (β := (a : ℂ)) habre 0 0)
  have hb0 := tendsto_primeShiftFactor_nat_cofinite_zero b hb
  have heq : (fun p : Nat.Primes =>
      (xiTransversePrimeApertureRatio a b p - 1) /
        primeShiftFactor (a : ℂ) p) =
      fun p => (primeShiftFactor (b : ℂ) p /
          primeShiftFactor (a : ℂ) p - 1) /
        (1 - primeShiftFactor (b : ℂ) p) := by
    funext p
    have hfa := primeShiftFactor_ne_zero (a : ℂ) p
    have hfb := one_sub_primeShiftFactor_nat_ne_zero b hb p
    simp only [xiTransversePrimeApertureRatio]
    field_simp
    ring
  rw [heq]
  have hnum : Tendsto (fun p : Nat.Primes =>
      primeShiftFactor (b : ℂ) p / primeShiftFactor (a : ℂ) p - (1 : ℂ))
      cofinite (𝓝 ((0 : ℂ) - 1)) := hratio.sub tendsto_const_nhds
  have hden : Tendsto (fun p : Nat.Primes =>
      (1 : ℂ) - primeShiftFactor (b : ℂ) p) cofinite (𝓝 ((1 : ℂ) - 0)) :=
    tendsto_const_nhds.sub hb0
  simpa using! hnum.div hden (by norm_num : (1 : ℂ) - 0 ≠ 0)

/-- If `b<a`, the first projective defect occurs at the smaller shift grade `b` and has
orientation `+1`. -/
theorem tendsto_xiTransversePrimeApertureRatio_firstDefect_of_gt
    {a b : ℕ} (hb : 0 < b) (hba : b < a) :
    Tendsto (fun p : Nat.Primes =>
      (xiTransversePrimeApertureRatio a b p - 1) /
        primeShiftFactor (b : ℂ) p) cofinite (𝓝 1) := by
  have ha : 0 < a := hb.trans hba
  have hbare : ((b : ℂ).re) < ((a : ℂ).re) := by
    simpa only [Complex.natCast_re] using (show (b : ℝ) < a by exact_mod_cast hba)
  have hratio : Tendsto (fun p : Nat.Primes =>
      primeShiftFactor (a : ℂ) p / primeShiftFactor (b : ℂ) p) cofinite (𝓝 0) := by
    simpa using
      (tendsto_primeShiftLog_ratio_of_re_lt
        (α := (a : ℂ)) (β := (b : ℂ)) hbare 0 0)
  have hb0 := tendsto_primeShiftFactor_nat_cofinite_zero b hb
  have heq : (fun p : Nat.Primes =>
      (xiTransversePrimeApertureRatio a b p - 1) /
        primeShiftFactor (b : ℂ) p) =
      fun p => (1 - primeShiftFactor (a : ℂ) p /
          primeShiftFactor (b : ℂ) p) /
        (1 - primeShiftFactor (b : ℂ) p) := by
    funext p
    have hfb0 := primeShiftFactor_ne_zero (b : ℂ) p
    have hfb := one_sub_primeShiftFactor_nat_ne_zero b hb p
    simp only [xiTransversePrimeApertureRatio]
    field_simp
    ring
  rw [heq]
  have hnum : Tendsto (fun p : Nat.Primes =>
      (1 : ℂ) - primeShiftFactor (a : ℂ) p / primeShiftFactor (b : ℂ) p)
      cofinite (𝓝 ((1 : ℂ) - 0)) := tendsto_const_nhds.sub hratio
  have hden : Tendsto (fun p : Nat.Primes =>
      (1 : ℂ) - primeShiftFactor (b : ℂ) p) cofinite (𝓝 ((1 : ℂ) - 0)) :=
    tendsto_const_nhds.sub hb0
  simpa using! hnum.div hden (by norm_num : (1 : ℂ) - 0 ≠ 0)

/-- Unified first-defect law: the normalization grade is exactly `min a b`, and the limiting
orientation records which aperture is smaller. -/
theorem tendsto_xiTransversePrimeApertureRatio_firstDefect
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    Tendsto (fun p : Nat.Primes =>
      (xiTransversePrimeApertureRatio a b p - 1) /
        primeShiftFactor ((min a b : ℕ) : ℂ) p) cofinite
      (𝓝 (if a < b then (-1 : ℂ) else 1)) := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · simpa [hab, min_eq_left hab.le] using
      tendsto_xiTransversePrimeApertureRatio_firstDefect_of_lt ha hab
  · have hnlt : ¬ a < b := Nat.not_lt.mpr hba.le
    simpa [hnlt, min_eq_right hba.le] using
      tendsto_xiTransversePrimeApertureRatio_firstDefect_of_gt hb hba

/-- The contact grade `min` obeys the non-Archimedean triangle inequality. -/
theorem xiTransverseApertureProjectiveGrade_ultrametric
    (a b c : ℕ) :
    min (min a b) (min b c) ≤ min a c := by
  omega

/-! ## Brownian--Laplace realization of the aperture grade -/

/-- The canonical Brownian metric carried by two positive integral apertures. -/
def xiTransverseApertureBrownianMetric (a b : ℕ) : ℝ :=
  (min a b : ℕ)

/-- The projective contact grade is exactly the Brownian aperture metric. -/
theorem xiTransverseApertureBrownianMetric_eq_grade (a b : ℕ) :
    xiTransverseApertureBrownianMetric a b = min a b :=
  rfl

/-- Every ordered two-point Brownian aperture Gram has strictly positive determinant. -/
theorem xiTransverseApertureBrownianMetric_twoPoint_det_pos
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    0 < xiTransverseApertureBrownianMetric a a *
        xiTransverseApertureBrownianMetric b b -
      xiTransverseApertureBrownianMetric a b ^ 2 := by
  simp only [xiTransverseApertureBrownianMetric, min_self, min_eq_left hab.le]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  nlinarith

/-- Exact scalar Laplace primitive behind every normalized transverse source coefficient. -/
theorem intervalIntegral_cexp_neg_rate
    {rate : ℝ} (hrate : 0 < rate) (a : ℝ) :
    (∫ t : ℝ in 0..a, Complex.exp (-(rate : ℂ) * t)) =
      (1 - Complex.exp (-(rate : ℂ) * a)) / (rate : ℂ) := by
  have hrate0 : -(rate : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hrate.ne')
  calc
    _ = (Complex.exp (-(rate : ℂ) * a) -
          Complex.exp (-(rate : ℂ) * 0)) / (-(rate : ℂ)) :=
      integral_exp_mul_complex hrate0
    _ = (1 - Complex.exp (-(rate : ℂ) * a)) / (rate : ℂ) := by
      rw [mul_zero, Complex.exp_zero]
      field_simp [hrate.ne']
      ring

/-- The Brownian interval vector sampled by the valuation-`e` prime Laplace clock. -/
def xiTransversePrimePowerBrownianLaplaceSample
    (a e : ℕ) (p : Nat.Primes) : ℂ :=
  ∫ t : ℝ in 0..(a : ℝ),
    Complex.exp (-((((e + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ) * t)

/-- A normalized valuation-layer defect is exactly the Laplace transform of the interval aperture
vector. -/
theorem xiTransversePrimePowerBrownianLaplaceSample_eq
    (a e : ℕ) (p : Nat.Primes) :
    xiTransversePrimePowerBrownianLaplaceSample a e p =
      (1 - primeShiftFactor ((((e + 1) * a : ℕ) : ℂ)) p) /
        ((((e + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hrate : 0 < ((e + 1 : ℕ) : ℝ) * Real.log (p : ℕ) :=
    mul_pos (by positivity) (Real.log_pos hp)
  rw [xiTransversePrimePowerBrownianLaplaceSample,
    intervalIntegral_cexp_neg_rate hrate]
  congr 2
  have hrateCast :
      (((((e + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ)) =
        ((e + 1 : ℕ) : ℂ) * (Real.log (p : ℕ) : ℂ) := by
    push_cast
    rfl
  have hshiftCast :
      ((((e + 1) * a : ℕ) : ℂ)) = ((e + 1 : ℕ) : ℂ) * (a : ℂ) := by
    push_cast
    rfl
  rw [primeShiftFactor, primeLogClock, hrateCast, hshiftCast]
  congr 1
  norm_num
  ring

/-- **Brownian--Laplace factorization of the actual Xi transverse source.**  After dividing the
valuation-`e` prime-power coefficient by its forced clock factor
`(e+1) * log(p)^2`, the source is exactly the Laplace sample of `1_[0,a]`. -/
theorem xiTransverseShiftArithmetic_primePow_normalized_eq_brownianLaplace
    (a e : ℕ) (p : Nat.Primes) :
    xiTransverseShiftArithmetic a ((p : ℕ) ^ (e + 1)) /
        (((e + 1 : ℕ) : ℂ) * (Real.log (p : ℕ) : ℂ) ^ 2) =
      xiTransversePrimePowerBrownianLaplaceSample a e p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : (Real.log (p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp).ne'
  have he : ((e + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e)
  have hrateCast :
      (((((e + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ)) =
        ((e + 1 : ℕ) : ℂ) * (Real.log (p : ℕ) : ℂ) := by
    push_cast
    rfl
  have hscaled : (e + 1) * a = e * a + a := by
    simp [Nat.add_mul]
  have hfactor :
      primeShiftFactor (((e + 1 : ℕ) : ℂ) * (a : ℂ)) p =
        primeShiftFactor (((e * a + a : ℕ) : ℂ)) p := by
    congr 2
    push_cast
    ring
  rw [xiTransverseShiftArithmetic_apply,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero e),
    ArithmeticFunction.vonMangoldt_apply_prime p.2,
    xiTransverse_cpowWeight_primePow,
    xiTransversePrimePowerBrownianLaplaceSample_eq]
  rw [hrateCast, hscaled]
  rw [hfactor]
  field_simp

/-- On valuation layer `e`, projective contact occurs at the accelerated grade
`(e+1) * min a b`, with the same orientation. -/
theorem tendsto_xiTransversePrimeApertureRatio_valuationLayer_firstDefect
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) (e : ℕ) :
    Tendsto (fun p : Nat.Primes =>
      (xiTransversePrimeApertureRatio ((e + 1) * a) ((e + 1) * b) p - 1) /
        primeShiftFactor (((e + 1) * min a b : ℕ) : ℂ) p) cofinite
      (𝓝 (if a < b then (-1 : ℂ) else 1)) := by
  have hscale : 0 < e + 1 := Nat.succ_pos e
  have hposa : 0 < (e + 1) * a := Nat.mul_pos hscale ha
  have hposb : 0 < (e + 1) * b := Nat.mul_pos hscale hb
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hscaled : (e + 1) * a < (e + 1) * b :=
      (Nat.mul_lt_mul_left hscale).2 hab
    simpa [hab, hscaled, min_eq_left hab.le] using
      tendsto_xiTransversePrimeApertureRatio_firstDefect_of_lt hposa hscaled
  · have hscaled : (e + 1) * b < (e + 1) * a :=
      (Nat.mul_lt_mul_left hscale).2 hba
    have hnlt : ¬ a < b := Nat.not_lt.mpr hba.le
    simpa [hnlt, min_eq_right hba.le] using
      tendsto_xiTransversePrimeApertureRatio_firstDefect_of_gt hposb hscaled

end

end RHTower
