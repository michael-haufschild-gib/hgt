import GaloisForLFunctions.RHTower.LogSineConductanceMoments
import GaloisForLFunctions.HTGeometry.CavityResponseConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!+# Kesten–McKay averaging as Poisson averaging

The phase density in Hartnoll–Yang, arXiv:2502.02661v2, (97), pulled back by
`θ = πt`, is an affine combination of the constant density and the Poisson
kernel of radius `1/p`. This evaluates every even cosine moment exactly.
The identities concern the explicit measure; no automorphic equidistribution
or Ramanujan conjecture is assumed.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Kesten–McKay phase density on the unit interval, including its Jacobian. -/
def kestenMcKayDensity (p : Nat.Primes) (t : ℝ) : ℝ :=
  2 * (p : ℝ) * ((p : ℝ) + 1) * Real.sin (Real.pi * t) ^ 2 /
    (1 + (p : ℝ) ^ 2 - 2 * (p : ℝ) * Real.cos (2 * Real.pi * t))

private theorem prime_real_one_lt (p : Nat.Primes) : 1 < (p : ℝ) := by
  exact_mod_cast p.property.one_lt

private theorem prime_radius_nonneg (p : Nat.Primes) : 0 ≤ (p : ℝ)⁻¹ := by
  exact inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one (prime_real_one_lt p)))

private theorem prime_radius_lt_one (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 := by
  exact (inv_lt_one₀ (lt_trans zero_lt_one (prime_real_one_lt p))).mpr
    (prime_real_one_lt p)

/-- The density is a constant minus a positive multiple of a Poisson kernel. -/
theorem kestenMcKayDensity_eq_poisson (p : Nat.Primes) (t : ℝ) :
    kestenMcKayDensity p t = ((p : ℝ) + 1) / 2 -
      ((p : ℝ) - 1) / 2 * poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t) := by
  have hp := prime_real_one_lt p
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hd := poissonKer_denom_pos
    (show |(p : ℝ)⁻¹| < 1 by
      rw [abs_of_nonneg (prime_radius_nonneg p)]; exact prime_radius_lt_one p)
    (2 * Real.pi * t)
  have hc : Real.cos (2 * Real.pi * t) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
  have hD : 1 + (p : ℝ) ^ 2 - 2 * (p : ℝ) * Real.cos (2 * Real.pi * t) ≠ 0 := by
    have hpos : 0 < (p : ℝ) ^ 2 *
        (1 - 2 * (p : ℝ)⁻¹ * Real.cos (2 * Real.pi * t) + ((p : ℝ)⁻¹) ^ 2) :=
      mul_pos (sq_pos_of_ne_zero hp0) hd
    field_simp at hpos
    nlinarith
  have hden : 1 - 2 * (p : ℝ)⁻¹ * Real.cos (2 * Real.pi * t) + ((p : ℝ)⁻¹) ^ 2 =
      (1 + (p : ℝ) ^ 2 - 2 * (p : ℝ) * Real.cos (2 * Real.pi * t)) / (p : ℝ) ^ 2 := by
    field_simp [hp0]
    ring
  have hP : poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t) =
      ((p : ℝ) ^ 2 - 1) /
        (1 + (p : ℝ) ^ 2 - 2 * (p : ℝ) * Real.cos (2 * Real.pi * t)) := by
    rw [poissonKer, hden]
    field_simp [hp0, hD]
  rw [hP, kestenMcKayDensity]
  field_simp [hD]
  rw [hc]
  ring

/-- The density is nonnegative at every phase. -/
theorem kestenMcKayDensity_nonneg (p : Nat.Primes) (t : ℝ) :
    0 ≤ kestenMcKayDensity p t := by
  have hp := prime_real_one_lt p
  have hcos := Real.cos_le_one (2 * Real.pi * t)
  have hden : 0 < 1 + (p : ℝ) ^ 2 - 2 * (p : ℝ) * Real.cos (2 * Real.pi * t) := by
    nlinarith [sq_pos_of_pos (show 0 < (p : ℝ) - 1 by linarith),
      mul_nonneg (show 0 ≤ (p : ℝ) by linarith) (sub_nonneg.mpr hcos)]
  unfold kestenMcKayDensity
  exact div_nonneg (by positivity) hden.le

/-- The phase density is continuous, since its Poisson radius lies inside the disk. -/
theorem continuous_kestenMcKayDensity (p : Nat.Primes) :
    Continuous (kestenMcKayDensity p) := by
  have hP : Continuous (fun t : ℝ => poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t)) :=
    (poissonKer_continuous (by
      rw [abs_of_nonneg (prime_radius_nonneg p)]; exact prime_radius_lt_one p)).comp
        (by fun_prop)
  simp_rw [show kestenMcKayDensity p = fun t => ((p : ℝ) + 1) / 2 -
    ((p : ℝ) - 1) / 2 * poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t) from
      funext (kestenMcKayDensity_eq_poisson p)]
  exact continuous_const.sub (continuous_const.mul hP)

/-- Phase reflection preserves the explicit density. -/
theorem kestenMcKayDensity_reflection (p : Nat.Primes) (t : ℝ) :
    kestenMcKayDensity p (1 - t) = kestenMcKayDensity p t := by
  have hs : Real.sin (Real.pi * (1 - t)) = Real.sin (Real.pi * t) := by
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring,
      Real.sin_sub, Real.sin_pi, Real.cos_pi]
    ring
  have hc : Real.cos (2 * Real.pi * (1 - t)) = Real.cos (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (1 - t) = 2 * Real.pi - 2 * Real.pi * t by ring,
      Real.cos_sub, Real.cos_two_mul, Real.sin_two_mul, Real.cos_pi, Real.sin_pi]
    ring
  simp only [kestenMcKayDensity, hs, hc]

/-- Every odd phase frequency averages to zero by reflection about the midpoint. -/
theorem integral_kestenMcKayDensity_cos_odd (p : Nat.Primes) (n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      Real.cos (Real.pi * (2 * (n : ℝ) + 1) * t)) = 0 := by
  let f := fun t => kestenMcKayDensity p t *
    Real.cos (Real.pi * (2 * (n : ℝ) + 1) * t)
  have hf : ∀ t, f (1 - t) = -f t := by
    intro t
    have hc : Real.cos (Real.pi * (2 * (n : ℝ) + 1) * (1 - t)) =
        -Real.cos (Real.pi * (2 * (n : ℝ) + 1) * t) := by
      rw [show Real.pi * (2 * (n : ℝ) + 1) * (1 - t) =
          ((2 * n + 1 : ℕ) : ℝ) * Real.pi - Real.pi * (2 * (n : ℝ) + 1) * t by
            push_cast; ring,
        Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      simp [pow_add, pow_mul]
    dsimp [f]
    rw [kestenMcKayDensity_reflection, hc]
    ring
  have hr := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1) f 1
  simp only [sub_self, sub_zero] at hr
  simp_rw [hf] at hr
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] at hr
  change (∫ t in Ioo (0 : ℝ) 1, f t) = 0
  linarith

/-- All even phase moments, with normalization included as the zeroth moment. -/
theorem integral_kestenMcKayDensity_cos (p : Nat.Primes) (n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1,
      kestenMcKayDensity p t * Real.cos (2 * Real.pi * n * t)) =
    ((p : ℝ) + 1) / 2 * (if n = 0 then 1 else 0) -
      ((p : ℝ) - 1) / 2 * ((p : ℝ)⁻¹) ^ n := by
  have hc : Continuous (fun t : ℝ => Real.cos (2 * Real.pi * n * t)) := by fun_prop
  have hP : Continuous (fun t : ℝ => poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t)) :=
    (poissonKer_continuous (by
      rw [abs_of_nonneg (prime_radius_nonneg p)]; exact prime_radius_lt_one p)).comp
        (by fun_prop)
  have hi : IntegrableOn (fun t : ℝ => Real.cos (2 * Real.pi * n * t)) (Ioo 0 1) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hPi : IntegrableOn (fun t : ℝ => poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t) *
      Real.cos (2 * Real.pi * n * t)) (Ioo 0 1) :=
    (hP.mul hc).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hcos : (∫ t in Ioo (0 : ℝ) 1, Real.cos (2 * Real.pi * n * t)) =
      if n = 0 then 1 else 0 := by
    simpa [poissonKer, zero_pow_eq] using
      RHTower.integral_unit_poissonKer_cos (r := 0) le_rfl zero_lt_one n
  have he : (fun t => kestenMcKayDensity p t * Real.cos (2 * Real.pi * n * t)) =
      fun t => ((p : ℝ) + 1) / 2 * Real.cos (2 * Real.pi * n * t) -
        ((p : ℝ) - 1) / 2 *
          (poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t) * Real.cos (2 * Real.pi * n * t)) := by
    funext t
    rw [kestenMcKayDensity_eq_poisson]
    ring
  rw [he]
  rw [integral_sub (hi.const_mul _) (hPi.const_mul _), integral_const_mul,
    integral_const_mul, hcos,
    RHTower.integral_unit_poissonKer_cos (prime_radius_nonneg p) (prime_radius_lt_one p)]

/-- The explicit Kesten–McKay phase density has total mass one. -/
theorem integral_kestenMcKayDensity (p : Nat.Primes) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t) = 1 := by
  have h := integral_kestenMcKayDensity_cos p 0
  simp at h
  linarith

/-- Every positive even phase frequency has a strictly negative moment. -/
theorem integral_kestenMcKayDensity_cos_succ (p : Nat.Primes) (n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1,
      kestenMcKayDensity p t * Real.cos (2 * Real.pi * (n + 1) * t)) =
      -((p : ℝ) - 1) / (2 * (p : ℝ) ^ (n + 1)) := by
  have h := integral_kestenMcKayDensity_cos p (n + 1)
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_one_ne_zero, if_false,
    mul_zero, zero_sub, inv_pow] at h
  rw [h]
  ring

/-- Exact averaging of a finite even Fourier observable. -/
theorem integral_kestenMcKayDensity_fourier (p : Nat.Primes) (N : ℕ) (a : ℕ → ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      ∑ n ∈ Finset.range N, a n * Real.cos (2 * Real.pi * (n + 1) * t)) =
    -((p : ℝ) - 1) / 2 * ∑ n ∈ Finset.range N, a n / (p : ℝ) ^ (n + 1) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    have he : (fun t => kestenMcKayDensity p t *
        (a n * Real.cos (2 * Real.pi * (n + 1) * t))) =
        fun t => a n * (kestenMcKayDensity p t * Real.cos (2 * Real.pi * (n + 1) * t)) := by
      funext t
      ring
    rw [he, integral_const_mul, integral_kestenMcKayDensity_cos_succ]
    ring
  · intro n _
    exact ((continuous_kestenMcKayDensity p).mul
      (continuous_const.mul (by fun_prop))).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self

/-- Every finite even logarithmic Euler truncation has nonpositive mean.
This is the bosonic-to-fermionic sign change before taking any limit. -/
theorem averaged_even_log_truncation_nonpos (p : Nat.Primes) (N : ℕ) (r : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      ∑ n ∈ Finset.range N, (r ^ (2 * (n + 1)) / ((n : ℝ) + 1)) *
        Real.cos (2 * Real.pi * (n + 1) * t)) ≤ 0 := by
  rw [integral_kestenMcKayDensity_fourier]
  apply mul_nonpos_of_nonpos_of_nonneg
  · have hp := prime_real_one_lt p
    linarith
  · apply Finset.sum_nonneg
    intro n _
    have hp := prime_real_one_lt p
    rw [pow_mul]
    positivity

/-- The integrated even logarithmic coefficients sum to the local fermionic
logarithm at every cavity disk coordinate. -/
theorem hasSum_averaged_even_log (p : Nat.Primes) (s : ℝ) :
    HasSum (fun n : ℕ =>
      (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
        Real.cos (2 * Real.pi * (n + 1) * t)) *
          cavityDiskCoordinate s ^ (2 * (n + 1)) / ((n : ℝ) + 1))
      (((p : ℝ) - 1) / 2 *
        Real.log (1 - cavityDiskCoordinate s ^ 2 / (p : ℝ))) := by
  let r := cavityDiskCoordinate s
  have hp := prime_real_one_lt p
  have hr := abs_cavityDiskCoordinate_lt_one s
  have hr2 : r ^ 2 < 1 := by
    have hsq := pow_lt_one₀ (abs_nonneg r) hr (by omega : (2 : ℕ) ≠ 0)
    simpa only [sq_abs] using hsq
  have hx : |r ^ 2 / (p : ℝ)| < 1 := by
    rw [abs_of_nonneg (div_nonneg (sq_nonneg r) (by linarith)),
      div_lt_one (by linarith : 0 < (p : ℝ))]
    linarith
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hx).mul_left (-((p : ℝ) - 1) / 2)
  have he : (fun n : ℕ =>
      (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
        Real.cos (2 * Real.pi * (n + 1) * t)) *
          cavityDiskCoordinate s ^ (2 * (n + 1)) / ((n : ℝ) + 1)) =
      fun n : ℕ => -((p : ℝ) - 1) / 2 *
        ((r ^ 2 / (p : ℝ)) ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext n
    rw [integral_kestenMcKayDensity_cos_succ, div_pow, pow_mul]
    dsimp [r]
    ring
  rw [he]
  simpa only [neg_div, neg_mul_neg] using h

end
end GaloisForLFunctions.SelbergClass.Primon
