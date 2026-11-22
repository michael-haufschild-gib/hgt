import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeIntervals
import Mathlib.NumberTheory.AbelSummation

/-! Abel summation on finite prime intervals. -/

open Finset MeasureTheory

namespace QH.PrimeProgressions

theorem abel_primesIoc_weight (a : ℕ → ℂ) (J J' : ℝ → ℝ) (x y r : ℝ)
    (hx : 1 ≤ x) (hxy : x ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y))
    (hb : ∀ t ∈ Set.Icc x y, |J' t| ≤ r / t) :
    ‖∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ)‖
      ≤ r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  let c (n : ℕ) : ℂ := if x < (n : ℝ) ∧ n.Prime then a n else 0
  let S (t : ℝ) : ℂ := ∑ p ∈ primesIoc x t, a p
  have hprefix (t : ℝ) : ∑ n ∈ Icc 0 ⌊t⌋₊, c n = S t := by
    have he : (Icc 0 ⌊t⌋₊).filter (fun n : ℕ => x < (n : ℝ) ∧ n.Prime) = primesIoc x t := by
      ext n
      simp only [primesIoc, mem_filter, mem_Ioc, mem_Icc, Nat.zero_le, true_and, Nat.floor_lt hx0]
      tauto
    simp only [c, ← sum_filter, he, S]
  let f (t : ℝ) : ℂ := J t
  have hf (t : ℝ) (ht : t ∈ Set.Icc x y) : HasDerivAt f (J' t : ℂ) t :=
    (hJ t ht).ofReal_comp
  have hcont : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  have hderiv : IntegrableOn (deriv f) (Set.Icc x y) :=
    (hcont.congr fun t ht => (hf t ht).deriv).integrableOn_Icc
  have hsum : ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, f n * c n =
      ∑ p ∈ primesIoc x y, a p * (J p : ℂ) := by
    rw [primesIoc, sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hxn : x < (n : ℝ) := (Nat.floor_lt hx0).1 (mem_Ioc.mp hn).1
    by_cases hp : n.Prime <;> simp [c, f, hxn, hp, mul_comm]
  have hzero : S x = 0 := by simp [S, primesIoc]
  have hab := sum_mul_eq_sub_sub_integral_mul (f := f) c hx0 hxy
    (fun t ht => (hf t ht).differentiableAt) hderiv
  rw [hsum] at hab
  simp_rw [hprefix, hzero, mul_zero, sub_zero] at hab
  have hint :
      (∫ t in Set.Ioc x y, deriv f t * S t) = ∫ t in x..y, (J' t : ℂ) * S t := by
    rw [intervalIntegral.integral_of_le hxy]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht =>
      congrArg (· * S t) (hf t (Set.Ioc_subset_Icc_self ht)).deriv
  rw [hint] at hab
  have hdiff : ∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ) =
      -∫ t in x..y, (J' t : ℂ) * S t := by
    simp only [Complex.ofReal_sub, mul_sub, sum_sub_distrib, ← sum_mul]
    rw [hab, ← show S y = ∑ p ∈ primesIoc x y, a p from rfl, show f y = (J y : ℂ) from rfl]
    ring
  have hprod {g : ℝ → ℂ} (hg : IntegrableOn g (Set.Icc x y)) :
      IntegrableOn (fun t => g t * S t) (Set.Icc x y) := by
    simpa only [hprefix] using integrableOn_mul_sum_Icc (m := 0) c hx0 hg
  have hF : IntervalIntegrable (fun t => ‖(J' t : ℂ) * S t‖) volume x y :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
      (hprod hcont.integrableOn_Icc)).norm
  have htpos (t : ℝ) (ht : t ∈ Set.Icc x y) : 0 < t :=
    zero_lt_one.trans_le (hx.trans ht.1)
  have hinv : ContinuousOn (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.inv₀ fun t ht => (htpos t ht).ne')
  have hG : IntervalIntegrable (fun t => ‖S t‖ / t) volume x y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
    refine IntegrableOn.congr_fun (hprod hinv.integrableOn_Icc).norm ?_ measurableSet_Icc
    intro t ht
    change ‖((t⁻¹ : ℝ) : ℂ) * S t‖ = ‖S t‖ / t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (htpos t ht).le),
      div_eq_mul_inv, mul_comm]
  change _ ≤ r * ∫ t in x..y, ‖S t‖ / t
  rw [hdiff, norm_neg, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm hxy).trans
    (intervalIntegral.integral_mono_on hxy hF (hG.const_mul r) fun t ht => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |J' t| * ‖S t‖ ≤ r / t * ‖S t‖ :=
    mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
    _ = r * (‖S t‖ / t) := by ring

end QH.PrimeProgressions
