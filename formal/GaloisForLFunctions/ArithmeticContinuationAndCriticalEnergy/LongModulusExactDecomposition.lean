import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.LongModulusQuadratureSampling
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsHilbertSchmidtAboveDampingOne

/-!
# The centered divisor prefix is a short sawtooth plus actual quadrature

The harmonic tail is retained with its sign. No absolute majorant replaces the
long-modulus remainder, and the prefix identity holds for every natural cutoff.
-/

noncomputable section
open MeasureTheory RHTower ArithmeticFunction
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
set_option autoImplicit false

/-- The finite short-modulus sawtooth, with the exact signed Möbius weight. -/
def pmShortModulusSawtooth (ε : ℝ) (n D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, pmLongModulusWeight ε d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)

/-- The long-modulus sawtooth alone, before including the full mean tail. -/
def pmLongModulusSawtooth (ε : ℝ) (n D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)

private theorem summable_reciprocalWeight {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => pmLongModulusWeight ε d / d) := by
  refine Summable.of_norm_bounded
    (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)) fun d => ?_
  rw [pmLongModulusWeight_div_eq, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) hμ

private theorem density_eq_head_add_tail {ε : ℝ} (hε : 0 < ε) (D : ℕ) :
    (pmPowerDampedDivisorDensity ε).re =
      (∑ d ∈ Finset.Icc 1 D, pmLongModulusWeight ε d / d) +
        ∑' d : ℕ, if D < d then pmLongModulusWeight ε d / d else 0 := by
  classical
  let f : ℕ → ℝ := fun d => pmLongModulusWeight ε d / d
  have hs : Summable f := summable_reciprocalWeight hε
  have hhead : Summable (fun d => if d ≤ D then f d else 0) := by
    refine Summable.of_norm_bounded hs.norm fun d => ?_
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (f d)
  have htail : Summable (fun d => if D < d then f d else 0) := by
    refine Summable.of_norm_bounded hs.norm fun d => ?_
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (f d)
  have hfinite : (∑' d, if d ≤ D then f d else 0) = ∑ d ∈ Finset.Icc 1 D, f d := by
    rw [tsum_eq_sum (s := Finset.Icc 1 D) (fun d hd => by
      by_cases hd0 : d = 0
      · subst d
        simp only [f, Nat.cast_zero, div_zero, ite_self]
      · have hnD : ¬d ≤ D := fun h => hd (Finset.mem_Icc.mpr ⟨by omega, h⟩)
        exact if_neg hnD)]
    exact Finset.sum_congr rfl fun d hd => if_pos (Finset.mem_Icc.mp hd).2
  have hdensity : (pmPowerDampedDivisorDensity ε).re = ∑' d, f d := by
    rw [SignedArithmeticEnergyIncidence.density_re_eq_tsum hε]
    apply tsum_congr
    intro d
    exact (pmLongModulusWeight_div_eq ε d).symm
  rw [hdensity, ← hfinite, ← Summable.tsum_add hhead htail]
  apply tsum_congr
  intro d
  by_cases h : d ≤ D
  · simp only [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · simp only [if_neg h, if_pos (lt_of_not_ge h), zero_add]

private theorem floor_sum_split_all_cutoffs (ε : ℝ) (n D : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ)) =
      (∑ d ∈ Finset.Icc 1 D, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ)) +
        ∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ) := by
  by_cases hDn : D ≤ n
  · have hI (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hI n, hI D, Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDn]
  · have hnD := (lt_of_not_ge hDn).le
    rw [Finset.Ioc_eq_empty_of_le hnD, Finset.sum_empty, add_zero]
    apply Finset.sum_subset
    · intro d hd
      obtain ⟨hd1, hdn⟩ := Finset.mem_Icc.mp hd
      exact Finset.mem_Icc.mpr ⟨hd1, hdn.trans hnD⟩
    · intro d hd hdn
      have hnd : n < d := by
        have hd1 := (Finset.mem_Icc.mp hd).1
        by_contra h
        exact hdn (Finset.mem_Icc.mpr ⟨hd1, le_of_not_gt h⟩)
      rw [Nat.div_eq_of_lt hnd, Nat.cast_zero, mul_zero]

/-- The actual centered prefix is the short sawtooth plus one integrable quadrature error. -/
theorem pmPowerDampedCenteredDivisorPrefix_eq_short_add_quadrature
    {ε : ℝ} (hε : 0 < ε) (n D : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      pmShortModulusSawtooth ε n D + pmLongModulusQuadrature ε n D := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq_floor_sum]
  change (∑ d ∈ Finset.Icc 1 n, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ)) -
    (pmPowerDampedDivisorDensity ε).re * n = _
  rw [floor_sum_split_all_cutoffs ε n D, density_eq_head_add_tail hε D,
    pmLongModulusQuadrature_eq hε, pmShortModulusSawtooth]
  have hh : (∑ d ∈ Finset.Icc 1 D, pmLongModulusWeight ε d *
      (((n / d : ℕ) : ℝ) - (n : ℝ) / d)) =
      (∑ d ∈ Finset.Icc 1 D, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ)) -
        (n : ℝ) * ∑ d ∈ Finset.Icc 1 D, pmLongModulusWeight ε d / d := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hh]
  ring

/-- For an interior cutoff, quadrature combines the long sawtooth and the entire mean tail past `n`. -/
theorem pmLongModulusQuadrature_eq_longSawtooth_sub_full_tail
    {ε : ℝ} (hε : 0 < ε) (n D : ℕ) (hDn : D ≤ n) :
    pmLongModulusQuadrature ε n D = pmLongModulusSawtooth ε n D -
      (n : ℝ) * ∑' d : ℕ, if n < d then pmLongModulusWeight ε d / d else 0 := by
  have hD := density_eq_head_add_tail hε D
  have hn := density_eq_head_add_tail hε n
  have hsplit : (∑ d ∈ Finset.Icc 1 n, pmLongModulusWeight ε d / d) =
      (∑ d ∈ Finset.Icc 1 D, pmLongModulusWeight ε d / d) +
        ∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d / d := by
    have hI (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hI n, hI D, Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDn]
  rw [hsplit] at hn
  have ht : (∑' d : ℕ, if D < d then pmLongModulusWeight ε d / d else 0) =
      (∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d / d) +
        ∑' d : ℕ, if n < d then pmLongModulusWeight ε d / d else 0 := by
    linarith only [hD, hn]
  rw [pmLongModulusQuadrature_eq hε, ht, pmLongModulusSawtooth]
  have hh : (∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d *
      (((n / d : ℕ) : ℝ) - (n : ℝ) / d)) =
      (∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d * ((n / d : ℕ) : ℝ)) -
        (n : ℝ) * ∑ d ∈ Finset.Ioc D n, pmLongModulusWeight ε d / d := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hh]
  ring

/-- Every natural cutoff keeps the entire mean tail beyond both cutoff and numerator. -/
theorem pmLongModulusQuadrature_eq_longSawtooth_sub_tail_max
    {ε : ℝ} (hε : 0 < ε) (n D : ℕ) :
    pmLongModulusQuadrature ε n D = pmLongModulusSawtooth ε n D -
      (n : ℝ) * ∑' d : ℕ, if max n D < d then pmLongModulusWeight ε d / d else 0 := by
  by_cases hDn : D ≤ n
  · rw [max_eq_left hDn]
    exact pmLongModulusQuadrature_eq_longSawtooth_sub_full_tail hε n D hDn
  · have hnD : n ≤ D := (lt_of_not_ge hDn).le
    simp only [max_eq_right hnD, pmLongModulusQuadrature_eq hε, pmLongModulusSawtooth,
      Finset.Ioc_eq_empty_of_le hnD, Finset.sum_empty]


end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
