import GaloisForLFunctions.RHTower.PMLogMobiusMellinPair
import GaloisForLFunctions.RHTower.PMDilationMellin
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation

/-!
# The prime logarithmic mean and the exact Möbius mean defect

The literal von Mangoldt logarithmic mean has Mellin transform
`-zeta'(s+1) / ((s+1)^2 * zeta(s+1))` on `Re s > 0`. Finite Abel summation
identifies it with the mean of `psi(x)/x` from one to the cutoff.
Subtracting it from the logarithmic Möbius coefficient gives the exact
reciprocal-zeta/logarithmic-derivative defect and its cleared identity.
No continuation to the critical boundary or canonical variance estimate is
asserted here.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

def pmInverseLogarithmicRamp (t : ℝ) : ℂ := pmLogarithmicRamp t⁻¹

theorem hasMellin_pmInverseLogarithmicRamp {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmInverseLogarithmicRamp s (1 / s ^ 2) := by
  constructor
  · change MellinConvergent (fun t => pmLogarithmicRamp t⁻¹) s
    have h : MellinConvergent (fun t => pmLogarithmicRamp (t ^ (-1 : ℝ))) s :=
      (MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0)).mpr
        (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using
          (hasMellin_pmLogarithmicRamp hs).1)
    simpa only [Real.rpow_neg_one] using h
  · exact (mellin_comp_inv pmLogarithmicRamp s).trans (hasMellin_pmLogarithmicRamp hs).2

theorem pmInverseLogarithmicRamp_eq_zero {t : ℝ} (ht : 1 < t) :
    pmInverseLogarithmicRamp t = 0 := by
  have hi : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht.le
  simp [pmInverseLogarithmicRamp, pmLogarithmicRamp, not_lt.mpr hi]

def pmPrimeLogMean (x : ℝ) : ℝ :=
  x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ArithmeticFunction.vonMangoldt n * Real.log (x / (n : ℝ))

def pmPrimeLogReciprocalProfile (t : ℝ) : ℂ :=
  (t : ℂ) * pmWeightedDilationSource (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    pmInverseLogarithmicRamp t

theorem hasMellin_pmPrimeLogReciprocalProfile {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmPrimeLogReciprocalProfile s
      (-deriv riemannZeta (s + 1) / ((s + 1) ^ 2 * riemannZeta (s + 1))) := by
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hw := hasMellin_pmInverseLogarithmicRamp (lt_trans zero_lt_one hs1)
  have hm := pmWeightedDilationSource_hasMellin
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) pmInverseLogarithmicRamp
    (by simp) (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1) hw.1
  rw [hw.2, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1] at hm
  constructor
  · change MellinConvergent
      (fun t => (t : ℂ) * pmWeightedDilationSource
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) pmInverseLogarithmicRamp t) s
    have h := (MellinConvergent.cpow_smul (s := s) (a := (1 : ℂ))).mpr hm.1
    simpa only [Complex.cpow_one, smul_eq_mul] using h
  · have h := mellin_cpow_smul
      (pmWeightedDilationSource (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        pmInverseLogarithmicRamp) s (1 : ℂ)
    simp only [Complex.cpow_one, smul_eq_mul] at h
    change mellin (fun t => (t : ℂ) * pmWeightedDilationSource
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) pmInverseLogarithmicRamp t) s = _
    rw [h, hm.2]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring

theorem pmPrimeLogReciprocalProfile_eq {t : ℝ} (ht : 0 < t) :
    pmPrimeLogReciprocalProfile t = (pmPrimeLogMean t⁻¹ : ℂ) := by
  classical
  have hcut : 1 < ((⌊t⁻¹⌋₊ : ℝ) + 1) * t := by
    have hm := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one t⁻¹) ht
    simpa only [inv_mul_cancel₀ ht.ne'] using hm
  rw [pmPrimeLogReciprocalProfile,
    pmWeightedDilationSource_eq_sum _ pmInverseLogarithmicRamp ⌊t⁻¹⌋₊ ht
      (fun _ h => pmInverseLogarithmicRamp_eq_zero h) hcut,
    Finset.mul_sum, Finset.sum_range_succ']
  simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
  rw [RHTower.sum_range_succ_eq_sum_Icc
    (fun n : ℕ => (t : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
      pmInverseLogarithmicRamp ((n : ℝ) * t))) ⌊t⁻¹⌋₊]
  unfold pmPrimeLogMean
  push_cast
  rw [inv_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1)
  have hnf : (n : ℝ) ≤ t⁻¹ :=
    (Nat.le_floor_iff (inv_pos.mpr ht).le).mp (Finset.mem_Icc.mp hn).2
  have hnt1 : (n : ℝ) * t ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hnf ht.le
    simpa only [inv_mul_cancel₀ ht.ne'] using hm
  have hinv : 1 ≤ ((n : ℝ) * t)⁻¹ := (one_le_inv₀ (mul_pos hn0 ht)).2 hnt1
  rw [pmInverseLogarithmicRamp, pmLogarithmicRamp_of_one_le hinv]
  have heq : ((n : ℝ) * t)⁻¹ = t⁻¹ / (n : ℝ) := by field_simp
  rw [heq]

theorem hasMellin_pmPrimeLogMean_inv {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (pmPrimeLogMean t⁻¹ : ℂ)) s
      (-deriv riemannZeta (s + 1) / ((s + 1) ^ 2 * riemannZeta (s + 1))) := by
  have h := hasMellin_pmPrimeLogReciprocalProfile hs
  constructor
  · apply h.1.congr_fun _ measurableSet_Ioi
    intro t ht
    exact congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z)
      (pmPrimeLogReciprocalProfile_eq ht)
  · calc
      _ = mellin pmPrimeLogReciprocalProfile s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z)
          (pmPrimeLogReciprocalProfile_eq ht).symm
      _ = _ := h.2

theorem hasMellin_pmPrimeLogMean {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun x : ℝ => (pmPrimeLogMean x : ℂ)) (-s)
      (-deriv riemannZeta (s + 1) / ((s + 1) ^ 2 * riemannZeta (s + 1))) := by
  have h := hasMellin_pmPrimeLogMean_inv hs
  constructor
  · have hi := (MellinConvergent.comp_rpow (s := -s)
      (f := fun t : ℝ => (pmPrimeLogMean t⁻¹ : ℂ))
      (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg,
        div_one, neg_neg] using h.1)
    simpa only [Real.rpow_neg_one, inv_inv] using hi
  · exact (mellin_comp_inv (fun x : ℝ => (pmPrimeLogMean x : ℂ)) s).symm.trans h.2

theorem pmPrimeLogMean_eq_integral_Ioc {x : ℝ} (hx : 1 ≤ x) :
    pmPrimeLogMean x = x⁻¹ * ∫ y in Ioc (1 : ℝ) x, Chebyshev.psi y / y := by
  let f : ℝ → ℝ := fun y => Real.log x - Real.log y
  have hfd (y : ℝ) (hy : y ∈ Icc (1 : ℝ) x) :
      HasDerivAt f (-y⁻¹) y := by
    exact (Real.hasDerivAt_log (zero_lt_one.trans_le hy.1).ne').const_sub (Real.log x)
  have hd (y : ℝ) (hy : y ∈ Icc (1 : ℝ) x) : deriv f y = -y⁻¹ := (hfd y hy).deriv
  have hi : IntegrableOn (deriv f) (Icc (1 : ℝ) x) := by
    have hc : ContinuousOn (fun y : ℝ => -y⁻¹) (Icc 1 x) := by
      apply ContinuousOn.neg
      exact continuousOn_id.inv₀ (fun y hy => (zero_lt_one.trans_le hy.1).ne')
    exact hc.integrableOn_Icc.congr_fun (fun y hy => (hd y hy).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (f := f) (a := (1 : ℝ)) (b := x) zero_le_one hx
    (fun y hy => (hfd y hy).differentiableAt) hi
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  simp only [f, sub_self, zero_mul, Chebyshev.psi_one, mul_zero,
    Nat.floor_one, zero_sub] at h
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * Real.log (x / (n : ℝ))) =
      ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (Real.log x - Real.log (n : ℝ)) *
        ArithmeticFunction.vonMangoldt n := by
    have hfloor : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
    rw [← Finset.Ioc_insert_left hfloor,
      Finset.sum_insert (by simp)]
    simp only [Nat.cast_one, ArithmeticFunction.vonMangoldt_apply_one, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (Finset.mem_Ioc.mp hn).1))
    rw [Real.log_div (zero_lt_one.trans_le hx).ne' hn0, mul_comm]
  rw [pmPrimeLogMean, hsum, h, ← integral_neg]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  change -(deriv f y * Chebyshev.psi y) = Chebyshev.psi y / y
  rw [hd y ⟨hy.1.le, hy.2⟩]
  simp only [div_eq_mul_inv]
  ring

def pmLogMobiusMeanDefect (x : ℝ) : ℝ :=
  Sieve.moebiusShiftedLogKernelReal 0 x - pmPrimeLogMean x

theorem hasMellin_pmLogMobiusMeanDefect {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun x : ℝ => (pmLogMobiusMeanDefect x : ℂ)) (-s)
      (1 / (s ^ 2 * riemannZeta (s + 1)) +
        deriv riemannZeta (s + 1) / ((s + 1) ^ 2 * riemannZeta (s + 1))) := by
  have hB := hasMellin_moebiusShiftedLogKernelReal hs
  have hm := hasMellin_pmPrimeLogMean hs
  have h := hasMellin_sub hB.1 hm.1
  rw [hB.2, hm.2] at h
  simpa only [pmLogMobiusMeanDefect, Complex.ofReal_sub, neg_div, sub_neg_eq_add] using h

theorem pmLogMobiusMeanDefect_mellin_cleared {s : ℂ} (hs : 0 < s.re) :
    s ^ 2 * (s + 1) ^ 2 * riemannZeta (s + 1) *
      mellin (fun x : ℝ => (pmLogMobiusMeanDefect x : ℂ)) (-s) =
        (s + 1) ^ 2 + s ^ 2 * deriv riemannZeta (s + 1) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hs10 : s + 1 ≠ 0 := by intro h; norm_num [h] at hs1
  have hz := riemannZeta_ne_zero_of_one_lt_re hs1
  rw [(hasMellin_pmLogMobiusMeanDefect hs).2]
  field_simp

end RHTower
