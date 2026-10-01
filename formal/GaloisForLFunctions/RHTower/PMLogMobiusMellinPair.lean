import GaloisForLFunctions.RHTower.RieszMellinPair
import GaloisForLFunctions.RHTower.ChronologicalWeightedMellin
import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogRealCutoff

/-!
# Mellin pair for the literal logarithmic Möbius coefficient

The real-cutoff sum is identified exactly with a reciprocal dilation source,
including its floor convention and endpoint at one. Its Mellin transform is
`1 / (s^2 * zeta(s+1))` for `Re s > 0`. All interchange uses absolute
convergence. No critical-line convergence or zero-simplicity conclusion is
asserted here.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

def pmLogarithmicRamp (x : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun y => (Real.log y : ℂ)) x

theorem hasMellin_pmLogarithmicRamp {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmLogarithmicRamp (-s) (1 / s ^ 2) := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  simp_rw [HasMellin, mellin, MellinConvergent, pmLogarithmicRamp,
    ← indicator_smul, IntegrableOn, integrable_indicator_iff measurableSet_Ioi,
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset hsub,
    smul_eq_mul]
  simpa only [IntegrableOn, Measure.restrict_restrict_of_subset hsub, mul_comm] using
    And.intro (GaloisForLFunctions.RHTower.integrableOn_log_cpow_neg_succ hs)
      (GaloisForLFunctions.RHTower.integral_Ioi_log_cpow_neg_succ hs)

def pmReciprocalLogRamp (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-1 : ℂ) • pmLogarithmicRamp t⁻¹

theorem hasMellin_pmReciprocalLogRamp {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmReciprocalLogRamp (s + 1) (1 / s ^ 2) := by
  have hi : MellinConvergent (fun t => pmLogarithmicRamp t⁻¹) s := by
    have h : MellinConvergent (fun t => pmLogarithmicRamp (t ^ (-1 : ℝ))) s :=
      (MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0)).mpr
        (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using
          (hasMellin_pmLogarithmicRamp hs).1)
    simpa only [Real.rpow_neg_one] using h
  have he : s + 1 + (-1 : ℂ) = s := by ring
  constructor
  · change MellinConvergent (fun t => (t : ℂ) ^ (-1 : ℂ) • pmLogarithmicRamp t⁻¹) (s + 1)
    rw [MellinConvergent.cpow_smul, he]
    exact hi
  · change mellin (fun t => (t : ℂ) ^ (-1 : ℂ) • pmLogarithmicRamp t⁻¹) (s + 1) = _
    rw [mellin_cpow_smul, he, mellin_comp_inv]
    exact (hasMellin_pmLogarithmicRamp hs).2

def pmLogCoefficientReciprocalProfile (t : ℝ) : ℂ :=
  (t : ℂ) * chronologicalMobiusWeightedSource pmReciprocalLogRamp t

theorem hasMellin_pmLogCoefficientReciprocalProfile {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmLogCoefficientReciprocalProfile s (1 / (s ^ 2 * riemannZeta (s + 1))) := by
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hw := hasMellin_pmReciprocalLogRamp hs
  have hm := chronologicalMobiusWeightedSource_hasMellin pmReciprocalLogRamp hs1 hw.1
  rw [hw.2] at hm
  constructor
  · change MellinConvergent
      (fun t => (t : ℂ) * chronologicalMobiusWeightedSource pmReciprocalLogRamp t) s
    have h := (MellinConvergent.cpow_smul (s := s) (a := (1 : ℂ))).mpr hm.1
    simpa only [Complex.cpow_one, smul_eq_mul] using h
  · have h := mellin_cpow_smul (chronologicalMobiusWeightedSource pmReciprocalLogRamp) s (1 : ℂ)
    simp only [Complex.cpow_one, smul_eq_mul] at h
    change mellin (fun t => (t : ℂ) * chronologicalMobiusWeightedSource pmReciprocalLogRamp t) s = _
    rw [h, hm.2]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring

theorem pmLogarithmicRamp_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    pmLogarithmicRamp x = (Real.log x : ℂ) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp [pmLogarithmicRamp]
  · simp [pmLogarithmicRamp, h]

theorem pmReciprocalLogRamp_eq_zero {t : ℝ} (ht : 1 < t) :
    pmReciprocalLogRamp t = 0 := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hi : t⁻¹ ≤ 1 := by
    have h := (div_le_iff₀ ht0).2 (show (1 : ℝ) ≤ 1 * t by simpa using ht.le)
    simpa only [one_div] using h
  simp [pmReciprocalLogRamp, pmLogarithmicRamp, not_lt.mpr hi]

theorem pmLogCoefficientReciprocalProfile_eq {t : ℝ} (ht : 0 < t) :
    pmLogCoefficientReciprocalProfile t =
      (Sieve.moebiusShiftedLogKernelReal 0 t⁻¹ : ℂ) := by
  classical
  have hcut : 1 < ((⌊t⁻¹⌋₊ : ℝ) + 1) * t := by
    have hf := Nat.lt_floor_add_one t⁻¹
    have hm := mul_lt_mul_of_pos_right hf ht
    simpa only [inv_mul_cancel₀ ht.ne'] using hm
  rw [pmLogCoefficientReciprocalProfile,
    chronologicalMobiusWeightedSource_eq_sum pmReciprocalLogRamp ⌊t⁻¹⌋₊ ht
      (fun _ h => pmReciprocalLogRamp_eq_zero h) hcut,
    Finset.mul_sum, Finset.sum_range_succ']
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, mul_zero, add_zero]
  rw [RHTower.sum_range_succ_eq_sum_Icc
    (fun n : ℕ => (t : ℂ) * ((ArithmeticFunction.moebius n : ℂ) *
      pmReciprocalLogRamp ((n : ℝ) * t))) ⌊t⁻¹⌋₊]
  unfold Sieve.moebiusShiftedLogKernelReal
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnf : (n : ℝ) ≤ t⁻¹ :=
    (Nat.le_floor_iff (inv_pos.mpr ht).le).mp (Finset.mem_Icc.mp hn).2
  have hnt0 : 0 < (n : ℝ) * t := mul_pos hn0 ht
  have hnt1 : (n : ℝ) * t ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hnf ht.le
    simpa only [inv_mul_cancel₀ ht.ne'] using hm
  have hinv : 1 ≤ ((n : ℝ) * t)⁻¹ := by
    have h := (le_div_iff₀ hnt0).2 (show 1 * ((n : ℝ) * t) ≤ 1 by simpa using hnt1)
    simpa only [one_div] using h
  rw [pmReciprocalLogRamp, pmLogarithmicRamp_of_one_le hinv,
    Complex.cpow_neg_one, smul_eq_mul]
  have hlog : ((n : ℝ) * t)⁻¹ = t⁻¹ / (n : ℝ) := by field_simp
  rw [hlog]
  push_cast
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [zero_add]
  field_simp

theorem hasMellin_moebiusShiftedLogKernelReal_inv {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (Sieve.moebiusShiftedLogKernelReal 0 t⁻¹ : ℂ)) s
      (1 / (s ^ 2 * riemannZeta (s + 1))) := by
  have h := hasMellin_pmLogCoefficientReciprocalProfile hs
  constructor
  · apply h.1.congr_fun _ measurableSet_Ioi
    intro t ht
    exact congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z)
      (pmLogCoefficientReciprocalProfile_eq ht)
  · calc
      _ = mellin pmLogCoefficientReciprocalProfile s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z)
          (pmLogCoefficientReciprocalProfile_eq ht).symm
      _ = _ := h.2

theorem hasMellin_moebiusShiftedLogKernelReal {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun x : ℝ => (Sieve.moebiusShiftedLogKernelReal 0 x : ℂ)) (-s)
      (1 / (s ^ 2 * riemannZeta (s + 1))) := by
  have h := hasMellin_moebiusShiftedLogKernelReal_inv hs
  constructor
  · have hi := (MellinConvergent.comp_rpow (s := -s)
      (f := fun t : ℝ => (Sieve.moebiusShiftedLogKernelReal 0 t⁻¹ : ℂ))
      (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg,
        div_one, neg_neg] using h.1)
    simpa only [Real.rpow_neg_one, inv_inv] using hi
  · exact (mellin_comp_inv
      (fun x : ℝ => (Sieve.moebiusShiftedLogKernelReal 0 x : ℂ)) s).symm.trans h.2

end RHTower
