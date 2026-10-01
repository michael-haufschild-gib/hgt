import GaloisForLFunctions.RHTower.FermiNymanRawMobiusTailFloor

/-!
# Finite coefficient errors and the literal canonical Fermi norm

Every finite real coefficient vector gives a square-integrable Nyman error on the
positive half-line. Its dyadic difference is the corresponding Haar/Fermi error on
`(0,1]` and vanishes beyond `1`. The full-half-line coercivity therefore bounds the
auxiliary norm by six times the actual canonical error, without a coefficient
cancellation or zero-location premise.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin
noncomputable section
namespace RHTower

/-- The finite Nyman error on the entire positive half-line. -/
def finiteNymanError (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t +
    ∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * nymanGen (d : ℝ) t

theorem measurable_finiteNymanError (N : ℕ) (c : ℕ → ℝ) :
    Measurable (finiteNymanError N c) := by
  unfold finiteNymanError
  exact (measurable_const.indicator measurableSet_Ioc).add
    (Finset.measurable_sum _ (fun d _ => measurable_const.mul (measurable_nymanGen _)))

theorem norm_finiteNymanError_le (N : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    ‖finiteNymanError N c t‖ ≤ 1 + ∑ d ∈ Finset.Icc 1 N, ‖(c d : ℂ)‖ := by
  have hchi : ‖(Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t‖ ≤ 1 := by
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  unfold finiteNymanError
  refine (norm_add_le _ _).trans (add_le_add hchi ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_nymanGen_le (d : ℝ) t)
    (norm_nonneg (c d : ℂ))

theorem finiteNymanError_eq_reciprocal_tail (N : ℕ) (c : ℕ → ℝ) {t : ℝ} (ht : 1 < t) :
    finiteNymanError N c t = (((∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ)) / t : ℝ) : ℂ) := by
  rw [finiteNymanError, indicator_of_notMem (fun h => not_le_of_gt ht h.2), zero_add,
    Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdt : 1 < (d : ℝ) * t := lt_of_lt_of_le ht (le_mul_of_one_le_left (by linarith) hd1)
  rw [nymanGen, Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one (by positivity)).mpr hdt⟩]
  push_cast
  ring

theorem integrableOn_normSq_finiteNymanError (N : ℕ) (c : ℕ → ℝ) :
    IntegrableOn (fun t => ‖finiteNymanError N c t‖ ^ 2) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded
      (M := (1 + ∑ d ∈ Finset.Icc 1 N, ‖(c d : ℂ)‖) ^ 2)
      measure_Ioc_lt_top.ne ((measurable_finiteNymanError N c).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_finiteNymanError_le N c t) 2
  · refine (integrableOn_normSq_real_div (∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ))
      (by norm_num : (0 : ℝ) < 1)).congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [finiteNymanError_eq_reciprocal_tail N c ht]

theorem fermiDilationDifference_finiteNymanError (N : ℕ) (c : ℕ → ℝ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    fermiDilationDifference (finiteNymanError N c) t =
      dyadicHaar t + ∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * fermiNymanGen (d : ℝ) t := by
  have hgen : ∀ d : ℕ, nymanGen (d : ℝ) (2 * t) = nymanGen (2 * d) t := by
    intro d
    unfold nymanGen
    rw [show (d : ℝ) * (2 * t) = 2 * d * t by ring]
  have hchi : (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
      2 * (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) (2 * t) = dyadicHaar t := by
    rw [indicator_of_mem ht, dyadicHaar]
    split_ifs with h
    · rw [indicator_of_mem (show 2 * t ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [ht.1])]
      norm_num
    · rw [indicator_of_notMem (show 2 * t ∉ Ioc (0 : ℝ) 1 by intro hmem; apply h; linarith [hmem.2])]
      simp
  unfold fermiDilationDifference finiteNymanError
  simp_rw [fermiNymanGen, hgen, mul_sub]
  rw [Finset.sum_sub_distrib, ← hchi]
  have hsum : (∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * (2 * nymanGen (2 * d) t)) =
      2 * ∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * nymanGen (2 * d) t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum]
  ring

theorem fermiDilationDifference_finiteNymanError_eq_zero (N : ℕ) (c : ℕ → ℝ) {t : ℝ}
    (ht : 1 < t) : fermiDilationDifference (finiteNymanError N c) t = 0 := by
  rw [fermiDilationDifference, finiteNymanError_eq_reciprocal_tail N c ht,
    finiteNymanError_eq_reciprocal_tail N c (by linarith : 1 < 2 * t)]
  push_cast
  field_simp
  ring

/-- Finite coefficient errors retain the full-half-line coercivity in the literal PM norm. -/
theorem integral_normSq_finiteNymanError_le_six (N : ℕ) (c : ℕ → ℝ) :
    (∫ t in Ioi (0 : ℝ), ‖finiteNymanError N c t‖ ^ 2) ≤
      6 * ∫ t in Ioc (0 : ℝ) 1,
        ‖dyadicHaar t + ∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * fermiNymanGen (d : ℝ) t‖ ^ 2 := by
  have hm := measurable_finiteNymanError N c
  have hi := integrableOn_normSq_finiteNymanError N c
  have hd := integrableOn_normSq_fermiDilationDifference hm hi
  have heq : (∫ t in Ioi (0 : ℝ), ‖fermiDilationDifference (finiteNymanError N c) t‖ ^ 2) =
      ∫ t in Ioc (0 : ℝ) 1,
        ‖dyadicHaar t + ∑ d ∈ Finset.Icc 1 N, (c d : ℂ) * fermiNymanGen (d : ℝ) t‖ ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hd.mono_set (Ioc_subset_Ioi_self)) (hd.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))]
    have hz : (∫ t in Ioi (1 : ℝ), ‖fermiDilationDifference (finiteNymanError N c) t‖ ^ 2) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      rw [fermiDilationDifference_finiteNymanError_eq_zero N c ht]
      simp
    rw [hz, add_zero]
    exact setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => congrArg (fun z : ℂ => ‖z‖ ^ 2) (fermiDilationDifference_finiteNymanError N c ht))
  rw [← heq]
  exact integral_normSq_le_six_fermiDilationDifference hm hi

end RHTower
