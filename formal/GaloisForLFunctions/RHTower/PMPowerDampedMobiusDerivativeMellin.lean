import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDerivative

/-!
# Exact Mellin transform of the dyadic Chebyshev tangent

Supported Haar dilation by von Mangoldt coefficients identifies the actual
source transform with the dyadic factor times the negative zeta logarithmic
derivative on its absolute-convergence half-plane.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower


def pmSupportedDyadicHaar : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator dyadicHaar

theorem pmSupportedDyadicHaar_eq_zero {t : ℝ} (ht : 1 < t) :
    pmSupportedDyadicHaar t = 0 := by
  exact Set.indicator_of_notMem (fun h => (not_le_of_gt ht) h.2) _

theorem pmSupportedDyadicHaar_eq_cutoffs {t : ℝ} (ht : 0 < t) :
    pmSupportedDyadicHaar t =
      (if t ≤ 1 then (1 : ℂ) else 0) - 2 * (if t ≤ 1 / 2 then (1 : ℂ) else 0) := by
  by_cases ht1 : t ≤ 1
  · rw [pmSupportedDyadicHaar, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩), dyadicHaar, if_pos ht1]
    split_ifs <;> norm_num
  · rw [pmSupportedDyadicHaar_eq_zero (lt_of_not_ge ht1), if_neg ht1,
      if_neg (by linarith : ¬ t ≤ 1 / 2)]
    ring

theorem hasMellin_pmSupportedDyadicHaar {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmSupportedDyadicHaar s ((1 - (2 : ℂ) ^ (1 - s)) / s) := by
  have hc : Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    integrableOn_Ioc_cpow_sub_one hs (by norm_num : (0 : ℝ) ≤ 1)
  have hi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * dyadicHaar t) (Ioc 0 1) := by
    refine hc.norm.mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact hc.aestronglyMeasurable.mul measurable_dyadicHaar.aestronglyMeasurable
    · rw [norm_mul, norm_dyadicHaar, mul_one]
  have hhead : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmSupportedDyadicHaar t)
      (Ioc 0 1) := by
    apply hi.congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp only
    rw [pmSupportedDyadicHaar, Set.indicator_of_mem ht]
  have htail : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmSupportedDyadicHaar t)
      (Ioi 1) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [pmSupportedDyadicHaar_eq_zero ht, mul_zero]
  constructor
  · change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * pmSupportedDyadicHaar t) (Ioi 0)
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)]
    exact hhead.union htail
  · unfold mellin
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)]
    · convert integral_dyadicHaar_mul_cpow hs using 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [pmSupportedDyadicHaar, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
    · intro t ht
      have ht1 : 1 < t := by
        rcases ht with ⟨ht0, htn⟩
        simp only [mem_Ioc, not_and, not_le] at htn
        exact htn ht0
      rw [pmSupportedDyadicHaar_eq_zero ht1, smul_zero]

theorem pm_vonMangoldt_cutoff_zero {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    {n : ℕ} (hn : n ∉ Finset.range (⌊c / t⌋₊ + 1)) :
    (ArithmeticFunction.vonMangoldt n : ℂ) * (if (n : ℝ) * t ≤ c then 1 else 0) = 0 := by
  have hnl : ¬ n ≤ ⌊c / t⌋₊ := by simpa using hn
  have hnr : ¬ (n : ℝ) ≤ c / t := fun h => hnl ((Nat.le_floor_iff (div_nonneg hc ht.le)).mpr h)
  rw [if_neg (fun h => hnr ((le_div_iff₀ ht).mpr h)), mul_zero]

theorem summable_pm_vonMangoldt_cutoff {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (if (n : ℝ) * t ≤ c then 1 else 0)) := by
  exact summable_of_ne_finset_zero (fun n hn => pm_vonMangoldt_cutoff_zero hc ht hn)

theorem pm_vonMangoldt_cutoff_sum {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (if (n : ℝ) * t ≤ c then 1 else 0)) = (Chebyshev.psi (c / t) : ℂ) := by
  rw [tsum_eq_sum (s := Finset.range (⌊c / t⌋₊ + 1))
    (fun n hn => pm_vonMangoldt_cutoff_zero hc ht hn),
    Nat.range_succ_eq_Icc_zero, Chebyshev.psi_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : (n : ℝ) ≤ c / t :=
    (Nat.le_floor_iff (div_nonneg hc ht.le)).mp (Finset.mem_Icc.mp hn).2
  rw [if_pos ((le_div_iff₀ ht).mp hnR), mul_one]

theorem pmDyadicChebyshevSource_eq_dilation {t : ℝ} (ht : 0 < t) :
    pmDyadicChebyshevSource t =
      pmWeightedDilationSource (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        pmSupportedDyadicHaar t := by
  have heq (n : ℕ) :
      (ArithmeticFunction.vonMangoldt n : ℂ) * pmSupportedDyadicHaar ((n : ℝ) * t) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (if (n : ℝ) * t ≤ 1 then 1 else 0) -
      2 * ((ArithmeticFunction.vonMangoldt n : ℂ) * (if (n : ℝ) * t ≤ 1 / 2 then 1 else 0)) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [pmSupportedDyadicHaar_eq_cutoffs (mul_pos hn0 ht)]
      ring
  unfold pmWeightedDilationSource
  simp_rw [heq]
  rw [(summable_pm_vonMangoldt_cutoff (by norm_num : (0 : ℝ) ≤ 1) ht).tsum_sub
    ((summable_pm_vonMangoldt_cutoff (by norm_num : (0 : ℝ) ≤ 1 / 2) ht).mul_left 2),
    tsum_mul_left, pm_vonMangoldt_cutoff_sum (by norm_num : (0 : ℝ) ≤ 1) ht,
    pm_vonMangoldt_cutoff_sum (by norm_num : (0 : ℝ) ≤ 1 / 2) ht]
  unfold pmDyadicChebyshevSource dyadicChebyshevError
  rw [show (1 / t) / 2 = (1 / 2) / t by ring]
  push_cast
  rfl

theorem hasMellin_pmDyadicChebyshevSource {s : ℂ} (hs : 1 < s.re) :
    HasMellin pmDyadicChebyshevSource s
      (-((1 - (2 : ℂ) ^ (1 - s)) / s) * logDeriv riemannZeta s) := by
  have hH := hasMellin_pmSupportedDyadicHaar (lt_trans zero_lt_one hs)
  have h := pmWeightedDilationSource_hasMellin
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) pmSupportedDyadicHaar
    (by simp) (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) hH.1
  have heq : mellin pmDyadicChebyshevSource s =
      mellin (pmWeightedDilationSource
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) pmSupportedDyadicHaar) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [pmDyadicChebyshevSource_eq_dilation ht]
  constructor
  · apply h.1.congr_fun _ measurableSet_Ioi
    intro t ht
    change (t : ℂ) ^ (s - 1) • _ = (t : ℂ) ^ (s - 1) • pmDyadicChebyshevSource t
    rw [pmDyadicChebyshevSource_eq_dilation ht]
  · rw [heq, h.2, hH.2,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, logDeriv_apply]
    ring


theorem pmDyadicChebyshevSource_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    pmDyadicChebyshevSource t = 0 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have h1 : 1 / t ≤ 1 := (div_le_one ht0).mpr ht.le
  unfold pmDyadicChebyshevSource dyadicChebyshevError
  rw [Chebyshev.psi_eq_zero_of_le_one h1,
    Chebyshev.psi_eq_zero_of_le_one (by linarith : (1 / t) / 2 ≤ 1)]
  simp

end RHTower
