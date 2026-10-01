import GaloisForLFunctions.RHTower.ChronologicalWeightedMellin

/-!
# Absolute Mellin interchange for arithmetic dilation sources

For an absolutely convergent Dirichlet series with zero coefficient at zero,
Mellin transformation of its dilation source factors into the Dirichlet series
and the weight transform. The proof includes absolute integrability and the
exact norm scaling. Compactly supported weights also admit exact finite sums.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem pm_mellin_norm_dilate (w : ℝ → ℂ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * w (a * t)‖) =
      a ^ (-s.re) * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * w t‖ := by
  let F : ℝ → ℝ := fun t => ‖(t : ℂ) ^ (s - 1) * w t‖
  have heq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ‖(t : ℂ) ^ (s - 1) * w (a * t)‖ = a ^ (1 - s.re) * F (a * t) := by
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha ht),
      Complex.sub_re, Complex.one_re, Real.mul_rpow ha.le ht.le]
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add ha]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    integral_comp_mul_left_Ioi F 0 ha]
  simp only [mul_zero, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_neg_one a, ← Real.rpow_add ha]
  congr 2
  ring

def pmWeightedDilationSource (a : ℕ → ℂ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, a n * w ((n : ℝ) * t)

theorem pmWeightedDilationSource_hasMellin (a : ℕ → ℂ) (w : ℝ → ℂ)
    {s : ℂ} (ha0 : a 0 = 0) (ha : LSeriesSummable a s) (hw : MellinConvergent w s) :
    HasMellin (pmWeightedDilationSource a w) s (LSeries a s * mellin w s) := by
  let F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (s - 1) * (a n * w ((n : ℝ) * t))
  have hi (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, ha0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h := ((MellinConvergent.comp_mul_left hnpos).mpr hw).const_smul (a n)
      simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, mul_left_comm, F] using h
  let C := ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * w t‖
  have hn (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖F n t‖) = ‖LSeries.term a s n‖ * C := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, ha0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have heq (t : ℝ) : F n t = a n * ((t : ℂ) ^ (s - 1) * w ((n : ℝ) * t)) := by
        dsimp [F]; ring
      simp_rw [heq, norm_mul (a n), integral_const_mul,
        pm_mellin_norm_dilate w s hnpos, Real.rpow_neg hnpos.le,
        LSeries.norm_term_eq, if_neg hn, div_eq_mul_inv, C]
      ring
  have hsum : Summable (fun n => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    simp_rw [hn]
    exact ha.norm.mul_right C
  have htotal : Integrable (fun t => ∑' n, F n t) (volume.restrict (Ioi 0)) := by
    refine ⟨(AEMeasurable.tsum (fun n => (hi n).aemeasurable)).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm))
    rw [lintegral_tsum (fun n => (hi n).1.enorm)]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => integral_nonneg (fun t => norm_nonneg _)) hsum]
    exact ENNReal.ofReal_lt_top
  have hswap := hasSum_integral_of_summable_integral_norm hi hsum
  have hterm (n : ℕ) : (∫ t : ℝ in Ioi 0, F n t) =
      LSeries.term a s n * mellin w s := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, ha0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [F, mul_left_comm _ (a n), integral_const_mul]
      change a n * mellin (fun t => w ((n : ℝ) * t)) s = _
      rw [mellin_comp_mul_left w s hnpos, smul_eq_mul,
        LSeries.term_of_ne_zero hn, Complex.cpow_neg]
      simp only [div_eq_mul_inv, mul_assoc, Complex.ofReal_natCast]
  simp_rw [hterm] at hswap
  constructor
  · simpa only [MellinConvergent, IntegrableOn, pmWeightedDilationSource, smul_eq_mul, F,
      tsum_mul_left] using htotal
  · have h := hswap.tsum_eq
    simpa only [mellin, pmWeightedDilationSource, smul_eq_mul, F,
      tsum_mul_left, tsum_mul_right, LSeries] using h.symm

theorem pmWeightedDilationSource_eq_sum (a : ℕ → ℂ) (w : ℝ → ℂ) (N : ℕ)
    {θ t : ℝ} (ht : 0 < t) (hw : ∀ x, θ < x → w x = 0)
    (hcut : θ < ((N : ℝ) + 1) * t) :
    pmWeightedDilationSource a w t =
      ∑ n ∈ Finset.range (N + 1), a n * w ((n : ℝ) * t) := by
  apply tsum_eq_sum
  intro n hn
  have hnN : N + 1 ≤ n := Nat.le_of_not_gt (by simpa using hn)
  have hnR : (N : ℝ) + 1 ≤ n := by exact_mod_cast hnN
  rw [hw _ (hcut.trans_le (mul_le_mul_of_nonneg_right hnR ht.le)), mul_zero]

end RHTower
