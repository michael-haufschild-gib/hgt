import GaloisForLFunctions.HTGeometry.GammaShiftSumSeparation
import GaloisForLFunctions.HTGeometry.PowerExpansionAlongRay

/-!
# The shift separation along a vertical ray

`eq_zero_of_digamma_shift_sum_small` reads the ladder along the real ray.  The boundary data of the
archimedean cards live on vertical tubes, where the variable escapes with bounded real part, so the
reading has to happen along `σ + it`.

The ladder itself already covers that region — it holds on `Re s > 0`, `‖s‖ ≥ R` — so only the
*reading principle* had to be generalized, which `PowerExpansionAlongRay` does.  This file combines
the two.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- **Reading the ladder moments along an arbitrary escaping sequence in the right half plane.** -/
theorem ladder_moments_of_digamma_shift_sum_small_ray {r : ℕ} (lam g : Fin r → ℂ) (M : ℕ)
    (K : ℝ) (S : ℕ → ℂ)
    (hre : ∀ n, 0 < (S n).re)
    (hS : Tendsto (fun n => ‖S n‖) atTop atTop)
    (hlog : Tendsto (fun n => ‖Complex.log (S n)‖) atTop atTop)
    (h : ∀ᶠ n in atTop, ‖∑ k, g k * Complex.digamma (S n + lam k)‖ ≤ K / ‖S n‖ ^ (M + 1)) :
    (∑ k, g k = 0) ∧ ∀ m, m < M → ∑ k, g k * shiftLadderCoeff (lam k) m = 0 := by
  classical
  choose Kk Rk hKk hRk hbk using fun k : Fin r => exists_norm_shiftLadderDefect_le (lam k) M
  have hRknn : ∀ k : Fin r, 0 ≤ Rk k := fun k => by linarith [hRk k]
  have hRksum : ∀ k : Fin r, Rk k ≤ ∑ j, Rk j :=
    fun k => Finset.single_le_sum (fun j _ => hRknn j) (Finset.mem_univ k)
  set K' : ℝ := K + ∑ k, ‖g k‖ * Kk k with hK'def
  have hbig : ∀ᶠ n in atTop, (∑ j, Rk j) + 1 ≤ ‖S n‖ := hS.eventually_ge_atTop _
  have hmain : ∀ᶠ n in atTop,
      ‖(∑ k, g k) * Complex.log (S n)
        + ∑ m ∈ Finset.range (M + 1), ladderMomentSeq lam g m / (S n) ^ m‖
        ≤ K' / ‖S n‖ ^ (M + 1) := by
    filter_upwards [h, hbig] with n hn hnbig
    have hdef : ∀ k : Fin r,
        ‖shiftLadderDefect (lam k) M (S n)‖ ≤ Kk k / ‖S n‖ ^ (M + 1) := by
      intro k
      have hRkt : Rk k ≤ ‖S n‖ := le_trans (hRksum k) (by linarith)
      exact hbk k (S n) (hre n) hRkt
    have hpeel : ∑ m ∈ Finset.range (M + 1), ladderMomentSeq lam g m / (S n) ^ m
        = ∑ m ∈ Finset.range M,
            (-(∑ k, g k * shiftLadderCoeff (lam k) m)) / (S n) ^ (m + 1) := by
      rw [Finset.sum_range_succ']
      simp [ladderMomentSeq]
    have hid : (∑ k, g k) * Complex.log (S n)
        + ∑ m ∈ Finset.range (M + 1), ladderMomentSeq lam g m / (S n) ^ m
        = (∑ k, g k * Complex.digamma (S n + lam k))
          - ∑ k, g k * shiftLadderDefect (lam k) M (S n) := by
      rw [hpeel]
      have hexpand : ∀ k : Fin r, g k * Complex.digamma (S n + lam k)
          = g k * shiftLadderDefect (lam k) M (S n) + g k * Complex.log (S n)
            - ∑ m ∈ Finset.range M, g k * (shiftLadderCoeff (lam k) m / (S n) ^ (m + 1)) := by
        intro k
        have hdd : shiftLadderDefect (lam k) M (S n)
            = Complex.digamma (S n + lam k) - Complex.log (S n)
              + ∑ m ∈ Finset.range M, shiftLadderCoeff (lam k) m / (S n) ^ (m + 1) := rfl
        rw [hdd, mul_add, mul_sub, Finset.mul_sum]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hexpand k)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [Finset.sum_comm]
      have hinner : ∀ m ∈ Finset.range M,
          (-(∑ k, g k * shiftLadderCoeff (lam k) m)) / (S n) ^ (m + 1)
            = -(∑ k, g k * (shiftLadderCoeff (lam k) m / (S n) ^ (m + 1))) := by
        intro m _
        rw [neg_div, Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by rw [mul_div_assoc]
      rw [Finset.sum_congr rfl hinner, Finset.sum_neg_distrib]
      ring
    rw [hid]
    refine le_trans (norm_sub_le _ _) ?_
    have hb2 : ‖∑ k, g k * shiftLadderDefect (lam k) M (S n)‖
        ≤ (∑ k, ‖g k‖ * Kk k) / ‖S n‖ ^ (M + 1) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hdef k) (norm_nonneg _)
    have hadd : K / ‖S n‖ ^ (M + 1) + (∑ k, ‖g k‖ * Kk k) / ‖S n‖ ^ (M + 1)
        = K' / ‖S n‖ ^ (M + 1) := by
      rw [hK'def]; ring
    linarith [hn, hb2, hadd.le, hadd.symm.le]
  obtain ⟨hb, ha⟩ := log_power_expansion_eq_zero_ray M (∑ k, g k) (ladderMomentSeq lam g) K' S
    hS hlog hmain
  refine ⟨hb, fun m hm => ?_⟩
  have hzero := ha (m + 1) (by omega)
  rw [ladderMomentSeq] at hzero
  linear_combination -hzero

/-- **The all-order shift separation along an escaping sequence in the right half plane.** -/
theorem eq_zero_of_digamma_shift_sum_small_ray {r : ℕ} (lam : Fin r → ℂ)
    (hinj : Function.Injective lam) (g : Fin r → ℂ) (K : ℝ) (S : ℕ → ℂ)
    (hre : ∀ n, 0 < (S n).re)
    (hS : Tendsto (fun n => ‖S n‖) atTop atTop)
    (hlog : Tendsto (fun n => ‖Complex.log (S n)‖) atTop atTop)
    (h : ∀ᶠ n in atTop, ‖∑ k, g k * Complex.digamma (S n + lam k)‖ ≤ K / ‖S n‖ ^ r) :
    ∀ k, g k = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · intro k
    exact absurd k.isLt (by omega)
  · obtain ⟨M, hM⟩ : ∃ M, r = M + 1 := ⟨r - 1, by omega⟩
    subst hM
    obtain ⟨h0, hmom⟩ := ladder_moments_of_digamma_shift_sum_small_ray lam g M K S hre hS hlog h
    refine eq_zero_of_ladder_moments_vanish lam hinj g h0 ?_
    intro m hmr
    exact hmom m (by omega)

/-- The vertical ray `σ + i n` escapes, and its logarithm escapes with it. -/
theorem tendsto_norm_verticalRay (σ : ℝ) :
    Tendsto (fun n : ℕ => ‖(σ : ℂ) + (n : ℂ) * Complex.I‖) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono (fun n => ?_) hbase
  have him : ((σ : ℂ) + (n : ℂ) * Complex.I).im = (n : ℝ) := by
    simp
  have h := Complex.abs_im_le_norm ((σ : ℂ) + (n : ℂ) * Complex.I)
  rw [him] at h
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_of_nonneg hn] at h
  exact h

theorem re_verticalRay (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    0 < ((σ : ℂ) + (n : ℂ) * Complex.I).re := by
  simpa using hσ


/-- If the variable escapes then so does its logarithm. -/
theorem tendsto_norm_log_of_tendsto_norm {S : ℕ → ℂ}
    (hS : Tendsto (fun n => ‖S n‖) atTop atTop) :
    Tendsto (fun n => ‖Complex.log (S n)‖) atTop atTop := by
  have h1 : Tendsto (fun n => Real.log ‖S n‖) atTop atTop :=
    Real.tendsto_log_atTop.comp hS
  refine tendsto_atTop_mono (fun n => ?_) h1
  have h2 := Complex.abs_re_le_norm (Complex.log (S n))
  rw [Complex.log_re] at h2
  exact le_trans (le_abs_self _) h2

/-- **The separation on a vertical line.**  This is the form the boundary data of the archimedean
cards live in: the real part stays fixed and the imaginary part escapes. -/
theorem eq_zero_of_digamma_shift_sum_small_vertical {r : ℕ} (lam : Fin r → ℂ)
    (hinj : Function.Injective lam) (g : Fin r → ℂ) (σ : ℝ) (hσ : 0 < σ) (K : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      ‖∑ k, g k * Complex.digamma (((σ : ℂ) + (n : ℂ) * Complex.I) + lam k)‖
        ≤ K / ‖(σ : ℂ) + (n : ℂ) * Complex.I‖ ^ r) :
    ∀ k, g k = 0 := by
  refine eq_zero_of_digamma_shift_sum_small_ray lam hinj g K
    (fun n => (σ : ℂ) + (n : ℂ) * Complex.I) (re_verticalRay σ hσ)
    (tendsto_norm_verticalRay σ)
    (tendsto_norm_log_of_tendsto_norm (tendsto_norm_verticalRay σ)) h

end

end GaloisForLFunctions.HTGeometry
