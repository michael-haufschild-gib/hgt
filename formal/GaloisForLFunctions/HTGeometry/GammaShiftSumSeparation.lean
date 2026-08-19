import GaloisForLFunctions.HTGeometry.GammaShiftLadderSeparation
import GaloisForLFunctions.HTGeometry.GammaLogPowerIndependence

/-!
# Reading a shifted digamma sum off its vertical asymptotics

This is the analytic capstone of the Stirling ladder: a finite combination
`∑_k g_k ψ(s + λ_k)` that is `O(t^{-r})` along the real ray must have `g = 0`, provided only that
the shifts are **distinct**.

The proof reads the ladder of `GammaShiftLadder` term by term.  The `log t` coefficient gives
`∑_k g_k = 0`, the `t^{-(m+1)}` coefficients give `∑_k g_k d_m(λ_k) = 0`, and the triangularity of
`GammaShiftLadderSeparation` turns those into `g = 0`.

This is the mechanism `finite-archimedean-gamma-product-boundary-law` §5 calls "no flat cancellation
in the archimedean residue field", with no `NoIntegerRelation` hypothesis anywhere — so it applies
to the commensurable scales `λ_j = n_j / H` that the order-one signature could not separate.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- The sequence of ladder moments of a shifted digamma combination. -/
def ladderMomentSeq {r : ℕ} (lam g : Fin r → ℂ) : ℕ → ℂ
  | 0 => 0
  | (m + 1) => -(∑ k, g k * shiftLadderCoeff (lam k) m)

/-- **Reading the ladder moments off the decay.** -/
theorem ladder_moments_of_digamma_shift_sum_small {r : ℕ} (lam g : Fin r → ℂ) (M : ℕ) (K R : ℝ)
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ‖∑ k, g k * Complex.digamma (((t : ℝ) : ℂ) + lam k)‖ ≤ K / t ^ (M + 1)) :
    (∑ k, g k = 0) ∧ ∀ m, m < M → ∑ k, g k * shiftLadderCoeff (lam k) m = 0 := by
  classical
  choose Kk Rk hKk hRk hbk using fun k : Fin r => exists_norm_shiftLadderDefect_le (lam k) M
  set R' : ℝ := max R 0 + (∑ k, Rk k) + 2 with hR'def
  set K' : ℝ := K + ∑ k, ‖g k‖ * Kk k with hK'def
  have hRknn : ∀ k : Fin r, 0 ≤ Rk k := fun k => by linarith [hRk k]
  have hRksum : ∀ k : Fin r, Rk k ≤ ∑ j, Rk j :=
    fun k => Finset.single_le_sum (fun j _ => hRknn j) (Finset.mem_univ k)
  have hmain : ∀ t : ℝ, R' ≤ t → 1 ≤ t →
      ‖(∑ k, g k) * ((Real.log t : ℝ) : ℂ)
        + ∑ m ∈ Finset.range (M + 1), ladderMomentSeq lam g m / (((t : ℝ) : ℂ)) ^ m‖
        ≤ K' / t ^ (M + 1) := by
    intro t hRt ht1
    have ht0 : (0 : ℝ) < t := by linarith
    have hsumnn : (0 : ℝ) ≤ ∑ k, Rk k := Finset.sum_nonneg fun j _ => hRknn j
    have hRt' : R ≤ t := by
      have : R ≤ max R 0 := le_max_left _ _
      simp only [hR'def] at hRt
      linarith
    set z : ℂ := ((t : ℝ) : ℂ) with hzdef
    have hznorm : ‖z‖ = t := by
      rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hzre : (0 : ℝ) < z.re := by rw [hzdef, Complex.ofReal_re]; exact ht0
    have hzlog : Complex.log z = ((Real.log t : ℝ) : ℂ) := by
      rw [hzdef, Complex.ofReal_log ht0.le]
    -- each defect is small
    have hdef : ∀ k : Fin r, ‖shiftLadderDefect (lam k) M z‖ ≤ Kk k / t ^ (M + 1) := by
      intro k
      have hRkt : Rk k ≤ ‖z‖ := by
        rw [hznorm]
        have := hRksum k
        simp only [hR'def] at hRt
        have h0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
        linarith
      have := hbk k z hzre hRkt
      rwa [hznorm] at this
    -- the algebraic identity
    have hpeel : ∑ m ∈ Finset.range (M + 1), ladderMomentSeq lam g m / z ^ m
        = ∑ m ∈ Finset.range M,
            (-(∑ k, g k * shiftLadderCoeff (lam k) m)) / z ^ (m + 1) := by
      rw [Finset.sum_range_succ']
      simp [ladderMomentSeq]
    have hid : (∑ k, g k) * ((Real.log t : ℝ) : ℂ)
        + ∑ m ∈ Finset.range (M + 1), ladderMomentSeq lam g m / z ^ m
        = (∑ k, g k * Complex.digamma (z + lam k))
          - ∑ k, g k * shiftLadderDefect (lam k) M z := by
      rw [hpeel, ← hzlog]
      have hexpand : ∀ k : Fin r, g k * Complex.digamma (z + lam k)
          = g k * shiftLadderDefect (lam k) M z + g k * Complex.log z
            - ∑ m ∈ Finset.range M, g k * shiftLadderCoeff (lam k) m / z ^ (m + 1) := by
        intro k
        have hdd : shiftLadderDefect (lam k) M z
            = Complex.digamma (z + lam k) - Complex.log z
              + ∑ m ∈ Finset.range M, shiftLadderCoeff (lam k) m / z ^ (m + 1) := rfl
        rw [hdd, mul_add, mul_sub, Finset.mul_sum]
        simp only [mul_div_assoc]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hexpand k)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [Finset.sum_comm]
      have hneg : ∀ m ∈ Finset.range M,
          (-(∑ k, g k * shiftLadderCoeff (lam k) m)) / z ^ (m + 1)
            = -(∑ k, g k * shiftLadderCoeff (lam k) m / z ^ (m + 1)) := by
        intro m _
        rw [neg_div, Finset.sum_div]
      rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib]
      ring
    rw [hid]
    refine le_trans (norm_sub_le _ _) ?_
    have hb1 := h t hRt' ht1
    have hb2 : ‖∑ k, g k * shiftLadderDefect (lam k) M z‖
        ≤ (∑ k, ‖g k‖ * Kk k) / t ^ (M + 1) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hdef k) (norm_nonneg _)
    have hadd : K / t ^ (M + 1) + (∑ k, ‖g k‖ * Kk k) / t ^ (M + 1) = K' / t ^ (M + 1) := by
      rw [hK'def]; ring
    linarith [hb1, hb2, hadd.le, hadd.symm.le]
  obtain ⟨hb, ha⟩ := log_power_expansion_eq_zero M (∑ k, g k) (ladderMomentSeq lam g) K' R' hmain
  refine ⟨hb, fun m hm => ?_⟩
  have := ha (m + 1) (by simp; omega)
  rw [ladderMomentSeq] at this
  linear_combination -this

/-- **The all-order shift separation.**  Distinct shifts, and decay of order `r`, force the whole
coefficient vector to vanish. -/
theorem eq_zero_of_digamma_shift_sum_small {r : ℕ} (lam : Fin r → ℂ)
    (hinj : Function.Injective lam) (g : Fin r → ℂ) (K R : ℝ)
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ‖∑ k, g k * Complex.digamma (((t : ℝ) : ℂ) + lam k)‖ ≤ K / t ^ r) :
    ∀ k, g k = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · intro k
    exact absurd k.isLt (by omega)
  · obtain ⟨M, hM⟩ : ∃ M, r = M + 1 := ⟨r - 1, by omega⟩
    subst hM
    obtain ⟨h0, hmom⟩ := ladder_moments_of_digamma_shift_sum_small lam g M K R h
    refine eq_zero_of_ladder_moments_vanish lam hinj g h0 ?_
    intro m hmr
    exact hmom m (by omega)

end

end GaloisForLFunctions.HTGeometry
