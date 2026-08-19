import GaloisForLFunctions.HTGeometry.GammaShiftSumSeparation

/-!
# The exact asymptotic order of a shifted digamma combination

`eq_zero_of_digamma_shift_sum_small` says a nonzero combination cannot decay like `t^{-r}`.  The
constructive form is sharper and is what a transseries boundary datum consumes: a nonzero
combination has a *first* nonvanishing ladder moment, and the combination is asymptotic to that
moment's term.

`archimedean-relative-prime-cocycle-curvature` needs exactly this: two Gamma monomials sharing the
leading shape — `Γ(s+α)Γ(s+β)` against `Γ(s+α+β)Γ(s)` — are separated by the first moment at which
their signatures differ, and this module locates that moment and gives the matching estimate.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- **A nonzero coefficient vector has a nonvanishing signature datum.** -/
theorem exists_ne_zero_ladder_moment {r : ℕ} (lam : Fin r → ℂ)
    (hinj : Function.Injective lam) (g : Fin r → ℂ) (hg : ∃ k, g k ≠ 0) :
    (∑ k, g k ≠ 0) ∨ ∃ m : ℕ, m + 2 ≤ r ∧ ∑ k, g k * shiftLadderCoeff (lam k) m ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, hm⟩ := hcon
  obtain ⟨k, hk⟩ := hg
  exact hk (eq_zero_of_ladder_moments_vanish lam hinj g h0 hm k)

/-- **The leading term of a shifted digamma combination.**  If the constant moment and the first
`m₀` ladder moments vanish, the combination is `-A_{m₀} s^{-(m₀+1)} + O(‖s‖^{-(m₀+2)})`. -/
theorem exists_norm_digamma_shift_sum_leading {r : ℕ} (lam g : Fin r → ℂ) (m0 : ℕ)
    (h0 : ∑ k, g k = 0)
    (hvan : ∀ m, m < m0 → ∑ k, g k * shiftLadderCoeff (lam k) m = 0) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖(∑ k, g k * Complex.digamma (s + lam k))
          + (∑ k, g k * shiftLadderCoeff (lam k) m0) / s ^ (m0 + 1)‖
        ≤ K / ‖s‖ ^ (m0 + 2) := by
  classical
  choose Kk Rk hKk hRk hbk using fun k : Fin r => exists_norm_shiftLadderDefect_le (lam k) (m0 + 1)
  have hRknn : ∀ k : Fin r, 0 ≤ Rk k := fun k => by linarith [hRk k]
  have hRksum : ∀ k : Fin r, Rk k ≤ ∑ j, Rk j :=
    fun k => Finset.single_le_sum (fun j _ => hRknn j) (Finset.mem_univ k)
  refine ⟨∑ k, ‖g k‖ * Kk k, (∑ k, Rk k) + 2, Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hKk k),
    by have : (0:ℝ) ≤ ∑ k, Rk k := Finset.sum_nonneg fun j _ => hRknn j; linarith, ?_⟩
  intro s hs hR
  have hsnorm : (0 : ℝ) < ‖s‖ := by
    have : (0:ℝ) ≤ ∑ k, Rk k := Finset.sum_nonneg fun j _ => hRknn j
    linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h, norm_zero] at hsnorm; linarith
  have hdef : ∀ k : Fin r, ‖shiftLadderDefect (lam k) (m0 + 1) s‖ ≤ Kk k / ‖s‖ ^ (m0 + 2) := by
    intro k
    have hRkt : Rk k ≤ ‖s‖ := by linarith [hRksum k]
    exact hbk k s hs hRkt
  have hid : (∑ k, g k * Complex.digamma (s + lam k))
      + (∑ k, g k * shiftLadderCoeff (lam k) m0) / s ^ (m0 + 1)
      = ∑ k, g k * shiftLadderDefect (lam k) (m0 + 1) s := by
    have hexpand : ∀ k : Fin r, g k * Complex.digamma (s + lam k)
        = g k * shiftLadderDefect (lam k) (m0 + 1) s + g k * Complex.log s
          - ∑ m ∈ Finset.range (m0 + 1), g k * (shiftLadderCoeff (lam k) m / s ^ (m + 1)) := by
      intro k
      have hdd : shiftLadderDefect (lam k) (m0 + 1) s
          = Complex.digamma (s + lam k) - Complex.log s
            + ∑ m ∈ Finset.range (m0 + 1), shiftLadderCoeff (lam k) m / s ^ (m + 1) := rfl
      rw [hdd, mul_add, mul_sub, Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hexpand k)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, h0, zero_mul]
    rw [Finset.sum_comm]
    have hinner : ∀ m ∈ Finset.range (m0 + 1),
        (∑ k, g k * (shiftLadderCoeff (lam k) m / s ^ (m + 1)))
          = (∑ k, g k * shiftLadderCoeff (lam k) m) / s ^ (m + 1) := by
      intro m _
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_div_assoc]
    rw [Finset.sum_congr rfl hinner, Finset.sum_range_succ]
    have hz : ∀ m ∈ Finset.range m0,
        (∑ k, g k * shiftLadderCoeff (lam k) m) / s ^ (m + 1) = 0 := by
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [hvan m hm, zero_div]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    ring
  rw [hid]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hdef k) (norm_nonneg _)

end

end GaloisForLFunctions.HTGeometry
