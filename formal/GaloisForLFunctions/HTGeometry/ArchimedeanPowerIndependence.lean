import GaloisForLFunctions.HTGeometry.ArchimedeanNoFlatCancellation

/-!
# Independence of the descending powers modulo the next one

`three_term_expansion_eq_zero` is the case `M = 1` of the general principle the finite-order
Stirling ladder needs: the scales `1, 1/t, …, 1/t^M` are independent modulo `O(t^{-(M+1)})`.

The induction is one line of algebra: the constant term is killed by letting `t → ∞`, and what is
left is `t^{-1}` times an expansion of one order less, so multiplying by `t` restores the shape.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- A vector dominated by `C/t` for arbitrarily large `t` is zero. -/
theorem eq_zero_of_norm_le_const_div {x : ℂ} {C R : ℝ}
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t → ‖x‖ ≤ C / t) : x = 0 := by
  by_contra hne
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hne
  set T : ℝ := max (max R 1) (C / ‖x‖ + 1) with hTdef
  have hTR : R ≤ T := le_trans (le_max_left R 1) (le_max_left _ _)
  have hT1 : 1 ≤ T := le_trans (le_max_right R 1) (le_max_left _ _)
  have hTbig : C / ‖x‖ + 1 ≤ T := le_max_right _ _
  have hT0 : (0 : ℝ) < T := by linarith
  have hb := h T hTR hT1
  rw [le_div_iff₀ hT0] at hb
  have hgt : C / ‖x‖ < T := by linarith
  rw [div_lt_iff₀ hpos] at hgt
  nlinarith [hb, hgt]

/-- **The descending powers are independent modulo the next one.** -/
theorem power_expansion_eq_zero : ∀ (M : ℕ) (a : ℕ → ℂ) (K R : ℝ),
    (∀ t : ℝ, R ≤ t → 1 ≤ t →
      ‖∑ m ∈ Finset.range (M + 1), a m / (((t : ℝ) : ℂ)) ^ m‖ ≤ K / t ^ (M + 1)) →
    ∀ m ∈ Finset.range (M + 1), a m = 0 := by
  intro M
  induction M with
  | zero =>
      intro a K R h m hm
      simp only [Finset.mem_range] at hm
      have hm0 : m = 0 := by omega
      subst hm0
      refine eq_zero_of_norm_le_const_div (C := K) (R := R) fun t hR ht1 => ?_
      have hb := h t hR ht1
      simpa using hb
  | succ M ih =>
      intro a K R h
      have ht0' : ∀ t : ℝ, 1 ≤ t → (0 : ℝ) < t := fun t ht => by linarith
      -- the constant coefficient
      have hzero : a 0 = 0 := by
        refine eq_zero_of_norm_le_const_div
          (C := K + ∑ m ∈ Finset.range (M + 1), ‖a (m + 1)‖) (R := R) fun t hR ht1 => ?_
        have ht0 : (0 : ℝ) < t := ht0' t ht1
        have htc : ‖((t : ℝ) : ℂ)‖ = t := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        have hsplit : ∑ m ∈ Finset.range (M + 2), a m / (((t : ℝ) : ℂ)) ^ m
            = a 0 + ∑ m ∈ Finset.range (M + 1), a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1) := by
          rw [Finset.sum_range_succ']
          simp
          ring
        have hmain := h t hR ht1
        rw [hsplit] at hmain
        have htail : ‖∑ m ∈ Finset.range (M + 1), a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1)‖
            ≤ (∑ m ∈ Finset.range (M + 1), ‖a (m + 1)‖) / t := by
          refine le_trans (norm_sum_le _ _) ?_
          rw [Finset.sum_div]
          refine Finset.sum_le_sum fun m _ => ?_
          rw [norm_div, norm_pow, htc]
          rw [div_le_div_iff₀ (by positivity) ht0]
          have hpow : t ≤ t ^ (m + 1) := by
            calc t = t ^ 1 := (pow_one t).symm
              _ ≤ t ^ (m + 1) := pow_le_pow_right₀ ht1 (by omega)
          nlinarith [norm_nonneg (a (m + 1)), hpow, ht0]
        have hKle : K / t ^ (M + 2) ≤ K / t := by
          have hK0 : 0 ≤ K := by
            have hnn := norm_nonneg (a 0 +
              ∑ m ∈ Finset.range (M + 1), a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1))
            have := le_trans hnn hmain
            rw [le_div_iff₀ (by positivity)] at this
            nlinarith [this, pow_pos ht0 (M + 2)]
          rw [div_le_div_iff₀ (by positivity) ht0]
          have hpow : t ≤ t ^ (M + 2) := by
            calc t = t ^ 1 := (pow_one t).symm
              _ ≤ t ^ (M + 2) := pow_le_pow_right₀ ht1 (by omega)
          nlinarith [hK0, hpow, ht0]
        have hstep : ‖a 0‖ ≤ ‖a 0 + ∑ m ∈ Finset.range (M + 1),
            a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1)‖
            + ‖∑ m ∈ Finset.range (M + 1), a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1)‖ := by
          have hid : a 0 = (a 0 + ∑ m ∈ Finset.range (M + 1),
              a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1))
              - ∑ m ∈ Finset.range (M + 1), a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1) := by ring
          calc ‖a 0‖ = ‖(a 0 + ∑ m ∈ Finset.range (M + 1),
                a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1))
                - ∑ m ∈ Finset.range (M + 1), a (m + 1) / (((t : ℝ) : ℂ)) ^ (m + 1)‖ := by
                rw [← hid]
            _ ≤ _ := norm_sub_le _ _
        have hsum : K / t + (∑ m ∈ Finset.range (M + 1), ‖a (m + 1)‖) / t
            = (K + ∑ m ∈ Finset.range (M + 1), ‖a (m + 1)‖) / t := by ring
        linarith [hstep, hmain, hKle, htail, hsum.le, hsum.ge]
      -- shift down
      have hshift : ∀ m ∈ Finset.range (M + 1), a (m + 1) = 0 := by
        refine ih (fun m => a (m + 1)) K R fun t hR ht1 => ?_
        have ht0 : (0 : ℝ) < t := ht0' t ht1
        have htne : (((t : ℝ) : ℂ)) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact ht0.ne'
        have htc : ‖((t : ℝ) : ℂ)‖ = t := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        have hsplit : ∑ m ∈ Finset.range (M + 2), a m / (((t : ℝ) : ℂ)) ^ m
            = (∑ m ∈ Finset.range (M + 1), a (m + 1) / (((t : ℝ) : ℂ)) ^ m)
              / ((t : ℝ) : ℂ) := by
          rw [Finset.sum_range_succ', hzero]
          rw [Finset.sum_div]
          simp only [add_zero, pow_zero, div_one]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [div_div, ← pow_succ]
        have hmain := h t hR ht1
        rw [hsplit, norm_div, htc] at hmain
        rw [div_le_div_iff₀ ht0 (by positivity)] at hmain
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < t ^ (M + 1))]
        have hpowid : t ^ (M + 1 + 1) = t ^ (M + 1) * t := by ring
        rw [hpowid] at hmain
        nlinarith [hmain, ht0, pow_pos ht0 (M + 1)]
      intro m hm
      simp only [Finset.mem_range] at hm
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact hzero
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        exact hshift j (Finset.mem_range.mpr (by omega))

end

end GaloisForLFunctions.HTGeometry
