import GaloisForLFunctions.RHTower.Sieve.EnergyCauchySchwarz

/-!
# Assembling the shell estimates

Two bounds are available for each reciprocal cofactor shell: one uniform in the shell index and one
decaying geometrically in it.  Cutting the shell range at the index where they cross, the uniform
bound is paid on the initial segment and the geometric bound sums on the tail, so the total cost is
the uniform bound times the cut index plus the geometric bound at it.
-/

namespace RHTower.Sieve

open Real

noncomputable section

theorem exp_neg_one_lt_one : Real.exp (-1) < 1 := by
  have h : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.2 (by norm_num)
  rwa [Real.exp_zero] at h

theorem inv_one_sub_exp_neg_one_le_two : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
  have h1 : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ he]
    linarith
  have h0 : (0 : ℝ) < 1 - Real.exp (-1) := by
    have := Real.exp_pos (-1 : ℝ)
    linarith
  rw [inv_le_iff_one_le_mul₀ h0]
  linarith

/-- The geometric tail of `exp (-k)` beyond an index. -/
theorem sum_exp_neg_tail_le (K₀ K : ℕ) :
    ∑ k ∈ Finset.Ico K₀ K, Real.exp (-(k : ℝ)) ≤ 2 * Real.exp (-(K₀ : ℝ)) := by
  classical
  set r : ℝ := Real.exp (-1) with hr
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := exp_neg_one_lt_one
  have hpow : ∀ k : ℕ, Real.exp (-(k : ℝ)) = r ^ k := by
    intro k
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  have hrw : ∑ k ∈ Finset.Ico K₀ K, Real.exp (-(k : ℝ))
      = ∑ j ∈ Finset.range (K - K₀), r ^ (K₀ + j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => hpow (K₀ + j)
  rw [hrw]
  have hfac : ∀ j : ℕ, r ^ (K₀ + j) = r ^ K₀ * r ^ j := fun j => pow_add r K₀ j
  rw [funext hfac, ← Finset.mul_sum]
  have hgeo : ∑ j ∈ Finset.range (K - K₀), r ^ j ≤ (1 - r)⁻¹ := by
    have hsum := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum
      (Finset.range (K - K₀)) (fun i _ => by positivity)
    rwa [tsum_geometric_of_lt_one hr0 hr1] at hsum
  have hK₀ : (0 : ℝ) ≤ r ^ K₀ := by positivity
  calc r ^ K₀ * ∑ j ∈ Finset.range (K - K₀), r ^ j
      ≤ r ^ K₀ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeo hK₀
    _ ≤ r ^ K₀ * 2 := mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two hK₀
    _ = 2 * Real.exp (-(K₀ : ℝ)) := by rw [hpow K₀]; ring

/-- **The shell assembly.**  The uniform bound is paid on the initial segment, the geometric bound
on the tail. -/
theorem shell_assembly_le {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) {S : ℕ → ℝ}
    (hu : ∀ k, S k ≤ c₁) (hg : ∀ k, S k ≤ c₂ * Real.exp (-(k : ℝ)))
    (K₀ K : ℕ) :
    ∑ k ∈ Finset.range K, S k ≤ c₁ * (K₀ : ℝ) + 2 * c₂ * Real.exp (-(K₀ : ℝ)) := by
  classical
  rcases le_or_gt K K₀ with hK | hK
  · have hhead : ∑ k ∈ Finset.range K, S k ≤ c₁ * (K : ℝ) := by
      calc ∑ k ∈ Finset.range K, S k ≤ ∑ _k ∈ Finset.range K, c₁ :=
            Finset.sum_le_sum fun k _ => hu k
        _ = c₁ * (K : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hmono : c₁ * (K : ℝ) ≤ c₁ * (K₀ : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ hc₁
      exact_mod_cast hK
    have htail : (0 : ℝ) ≤ 2 * c₂ * Real.exp (-(K₀ : ℝ)) := by positivity
    linarith
  · have hsplit : ∑ k ∈ Finset.range K, S k
        = (∑ k ∈ Finset.range K₀, S k) + ∑ k ∈ Finset.Ico K₀ K, S k := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le K₀) hK.le]
    rw [hsplit]
    have hhead : ∑ k ∈ Finset.range K₀, S k ≤ c₁ * (K₀ : ℝ) := by
      calc ∑ k ∈ Finset.range K₀, S k ≤ ∑ _k ∈ Finset.range K₀, c₁ :=
            Finset.sum_le_sum fun k _ => hu k
        _ = c₁ * (K₀ : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have htail : ∑ k ∈ Finset.Ico K₀ K, S k ≤ 2 * c₂ * Real.exp (-(K₀ : ℝ)) := by
      calc ∑ k ∈ Finset.Ico K₀ K, S k
          ≤ ∑ k ∈ Finset.Ico K₀ K, c₂ * Real.exp (-(k : ℝ)) :=
            Finset.sum_le_sum fun k _ => hg k
        _ = c₂ * ∑ k ∈ Finset.Ico K₀ K, Real.exp (-(k : ℝ)) := by rw [Finset.mul_sum]
        _ ≤ c₂ * (2 * Real.exp (-(K₀ : ℝ))) :=
            mul_le_mul_of_nonneg_left (sum_exp_neg_tail_le K₀ K) hc₂
        _ = 2 * c₂ * Real.exp (-(K₀ : ℝ)) := by ring
    linarith

end

end RHTower.Sieve
