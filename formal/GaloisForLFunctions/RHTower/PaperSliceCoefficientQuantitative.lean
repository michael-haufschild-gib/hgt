import GaloisForLFunctions.RHTower.PaperSliceCoefficientRepair

/-! # Quantitative bounds retaining the full signed source

Entire Taylor convergence gives arbitrary geometric coefficient and operator-tail
bounds. Native high-order positivity bounds the exact minimum repair rank by the
number of even orders below its logarithmic threshold.
-/

noncomputable section

namespace RHTower.PaperSliceCoefficient

def radiusBudget (t R : ℝ) : ℝ := ∑' n, ‖xiSliceCoeff t n * (R : ℂ) ^ n‖

theorem summable_radius (t R : ℝ) :
    Summable (fun n => ‖xiSliceCoeff t n * (R : ℂ) ^ n‖) :=
  (hasSum_xiSliceCoeff t (R : ℂ)).summable.norm

theorem radiusBudget_nonneg (t R : ℝ) : 0 ≤ radiusBudget t R :=
  tsum_nonneg fun _ => norm_nonneg _

theorem coefficient_radius_bound (t R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ‖xiSliceCoeff t n‖ * R ^ n ≤ radiusBudget t R := by
  have h := (summable_radius t R).le_tsum n (fun _ _ => norm_nonneg _)
  simpa only [radiusBudget, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hR] using h

theorem coefficient_geometric_bound (t R : ℝ) (hR : 0 < R) (n : ℕ) :
    ‖xiSliceCoeff t n‖ ≤ radiusBudget t R / R ^ n :=
  (le_div_iff₀ (pow_pos hR n)).2 (coefficient_radius_bound t R hR.le n)

theorem coefficient_tail_bound (t R : ℝ) (hR : 1 ≤ R) {N n : ℕ} (hn : N ≤ n) :
    ‖xiSliceCoeff t n‖ ≤ radiusBudget t R / R ^ N := by
  apply (le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hR) N)).2
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hn) (norm_nonneg _)).trans
    (coefficient_radius_bound t R (zero_le_one.trans hR) n)

def coefficientPrefix (t : ℝ) (N : ℕ) : EllTwo →L[ℂ] EllTwo :=
  diagonalOperator (truncMultiplier (xiSliceCoeff t) N)
    (norm_truncMultiplier_le (norm_source_le_budget t) N)

theorem hasRankLE_prefix (t : ℝ) (N : ℕ) : HasRankLE (coefficientPrefix t N) N :=
  hasRankLE_diagonalOperator_trunc (xiSliceCoeff t) (norm_source_le_budget t) N

theorem norm_sub_prefix_le (t R : ℝ) (hR : 1 ≤ R) (N : ℕ) :
    ‖operator t - coefficientPrefix t N‖ ≤ radiusBudget t R / R ^ N := by
  let tail : ℕ → ℂ := fun n => if n < N then 0 else xiSliceCoeff t n
  have hb : ∀ n, ‖tail n‖ ≤ radiusBudget t R / R ^ N := by
    intro n
    dsimp [tail]
    split_ifs with hn
    · simpa only [norm_zero] using div_nonneg (radiusBudget_nonneg t R)
        (pow_nonneg (zero_le_one.trans hR) N)
    · exact coefficient_tail_bound t R hR (Nat.le_of_not_gt hn)
  have heq : operator t - coefficientPrefix t N = diagonalOperator tail hb := by
    ext f n
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, operator_apply_source, coefficientPrefix,
      diagonalOperator_apply, truncMultiplier, tail]
    split_ifs <;> simp
  rw [heq]
  exact norm_diagonalOperator_le _ _

theorem exists_negative_count_bound : ∃ K κ : ℝ, ∀ t : Height, ∀ N : ℕ,
    max K (κ * Real.log t) ≤ (N : ℝ) → negativeCount t ≤ N := by
  classical
  obtain ⟨K, κ, h⟩ := exists_negative_order_bound
  refine ⟨K, κ, fun t N hN => ?_⟩
  have hs : negatives t ⊆ (Finset.range N).image (fun k => 2 * k) := by
    intro n hn
    obtain ⟨k, rfl, hk⟩ := h t n ((mem_negatives t n).1 hn)
    have hkN : k < N := by exact_mod_cast hk.trans_le hN
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkN, rfl⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (Finset.card_range N))

theorem exists_bounded_positive_repair : ∃ K κ : ℝ, ∀ t : Height, ∀ N : ℕ,
    max K (κ * Real.log t) ≤ (N : ℝ) →
      ∃ C : EllTwo →L[ℂ] EllTwo, HasRankLE C N ∧ (operator t + C).IsPositive := by
  obtain ⟨K, κ, h⟩ := exists_negative_count_bound
  exact ⟨K, κ, fun t N hN => (positive_repair_rank_iff t N).2 (h t N hN)⟩

end RHTower.PaperSliceCoefficient
