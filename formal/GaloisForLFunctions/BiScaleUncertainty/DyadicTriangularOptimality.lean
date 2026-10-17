import GaloisForLFunctions.BiScaleUncertainty.DyadicAnchoredProducer

/-!
# Triangular weights realize the sharp anchored minimum

The explicit average of symmetric chains is precisely a positive triangular
allocation on the signed dyadic nodes. This identifies the attaining weights,
not merely a Hilbert-space vector with a desirable norm.
-/

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
open RHTower.ArchimedeanAnomaly
noncomputable section

/-- Coefficient at each of the two nodes with exponent `k + 1`. -/
def triangle (m k : ℕ) : ℝ := ((m : ℝ) - (k : ℝ)) / ((m : ℝ) + 1)

theorem triangle_pos (m k : ℕ) (hk : k < m) : 0 < triangle m k := by
  have h : (k : ℝ) < m := by exact_mod_cast hk
  exact div_pos (sub_pos.mpr h) (by positivity)

theorem triangle_le_one (m k : ℕ) : triangle m k ≤ 1 := by
  unfold triangle
  apply (div_le_one (by positivity : 0 < (m : ℝ) + 1)).mpr
  linarith only [Nat.cast_nonneg (α := ℝ) k]

private def weightedChain (m : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ((m : ℂ) + 1) • edge 0 + Finset.sum (Finset.range m) (fun k =>
    ((m : ℂ) - (k : ℂ)) • edge (-((k : ℤ) + 1)) +
      ((m : ℂ) - (k : ℂ)) • edge ((k : ℤ) + 1))

private theorem weightedChain_succ (m : ℕ) :
    weightedChain (m + 1) = weightedChain m + chain (m + 1) := by
  have hc (k : ℕ) :
      ((m : ℂ) + 1 - (k : ℂ)) • edge (-((k : ℤ) + 1)) +
          ((m : ℂ) + 1 - (k : ℂ)) • edge ((k : ℤ) + 1) =
        (((m : ℂ) - (k : ℂ)) • edge (-((k : ℤ) + 1)) +
          ((m : ℂ) - (k : ℂ)) • edge ((k : ℤ) + 1)) +
          (edge (-((k : ℤ) + 1)) + edge ((k : ℤ) + 1)) := by
    simp only [show (m : ℂ) + 1 - (k : ℂ) = ((m : ℂ) - (k : ℂ)) + 1 by ring,
      add_smul, one_smul]
    abel
  simp only [weightedChain, chain, anchoredPacket, Finset.sum_range_succ,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_one, one_smul]
  simp_rw [hc]
  rw [Finset.sum_add_distrib]
  simp only [sub_self, zero_smul, zero_add]
  simp only [add_smul, one_smul]
  abel

private theorem weightedChain_eq_sum (m : ℕ) :
    weightedChain m = ∑ k ∈ Finset.range (m + 1), chain k := by
  induction m with
  | zero => simp [weightedChain, chain, anchoredPacket]
  | succ m ih =>
    rw [weightedChain_succ, ih, Finset.sum_range_succ _ (m + 1)]

private theorem scale_triangle_packet (m : ℕ) :
    ((m : ℂ) + 1) • anchoredPacket m (triangle m) (triangle m) = weightedChain m := by
  have hc0 : (m : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (m : ℝ) + 1 ≠ 0 by positivity)
  have hc (k : ℕ) : ((m : ℂ) + 1) * (triangle m k : ℂ) = (m : ℂ) - (k : ℂ) := by
    unfold triangle
    push_cast
    field_simp [hc0]
  simp only [anchoredPacket, weightedChain, smul_add, Finset.smul_sum, smul_smul]
  simp_rw [hc]

/-- The producer is an actual anchored packet with positive explicit coefficients. -/
theorem triangle_attains (m : ℕ) : anchoredPacket m (triangle m) (triangle m) = producer m := by
  rw [producer, ← weightedChain_eq_sum, ← scale_triangle_packet, smul_smul]
  have hc : ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ((m : ℂ) + 1) = 1 := by
    have hc0 : (m : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (show (m : ℝ) + 1 ≠ 0 by positivity)
    push_cast
    exact inv_mul_cancel₀ hc0
  rw [hc, one_smul]

theorem triangle_exact_error (m : ℕ) :
    ‖anchoredPacket m (triangle m) (triangle m)‖ ^ 2 =
      autocorr source 0 / ((m : ℝ) + 1) := by
  rw [triangle_attains, producer_norm_sq]

private def leftTest (k : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ j ∈ Finset.range (k + 1), atom (-(j : ℤ))

private def rightTest (k : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ j ∈ Finset.range (k + 1), atom ((j : ℤ) + 1)

private theorem atom_leftTest_left (k j : ℕ) :
    inner ℂ (atom (-(j : ℤ))) (leftTest k) =
      if j ≤ k then (autocorr seed 0 : ℂ) else 0 := by
  rw [leftTest, inner_sum]
  by_cases h : j ≤ k
  · rw [if_pos h, Finset.sum_eq_single j]
    · rw [atom_inner, if_pos rfl]
    · intro i _ hi
      rw [atom_inner, if_neg (by omega : -(j : ℤ) ≠ -(i : ℤ))]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [atom_inner, if_neg (by omega : -(j : ℤ) ≠ -(i : ℤ))]

private theorem atom_leftTest_right (k j : ℕ) :
    inner ℂ (atom ((j : ℤ) + 1)) (leftTest k) = 0 := by
  rw [leftTest, inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [atom_inner, if_neg (by omega : (j : ℤ) + 1 ≠ -(i : ℤ))]

private theorem atom_rightTest_right (k j : ℕ) :
    inner ℂ (atom ((j : ℤ) + 1)) (rightTest k) =
      if j ≤ k then (autocorr seed 0 : ℂ) else 0 := by
  rw [rightTest, inner_sum]
  by_cases h : j ≤ k
  · rw [if_pos h, Finset.sum_eq_single j]
    · rw [atom_inner, if_pos rfl]
    · intro i _ hi
      rw [atom_inner, if_neg (by omega : (j : ℤ) + 1 ≠ (i : ℤ) + 1)]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [atom_inner, if_neg (by omega : (j : ℤ) + 1 ≠ (i : ℤ) + 1)]

private theorem atom_rightTest_left (k j : ℕ) :
    inner ℂ (atom (-(j : ℤ))) (rightTest k) = 0 := by
  rw [rightTest, inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [atom_inner, if_neg (by omega : -(j : ℤ) ≠ (i : ℤ) + 1)]

private theorem edge_leftTest_left (k j : ℕ) :
    inner ℂ (edge (-((j : ℤ) + 1))) (leftTest k) =
      if j = k then -(autocorr seed 0 : ℂ) else 0 := by
  rw [edge_eq, inner_sub_left, show -((j : ℤ) + 1) + 1 = -(j : ℤ) by omega]
  have h := atom_leftTest_left k (j + 1)
  push_cast at h
  rw [h, atom_leftTest_left]
  by_cases he : j = k
  · subst j
    simp
  · rcases lt_or_gt_of_ne he with hl | hr
    · simp [he, show j + 1 ≤ k by omega, show j ≤ k by omega]
    · simp [he, show ¬j + 1 ≤ k by omega, show ¬j ≤ k by omega]

private theorem edge_leftTest_right (k j : ℕ) :
    inner ℂ (edge ((j : ℤ) + 1)) (leftTest k) = 0 := by
  rw [edge_eq, inner_sub_left, atom_leftTest_right]
  have h := atom_leftTest_right k (j + 1)
  push_cast at h
  rw [h, sub_self]

private theorem edge_rightTest_right (k j : ℕ) :
    inner ℂ (edge ((j : ℤ) + 1)) (rightTest k) =
      if j = k then (autocorr seed 0 : ℂ) else 0 := by
  rw [edge_eq, inner_sub_left, atom_rightTest_right]
  have h := atom_rightTest_right k (j + 1)
  push_cast at h
  rw [h]
  by_cases he : j = k
  · subst j
    simp
  · rcases lt_or_gt_of_ne he with hl | hr
    · simp [he, show j + 1 ≤ k by omega, show j ≤ k by omega]
    · simp [he, show ¬j + 1 ≤ k by omega, show ¬j ≤ k by omega]

private theorem edge_rightTest_left (k j : ℕ) :
    inner ℂ (edge (-((j : ℤ) + 1))) (rightTest k) = 0 := by
  rw [edge_eq, inner_sub_left, show -((j : ℤ) + 1) + 1 = -(j : ℤ) by omega,
    atom_rightTest_left]
  have h := atom_rightTest_left k (j + 1)
  push_cast at h
  rw [h, sub_self]

private theorem packet_leftTest (m k : ℕ) (a b : ℕ → ℝ) (hk : k < m) :
    inner ℂ (anchoredPacket m a b) (leftTest k) =
      (autocorr seed 0 * (1 - a k) : ℝ) := by
  have h0 : inner ℂ (edge 0) (leftTest k) = (autocorr seed 0 : ℂ) := by
    have he : edge 0 = atom (-(0 : ℤ)) - atom ((0 : ℤ) + 1) := by simp [edge_eq]
    rw [he, inner_sub_left, atom_leftTest_left k 0, atom_leftTest_right k 0]
    simp
  rw [anchoredPacket, inner_add_left, h0, sum_inner]
  simp_rw [inner_add_left, inner_smul_left,
    edge_leftTest_left, edge_leftTest_right]
  simp only [Complex.conj_ofReal, mul_zero, add_zero]
  rw [Finset.sum_eq_single k]
  · simp only [if_pos rfl]
    push_cast
    ring
  · intro j _ hj
    rw [if_neg hj, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

private theorem packet_rightTest (m k : ℕ) (a b : ℕ → ℝ) (hk : k < m) :
    inner ℂ (anchoredPacket m a b) (rightTest k) =
      (autocorr seed 0 * (b k - 1) : ℝ) := by
  have h0 : inner ℂ (edge 0) (rightTest k) = -(autocorr seed 0 : ℂ) := by
    have he : edge 0 = atom (-(0 : ℤ)) - atom ((0 : ℤ) + 1) := by simp [edge_eq]
    rw [he, inner_sub_left, atom_rightTest_left k 0, atom_rightTest_right k 0]
    simp
  rw [anchoredPacket, inner_add_left, h0, sum_inner]
  simp_rw [inner_add_left, inner_smul_left,
    edge_rightTest_left, edge_rightTest_right]
  simp only [Complex.conj_ofReal, mul_zero, zero_add]
  rw [Finset.sum_eq_single k]
  · simp only [if_pos rfl]
    push_cast
    ring
  · intro j _ hj
    rw [if_neg hj, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

private theorem producer_leftTest_re (m k : ℕ) (hk : k ≤ m) :
    RCLike.re (inner ℂ (producer m) (leftTest k)) =
      autocorr seed 0 * ((k : ℝ) + 1) / ((m : ℝ) + 1) := by
  have hi : inner ℂ (leftTest k) (plateau m) =
      (((k : ℝ) + 1) * autocorr seed 0 : ℝ) := by
    rw [leftTest, sum_inner]
    have he (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
        inner ℂ (atom (-(j : ℤ))) (plateau m) = (autocorr seed 0 : ℂ) :=
      atom_inner_plateau_left m j (by have := Finset.mem_range.mp hj; omega)
    rw [Finset.sum_congr rfl he]
    simp
  rw [inner_re_symm, producer_eq_plateau, inner_smul_right, hi]
  rw [← Complex.ofReal_mul]
  change ((m : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * autocorr seed 0) =
    autocorr seed 0 * ((k : ℝ) + 1) / ((m : ℝ) + 1)
  ring

private theorem producer_rightTest_re (m k : ℕ) (hk : k ≤ m) :
    RCLike.re (inner ℂ (producer m) (rightTest k)) =
      -(autocorr seed 0 * ((k : ℝ) + 1) / ((m : ℝ) + 1)) := by
  have hi : inner ℂ (rightTest k) (plateau m) =
      (-(((k : ℝ) + 1) * autocorr seed 0) : ℝ) := by
    rw [rightTest, sum_inner]
    have he (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
        inner ℂ (atom ((j : ℤ) + 1)) (plateau m) = -(autocorr seed 0 : ℂ) :=
      atom_inner_plateau_right m j (by have := Finset.mem_range.mp hj; omega)
    rw [Finset.sum_congr rfl he]
    simp
  rw [inner_re_symm, producer_eq_plateau, inner_smul_right, hi]
  rw [← Complex.ofReal_mul]
  change ((m : ℝ) + 1)⁻¹ * (-(((k : ℝ) + 1) * autocorr seed 0)) =
    -(autocorr seed 0 * ((k : ℝ) + 1) / ((m : ℝ) + 1))
  ring

/-- Equality determines every active coefficient, on both signed arms. -/
theorem producer_coefficients_unique (m : ℕ) (a b : ℕ → ℝ) :
    anchoredPacket m a b = producer m ↔
      ∀ k < m, a k = triangle m k ∧ b k = triangle m k := by
  constructor
  · intro h k hk
    have hL := congrArg (fun v => RCLike.re (inner ℂ v (leftTest k))) h
    have hR := congrArg (fun v => RCLike.re (inner ℂ v (rightTest k))) h
    rw [packet_leftTest m k a b hk, producer_leftTest_re m k (by omega)] at hL
    rw [packet_rightTest m k a b hk, producer_rightTest_re m k (by omega)] at hR
    change autocorr seed 0 * (1 - a k) =
      autocorr seed 0 * ((k : ℝ) + 1) / ((m : ℝ) + 1) at hL
    change autocorr seed 0 * (b k - 1) =
      -(autocorr seed 0 * ((k : ℝ) + 1) / ((m : ℝ) + 1)) at hR
    have hl : 1 - a k = ((k : ℝ) + 1) / ((m : ℝ) + 1) := by
      apply mul_left_cancel₀ seed_energy_pos.ne'
      simpa only [mul_div_assoc] using hL
    have hr : b k - 1 = -(((k : ℝ) + 1) / ((m : ℝ) + 1)) := by
      apply mul_left_cancel₀ seed_energy_pos.ne'
      simpa only [mul_div_assoc, mul_neg] using hR
    unfold triangle
    field_simp at hl hr ⊢
    constructor <;> nlinarith only [hl, hr]
  · intro h
    rw [← triangle_attains m]
    unfold anchoredPacket
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [(h k (Finset.mem_range.mp hk)).1, (h k (Finset.mem_range.mp hk)).2]

theorem anchoredPacket_minimum_iff_triangle (m : ℕ) (a b : ℕ → ℝ) :
    ‖anchoredPacket m a b‖ ^ 2 = autocorr source 0 / ((m : ℝ) + 1) ↔
      ∀ k < m, a k = triangle m k ∧ b k = triangle m k := by
  rw [anchoredPacket_minimum_iff, producer_coefficients_unique]

end
end GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
