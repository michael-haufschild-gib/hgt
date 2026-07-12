import Mathlib

/-!
# The balanced tuple strictly minimizes a strictly convex power valuation

For an exponent `p > 1`, the valuation `∑ᵢ tᵢ^p` of a nonnegative tuple with fixed sum
`∑ᵢ tᵢ = D·m` is strictly larger than its balanced value `D·m^p` whenever the tuple is not
constant (`balanced_rpow_lt_sum`).  This is strict Jensen for the strictly convex map
`x ↦ x^p`: the only minimizer at fixed mean is the constant tuple.  Read on Taylor-magnitude
valuations `B·∑ᵢ νᵢ·nᵢ^β`, the balanced convolution atom uniquely minimizes the valuation at
fixed source sum, and its degree-`d` leading value `B·N^β·d^{1−β}` is strictly decreasing in
the degree (`rpow_one_sub_antitone`), separating atoms of different degrees.
-/

open Finset

namespace GaloisForLFunctions

/-- **Balanced minimization of a strictly convex power valuation.**  For `p > 1` and a
nonnegative tuple with mean `m`, the power valuation `∑ tᵢ^p` strictly exceeds the balanced
value `D·m^p` unless the tuple is constant. -/
theorem balanced_rpow_lt_sum {D : ℕ} (hD : 0 < D) {p m : ℝ} (hp : 1 < p)
    {t : Fin D → ℝ} (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = (D : ℝ) * m)
    (hne : ∃ i, t i ≠ m) : (D : ℝ) * m ^ p < ∑ i, t i ^ p := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hdistinct : ∃ j ∈ (univ : Finset (Fin D)), ∃ k ∈ (univ : Finset (Fin D)), t j ≠ t k := by
    obtain ⟨i, hi⟩ := hne
    by_contra hcon
    push Not at hcon
    apply hi
    have hall : ∀ k, t k = t i := fun k => hcon k (mem_univ k) i (mem_univ i)
    have hval : (D : ℝ) * t i = (D : ℝ) * m := by
      rw [← hsum, Finset.sum_congr rfl (fun k _ => hall k), Finset.sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    exact mul_left_cancel₀ (ne_of_gt hDR) hval
  have hw1 : ∑ _i : Fin D, (D : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ (ne_of_gt hDR)]
  have hjensen := (strictConvexOn_rpow hp).map_sum_lt
    (fun _ _ => by positivity) hw1 (fun i _ => Set.mem_Ici.mpr (ht i)) hdistinct
  simp only [smul_eq_mul] at hjensen
  have hcenter : ∑ i, (D : ℝ)⁻¹ * t i = m := by
    rw [← Finset.mul_sum, hsum, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDR), one_mul]
  have hrhs : ∑ i, (D : ℝ)⁻¹ * t i ^ p = (D : ℝ)⁻¹ * ∑ i, t i ^ p := by
    rw [Finset.mul_sum]
  rw [hcenter, hrhs] at hjensen
  have h2 : (D : ℝ) * m ^ p < (D : ℝ) * ((D : ℝ)⁻¹ * ∑ i, t i ^ p) :=
    mul_lt_mul_of_pos_left hjensen hDR
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hDR), one_mul] at h2
  exact h2

/-- Natural-index form: a nonnegative-integer tuple with source sum `D·m` and a non-balanced
entry has power valuation strictly above `D·m^p`. -/
theorem balanced_rpow_lt_sum_nat {D : ℕ} (hD : 0 < D) {p : ℝ} (hp : 1 < p) {m : ℕ}
    {t : Fin D → ℕ} (hsum : ∑ i, t i = D * m) (hne : ∃ i, t i ≠ m) :
    (D : ℝ) * (m : ℝ) ^ p < ∑ i, (t i : ℝ) ^ p := by
  refine balanced_rpow_lt_sum hD hp (fun i => Nat.cast_nonneg _) ?_ ?_
  · rw [← Nat.cast_sum, hsum]; push_cast; ring
  · obtain ⟨i, hi⟩ := hne
    exact ⟨i, by exact_mod_cast hi⟩

/-- The degree-scaling factor `d ↦ d^{1−β}` of the balanced leading value is strictly
antitone for `β > 1`: higher-degree balanced atoms have strictly smaller leading valuation
at fixed source sum. -/
theorem rpow_one_sub_antitone {β : ℝ} (hβ : 1 < β) {d e : ℝ} (hd : 0 < d) (hde : d < e) :
    e ^ (1 - β) < d ^ (1 - β) :=
  Real.rpow_lt_rpow_of_neg hd hde (by linarith)

end GaloisForLFunctions
