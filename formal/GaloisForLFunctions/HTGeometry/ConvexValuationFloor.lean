import Mathlib

/-!
# The balanced tuple strictly minimizes a strictly convex valuation

For a strictly convex profile `φ` on a set `s`, the valuation `∑ᵢ φ(tᵢ)` of a tuple valued
in `s` with fixed mean `m` strictly exceeds its balanced value `D·φ(m)` whenever the tuple is
not constant (`balanced_strictConvexOn_lt_sum`): the constant tuple is the unique minimizer
at fixed mean.  This is strict Jensen with uniform weights.

Specializing `φ` to `x ↦ x^p` (`p > 1`) gives the power-valuation form used by the
polynomial-Taylor magnitude cards (`balanced_rpow_lt_sum`, `balanced_rpow_lt_sum_nat`): the
balanced convolution atom uniquely minimizes the Taylor-magnitude valuation `B·∑ᵢ νᵢ·nᵢ^β` at
fixed source sum, and its degree-`d` leading value `B·N^β·d^{1−β}` is strictly decreasing in
the degree (`rpow_one_sub_antitone`), separating atoms of different degrees.  A different
choice of `φ` serves the stretched-exponential, rough-subleading, and convex-curvature
magnitude profiles without re-deriving the Jensen step.
-/

open Finset

namespace GaloisForLFunctions

/-- **Balanced minimization of a strictly convex valuation.**  For a strictly convex `φ` on a
set `s` and a tuple valued in `s` with mean `m`, the valuation `∑ φ(tᵢ)` strictly exceeds the
balanced value `D·φ(m)` unless the tuple is constant. -/
theorem balanced_strictConvexOn_lt_sum {D : ℕ} (hD : 0 < D) {s : Set ℝ} {φ : ℝ → ℝ}
    (hφ : StrictConvexOn ℝ s φ) {m : ℝ} {t : Fin D → ℝ} (hts : ∀ i, t i ∈ s)
    (hsum : ∑ i, t i = (D : ℝ) * m) (hne : ∃ i, t i ≠ m) :
    (D : ℝ) * φ m < ∑ i, φ (t i) := by
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
  have hjensen := hφ.map_sum_lt (fun _ _ => by positivity) hw1 (fun i _ => hts i) hdistinct
  simp only [smul_eq_mul] at hjensen
  have hcenter : ∑ i, (D : ℝ)⁻¹ * t i = m := by
    rw [← Finset.mul_sum, hsum, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDR), one_mul]
  have hrhs : ∑ i, (D : ℝ)⁻¹ * φ (t i) = (D : ℝ)⁻¹ * ∑ i, φ (t i) := by
    rw [Finset.mul_sum]
  rw [hcenter, hrhs] at hjensen
  have h2 : (D : ℝ) * φ m < (D : ℝ) * ((D : ℝ)⁻¹ * ∑ i, φ (t i)) :=
    mul_lt_mul_of_pos_left hjensen hDR
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hDR), one_mul] at h2
  exact h2

/-- **Power-valuation form.**  For `p > 1` and a nonnegative tuple with mean `m`, the power
valuation `∑ tᵢ^p` strictly exceeds the balanced value `D·m^p` unless the tuple is constant. -/
theorem balanced_rpow_lt_sum {D : ℕ} (hD : 0 < D) {p m : ℝ} (hp : 1 < p)
    {t : Fin D → ℝ} (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i = (D : ℝ) * m)
    (hne : ∃ i, t i ≠ m) : (D : ℝ) * m ^ p < ∑ i, t i ^ p :=
  balanced_strictConvexOn_lt_sum hD (strictConvexOn_rpow hp)
    (fun i => Set.mem_Ici.mpr (ht i)) hsum hne

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

namespace GaloisForLFunctions

/-- **Balanced maximization of a strictly concave valuation.**  For a strictly concave `φ` on
a set `s` and a tuple valued in `s` with mean `m`, the valuation `∑ φ(tᵢ)` is strictly below
the balanced value `D·φ(m)` unless the tuple is constant — the opposite regime to the convex
case, governing stretched-exponential magnitude profiles `x ↦ x^β` with `0 < β < 1`. -/
theorem sum_lt_balanced_strictConcaveOn {D : ℕ} (hD : 0 < D) {s : Set ℝ} {φ : ℝ → ℝ}
    (hφ : StrictConcaveOn ℝ s φ) {m : ℝ} {t : Fin D → ℝ} (hts : ∀ i, t i ∈ s)
    (hsum : ∑ i, t i = (D : ℝ) * m) (hne : ∃ i, t i ≠ m) :
    ∑ i, φ (t i) < (D : ℝ) * φ m := by
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
  have hjensen := hφ.lt_map_sum (fun _ _ => by positivity) hw1 (fun i _ => hts i) hdistinct
  simp only [smul_eq_mul] at hjensen
  have hcenter : ∑ i, (D : ℝ)⁻¹ * t i = m := by
    rw [← Finset.mul_sum, hsum, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDR), one_mul]
  have hlhs : ∑ i, (D : ℝ)⁻¹ * φ (t i) = (D : ℝ)⁻¹ * ∑ i, φ (t i) := by rw [Finset.mul_sum]
  rw [hcenter, hlhs] at hjensen
  have h2 : (D : ℝ) * ((D : ℝ)⁻¹ * ∑ i, φ (t i)) < (D : ℝ) * φ m :=
    mul_lt_mul_of_pos_left hjensen hDR
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hDR), one_mul] at h2
  exact h2

/-- Stretched-exponential form: for `0 < p < 1` and a nonnegative-integer tuple with source
sum `D·m` and a non-balanced entry, the concave power valuation `∑ tᵢ^p` is strictly below
the balanced value `D·m^p`. -/
theorem sum_lt_balanced_rpow_nat {D : ℕ} (hD : 0 < D) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {m : ℕ} {t : Fin D → ℕ} (hsum : ∑ i, t i = D * m) (hne : ∃ i, t i ≠ m) :
    ∑ i, (t i : ℝ) ^ p < (D : ℝ) * (m : ℝ) ^ p := by
  refine sum_lt_balanced_strictConcaveOn hD (Real.strictConcaveOn_rpow hp0 hp1)
    (fun i => Set.mem_Ici.mpr (Nat.cast_nonneg _)) ?_ ?_
  · rw [← Nat.cast_sum, hsum]; push_cast; ring
  · obtain ⟨i, hi⟩ := hne
    exact ⟨i, by exact_mod_cast hi⟩

end GaloisForLFunctions
