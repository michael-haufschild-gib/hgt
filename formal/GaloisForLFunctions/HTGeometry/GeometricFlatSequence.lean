import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Geometrically small sequences are flat to all orders

A sequence bounded by `C·r^m` with `r < 1` is, for every `k`, the weight `(m+1)^{-k}` times a
bounded sequence.  In the bounded-sequence algebra with weight `w_m = 1/(m+1)` this says exactly
that the sequence lies in every power `w^k A`, that is, in the bornological Krull radical.

The only analytic input is that a polynomial times a geometric sequence tends to zero, hence is
bounded.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A polynomial weight times a geometric sequence is bounded. -/
theorem exists_bound_pow_mul_geometric (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, ((m : ℝ) + 1) ^ k * r ^ m ≤ B := by
  have habs : |r| < 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  rcases eq_or_lt_of_le hr0 with hr | hrpos
  · refine ⟨1, zero_le_one, fun m => ?_⟩
    cases m with
    | zero => simp
    | succ p =>
        rw [← hr]
        simp
  · have hf := tendsto_pow_const_mul_const_pow_of_abs_lt_one k habs
    have hshift : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r ^ (n + 1)) atTop (nhds 0) :=
      hf.comp (tendsto_add_atTop_nat 1)
    have hval : ∀ n : ℕ, ((n : ℝ) + 1) ^ k * r ^ n
        = (((n + 1 : ℕ) : ℝ) ^ k * r ^ (n + 1)) / r := by
      intro n
      push_cast
      field_simp
      rw [pow_succ]
    have hdiv : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) atTop (nhds 0) := by
      have hq := hshift.div_const r
      rw [zero_div] at hq
      exact hq.congr fun n => (hval n).symm
    obtain ⟨B, hB⟩ := hdiv.bddAbove_range
    refine ⟨max B 0, le_max_right _ _, fun m => ?_⟩
    exact le_trans (hB ⟨m, rfl⟩) (le_max_left _ _)

/-- Decay faster than a fixed geometric rate. -/
def IsGeometricallySmall {E : Type*} [NormedAddCommGroup E] (D : ℕ → E) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧ ∀ m, ‖D m‖ ≤ C * r ^ m

/-- **Flatness to all orders.**  A geometrically small sequence is the weight `(m+1)^{-k}` times a
bounded sequence, for every `k`. -/
theorem IsGeometricallySmall.exists_bounded_quotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : ℕ → E} (hD : IsGeometricallySmall D) (k : ℕ) :
    ∃ (g : ℕ → E) (B : ℝ), (∀ m, ‖g m‖ ≤ B) ∧
      ∀ m, D m = (((m : ℝ) + 1) ^ k)⁻¹ • g m := by
  obtain ⟨C, r, hC, hr0, hr1, hbound⟩ := hD
  obtain ⟨B, hB0, hB⟩ := exists_bound_pow_mul_geometric k hr0 hr1
  refine ⟨fun m => (((m : ℝ) + 1) ^ k) • D m, C * B, fun m => ?_, fun m => ?_⟩
  · have hpow : (0 : ℝ) < ((m : ℝ) + 1) ^ k := by positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpow]
    calc ((m : ℝ) + 1) ^ k * ‖D m‖ ≤ ((m : ℝ) + 1) ^ k * (C * r ^ m) :=
          mul_le_mul_of_nonneg_left (hbound m) hpow.le
      _ = C * (((m : ℝ) + 1) ^ k * r ^ m) := by ring
      _ ≤ C * B := mul_le_mul_of_nonneg_left (hB m) hC
  · have hpow : (((m : ℝ) + 1) ^ k) ≠ 0 := by positivity
    rw [smul_smul, inv_mul_cancel₀ hpow, one_smul]

/-- A geometrically small sequence with one nonzero coordinate is a nonzero flat element. -/
theorem IsGeometricallySmall.ne_zero_of_coordinate {E : Type*} [NormedAddCommGroup E]
    {D : ℕ → E} {m : ℕ} (hm : D m ≠ 0) : D ≠ 0 := by
  intro h0
  exact hm (by rw [h0]; rfl)

end

end GaloisForLFunctions.HTGeometry
