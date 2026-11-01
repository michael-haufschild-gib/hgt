import GaloisForLFunctions.HTGeometry.SubexponentialIntegerGrowth
import GaloisForLFunctions.HeckeKreinToeplitz.GrowthReadsTheDepthOfTheDeepestPair

/-!
# Subexponential scalar recurrences have unit modulus

A nonzero two-sided scalar recurrence exposes geometric growth in both
integer directions. The finite exponential non-cancellation theorem,
applied to one node, forces the multiplier and its inverse into the
closed unit disk.
-/

noncomputable section
set_option autoImplicit false
open Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- A nonzero geometric sequence cannot grow subexponentially with modulus above one. -/
theorem norm_le_one_of_subexponential_geometric {a c : ℂ} (hc : c ≠ 0)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ,
      ‖c * a ^ n‖ ≤ C * Real.exp (ε * n)) : ‖a‖ ≤ 1 := by
  by_contra hn
  obtain ⟨r, hr, hra⟩ := exists_between (lt_of_not_ge hn)
  obtain ⟨C, hC⟩ := h (Real.log r) (Real.log_pos hr)
  have hexp (n : ℕ) : Real.exp (Real.log r * n) = r ^ n := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hr)]
  have hb (n : ℕ) : ‖∑ _i : Fin 1, c * a ^ n‖ ≤ C * r ^ n := by
    simpa only [Fin.sum_univ_one, hexp] using hC n
  exact hc (coeff_eq_zero_of_norm_le (ν := fun _ : Fin 1 => a)
    (fun i j _ => Subsingleton.elim i j) (fun _ => c)
    (zero_lt_one.trans hr) hb (i := 0) hra)

private theorem norm_le_one_of_backward_recurrence {f : ℤ → ℂ} {a : ℂ}
    (hf : HasSubexponentialIntegerGrowth f) (h0 : f 0 ≠ 0)
    (hrec : ∀ z : ℤ, a * f (z + 1) = f z) : ‖a‖ ≤ 1 := by
  have hneg (n : ℕ) : f (-(n : ℤ)) = f 0 * a ^ n := by
    induction n with
    | zero => simp only [Nat.cast_zero, neg_zero, pow_zero, mul_one]
    | succ n ih =>
      have he : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
      have hr := hrec (-((n + 1 : ℕ) : ℤ))
      rw [he, ih] at hr
      rw [pow_succ]
      calc
        f (-((n + 1 : ℕ) : ℤ)) = a * (f 0 * a ^ n) := hr.symm
        _ = _ := by ring
  apply norm_le_one_of_subexponential_geometric h0
  intro ε hε
  obtain ⟨C, _, hC⟩ := hf ε hε
  refine ⟨C, fun n => ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simpa only [hneg, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg hn] using
    hC (-(n : ℤ))

/-- Two-sided subexponential growth forces a nonzero scalar recurrence onto the unit circle. -/
theorem norm_eq_one_of_subexponential_recurrence {f : ℤ → ℂ} {a : ℂ}
    (hf : HasSubexponentialIntegerGrowth f) (h0 : f 0 ≠ 0)
    (hrec : ∀ z : ℤ, a * f (z + 1) = f z) : ‖a‖ = 1 := by
  have ha : a ≠ 0 := by
    intro ha
    exact h0 (by simpa only [ha, zero_mul] using (hrec 0).symm)
  have hn := norm_le_one_of_backward_recurrence hf h0 hrec
  have hinvrec (z : ℤ) : a⁻¹ * f (-(z + 1)) = f (-z) := by
    have he : -(z + 1) + 1 = -z := by omega
    have hr := hrec (-(z + 1))
    rw [he] at hr
    rw [← hr, inv_mul_cancel_left₀ ha]
  have hi := norm_le_one_of_backward_recurrence hf.reflect h0 hinvrec
  have hm : ‖a‖ * ‖a⁻¹‖ = 1 := by rw [← norm_mul, mul_inv_cancel₀ ha, norm_one]
  have hl := mul_le_mul_of_nonneg_left hi (norm_nonneg a)
  rw [hm, mul_one] at hl
  exact le_antisymm hn hl

#print axioms norm_eq_one_of_subexponential_recurrence

end GaloisForLFunctions.HeckeKreinToeplitz
