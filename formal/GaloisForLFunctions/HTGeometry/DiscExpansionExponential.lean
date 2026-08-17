import GaloisForLFunctions.HTGeometry.DiscExpansionCalculus

/-!
# Powers and exponentials of truncated expansions

Iterating the product rule expands every power of a function that has an expansion, with a constant
growing linearly in the exponent.  If in addition the function vanishes to first order at the origin,
its exponential is expanded by the truncated exponential series of its polynomial: the tail of the
exponential series is already of the required order, because each further term carries one more power
of the argument.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section PowersAndExp

/-- **Powers of an expansion.** -/
theorem HasPolyExpansion.pow {r C M : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ M) (hPb : ∀ w : ℂ, ‖w‖ ≤ r → ‖P.eval w‖ ≤ M)
    (hM1 : 1 ≤ M) (hC : 0 ≤ C) (j : ℕ) :
    HasPolyExpansion r n (C * (j : ℝ) * M ^ j) (fun w => (f w) ^ j) (P ^ j) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  induction j with
  | zero =>
      intro w hw
      simp
  | succ j ih =>
      have hPjb : ∀ w : ℂ, ‖w‖ ≤ r → ‖(P ^ j).eval w‖ ≤ M ^ j := by
        intro w hw
        rw [Polynomial.eval_pow, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hPb w hw) j
      have hmul := HasPolyExpansion.mul (f := fun w => (f w) ^ j) (g := f)
        (P := P ^ j) (Q := P) ih hf hfb hPjb (by positivity)
      have hfun : (fun w => (f w) ^ j * f w) = fun w => (f w) ^ (j + 1) := by
        funext w
        rw [pow_succ]
      rw [hfun, ← pow_succ] at hmul
      intro w hw
      refine le_trans (hmul w hw) ?_
      have hconst : C * (j : ℝ) * M ^ j * M + M ^ j * C
          ≤ C * ((j : ℝ) + 1) * M ^ (j + 1) := by
        have h1 : M ^ j ≤ M ^ (j + 1) := by
          refine pow_le_pow_right₀ hM1 (by omega)
        have h2 : C * (j : ℝ) * M ^ j * M = C * (j : ℝ) * M ^ (j + 1) := by
          rw [pow_succ]
          ring
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        nlinarith [h1, h2, hC, pow_nonneg hM0 j]
      have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact mul_le_mul_of_nonneg_right hconst (by positivity)

/-- **The exponential of an expansion that vanishes to first order.** -/
theorem HasPolyExpansion.cexp {r C M K : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P)
    (hfb : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ M) (hPb : ∀ w : ℂ, ‖w‖ ≤ r → ‖P.eval w‖ ≤ M)
    (hM1 : 1 ≤ M) (hC : 0 ≤ C)
    (hsmall : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ K * ‖w‖)
    (htiny : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ / ((n : ℝ) + 1) ≤ 1 / 2) :
    HasPolyExpansion r n
      (2 * K ^ n / (Nat.factorial n : ℝ)
        + ∑ j ∈ Finset.range n, C * (j : ℝ) * M ^ j / (Nat.factorial j : ℝ))
      (fun w => Complex.exp (f w))
      (∑ j ∈ Finset.range n, Polynomial.C (((Nat.factorial j : ℕ) : ℂ)⁻¹) * P ^ j) := by
  intro w hw
  have hpolyeval : (∑ j ∈ Finset.range n,
      Polynomial.C (((Nat.factorial j : ℕ) : ℂ)⁻¹) * P ^ j).eval w
      = ∑ j ∈ Finset.range n, ((P ^ j).eval w) / ((Nat.factorial j : ℕ) : ℂ) := by
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, div_eq_inv_mul]
  have hsplit : Complex.exp (f w)
      - (∑ j ∈ Finset.range n, Polynomial.C (((Nat.factorial j : ℕ) : ℂ)⁻¹) * P ^ j).eval w
      = (Complex.exp (f w)
          - ∑ j ∈ Finset.range n, (f w) ^ j / ((Nat.factorial j : ℕ) : ℂ))
        + ∑ j ∈ Finset.range n,
            ((f w) ^ j - (P ^ j).eval w) / ((Nat.factorial j : ℕ) : ℂ) := by
    rw [hpolyeval]
    have hsum : ∑ j ∈ Finset.range n,
        ((f w) ^ j - (P ^ j).eval w) / ((Nat.factorial j : ℕ) : ℂ)
        = (∑ j ∈ Finset.range n, (f w) ^ j / ((Nat.factorial j : ℕ) : ℂ))
          - ∑ j ∈ Finset.range n, ((P ^ j).eval w) / ((Nat.factorial j : ℕ) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [sub_div]
    rw [hsum]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hexpb : ‖Complex.exp (f w)
      - ∑ j ∈ Finset.range n, (f w) ^ j / ((Nat.factorial j : ℕ) : ℂ)‖
      ≤ 2 * K ^ n / (Nat.factorial n : ℝ) * ‖w‖ ^ n := by
    have h := Complex.exp_bound' (x := f w) (n := n) (by
      have := htiny w hw
      simpa using this)
    refine le_trans h ?_
    have hfn : ‖f w‖ ^ n ≤ (K * ‖w‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (hsmall w hw) n
    have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    rw [mul_pow] at hfn
    calc ‖f w‖ ^ n / (Nat.factorial n : ℝ) * 2
        ≤ (K ^ n * ‖w‖ ^ n) / (Nat.factorial n : ℝ) * 2 := by
          gcongr
      _ = 2 * K ^ n / (Nat.factorial n : ℝ) * ‖w‖ ^ n := by ring
  have htermb : ‖∑ j ∈ Finset.range n,
      ((f w) ^ j - (P ^ j).eval w) / ((Nat.factorial j : ℕ) : ℂ)‖
      ≤ (∑ j ∈ Finset.range n, C * (j : ℝ) * M ^ j / (Nat.factorial j : ℝ)) * ‖w‖ ^ n := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hpow := HasPolyExpansion.pow hf hfb hPb hM1 hC j w hw
    have hfacpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    rw [norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hfacpos]
    calc ‖(f w) ^ j - (P ^ j).eval w‖
        ≤ C * (j : ℝ) * M ^ j * ‖w‖ ^ n := hpow
      _ = C * (j : ℝ) * M ^ j / (Nat.factorial j : ℝ) * ‖w‖ ^ n * (Nat.factorial j : ℝ) := by
          field_simp
  linarith [hexpb, htermb]

end PowersAndExp

end

end GaloisForLFunctions.HTGeometry
