import GaloisForLFunctions.HTGeometry.GevreyFormalSeries

/-!
# A submultiplicative Gevrey bound

The plain Gevrey bound `‖aₙ‖ ≤ C Aⁿ (n!)^r` is not submultiplicative: a Cauchy product picks up the
factor `n+1` from the size of the antidiagonal, which forces the geometric base to grow at every
multiplication.  Weighting by `(n+1)²` repairs this, because

```text
(n+1)² ∑_{i+j=n} 1/((i+1)²(j+1)²) ≤ 16 ,
```

so the weighted bounds multiply with a fixed constant and a fixed base.  That is what lets a
nonlinear recursion see the **square** of the size of a perturbation rather than merely its first
power.

The displayed inequality comes from `(a+b)² ≤ 4(a²+b²)` together with `1/min² ≤ 1/a² + 1/b²` and the
elementary bound `∑_{k<n} 1/(k+1)² ≤ 2`.
-/

open PowerSeries
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The convolution weight -/

theorem sum_inv_sq_le_two (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        norm_num
      · -- the stronger telescoping bound is not needed: reuse the tail estimate
        have hstrong : ∀ k : ℕ, 1 ≤ k →
            ∑ j ∈ Finset.range k, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / (k : ℝ) := by
          intro k hk
          induction k with
          | zero => omega
          | succ k ihk =>
              rcases Nat.eq_zero_or_pos k with hk0 | hk0
              · subst hk0
                norm_num
              · have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
                have hprev := ihk hk0
                have hstep' : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
                  rw [div_sub_div _ _ (ne_of_gt hk1) (by positivity),
                    div_le_div_iff₀ (by positivity) (by positivity)]
                  ring_nf
                  nlinarith [hk1]
                rw [Finset.sum_range_succ]
                have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
                rw [hcast]
                linarith
        have hres := hstrong (n + 1) (by omega)
        have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hinv : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
        linarith

/-- **The convolution weight is bounded.**  The antidiagonal sum of the inverse squares is
`O(1/(n+1)²)`. -/
theorem antidiagonal_inv_sq_le (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2) ≤ 16 := by
  classical
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
        ≤ (4 / ((n : ℝ) + 1) ^ 2)
          * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2) := by
    intro p hp
    have hsum : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
    have ha : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
    have hn : ((n : ℝ) + 1) ≤ ((p.1 : ℝ) + 1) + ((p.2 : ℝ) + 1) := by
      have : ((p.1 + p.2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hsum
      push_cast at this ⊢
      linarith
    have hkey : ((n : ℝ) + 1) ^ 2 ≤ 4 * (((p.1 : ℝ) + 1) ^ 2 + ((p.2 : ℝ) + 1) ^ 2) := by
      nlinarith [hn, ha, hb, sq_nonneg (((p.1 : ℝ) + 1) - ((p.2 : ℝ) + 1))]
    rw [div_le_iff₀ (by positivity)]
    have hexp : (4 / ((n : ℝ) + 1) ^ 2)
          * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2)
          * (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
        = 4 * (((p.2 : ℝ) + 1) ^ 2 + ((p.1 : ℝ) + 1) ^ 2) / ((n : ℝ) + 1) ^ 2 := by
      field_simp
    rw [hexp, le_div_iff₀ (by positivity)]
    nlinarith [hkey]
  have hsplit : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (4 / ((n : ℝ) + 1) ^ 2)
        * ((1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 + (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2)
      = (4 / ((n : ℝ) + 1) ^ 2)
        * ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2)
          + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  have hfirst : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 ≤ 2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2) n]
    exact sum_inv_sq_le_two (n + 1)
  have hsecond : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2 ≤ 2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => (1 : ℝ) / ((p.2 : ℝ) + 1) ^ 2) n]
    have hproj : ∀ k : ℕ, ((k, n - k) : ℕ × ℕ).2 = n - k := fun _ => rfl
    simp only [hproj]
    have hrefl := Finset.sum_range_reflect (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) (n + 1)
    have heq : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (((n - k : ℕ) : ℝ) + 1) ^ 2
        = ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
      rw [← hrefl]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 3
      omega
    rw [heq]
    exact sum_inv_sq_le_two (n + 1)
  have hbound : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
      ≤ (4 / ((n : ℝ) + 1) ^ 2) * 4 := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  calc ((n : ℝ) + 1) ^ 2 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
      ≤ ((n : ℝ) + 1) ^ 2 * ((4 / ((n : ℝ) + 1) ^ 2) * 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 16 := by
        field_simp
        norm_num

end GaloisForLFunctions.HTGeometry
