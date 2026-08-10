import GaloisForLFunctions.RHTower.Sieve.FibreDiagonalSplit

/-!
# The diagonal sum

Assembling `FibreDiagonal`: the diagonal part of the bilinear form is carried by the integers in
`[√x/2, √x + h]`, on which the kernel is at most `h√x/m + 1`, so

```text
∑_m f(m)²·K(m,m) ≤ ∑_{⌈√x/2⌉ ≤ m ≤ ⌊√x + h⌋} ( h√x/m + 1 ) ≍ h√x + √x .
```

Against the target `o(h²√x)` this is smaller by a factor `h`; but it is exactly the size a termwise
bound would give for the *whole* form, the off-diagonal having `≍ h` times as many terms.  So the
diagonal is harmless and the off-diagonal is everything.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The diagonal sum.** -/
theorem fibre_diag_sum_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ∑ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
        f m * f m
          * (((outerBlock x h).filter
              (fun a => m ∈ innerFibre x h a ∧ m ∈ innerFibre x h a)).card : ℝ)
      ≤ ∑ m ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌊Real.sqrt x + h⌋₊,
          (h * Real.sqrt x / m + 1) := by
  classical
  set R := Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌊Real.sqrt x + h⌋₊ with hRdef
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  -- termwise
  have hstep : ∀ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
      f m * f m
          * (((outerBlock x h).filter
              (fun a => m ∈ innerFibre x h a ∧ m ∈ innerFibre x h a)).card : ℝ)
        ≤ if m ∈ R then h * Real.sqrt x / m + 1 else 0 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    by_cases hmem : m ∈ R
    · rw [if_pos hmem]
      have hK0 : (0 : ℝ) ≤ (((outerBlock x h).filter
          (fun a => m ∈ innerFibre x h a ∧ m ∈ innerFibre x h a)).card : ℝ) :=
        Nat.cast_nonneg _
      have hsq : f m * f m ≤ 1 := by
        have := hf m
        nlinarith [abs_le.1 this]
      have hdiag := fibre_kernel_diag_le hx.le hh hm1
      nlinarith [hK0, hsq, hdiag]
    · rw [if_neg hmem]
      have hout : ¬ (Real.sqrt x / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ Real.sqrt x + h) := by
        intro hc
        refine hmem ?_
        rw [hRdef, Finset.mem_Icc]
        exact ⟨Nat.ceil_le.2 hc.1, Nat.le_floor hc.2⟩
      rw [fibre_diag_kernel_eq_zero hx hout]
      simp
  refine le_trans (Finset.sum_le_sum hstep) ?_
  -- the indicator sum is at most the sum over `R`
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    exact (Finset.mem_filter.1 hm).2
  · intro m _ _
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    positivity

end RHTower.Sieve

end
