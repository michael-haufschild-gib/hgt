import GaloisForLFunctions.RHTower.Sieve.FibreDiagonal

/-!
# Splitting the bilinear form

The fibre mean square, separated into its diagonal and off-diagonal parts:

```text
∑_{a ∈ outerBlock} (∑_{b ∈ innerFibre a} f(b))²
  = ∑_m f(m)²·K(m,m) + ∑_m ∑_{n ≠ m} f(m)·f(n)·K(m,n) .
```

The diagonal is bounded by `FibreDiagonal` and, by `fibre_kernel_support`, is carried by the `≍ √x`
integers in `[√x/2, √x + h]`, giving `≍ h√x + √x`.  Everything the theorem asserts beyond that lives
in the second sum.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The diagonal kernel vanishes outside the reachable range. -/
theorem fibre_diag_kernel_eq_zero {x h : ℝ} (hx : 0 < x) {m : ℕ}
    (hout : ¬ (Real.sqrt x / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ Real.sqrt x + h)) :
    (outerBlock x h).filter
        (fun a => m ∈ innerFibre x h a ∧ m ∈ innerFibre x h a) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
  rw [Finset.mem_filter] at ha
  exact hout (fibre_kernel_support hx ha.1 ha.2.1)

/-- **The bilinear form, split into diagonal and off-diagonal.** -/
theorem sum_fibreSq_diag_split (f : ℕ → ℝ) (x h : ℝ) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      = (∑ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
            f m * f m
              * (((outerBlock x h).filter
                  (fun a => m ∈ innerFibre x h a ∧ m ∈ innerFibre x h a)).card : ℝ))
        + ∑ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
            ∑ n ∈ (Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊).erase m,
              f m * f n
                * (((outerBlock x h).filter
                    (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℝ) := by
  classical
  rw [sum_fibreSq_eq_count f x h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  exact (Finset.add_sum_erase _ _ hm).symm

end RHTower.Sieve

end
