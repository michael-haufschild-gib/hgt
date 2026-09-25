import GaloisForLFunctions.RHTower.HadamardRegularizationLaw
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Translation positivity is free; reflection positivity is a comparison

The Gram matrices that come free from the prime side are **Toeplitz**: their entries depend on
`m − n`, because the explicit formula is translation covariant.  The Gram matrices a zero criterion
needs are **Hankel**: their entries depend on `m + n`, because the functional equation is a
reflection.  The two forms differ by one sign, and that sign is everything:

`∑_{m,n} u_m u_n cos((m−n)x) = C² + S²`,
`∑_{m,n} u_m u_n cos((m+n)x) = C² − S²`,

with `C = ∑ u_m cos(mx)` and `S = ∑ u_m sin(mx)`.

So the translation form is a sum of squares and is nonnegative for every weight and every frequency,
with no hypothesis — that is the free positivity.  The reflection form is a **difference** of
squares.  It is not a positivity at all but a comparison, `S² ≤ C²`, and a single atom at `x = π/2`
with weight on the index `1` already makes it `−1`.

No amount of positivity yields a comparison.  This is the same shape as the failure of the factorial
regularization — there the multiplier's off-diagonal entry exceeded the geometric mean of its
diagonal — and it is why the free prime-side positivity has never transported to any criterion.
-/

open Finset

namespace RHTower

variable {N : ℕ}

/-- The even part of a weight against a frequency. -/
noncomputable def cosPart (x : ℝ) (u : Fin N → ℝ) : ℝ :=
  ∑ m : Fin N, u m * Real.cos ((m : ℕ) * x)

/-- The odd part of a weight against a frequency. -/
noncomputable def sinPart (x : ℝ) (u : Fin N → ℝ) : ℝ :=
  ∑ m : Fin N, u m * Real.sin ((m : ℕ) * x)

/-- **The translation form is a sum of squares.** -/
theorem translation_form_eq (x : ℝ) (u : Fin N → ℝ) :
    (∑ m : Fin N, ∑ n : Fin N,
        u m * u n * Real.cos (((m : ℕ) : ℝ) * x - ((n : ℕ) : ℝ) * x))
      = cosPart x u ^ 2 + sinPart x u ^ 2 := by
  have hsplit : ∀ m n : Fin N,
      u m * u n * Real.cos (((m : ℕ) : ℝ) * x - ((n : ℕ) : ℝ) * x)
        = (u m * Real.cos ((m : ℕ) * x)) * (u n * Real.cos ((n : ℕ) * x))
          + (u m * Real.sin ((m : ℕ) * x)) * (u n * Real.sin ((n : ℕ) * x)) := by
    intro m n
    rw [Real.cos_sub]
    ring
  calc (∑ m : Fin N, ∑ n : Fin N,
        u m * u n * Real.cos (((m : ℕ) : ℝ) * x - ((n : ℕ) : ℝ) * x))
      = ∑ m : Fin N, ∑ n : Fin N,
          ((u m * Real.cos ((m : ℕ) * x)) * (u n * Real.cos ((n : ℕ) * x))
            + (u m * Real.sin ((m : ℕ) * x)) * (u n * Real.sin ((n : ℕ) * x))) :=
        Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hsplit m n))
    _ = cosPart x u ^ 2 + sinPart x u ^ 2 := by
        rw [cosPart, sinPart, sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun m _ => Finset.sum_add_distrib)

/-- **The reflection form is a difference of squares.** -/
theorem reflection_form_eq (x : ℝ) (u : Fin N → ℝ) :
    (∑ m : Fin N, ∑ n : Fin N,
        u m * u n * Real.cos (((m : ℕ) : ℝ) * x + ((n : ℕ) : ℝ) * x))
      = cosPart x u ^ 2 - sinPart x u ^ 2 := by
  have hsplit : ∀ m n : Fin N,
      u m * u n * Real.cos (((m : ℕ) : ℝ) * x + ((n : ℕ) : ℝ) * x)
        = (u m * Real.cos ((m : ℕ) * x)) * (u n * Real.cos ((n : ℕ) * x))
          - (u m * Real.sin ((m : ℕ) * x)) * (u n * Real.sin ((n : ℕ) * x)) := by
    intro m n
    rw [Real.cos_add]
    ring
  calc (∑ m : Fin N, ∑ n : Fin N,
        u m * u n * Real.cos (((m : ℕ) : ℝ) * x + ((n : ℕ) : ℝ) * x))
      = ∑ m : Fin N, ∑ n : Fin N,
          ((u m * Real.cos ((m : ℕ) * x)) * (u n * Real.cos ((n : ℕ) * x))
            - (u m * Real.sin ((m : ℕ) * x)) * (u n * Real.sin ((n : ℕ) * x))) :=
        Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hsplit m n))
    _ = cosPart x u ^ 2 - sinPart x u ^ 2 := by
        rw [cosPart, sinPart, sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun m _ => Finset.sum_sub_distrib _ _)

/-- **The free positivity.**  The translation form is nonnegative for every weight and every
frequency, with no hypothesis. -/
theorem translation_form_nonneg (x : ℝ) (u : Fin N → ℝ) :
    0 ≤ ∑ m : Fin N, ∑ n : Fin N,
        u m * u n * Real.cos (((m : ℕ) : ℝ) * x - ((n : ℕ) : ℝ) * x) := by
  rw [translation_form_eq]
  positivity

/-- **The reflection form is a comparison, not a positivity.**  It is nonnegative exactly when the
odd part is dominated by the even part. -/
theorem reflection_form_nonneg_iff (x : ℝ) (u : Fin N → ℝ) :
    0 ≤ (∑ m : Fin N, ∑ n : Fin N,
        u m * u n * Real.cos (((m : ℕ) : ℝ) * x + ((n : ℕ) : ℝ) * x))
      ↔ sinPart x u ^ 2 ≤ cosPart x u ^ 2 := by
  rw [reflection_form_eq, sub_nonneg]

/-- **A single atom already breaks it.**  At the frequency `π/2` with the weight on the index `1`
the reflection form is `−1`. -/
theorem reflection_form_neg_witness :
    (∑ m : Fin 2, ∑ n : Fin 2,
        (![0, 1] : Fin 2 → ℝ) m * (![0, 1] : Fin 2 → ℝ) n *
          Real.cos (((m : ℕ) : ℝ) * (Real.pi / 2) + ((n : ℕ) : ℝ) * (Real.pi / 2))) = -1 := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  have hpi : (1 : ℝ) * (Real.pi / 2) + 1 * (Real.pi / 2) = Real.pi := by ring
  rw [hpi, Real.cos_pi]
  ring

end RHTower
