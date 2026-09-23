import Mathlib

/-!
# The constraint-coordinate Bessel inputs are Bessel's inequality

The CCM constrained-prolate transfer carries two hypotheses on the constraint coordinates
`ℓ : ℝ → ℕ → ℝ`:

```text
hsum    : Summable fun j => ℓ lam j ^ (2 : ℕ)
hbessel : (∑' j, ℓ lam j ^ (2 : ℕ)) ≤ 2 * lam
```

If the coordinates are the expansion of one vector against an orthonormal family — which is what
they are, the family being the prolate basis and the vector the constraint functional — then both
are Bessel's inequality, and the only content is the norm of that vector.

For the band-limited setting the constraint vector is the reproducing kernel of the Paley–Wiener
space at the origin, whose squared norm is `K(0,0) = lam/π`.  Since `1/π < 2` the bound holds with a
factor of more than six to spare, so `hbessel` is not a sharp constraint on the construction.
-/

open RCLike

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Both constraint-coordinate hypotheses from Bessel.**  If the coordinates are inner products
of a fixed vector against an orthonormal family, summability and the bound follow from the vector's
norm alone. -/
theorem constraint_bessel_of_orthonormal {e : ℕ → E} (he : Orthonormal ℝ e) {v : E} {lam : ℝ}
    (hnorm : ‖v‖ ^ (2 : ℕ) ≤ 2 * lam) :
    (Summable fun j => (inner ℝ (e j) v : ℝ) ^ (2 : ℕ)) ∧
      (∑' j, (inner ℝ (e j) v : ℝ) ^ (2 : ℕ)) ≤ 2 * lam := by
  have hsq : ∀ j : ℕ, ‖(inner ℝ (e j) v : ℝ)‖ ^ (2 : ℕ) = (inner ℝ (e j) v : ℝ) ^ (2 : ℕ) := by
    intro j
    rw [Real.norm_eq_abs, sq_abs]
  constructor
  · have := he.inner_products_summable (x := v)
    simpa [hsq] using this
  · have := he.tsum_inner_products_le (x := v)
    simp only [hsq] at this
    exact le_trans this hnorm

/-- The Paley–Wiener margin: the reproducing-kernel norm `lam/π` satisfies the required bound with
room, since `1/π < 2`. -/
theorem paleyWiener_kernel_norm_le {lam : ℝ} (hlam : 0 ≤ lam) :
    lam / Real.pi ≤ 2 * lam := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpos : (0 : ℝ) < Real.pi := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **The discharge, in the form the transfer consumes.**  With the constraint vector taken to be
the band-limited evaluation kernel, whose squared norm is `lam/π`, both hypotheses hold. -/
theorem constraint_bessel_of_paleyWiener {e : ℕ → E} (he : Orthonormal ℝ e) {v : E} {lam : ℝ}
    (hlam : 0 ≤ lam) (hker : ‖v‖ ^ (2 : ℕ) = lam / Real.pi) :
    (Summable fun j => (inner ℝ (e j) v : ℝ) ^ (2 : ℕ)) ∧
      (∑' j, (inner ℝ (e j) v : ℝ) ^ (2 : ℕ)) ≤ 2 * lam :=
  constraint_bessel_of_orthonormal he (by rw [hker]; exact paleyWiener_kernel_norm_le hlam)

end RHTower
