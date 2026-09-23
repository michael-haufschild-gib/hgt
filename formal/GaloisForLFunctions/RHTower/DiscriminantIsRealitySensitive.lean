import GaloisForLFunctions.RHTower.SeparationVersusReality

/-!
# Reality-sensitive unconditional tools exist: the discriminant

The previous entry closed the last lane pointing at the refutation witness, and listed as an open
category a **reality-sensitive** — as opposed to separation-sensitive — unconditional theorem.  That
category is not empty, and this file exhibits its canonical member, correcting the terminal statement.

**The discriminant.**  For a real polynomial with roots `r₁, …, r_n`, the discriminant is
`∏_{i<j}(r_i - r_j)²` up to a positive factor.  If every root is real, every factor is a square of a
real number, so the discriminant is nonnegative.  Contrapositively:

> **A negative discriminant refutes real-rootedness — unconditionally, and by a polynomial in the
> coefficients.  The discriminant is reality-sensitive, codimension-sensitive, polynomial, and needs
> no contour, no spectrum and no separation hypothesis.**

**Applied to the hypothesis.**  The Jensen polynomials of `Ξ` are built from its Taylor coefficients,
and the hypothesis implies every one of them is real-rooted, hence has nonnegative discriminant.  A
single negative discriminant refutes it.  This is the same shape as the symmetric-function ladder
found earlier — one negative value at one place refutes — but in a variable that detects **reality**
rather than positivity.

**Correction to the terminal statement.**  The earlier claim that no reality-sensitive unconditional
tool was available is too strong.  Such tools exist; what they lack is not sensitivity but
**decidability**: the discriminants of the low-degree Jensen polynomials are not known to be
nonnegative for all indices, and the known results establish it only for large index at each fixed
degree.  The open category is therefore not empty but hard.

This file formalizes the nonnegativity of a product of squares, the refutation from a negative
discriminant, and the quadratic case in closed form.
-/

open Finset

noncomputable section

namespace RHTower

/-- **A product of squares of real numbers is nonnegative.**  This is the discriminant's positivity
when all roots are real. -/
theorem prod_sq_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    0 ≤ ∏ i ∈ s, (f i) ^ (2 : ℕ) :=
  Finset.prod_nonneg (fun i _ => sq_nonneg (f i))

/-- **A negative value refutes.**  If the product of squares is negative, the values are not all
real — contrapositive of the previous statement. -/
theorem neg_refutes_reality {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∏ i ∈ s, (f i) ^ (2 : ℕ) < 0) : False := by
  exact absurd (prod_sq_nonneg s f) (not_le.mpr h)

/-- **The quadratic case.**  For `a x² + b x + c` with `a ≠ 0`, real roots force `b² - 4ac ≥ 0`. -/
theorem quadratic_discriminant_nonneg {a b c r : ℝ} (_ha : a ≠ 0)
    (hroot : a * r ^ (2 : ℕ) + b * r + c = 0) : 0 ≤ b ^ (2 : ℕ) - 4 * a * c := by
  have hfac : b ^ (2 : ℕ) - 4 * a * c = (2 * a * r + b) ^ (2 : ℕ) := by
    have h4 : 4 * a * (a * r ^ (2 : ℕ) + b * r + c) = 0 := by rw [hroot]; ring
    nlinarith [h4]
  rw [hfac]
  exact sq_nonneg _

/-- **And a negative discriminant excludes a real root.** -/
theorem no_real_root_of_neg_discriminant {a b c : ℝ} (ha : a ≠ 0)
    (hd : b ^ (2 : ℕ) - 4 * a * c < 0) : ∀ r : ℝ, a * r ^ (2 : ℕ) + b * r + c ≠ 0 := by
  intro r hroot
  exact absurd (quadratic_discriminant_nonneg ha hroot) (not_le.mpr hd)

/-- **The category is nonempty.**  A reality-sensitive unconditional criterion exists: nonnegativity
of the discriminant, polynomial in the coefficients. -/
theorem reality_sensitive_criterion_exists {a b c : ℝ} (ha : a ≠ 0) :
    (∃ r : ℝ, a * r ^ (2 : ℕ) + b * r + c = 0) → 0 ≤ b ^ (2 : ℕ) - 4 * a * c := by
  rintro ⟨r, hr⟩
  exact quadratic_discriminant_nonneg ha hr

end RHTower
