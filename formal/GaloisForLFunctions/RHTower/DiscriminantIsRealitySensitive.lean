import GaloisForLFunctions.RHTower.SeparationVersusReality

/-!
# The quadratic discriminant and products of squares

* `prod_sq_nonneg`, `neg_refutes_reality`: a finite product of squares of reals is nonnegative.
* `quadratic_discriminant_nonneg`, `no_real_root_of_neg_discriminant`,
  `reality_sensitive_criterion_exists`: a real quadratic `ax² + bx + c` (`a ≠ 0`) with a real root has
  `b² − 4ac ≥ 0`.

These are the degree-two case of the fact that the discriminant `∏_{i<j}(r_i − r_j)²` of a polynomial
with real roots is nonnegative.  Nothing here concerns the Jensen polynomials of `Ξ` or their
discriminants.
-/

open Finset

noncomputable section

namespace RHTower

/-- A finite product of squares of reals is nonnegative. -/
theorem prod_sq_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    0 ≤ ∏ i ∈ s, (f i) ^ (2 : ℕ) :=
  Finset.prod_nonneg (fun i _ => sq_nonneg (f i))

/-- A finite product of squares of reals is not negative. -/
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

/-- A real quadratic with negative discriminant has no real root. -/
theorem no_real_root_of_neg_discriminant {a b c : ℝ} (ha : a ≠ 0)
    (hd : b ^ (2 : ℕ) - 4 * a * c < 0) : ∀ r : ℝ, a * r ^ (2 : ℕ) + b * r + c ≠ 0 := by
  intro r hroot
  exact absurd (quadratic_discriminant_nonneg ha hroot) (not_le.mpr hd)

/-- A real quadratic with a real root has nonnegative discriminant. -/
theorem reality_sensitive_criterion_exists {a b c : ℝ} (ha : a ≠ 0) :
    (∃ r : ℝ, a * r ^ (2 : ℕ) + b * r + c = 0) → 0 ≤ b ^ (2 : ℕ) - 4 * a * c := by
  rintro ⟨r, hr⟩
  exact quadratic_discriminant_nonneg ha hr

end RHTower
