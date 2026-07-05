/-
# The Hermite two-term boundary (Lemma R structure, task #139)

Doc 25 §3.1 / doc 34: the (E5) two-term section expansion at an `m`-fold zero is
`aₘ σᵐ (uᵐ − C(m,2) uᵐ⁻²)`. This equals `aₘ σᵐ Heₘ(u)` — closing the cluster splitting with
NO further terms — exactly when `Heₘ` itself has only two terms, i.e. `m ≤ 3`:

* `He₂ = X² − 1 = X² − C(2,2)`,  `He₃ = X³ − 3X = X³ − C(3,2)X`  — two terms, matched;
* `He₄ = X⁴ − 6X² + 3` — the trailing `+3 = C(4,2)·C(2,2)/…` is a THIRD term, so the two-term
  expansion misses it: this is precisely why `m ≥ 4` needs the full heat-resummed Lemma R
  (all cumulant orders), while `m ≤ 3` is unconditional from (E5) alone.

These are the exact probabilists' Hermite values (mathlib `Polynomial.hermite`, via the
recurrence `Heₙ₊₁ = X·Heₙ − Heₙ'`); `decide` cannot evaluate polynomial equality, so they are
derived from `hermite_succ`.
-/
import Mathlib

namespace RHTower

open Polynomial

theorem hermite_one_eq : (Polynomial.hermite 1 : Polynomial ℤ) = X := by
  rw [hermite_succ, hermite_zero]; simp

/-- `He₂ = X² − 1` — the two-term form `X² − C(2,2)`. -/
theorem hermite_two_eq : (Polynomial.hermite 2 : Polynomial ℤ) = X ^ 2 - 1 := by
  rw [hermite_succ, hermite_one_eq, derivative_X]
  ring

/-- `He₃ = X³ − 3X` — the two-term form `X³ − C(3,2)·X`. -/
theorem hermite_three_eq : (Polynomial.hermite 3 : Polynomial ℤ) = X ^ 3 - 3 * X := by
  rw [hermite_succ, hermite_two_eq]
  simp only [derivative_sub, derivative_pow, derivative_X, derivative_one, map_ofNat,
    Nat.cast_ofNat, mul_one]
  ring

/-- `He₄ = X⁴ − 6X² + 3` — THREE terms: the trailing `+3` is beyond the two-term (E5)
expansion, so `m = 4` clusters are the first that need the full heat-resummed Lemma R. -/
theorem hermite_four_eq : (Polynomial.hermite 4 : Polynomial ℤ) = X ^ 4 - 6 * X ^ 2 + 3 := by
  rw [hermite_succ, hermite_three_eq]
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
    map_ofNat, Nat.cast_ofNat, mul_one, zero_mul, zero_add]
  ring

/-- **The two-term boundary**: for `m ≤ 3` the probabilists' Hermite polynomial IS the
two-term `Xᵐ − C(m,2)·Xᵐ⁻²`, so doc 25's (E5) two-term expansion closes the cluster splitting
unconditionally; `He₄ ≠ X⁴ − 6X²` (`= X⁴ − C(4,2)X²`) shows the two-term form first fails at
`m = 4`, which is exactly where Lemma R (all cumulant orders) becomes necessary. -/
theorem hermite_two_term_boundary :
    (Polynomial.hermite 2 : Polynomial ℤ) = X ^ 2 - 1 ∧
    (Polynomial.hermite 3 : Polynomial ℤ) = X ^ 3 - 3 * X ∧
    (Polynomial.hermite 4 : Polynomial ℤ) ≠ X ^ 4 - 6 * X ^ 2 := by
  refine ⟨hermite_two_eq, hermite_three_eq, ?_⟩
  rw [hermite_four_eq]
  intro h
  have h3 : (3 : Polynomial ℤ) = 0 := by linear_combination h
  simp at h3

/-- Real evaluation `He₂(u) = u² − 1`. -/
theorem aeval_hermite_two (u : ℝ) :
    (Polynomial.aeval u (Polynomial.hermite 2) : ℝ) = u ^ 2 - 1 := by
  rw [hermite_two_eq]
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]

/-- Real evaluation `He₃(u) = u³ − 3u`. -/
theorem aeval_hermite_three (u : ℝ) :
    (Polynomial.aeval u (Polynomial.hermite 3) : ℝ) = u ^ 3 - 3 * u := by
  rw [hermite_three_eq]
  simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, map_ofNat]

/-- **Cluster–Hermite scaling (m ≤ 3).** At the cluster scale, the (E5) two-term section form
`aₘ σᵐ (uᵐ − C(m,2) uᵐ⁻²)` equals `aₘ σᵐ Heₘ(u)` — the cluster splits into the probabilists'
Hermite configuration, unconditionally for `m ∈ {2,3}` (the two-term expansion IS `Heₘ`); the
doc 25 §3.1 conclusion for `m ≤ 3` at the algebraic level. -/
theorem cluster_hermite_scaling_two (am σ u : ℝ) :
    am * σ ^ 2 * (u ^ 2 - (Nat.choose 2 2 : ℝ) * u ^ 0)
      = am * σ ^ 2 * (Polynomial.aeval u (Polynomial.hermite 2) : ℝ) := by
  rw [aeval_hermite_two]; norm_num

theorem cluster_hermite_scaling_three (am σ u : ℝ) :
    am * σ ^ 3 * (u ^ 3 - (Nat.choose 3 2 : ℝ) * u ^ 1)
      = am * σ ^ 3 * (Polynomial.aeval u (Polynomial.hermite 3) : ℝ) := by
  rw [aeval_hermite_three]; norm_num

end RHTower
