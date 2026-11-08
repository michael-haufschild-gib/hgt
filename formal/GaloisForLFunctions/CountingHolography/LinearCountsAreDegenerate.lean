import GaloisForLFunctions.CountingHolography.TheBornRuleOfABlackHole

/-!
# Linear counts are degenerate

The natural counts of the review's §2.7 are **linear in the source**: the number of cusp images in
horoball regions cut out by a source (the shell and Farey counts of
`TheFareyReadingOfTheHorocycle`), the number of echoes weighted by `φ(c)`, the degree of a line bundle
attached to a source. This module decides what such counts can do for the count law.

* **A linear count never obeys the law.** An additive `K` with the parallelogram law vanishes
  (`eq_zero_of_additive_countLaw`): the law asks `K(2φ) = 4K(φ)`, additivity gives `2K(φ)`.
* **A count read through one linear count is degenerate.** If a count law `K` on the probes of a black
  hole depends only on one linear functional `αx + βy` of the probe, its binary form has discriminant
  zero (`countLaw_through_linear_degenerate`): it is a multiple of `(αx + βy)²`, of rank one.
* **The Krein square is such a count only at the critical edge** (`kreinSquare_through_linear_iff`):
  `𝒬` factors through one linear count iff `t² = 4q`. A damped black hole (`t² < 4q`) needs a count of
  rank two, the boundary square `|y − xα|²` of `TheBoundarySquareIsTheOscillation`, which is the sum of
  the squares of two linear counts, the real and imaginary parts of the probe at its mode.

So the linear candidates are refuted as counts of a damped system, and the survivor is exact: a count
of channels must be quadratic of full rank, a sum of at least as many squares of linear counts as the
system has oscillating modes.
-/

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

/-- **A linear count never obeys the law.** -/
theorem eq_zero_of_additive_countLaw {M : Type*} [AddCommGroup M] {K : M → ℤ}
    (hadd : ∀ x y, K (x + y) = K x + K y)
    (hlaw : ∀ x y, K (x + y) + K (x - y) = 2 * K x + 2 * K y) (x : M) : K x = 0 := by
  have h := hlaw x x
  rw [sub_self, hadd x x] at h
  have h0 : K 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    linarith
  rw [h0] at h
  linarith

/-- **A count law read through one linear count is degenerate.** If `K` obeys the count law and is
constant along the kernel direction `(-β, α)` of the linear count `αx + βy`, its binary form
`K(0,1) y² + (K(1,1) − K(0,1) − K(1,0)) xy + K(1,0) x²` has discriminant zero. -/
theorem countLaw_through_linear_degenerate {K : ℤ → ℤ → ℕ} (hK : CountLaw K) {α β : ℤ}
    (hαβ : α ≠ 0 ∨ β ≠ 0) (hconst : ∀ x y m : ℤ, K (x - m * β) (y + m * α) = K x y) :
    ((K 1 1 : ℤ) - K 0 1 - K 1 0) ^ 2 = 4 * (K 0 1 : ℤ) * K 1 0 := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = K 0 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = K 1 0 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = (K 1 1 : ℤ) - K 0 1 - K 1 0 := ⟨_, rfl⟩
  have hform (x y : ℤ) : (K x y : ℤ) = A * y ^ 2 + C * x * y + B * x ^ 2 := by
    rw [hA, hB, hC]
    exact countLaw_eq_form hK x y
  -- the form vanishes on the kernel direction `w = (-β, α)` and is orthogonal to everything there
  have h0 := hconst 0 0 1
  have h1 := hconst 1 0 1
  have h2 := hconst 0 1 1
  have h0' : ((K (0 - 1 * β) (0 + 1 * α) : ℕ) : ℤ) = K 0 0 := by exact_mod_cast h0
  have h1' : ((K (1 - 1 * β) (0 + 1 * α) : ℕ) : ℤ) = K 1 0 := by exact_mod_cast h1
  have h2' : ((K (0 - 1 * β) (1 + 1 * α) : ℕ) : ℤ) = K 0 1 := by exact_mod_cast h2
  rw [hform, hform] at h0' h1' h2'
  -- `Q(w) = 0`, `2B(e₁, w) = 0`, `2B(e₂, w) = 0`
  have q0 : A * α ^ 2 - C * β * α + B * β ^ 2 = 0 := by linear_combination h0'
  have q1 : 2 * B * (-β) + C * α = 0 := by linear_combination h1' - q0
  have q2 : 2 * A * α - C * β = 0 := by linear_combination h2' - q0
  -- a nonzero vector in the radical: the Gram determinant vanishes
  have hdet : (C ^ 2 - 4 * A * B) * α = 0 ∧ (C ^ 2 - 4 * A * B) * β = 0 := by
    constructor
    · linear_combination C * q1 - 2 * B * q2
    · linear_combination 2 * A * q1 - C * q2
  have : C ^ 2 - 4 * A * B = 0 := by
    rcases hαβ with h | h
    · exact (mul_eq_zero.mp hdet.1).resolve_right h
    · exact (mul_eq_zero.mp hdet.2).resolve_right h
  rw [← hA, ← hB, show (K 1 1 : ℤ) - A - B = C by rw [hC, hA, hB]]
  linarith

/-- **The Krein square factors through one linear count exactly at the critical edge.** -/
theorem kreinSquare_through_linear_iff {q t : ℤ} :
    (∃ α β : ℤ, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ x y m : ℤ,
      kreinSquare q t (x - m * β) (y + m * α) = kreinSquare q t x y) ↔ t ^ 2 = 4 * q := by
  constructor
  · rintro ⟨α, β, hαβ, hconst⟩
    have h0 := hconst 0 0 1
    have h1 := hconst 1 0 1
    have h2 := hconst 0 1 1
    simp only [kreinSquare] at h0 h1 h2
    have q0 : α ^ 2 + t * β * α + q * β ^ 2 = 0 := by linear_combination h0
    have q1 : -(t * α) - 2 * q * β = 0 := by linear_combination h1 - q0
    have q2 : 2 * α + t * β = 0 := by linear_combination h2 - q0
    have hdet : (t ^ 2 - 4 * q) * α = 0 ∧ (t ^ 2 - 4 * q) * β = 0 := by
      constructor
      · linear_combination -t * q1 - 2 * q * q2
      · linear_combination t * q2 + 2 * q1
    rcases hαβ with h | h
    · linarith [(mul_eq_zero.mp hdet.1).resolve_right h]
    · linarith [(mul_eq_zero.mp hdet.2).resolve_right h]
  · intro h
    -- the critical form is `(y − t x / 2)²`; its kernel direction is `(2, t)`
    refine ⟨t, -2, Or.inr (by norm_num), fun x y m => ?_⟩
    simp only [kreinSquare]
    linear_combination -(m ^ 2 + m * x) * h

end GaloisForLFunctions.CountingHolography

end
