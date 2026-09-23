import GaloisForLFunctions.HTGeometry.ConservedLocalCompressionWitness

/-!
# Dimension-linear conserved-local two-query signal

This module strengthens the inverse-dictionary-squared compression bound to
the normalization used by the physical two-query protocol.  The randomized
product-state twirl averages the input Pauli uniformly but sums the squared
output coefficients with weight `3^{-w}`.  Consequently only one dictionary
cardinality is paid:

`signal ≥ 3^{-q} / M`.

The proof is finite-dimensional and uses only the conserved coefficient
already certified by `localCompression_frobenius_sq_ge_one`.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Product-stabilizer two-query signal written in a local orthonormal Pauli
dictionary.  Inputs are sampled uniformly; output Pauli coefficients receive
the exact product-state twirl weight `3^{-weight}`. -/
def twoQueryProductStabilizerSignal
    (weight : ι → ℕ) (C : Matrix ι ι ℝ) : ℝ :=
  (∑ i, ∑ j, ((1 : ℝ) / 3) ^ weight j * (C j i) ^ (2 : ℕ)) /
    (Fintype.card ι : ℝ)

/-- **Dimension-linear conserved-local signal.**  If every dictionary element
has Pauli weight at most `q`, one nonzero conserved local coordinate forces
the exact lower bound `3^{-q}/M`, uniformly in evolution time. -/
theorem twoQueryProductStabilizerSignal_ge
    [Nonempty ι] (q : ℕ) (weight : ι → ℕ)
    (hweight : ∀ j, weight j ≤ q)
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h) :
    ((1 : ℝ) / 3) ^ q / (Fintype.card ι : ℝ) ≤
      twoQueryProductStabilizerSignal weight C := by
  classical
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  rw [twoQueryProductStabilizerSignal,
    div_le_div_iff_of_pos_right hcard]
  have hF :
      1 ≤ ∑ i, ∑ j, (C j i) ^ (2 : ℕ) := by
    have hswap :
        (∑ i, ∑ j, (C i j) ^ (2 : ℕ)) =
          ∑ i, ∑ j, (C j i) ^ (2 : ℕ) := by
      have hs := Finset.sum_comm
        (s := (Finset.univ : Finset ι))
        (t := (Finset.univ : Finset ι))
        (f := fun i j => (C i j) ^ (2 : ℕ))
      simpa using hs
    rw [← hswap]
    exact localCompression_frobenius_sq_ge_one C h hh hfix
  have hbase : 0 ≤ ((1 : ℝ) / 3) ^ q := by positivity
  calc
    ((1 : ℝ) / 3) ^ q ≤
        ((1 : ℝ) / 3) ^ q * (∑ i, ∑ j, (C j i) ^ (2 : ℕ)) := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hF hbase)
    _ = ∑ i, ∑ j,
        ((1 : ℝ) / 3) ^ q * (C j i) ^ (2 : ℕ) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j,
        ((1 : ℝ) / 3) ^ weight j * (C j i) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
          (by norm_num : (1 : ℝ) / 3 ≤ 1) (hweight j))
        (sq_nonneg (C j i))

/-- Replace the exact dictionary cardinality by any upper bound. -/
theorem twoQueryProductStabilizerSignal_ge_of_card_le
    [Nonempty ι] (q : ℕ) (weight : ι → ℕ)
    (hweight : ∀ j, weight j ≤ q)
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h) {B : ℝ}
    (hcard : (Fintype.card ι : ℝ) ≤ B) :
    ((1 : ℝ) / 3) ^ q / B ≤
      twoQueryProductStabilizerSignal weight C := by
  have hM : 0 < (Fintype.card ι : ℝ) := by positivity
  have hpow : 0 ≤ ((1 : ℝ) / 3) ^ q := by positivity
  calc
    ((1 : ℝ) / 3) ^ q / B ≤
        ((1 : ℝ) / 3) ^ q / (Fintype.card ι : ℝ) :=
      div_le_div_of_nonneg_left hpow hM hcard
    _ ≤ twoQueryProductStabilizerSignal weight C :=
      twoQueryProductStabilizerSignal_ge
        q weight hweight C h hh hfix

/-- One-dimensional fixed-`q` dictionary form:
`M ≤ 4^q n` gives signal at least `1/(12^q n)`. -/
theorem twoQueryProductStabilizerSignal_ge_oneDimensional
    [Nonempty ι] (q n : ℕ)
    (weight : ι → ℕ) (hweight : ∀ j, weight j ≤ q)
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h)
    (hcard : Fintype.card ι ≤ 4 ^ q * n) :
    1 / (((12 : ℕ) ^ q * n : ℕ) : ℝ) ≤
      twoQueryProductStabilizerSignal weight C := by
  have hcardR :
      (Fintype.card ι : ℝ) ≤ ((4 ^ q * n : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hsignal :=
    twoQueryProductStabilizerSignal_ge_of_card_le
      q weight hweight C h hh hfix hcardR
  have hscale :
      ((12 : ℝ)⁻¹) ^ q =
        ((4 : ℝ)⁻¹) ^ q * ((1 : ℝ) / 3) ^ q := by
    rw [show (12 : ℝ)⁻¹ = (4 : ℝ)⁻¹ * (3 : ℝ)⁻¹ by norm_num, mul_pow]
    norm_num [div_eq_mul_inv]
  convert hsignal using 1
  norm_num [div_eq_mul_inv, Nat.cast_mul, Nat.cast_pow]
  rw [← inv_pow, ← inv_pow, hscale]
  ring

/-- All-to-all fixed-`q` dictionary form:
`M ≤ (4n)^q` gives signal at least `1/(12n)^q`. -/
theorem twoQueryProductStabilizerSignal_ge_allToAll
    [Nonempty ι] (q n : ℕ)
    (weight : ι → ℕ) (hweight : ∀ j, weight j ≤ q)
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h)
    (hcard : Fintype.card ι ≤ (4 * n) ^ q) :
    1 / ((((12 * n : ℕ) ^ q : ℕ)) : ℝ) ≤
      twoQueryProductStabilizerSignal weight C := by
  have hcardR :
      (Fintype.card ι : ℝ) ≤ ((((4 * n : ℕ) ^ q : ℕ)) : ℝ) := by
    exact_mod_cast hcard
  have hsignal :=
    twoQueryProductStabilizerSignal_ge_of_card_le
      q weight hweight C h hh hfix hcardR
  have hscale :
      ((12 : ℝ)⁻¹) ^ q =
        ((4 : ℝ)⁻¹) ^ q * ((1 : ℝ) / 3) ^ q := by
    rw [show (12 : ℝ)⁻¹ = (4 : ℝ)⁻¹ * (3 : ℝ)⁻¹ by norm_num, mul_pow]
    norm_num [div_eq_mul_inv]
  convert hsignal using 1
  norm_num [div_eq_mul_inv, Nat.cast_mul, Nat.cast_pow]
  rw [← inv_pow, ← inv_pow, mul_inv, mul_inv, mul_pow, mul_pow, hscale]
  ring

end

end GaloisForLFunctions.HTGeometry
