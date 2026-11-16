import GaloisForLFunctions.SelbergClass.Primon.SpectralCharacterAlgebra
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Tensor characters and their exact Casimir moment

Repeated tensoring by the two-dimensional character branches a highest
weight `j > 0` into `j-1` and `j+1`, and weight zero into weight one.
The resulting list records every multiplicity and expands `xⁿ` in the
existing spectral characters. Its dimension is `2ⁿ`, and its dimension-
weighted Casimir moment is exactly `3n2ⁿ`.

This applies the character-differentiation and second-moment mechanism of
Zehavi, Proposition 4.14, arXiv:2611.18218, to tensor powers. The moment
also bounds the entire high-weight sector without assumptions on its support.
-/

namespace GaloisForLFunctions.RepresentationLifting.Symplectic

open GaloisForLFunctions.SelbergClass.Primon

/-- Tensoring an irreducible character with the standard two-dimensional one. -/
def spinBranch : ℕ → List ℕ
  | 0 => [1]
  | j + 1 => [j, j + 2]

/-- Highest weights with repetitions recording their tensor multiplicities. -/
def tensorSpinWeights : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (tensorSpinWeights n).flatMap spinBranch

private theorem sum_flatMap_spin {R : Type*} [AddMonoid R] (l : List ℕ) (f : ℕ → R) :
    ((l.flatMap spinBranch).map f).sum =
      (l.map fun j => ((spinBranch j).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons j l ih => simp [ih]

private theorem sum_map_mul {R : Type*} [Semiring R] (l : List ℕ) (c : R) (f : ℕ → R) :
    (l.map fun j => c * f j).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, mul_add]

/-- Tensoring doubles the dimension of every constituent. -/
theorem spinBranch_dimension (j : ℕ) :
    ((spinBranch j).map fun k => k + 1).sum = 2 * (j + 1) := by
  cases j <;> simp [spinBranch]
  omega

/-- The Casimir increment is six times the constituent dimension. -/
theorem spinBranch_casimir (j : ℕ) :
    ((spinBranch j).map fun k => (k + 1) * k * (k + 2)).sum =
      2 * ((j + 1) * j * (j + 2)) + 6 * (j + 1) := by
  cases j <;> simp [spinBranch]
  ring

/-- The branching rule is an identity of the corpus's actual spectral characters. -/
theorem spinBranch_character (j : ℕ) (x : ℝ) :
    ((spinBranch j).map fun k => spectralCharacter k x).sum = x * spectralCharacter j x := by
  cases j with
  | zero => simp [spinBranch]
  | succ j =>
    simp only [spinBranch, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [spectralCharacter_add_two]
    ring

/-- No tensor constituent lies above the tensor degree. -/
theorem tensorSpinWeights_le (n : ℕ) : ∀ j ∈ tensorSpinWeights n, j ≤ n := by
  induction n with
  | zero => simp [tensorSpinWeights]
  | succ n ih =>
    intro j hj
    obtain ⟨k, hk, hj⟩ := List.mem_flatMap.mp hj
    have hkn := ih k hk
    cases k <;> simp [spinBranch] at hj <;> omega

/-- Exact character expansion of every tensor power, including every multiplicity. -/
theorem tensorSpin_character (n : ℕ) (x : ℝ) :
    ((tensorSpinWeights n).map fun j => spectralCharacter j x).sum = x ^ n := by
  induction n with
  | zero => simp [tensorSpinWeights]
  | succ n ih =>
    rw [tensorSpinWeights, sum_flatMap_spin]
    simp_rw [spinBranch_character]
    rw [sum_map_mul, ih, pow_succ']

/-- The character decomposition preserves the full tensor dimension. -/
theorem tensorSpin_dimension (n : ℕ) :
    ((tensorSpinWeights n).map fun j => j + 1).sum = 2 ^ n := by
  induction n with
  | zero => simp [tensorSpinWeights]
  | succ n ih =>
    rw [tensorSpinWeights, sum_flatMap_spin]
    simp_rw [spinBranch_dimension]
    rw [sum_map_mul, ih, pow_succ']

/-- The exact second Casimir moment grows linearly after division by tensor dimension. -/
theorem tensorSpin_casimir_moment (n : ℕ) :
    ((tensorSpinWeights n).map fun j => (j + 1) * j * (j + 2)).sum = 3 * n * 2 ^ n := by
  induction n with
  | zero => simp [tensorSpinWeights]
  | succ n ih =>
    rw [tensorSpinWeights, sum_flatMap_spin]
    simp_rw [spinBranch_casimir]
    rw [List.sum_map_add, sum_map_mul, sum_map_mul, ih, tensorSpin_dimension, pow_succ]
    ring

/-- Dimension contained in the sector above a specified highest weight. -/
def tensorSpinTailDimension (n L : ℕ) : ℕ :=
  ((tensorSpinWeights n).map fun j => if L + 1 ≤ j then j + 1 else 0).sum

/-- The Casimir moment bounds all large constituents at once. -/
theorem tensorSpin_tail_bound (n L : ℕ) :
    (L + 1) * (L + 3) * tensorSpinTailDimension n L ≤ 3 * n * 2 ^ n := by
  rw [tensorSpinTailDimension, ← sum_map_mul, ← tensorSpin_casimir_moment]
  apply List.sum_le_sum
  intro j _
  by_cases hj : L + 1 ≤ j
  · rw [if_pos hj]
    have hprod : (L + 1) * (L + 3) ≤ j * (j + 2) :=
      Nat.mul_le_mul hj (by omega)
    calc
      _ ≤ (j * (j + 2)) * (j + 1) := Nat.mul_le_mul_right (j + 1) hprod
      _ = _ := by ring
  · rw [if_neg hj, mul_zero]
    exact Nat.zero_le _

/-- The next Casimir moment closes on the first two moments. -/
theorem spinBranch_casimir_square (j : ℕ) :
    ((spinBranch j).map fun k => (k + 1) * (k * (k + 2)) ^ 2).sum =
      2 * ((j + 1) * (j * (j + 2)) ^ 2) +
        20 * ((j + 1) * j * (j + 2)) + 18 * (j + 1) := by
  cases j <;> simp [spinBranch]
  ring

/-- The fourth weight moment is exact; the additive form avoids natural-number subtraction. -/
theorem tensorSpin_casimir_square_moment (n : ℕ) :
    ((tensorSpinWeights n).map fun j => (j + 1) * (j * (j + 2)) ^ 2).sum +
      6 * n * 2 ^ n = 15 * n ^ 2 * 2 ^ n := by
  induction n with
  | zero => simp [tensorSpinWeights]
  | succ n ih =>
    rw [tensorSpinWeights, sum_flatMap_spin]
    simp_rw [spinBranch_casimir_square]
    rw [List.sum_map_add, List.sum_map_add, sum_map_mul, sum_map_mul, sum_map_mul,
      tensorSpin_casimir_moment, tensorSpin_dimension, pow_succ]
    nlinarith only [ih]

/-- The fourth moment gives a quartic tail bound for the same actual constituent distribution. -/
theorem tensorSpin_tail_bound_fourth (n L : ℕ) :
    ((L + 1) * (L + 3)) ^ 2 * tensorSpinTailDimension n L + 6 * n * 2 ^ n ≤
      15 * n ^ 2 * 2 ^ n := by
  have hb : ((L + 1) * (L + 3)) ^ 2 * tensorSpinTailDimension n L ≤
      ((tensorSpinWeights n).map fun j => (j + 1) * (j * (j + 2)) ^ 2).sum := by
    rw [tensorSpinTailDimension, ← sum_map_mul]
    apply List.sum_le_sum
    intro j _
    by_cases hj : L + 1 ≤ j
    · rw [if_pos hj]
      have hprod : (L + 1) * (L + 3) ≤ j * (j + 2) :=
        Nat.mul_le_mul hj (by omega)
      calc
        _ ≤ (j * (j + 2)) ^ 2 * (j + 1) :=
          Nat.mul_le_mul_right (j + 1) (Nat.pow_le_pow_left hprod 2)
        _ = _ := by ring
    · rw [if_neg hj, mul_zero]
      exact Nat.zero_le _
  have hm := tensorSpin_casimir_square_moment n
  omega

end GaloisForLFunctions.RepresentationLifting.Symplectic

#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_character
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_dimension
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_casimir_moment
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_tail_bound
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_casimir_square_moment
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_tail_bound_fourth
