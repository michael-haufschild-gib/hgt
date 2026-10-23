import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.PNat.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Parity coordinates for the shifted determinant

On `mn + 2 = qh`, a Liouville change of row and column coordinates
moves the Möbius signs to `λ(mn)λ(mn + 2)`. The change preserves
Euclidean unit balls, so it preserves all finite bilinear tests.
-/

namespace TwinPrime

open Finset ArithmeticFunction

noncomputable section

/-- The complex Liouville sign. -/
def liouvilleSign (n : ℕ) : ℂ := (liouville n : ℤ)

/-- The complex Möbius coefficient. -/
def moebiusValue (n : ℕ) : ℂ := (moebius n : ℤ)

theorem liouvilleSign_mul (m n : ℕ) :
    liouvilleSign (m * n) = liouvilleSign m * liouvilleSign n := by
  simp only [liouvilleSign, liouville_apply_mul, Int.cast_mul]

@[simp] theorem liouvilleSign_sq (n : ℕ+) : liouvilleSign n ^ 2 = 1 := by
  simp only [liouvilleSign, liouville_apply n.ne_zero, Int.cast_pow,
    Int.cast_neg, Int.cast_one]
  rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]

@[simp] theorem norm_liouvilleSign (n : ℕ+) : ‖liouvilleSign n‖ = 1 := by
  simp [liouvilleSign, liouville_apply n.ne_zero]

/-- On squarefree support the Möbius sign is Liouville's sign. -/
theorem moebiusValue_eq_liouvilleSign_mul_sq (n : ℕ) :
    moebiusValue n = liouvilleSign n * moebiusValue n ^ 2 := by
  by_cases hn : Squarefree n
  · have heq : liouvilleSign n = moebiusValue n := by
      simp only [liouvilleSign, moebiusValue, liouville_apply hn.ne_zero,
        moebius_apply_of_squarefree hn]
    rw [heq]
    rcases moebius_eq_or n with h | h | h <;> simp [moebiusValue, h]
  · simp [moebiusValue, moebius_eq_zero_of_not_squarefree hn]

/-- The sign remaining after crossing the additive gap two. -/
def shiftedParity (s : ℕ) : ℂ := liouvilleSign s * liouvilleSign (s + 2)

/-- Two Möbius factors on the determinant surface, zero away from it. -/
def moebiusDeterminantTerm (m n q h : ℕ+) : ℂ :=
  if (m : ℕ) * n + 2 = (q : ℕ) * h then moebiusValue m * moebiusValue h else 0

/-- Nonnegative squarefree weights carrying only the shifted parity sign. -/
def parityDeterminantTerm (m n q h : ℕ+) : ℂ :=
  if (m : ℕ) * n + 2 = (q : ℕ) * h then
    shiftedParity ((m : ℕ) * n) * moebiusValue m ^ 2 * moebiusValue h ^ 2
  else 0

/-- Exact conjugation; the determinant relation is part of the kernel. -/
theorem moebiusDeterminantTerm_eq_parity (m n q h : ℕ+) :
    moebiusDeterminantTerm m n q h =
      liouvilleSign q * liouvilleSign n * parityDeterminantTerm m n q h := by
  by_cases he : (m : ℕ) * n + 2 = (q : ℕ) * h
  · simp only [moebiusDeterminantTerm, parityDeterminantTerm, if_pos he]
    rw [shiftedParity, he, liouvilleSign_mul, liouvilleSign_mul]
    calc
      moebiusValue m * moebiusValue h =
          (liouvilleSign m * moebiusValue m ^ 2) *
            (liouvilleSign h * moebiusValue h ^ 2) :=
        congrArg₂ (· * ·) (moebiusValue_eq_liouvilleSign_mul_sq m)
          (moebiusValue_eq_liouvilleSign_mul_sq h)
      _ = liouvilleSign q ^ 2 * liouvilleSign n ^ 2 *
          ((liouvilleSign m * moebiusValue m ^ 2) *
            (liouvilleSign h * moebiusValue h ^ 2)) := by
        rw [liouvilleSign_sq, liouvilleSign_sq, one_mul, one_mul]
      _ = _ := by ring
  · simp only [moebiusDeterminantTerm, parityDeterminantTerm, if_neg he, mul_zero]

/-- Finite determinant matrix with an arbitrary complex arithmetic weight. -/
def moebiusDeterminantMatrix (M H : Finset ℕ+)
    (w : ℕ+ → ℕ+ → ℕ+ → ℕ+ → ℂ) (q n : ℕ+) : ℂ :=
  ∑ m ∈ M, ∑ h ∈ H, moebiusDeterminantTerm m n q h * w m n q h

/-- The same matrix after moving the factor signs to shifted products. -/
def parityDeterminantMatrix (M H : Finset ℕ+)
    (w : ℕ+ → ℕ+ → ℕ+ → ℕ+ → ℂ) (q n : ℕ+) : ℂ :=
  ∑ m ∈ M, ∑ h ∈ H, parityDeterminantTerm m n q h * w m n q h

theorem moebiusDeterminantMatrix_eq_parity (M H : Finset ℕ+)
    (w : ℕ+ → ℕ+ → ℕ+ → ℕ+ → ℂ) (q n : ℕ+) :
    moebiusDeterminantMatrix M H w q n =
      liouvilleSign q * liouvilleSign n * parityDeterminantMatrix M H w q n := by
  simp only [moebiusDeterminantMatrix, parityDeterminantMatrix, mul_sum]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro h _
  rw [moebiusDeterminantTerm_eq_parity]
  ring

/-- Multiplication of each positive coordinate by its Liouville sign. -/
def liouvilleGauge (x : ℕ+ → ℂ) (n : ℕ+) : ℂ := liouvilleSign n * x n

@[simp] theorem liouvilleGauge_involutive (x : ℕ+ → ℂ) :
    liouvilleGauge (liouvilleGauge x) = x := by
  funext n
  change liouvilleSign n * (liouvilleSign n * x n) = x n
  calc
    _ = liouvilleSign n ^ 2 * x n := by ring
    _ = x n := by rw [liouvilleSign_sq, one_mul]

@[simp] theorem sum_norm_sq_liouvilleGauge (S : Finset ℕ+) (x : ℕ+ → ℂ) :
    (∑ n ∈ S, ‖liouvilleGauge x n‖ ^ 2) = ∑ n ∈ S, ‖x n‖ ^ 2 := by
  simp only [liouvilleGauge, norm_mul, norm_liouvilleSign, one_mul]

/-- A finite bilinear test of a matrix. -/
def determinantPairing (Q N : Finset ℕ+) (K : ℕ+ → ℕ+ → ℂ)
    (x y : ℕ+ → ℂ) : ℂ :=
  ∑ q ∈ Q, ∑ n ∈ N, x q * K q n * y n

/-- Every signed test is exactly a shifted-parity test on isometric coordinates. -/
theorem determinantPairing_moebius_eq_parity (M H Q N : Finset ℕ+)
    (w : ℕ+ → ℕ+ → ℕ+ → ℕ+ → ℂ) (x y : ℕ+ → ℂ) :
    determinantPairing Q N (moebiusDeterminantMatrix M H w) x y =
      determinantPairing Q N (parityDeterminantMatrix M H w)
        (liouvilleGauge x) (liouvilleGauge y) := by
  unfold determinantPairing
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro n _
  rw [moebiusDeterminantMatrix_eq_parity]
  simp only [liouvilleGauge]
  ring

/-- All pairing values on two finite Euclidean unit balls. -/
def determinantUnitPairingValues (Q N : Finset ℕ+) (K : ℕ+ → ℕ+ → ℂ) : Set ℂ :=
  {z | ∃ x y : ℕ+ → ℂ, (∑ q ∈ Q, ‖x q‖ ^ 2) ≤ 1 ∧
    (∑ n ∈ N, ‖y n‖ ^ 2) ≤ 1 ∧ determinantPairing Q N K x y = z}

/-- The full unit-ball tests agree, not merely their unsigned coefficient bounds. -/
theorem determinantUnitPairingValues_moebius_eq_parity (M H Q N : Finset ℕ+)
    (w : ℕ+ → ℕ+ → ℕ+ → ℕ+ → ℂ) :
    determinantUnitPairingValues Q N (moebiusDeterminantMatrix M H w) =
      determinantUnitPairingValues Q N (parityDeterminantMatrix M H w) := by
  ext z
  constructor
  · rintro ⟨x, y, hx, hy, hz⟩
    refine ⟨liouvilleGauge x, liouvilleGauge y, ?_, ?_, ?_⟩
    · simpa only [sum_norm_sq_liouvilleGauge] using hx
    · simpa only [sum_norm_sq_liouvilleGauge] using hy
    · rw [← determinantPairing_moebius_eq_parity]
      exact hz
  · rintro ⟨x, y, hx, hy, hz⟩
    refine ⟨liouvilleGauge x, liouvilleGauge y, ?_, ?_, ?_⟩
    · simpa only [sum_norm_sq_liouvilleGauge] using hx
    · simpa only [sum_norm_sq_liouvilleGauge] using hy
    · rw [determinantPairing_moebius_eq_parity, liouvilleGauge_involutive,
        liouvilleGauge_involutive]
      exact hz

end

end TwinPrime
