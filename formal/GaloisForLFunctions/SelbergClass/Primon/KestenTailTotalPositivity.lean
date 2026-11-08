import GaloisForLFunctions.SelbergClass.Primon.KestenTailGeometry
import GaloisForLFunctions.HTGeometry.ToeplitzGeometricTotalPositivity
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Total positivity of likelihood-tail character coordinates

The actual Hilbert coefficients of normalized tails form the zero-extended
geometric Toeplitz kernel. Every minor with increasing depth and character
indices is nonnegative; matching consecutive blocks have determinant one.
-/

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- All even-character coordinates of a normalized likelihood tail. -/
theorem inner_kestenNormalizedTail_evenCharacter (p : Nat.Primes) (N m : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (spectralCharacterVector (2 * m)) =
      if N ≤ m then primeReciprocal p ^ (m - N) else 0 := by
  by_cases h : N ≤ m
  · rw [if_pos h]
    have he := inner_kestenNormalizedTail_later p N (m - N)
    rwa [Nat.add_sub_of_le h] at he
  · rw [if_neg h, inner_kestenNormalizedTail_earlier p N m (by omega)]

/-- The character-coordinate kernel is exactly the geometric Toeplitz kernel. -/
theorem inner_kestenNormalizedTail_eq_zext (p : Nat.Primes) (N m : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (spectralCharacterVector (2 * m)) =
      zext (fun n : ℕ => primeReciprocal p ^ n) ((m : ℤ) - N) := by
  rw [inner_kestenNormalizedTail_evenCharacter, zext_geometric]
  by_cases h : N ≤ m
  · rw [if_pos h, if_pos (by omega)]
    congr 1
    omega
  · rw [if_neg h, if_neg (by omega)]

/-- Every ordered minor of the actual tail-to-character coefficient matrix is nonnegative. -/
theorem det_kestenTail_character_minor_nonneg (p : Nat.Primes) (n : ℕ)
    (rows cols : Fin n ↪o ℕ) :
    0 ≤ Matrix.det (fun i j : Fin n => inner ℝ (kestenNormalizedTail p (rows i))
      (spectralCharacterVector (2 * cols j))) := by
  have h := PFSeq.geometric (primeReciprocal_pos p).le n n le_rfl
    rows cols rows.strictMono cols.strictMono
  unfold toeplitzMinor at h
  have he : (Matrix.of fun r c : Fin n =>
      zext (fun k : ℕ => primeReciprocal p ^ k) ((cols c : ℤ) - rows r)) =
      (fun r c : Fin n => inner ℝ (kestenNormalizedTail p (rows r))
        (spectralCharacterVector (2 * cols c))) := by
    ext r c
    exact (inner_kestenNormalizedTail_eq_zext p (rows r) (cols c)).symm
  rwa [he] at h

/-- Consecutive matching depth and character windows preserve oriented volume exactly. -/
theorem det_kestenTail_character_window (p : Nat.Primes) (N n : ℕ) :
    Matrix.det (fun i j : Fin n => inner ℝ (kestenNormalizedTail p (N + i))
      (spectralCharacterVector (2 * (N + j)))) = 1 := by
  have ht : Matrix.BlockTriangular (fun i j : Fin n =>
      inner ℝ (kestenNormalizedTail p (N + i))
        (spectralCharacterVector (2 * (N + j)))) id := by
    intro i j hij
    exact inner_kestenNormalizedTail_earlier p _ _ (Nat.add_lt_add_left hij N)
  rw [Matrix.det_of_upperTriangular ht]
  simp only [inner_kestenNormalizedTail_leading, Finset.prod_const_one]

end
end GaloisForLFunctions.SelbergClass.Primon

