import GaloisForLFunctions.goldbach.OddCharacterProjection
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Positive Gram matrices of odd arithmetic moments

Li--Liu's finite character kernel is a Gram kernel. For arbitrary residue
profiles its matrix is positive semidefinite, with rank exactly the rank
of the odd-character feature matrix. The entrywise reflection formula
identifies this positive matrix with diagonal correlation minus reflected
correlation, extending the scalar moment identity to mixed profiles.
-/

namespace GaloisForLFunctions.Goldbach

open Finset Matrix
open scoped Classical

noncomputable section

/-- Odd-character transforms of a finite family of arithmetic profiles. -/
def oddCharacterFeatures (N : ℕ) {ι : Type*}
    (w : ι → (ZMod (N + 1))ˣ → ℂ) :
    Matrix ι {χ : DirichletCharacter ℂ (N + 1) // χ.Odd} ℂ :=
  fun i χ => unitCharacterSum N (w i) χ.val

/-- The finite mixed odd-character moment matrix. -/
def oddCharacterGram (N : ℕ) {ι : Type*}
    (w : ι → (ZMod (N + 1))ˣ → ℂ) : Matrix ι ι ℂ :=
  oddCharacterFeatures N w * (oddCharacterFeatures N w)ᴴ

/-- Every finite family of arithmetic profiles gives a positive semidefinite moment matrix. -/
theorem oddCharacterGram_posSemidef (N : ℕ) {ι : Type*} [Fintype ι]
    (w : ι → (ZMod (N + 1))ˣ → ℂ) : (oddCharacterGram N w).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- Gram formation preserves the exact feature rank. -/
theorem oddCharacterGram_rank (N : ℕ) {ι : Type*} [Fintype ι]
    (w : ι → (ZMod (N + 1))ˣ → ℂ) :
    (oddCharacterGram N w).rank = (oddCharacterFeatures N w).rank :=
  Matrix.rank_self_mul_conjTranspose _

/-- The number of odd characters bounds the rank, regardless of the number of profiles. -/
theorem oddCharacterGram_rank_le (N : ℕ) {ι : Type*} [Fintype ι]
    (w : ι → (ZMod (N + 1))ˣ → ℂ) :
    (oddCharacterGram N w).rank ≤
      Fintype.card {χ : DirichletCharacter ℂ (N + 1) // χ.Odd} := by
  rw [oddCharacterGram_rank]
  exact Matrix.rank_le_card_width _

/-- Matrix entries are the filtered mixed character moments. -/
theorem oddCharacterGram_apply (N : ℕ) {ι : Type*}
    (w : ι → (ZMod (N + 1))ˣ → ℂ) (i j : ι) :
    oddCharacterGram N w i j =
      ∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
        unitCharacterSum N (w i) χ * star (unitCharacterSum N (w j) χ) := by
  unfold oddCharacterGram
  rw [Matrix.mul_apply]
  change (∑ χ : {χ : DirichletCharacter ℂ (N + 1) // χ.Odd},
    unitCharacterSum N (w i) χ.val * star (unitCharacterSum N (w j) χ.val)) = _
  simpa only [Finset.univ_subtype] using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (DirichletCharacter ℂ (N + 1))))
      (p := fun χ => χ.Odd)
      (fun χ => unitCharacterSum N (w i) χ * star (unitCharacterSum N (w j) χ)))

/-- The positive Gram kernel is exactly the mixed diagonal-reflection gap. -/
theorem twice_oddCharacterGram_eq_reflection_gap (N : ℕ) {ι : Type*}
    (w : ι → (ZMod (N + 1))ˣ → ℂ) (i j : ι) :
    2 * oddCharacterGram N w i j = ((N + 1).totient : ℂ) *
      ((∑ a, w i a * star (w j a)) - ∑ a, w i (-a) * star (w j a)) := by
  rw [oddCharacterGram_apply]
  exact twice_sum_odd_unitCharacterSum_mul_star N (w i) (w j)

end

end GaloisForLFunctions.Goldbach
