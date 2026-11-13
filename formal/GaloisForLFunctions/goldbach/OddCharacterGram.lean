import GaloisForLFunctions.goldbach.OddCharacterProjection
import GaloisForLFunctions.goldbach.ReducedResidueAntidiagonal
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
open scoped Classical ComplexOrder

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

/-- For a modulus greater than two, exactly half its characters are odd. -/
theorem twice_card_oddCharacters (N : ℕ) :
    2 * Fintype.card {χ : DirichletCharacter ℂ (N + 3) // χ.Odd} =
      (N + 3).totient := by
  letI : Fact (1 < N + 3) := ⟨by omega⟩
  have hne : -(1 : (ZMod (N + 3))ˣ) ≠ 1 := by
    intro he
    have hs := unit_val_add_neg_val (N + 1) (1 : (ZMod (N + 3))ˣ)
    rw [he] at hs
    simp only [Units.val_one, ZMod.val_one] at hs
    omega
  have h := twice_sum_odd_unitCharacter_mul_star (N + 2) 1 1
  simp only [Units.val_one, map_one, star_one, mul_one, if_pos rfl,
    if_neg hne, sub_zero, sum_const, nsmul_eq_mul, mul_one] at h
  rw [Fintype.card_subtype]
  exact_mod_cast h

/-- The odd-character Gram rank is at most half the totient. -/
theorem oddCharacterGram_rank_le_totient_div_two (N : ℕ) {ι : Type*} [Fintype ι]
    (w : ι → (ZMod (N + 3))ˣ → ℂ) :
    (oddCharacterGram (N + 2) w).rank ≤ (N + 3).totient / 2 := by
  have hc := twice_card_oddCharacters N
  have hr := oddCharacterGram_rank_le (N + 2) w
  omega

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
  simpa only [Finset.subtype_univ] using
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

/-- The odd-character energy vanishes exactly on reflection-invariant real profiles. -/
theorem odd_character_moment_eq_zero_iff_even (N : ℕ) (w : (ZMod (N + 1))ˣ → ℝ) :
    (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
      ‖unitCharacterSum N (fun a => (w a : ℂ)) χ‖ ^ 2) = 0 ↔
        ∀ a, w (-a) = w a := by
  have h := four_mul_odd_moment_eq_reflection_defect N w
  constructor
  · intro hz a
    have ht : 0 < ((N + 1).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < N + 1)
    rw [hz, mul_zero] at h
    have hs : (∑ b, (w b - w (-b)) ^ 2) = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left ht.ne'
    have ha := (sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (w b - w (-b)))).mp hs a
      (mem_univ a)
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp ha)).symm
  · intro he
    simp only [he, sub_self, zero_pow two_ne_zero, sum_const_zero, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num : (4 : ℝ) ≠ 0)

end

end GaloisForLFunctions.Goldbach

-- Temporary dependency audit.
#print axioms GaloisForLFunctions.Goldbach.oddCharacterFeatures
#print axioms GaloisForLFunctions.Goldbach.oddCharacterGram
#print axioms GaloisForLFunctions.Goldbach.oddCharacterGram_posSemidef
#print axioms GaloisForLFunctions.Goldbach.oddCharacterGram_rank
#print axioms GaloisForLFunctions.Goldbach.oddCharacterGram_rank_le
#print axioms GaloisForLFunctions.Goldbach.twice_card_oddCharacters
#print axioms GaloisForLFunctions.Goldbach.oddCharacterGram_rank_le_totient_div_two
#print axioms GaloisForLFunctions.Goldbach.oddCharacterGram_apply
#print axioms GaloisForLFunctions.Goldbach.twice_oddCharacterGram_eq_reflection_gap
#print axioms GaloisForLFunctions.Goldbach.odd_character_moment_eq_zero_iff_even
