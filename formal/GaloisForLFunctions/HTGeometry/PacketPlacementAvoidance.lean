import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite
import GaloisForLFunctions.HTGeometry.RankDefectAlgebraicCore

/-!
# Placing a row packet away from a finite bad set

The rank-defect mechanism produces, for each nonzero coefficient vector, a finite set of bad row
nodes — those at which every coefficient polynomial vanishes.  To use it one needs a row packet
avoiding that set, while also sitting high enough in the upper half-plane for the admissibility
condition.

Vertical translation supplies both at once.  For each row the translations landing in the bad set
are finite, because a vertical line meets a finite set finitely often; finitely many rows give a
finite union, and the translations above any prescribed height are infinite.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A vertical line meets a finite set in finitely many translations. -/
theorem finite_translations_into_finite (z : ℂ) {S : Set ℂ} (hS : S.Finite) :
    {t : ℝ | z + (t : ℂ) * Complex.I ∈ S}.Finite := by
  have hinj : Function.Injective (fun t : ℝ => z + (t : ℂ) * Complex.I) := by
    intro a b hab
    have him := congrArg Complex.im hab
    simpa using him
  exact hS.preimage hinj.injOn

/-- **Vertical placement avoiding a finite set.**  Above every prescribed height there is a
translation carrying an entire finite row family off a prescribed finite bad set. -/
theorem exists_translation_avoiding_finite
    {row : Type*} [Finite row] (z : row → ℂ) {S : Set ℂ} (hS : S.Finite) (H : ℝ) :
    ∃ t : ℝ, H < t ∧ ∀ r, (z r + (t : ℂ) * Complex.I) ∉ S := by
  classical
  have hunion :
      (⋃ r : row, {t : ℝ | z r + (t : ℂ) * Complex.I ∈ S}).Finite :=
    Set.finite_iUnion fun r => finite_translations_into_finite (z r) hS
  have hnotsub : ¬ Set.Ioi H ⊆
      ⋃ r : row, {t : ℝ | z r + (t : ℂ) * Complex.I ∈ S} := by
    intro hsub
    exact (Set.Ioi_infinite H) (hunion.subset hsub)
  obtain ⟨t, htIoi, htnot⟩ := Set.not_subset.mp hnotsub
  refine ⟨t, htIoi, ?_⟩
  intro r hmem
  exact htnot (Set.mem_iUnion.mpr ⟨r, hmem⟩)

/-- Vertical translation preserves injectivity of a row family. -/
theorem injective_translate {row : Type*} (z : row → ℂ)
    (hz : Function.Injective z) (t : ℝ) :
    Function.Injective (fun r => z r + (t : ℂ) * Complex.I) := by
  intro a b hab
  exact hz (by simpa using add_right_cancel hab)

/-- Translating high enough puts every row strictly in the upper half-plane, uniformly over a
finite family of offsets. -/
theorem exists_translation_upper_and_avoiding
    {row ι : Type*} [Finite row] [Finite ι]
    (z : row → ℂ) (shift : ι → ℂ) {S : Set ℂ} (hS : S.Finite) :
    ∃ t : ℝ, (∀ r i, 0 < (z r + (t : ℂ) * Complex.I + shift i).im) ∧
      ∀ r, (z r + (t : ℂ) * Complex.I) ∉ S := by
  classical
  cases nonempty_fintype row
  cases nonempty_fintype ι
  set H : ℝ := ∑ r : row, |(z r).im| + ∑ i : ι, |(shift i).im| with hH
  obtain ⟨t, htH, htS⟩ := exists_translation_avoiding_finite z hS H
  refine ⟨t, ?_, htS⟩
  intro r i
  have hr : |(z r).im| ≤ ∑ r' : row, |(z r').im| :=
    Finset.single_le_sum (f := fun r' : row => |(z r').im|)
      (fun r' _ => abs_nonneg _) (Finset.mem_univ r)
  have hi : |(shift i).im| ≤ ∑ i' : ι, |(shift i').im| :=
    Finset.single_le_sum (f := fun i' : ι => |(shift i').im|)
      (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
  have hzr : -(z r).im ≤ |(z r).im| := neg_le_abs _
  have hsi : -(shift i).im ≤ |(shift i).im| := neg_le_abs _
  have hsum : (z r + (t : ℂ) * Complex.I + shift i).im =
      (z r).im + t + (shift i).im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [hsum]
  have : H < t := htH
  rw [hH] at this
  linarith

/-- **A placed packet on which every row is nondegenerate.**  Given a nonzero coefficient vector,
one vertical translation simultaneously lifts an arbitrary injective row family into admissible
position and carries it off the finite degenerate set, so at *every* row the relation polynomial is
nonzero. -/
theorem exists_placed_packet_all_rows_nondegenerate
    {row κ ι : Type*} [Finite row] [Fintype κ] [DecidableEq κ] [Finite ι]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (coeff : κ × Fin (q + 1) → ℂ) (β₀ : κ) {d₀ : Fin (q + 1)}
    (hcoeff : coeff (β₀, d₀) ≠ 0)
    (z₀ : row → ℂ) (hz₀ : Function.Injective z₀) (shift : ι → ℂ) :
    ∃ z : row → ℂ, Function.Injective z ∧
      (∀ r i, 0 < (z r + shift i).im) ∧
      ∀ r, (∑ β : κ, MvPolynomial.monomial (exponent β)
        (rowCoefficientPolynomial q coeff β (z r))) ≠ 0 := by
  classical
  obtain ⟨t, hupper, havoid⟩ := exists_translation_upper_and_avoiding z₀ shift
    (finite_degenerate_rowNodes q coeff β₀ hcoeff)
  refine ⟨fun r => z₀ r + (t : ℂ) * Complex.I,
    injective_translate z₀ hz₀ t, hupper, ?_⟩
  intro r
  have hnot := havoid r
  simp only [Set.mem_setOf_eq, not_forall] at hnot
  obtain ⟨β, hβ⟩ := hnot
  exact sum_monomial_ne_zero exponent hexp _ hβ

end

end GaloisForLFunctions.HTGeometry
