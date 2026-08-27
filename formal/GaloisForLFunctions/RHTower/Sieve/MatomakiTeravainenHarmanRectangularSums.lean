import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellIteration
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanNonrectangular

/-!
# Exact rectangular sums in Harman's minorant

Good cells are assembled as disjoint tuple families.  Their cellwise divisor-sift sums equal the
literal rectangular projection of the admissible Harman pair and triple sums.  The complementary
terms retain the exact source order, divisibility, and threshold predicates.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Source primes from one adjacent block. -/
def mtHarmanSourceBlock {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ) (i : Fin t) :
    Finset ℕ :=
  mtAdjacentPrimeBlock endpoint i ∩ P

/-- Pair tuples attached to one source-restricted good cell. -/
def mtHarmanPairCellSourceTuples {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (cell : Fin t × Fin t) : Finset (ℕ × ℕ) :=
  (mtHarmanSourceBlock endpoint P cell.1).product
    (mtHarmanSourceBlock endpoint P cell.2)

/-- Disjoint union of all source-restricted good pair rectangles. -/
def mtHarmanPairRectangularTuples {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) : Finset (ℕ × ℕ) :=
  (mtHarmanActiveGoodPairCells endpoint E).biUnion
    (mtHarmanPairCellSourceTuples endpoint P)

theorem pairwiseDisjoint_mtHarmanPairCellSourceTuples
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) :
    (↑(mtHarmanActiveGoodPairCells (t := t) endpoint E) : Set (Fin t × Fin t)).PairwiseDisjoint
      (mtHarmanPairCellSourceTuples endpoint P) := by
  intro cell hcell other hother hne
  rw [Finset.disjoint_left]
  intro q hq hqOther
  have hq' := Finset.mem_product.mp hq
  have hqOther' := Finset.mem_product.mp hqOther
  have hq₁ := (Finset.mem_inter.mp hq'.1).1
  have hq₂ := (Finset.mem_inter.mp hq'.2).1
  have hqOther₁ := (Finset.mem_inter.mp hqOther'.1).1
  have hqOther₂ := (Finset.mem_inter.mp hqOther'.2).1
  by_cases hfirst : cell.1 = other.1
  · have hsecond : cell.2 ≠ other.2 := by
      intro h
      exact hne (Prod.ext hfirst h)
    exact (Finset.disjoint_left.mp
      (mtAdjacentPrimeBlock_disjoint endpoint hmono cell.2 other.2 hsecond))
        hq₂ hqOther₂
  · exact (Finset.disjoint_left.mp
      (mtAdjacentPrimeBlock_disjoint endpoint hmono cell.1 other.1 hfirst))
        hq₁ hqOther₁

theorem mtHarmanPairRectangularTuples_eq_filter
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) :
    mtHarmanPairRectangularTuples (t := t) endpoint P E =
      (P.product P).filter fun q =>
        MTHarmanPairRectangular t endpoint E q.1 q.2 := by
  ext q
  simp only [mtHarmanPairRectangularTuples, Finset.mem_biUnion,
    mtHarmanPairCellSourceTuples, Finset.mem_product, mtHarmanSourceBlock,
    Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨cell, hcell, hq₁, hq₂⟩
    exact ⟨⟨hq₁.2, hq₂.2⟩, cell.1, cell.2, hcell, hq₁.1, hq₂.1⟩
  · rintro ⟨⟨hq₁P, hq₂P⟩, i₁, i₂, hcell, hq₁, hq₂⟩
    exact ⟨(i₁, i₂), hcell, ⟨hq₁, hq₁P⟩, hq₂, hq₂P⟩

/-- Sum of exact pair-cell convolutions across every active good rectangle. -/
def mtHarmanPairCellFamilySiftSum {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ :=
  ∑ cell ∈ mtHarmanActiveGoodPairCells endpoint E,
    mtHarmanPairCellSiftSum
      (mtHarmanSourceBlock endpoint P cell.1)
      (mtHarmanSourceBlock endpoint P cell.2) z n

/-- The pair-cell family is exactly the rectangular projection, with no multiplicity loss. -/
theorem mtHarmanPairCellFamilySiftSum_eq
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (z n : ℕ) :
    mtHarmanPairCellFamilySiftSum (t := t) endpoint P E z n =
      ∑ q ∈ P.product P,
        if MTHarmanPairRectangular t endpoint E q.1 q.2 then
          if q.1 * q.2 ∣ n then (rho (n / q.1 / q.2) z : ℂ) else 0
        else 0 := by
  let f : ℕ × ℕ → ℂ := fun q =>
    if q.1 * q.2 ∣ n then (rho (n / q.1 / q.2) z : ℂ) else 0
  calc
    mtHarmanPairCellFamilySiftSum (t := t) endpoint P E z n =
        ∑ cell ∈ mtHarmanActiveGoodPairCells endpoint E,
          ∑ q ∈ mtHarmanPairCellSourceTuples endpoint P cell, f q := by
      unfold mtHarmanPairCellFamilySiftSum mtHarmanPairCellSiftSum
      apply Finset.sum_congr rfl
      intro cell hcell
      exact (Finset.sum_product
        (mtHarmanSourceBlock endpoint P cell.1)
        (mtHarmanSourceBlock endpoint P cell.2) f).symm
    _ = ∑ q ∈ mtHarmanPairRectangularTuples endpoint P E, f q := by
      rw [Finset.sum_biUnion
        (pairwiseDisjoint_mtHarmanPairCellSourceTuples hmono P E)]
    _ = ∑ q ∈ (P.product P).filter fun q =>
        MTHarmanPairRectangular t endpoint E q.1 q.2, f q := by
      rw [mtHarmanPairRectangularTuples_eq_filter hmono]
    _ = ∑ q ∈ P.product P,
        if MTHarmanPairRectangular t endpoint E q.1 q.2 then f q else 0 := by
      rw [Finset.sum_filter]

/-- Literal pair term with all source predicates exposed. -/
def mtHarmanAdmissiblePairSiftSum
    (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ :=
  ∑ q ∈ P.product P,
    if q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < E ∧ q.1 * q.2 ∣ n then
      (rho (n / q.1 / q.2) z : ℂ)
    else 0

/-- Literal nonrectangular pair remainder. -/
def mtHarmanPairNonrectangularError {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ :=
  ∑ q ∈ P.product P,
    if q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < E ∧ q.1 * q.2 ∣ n ∧
        ¬MTHarmanPairRectangular t endpoint E q.1 q.2 then
      (rho (n / q.1 / q.2) z : ℂ)
    else 0

/-- Exact pair rectangularization: source term equals good-cell family plus literal bad support. -/
theorem mtHarmanAdmissiblePairSiftSum_eq_cells_add_error
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (z n : ℕ) :
    mtHarmanAdmissiblePairSiftSum P E z n =
      mtHarmanPairCellFamilySiftSum (t := t) endpoint P E z n +
        mtHarmanPairNonrectangularError endpoint P E z n := by
  rw [mtHarmanPairCellFamilySiftSum_eq hmono]
  unfold mtHarmanAdmissiblePairSiftSum mtHarmanPairNonrectangularError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hrect : MTHarmanPairRectangular t endpoint E q.1 q.2
  · obtain ⟨i₁, i₂, hcell, hq₁, hq₂⟩ := hrect
    have hadm := mtHarmanGoodPairCell_order_geometry
      hendpoint hmono (mem_mtHarmanActiveGoodPairCells.mp hcell).1 hq₁ hq₂
    by_cases hdvd : q.1 * q.2 ∣ n <;> simp [hrect, hadm.1, hadm.2, hdvd]
  · simp [hrect]

end

end RHTower.Sieve
