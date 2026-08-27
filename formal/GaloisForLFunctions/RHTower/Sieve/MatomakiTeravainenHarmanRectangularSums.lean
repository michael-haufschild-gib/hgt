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

local instance instDecidableMTHarmanPairRectangular
    {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) (q₁ q₂ : ℕ) :
    Decidable (MTHarmanPairRectangular t endpoint E q₁ q₂) :=
  Classical.propDecidable _

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
  (mtHarmanActiveGoodPairCells (t := t) endpoint E).biUnion
    (mtHarmanPairCellSourceTuples (t := t) endpoint P)

theorem pairwiseDisjoint_mtHarmanPairCellSourceTuples
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) :
    (↑(mtHarmanActiveGoodPairCells (t := t) endpoint E) : Set (Fin t × Fin t)).PairwiseDisjoint
      (mtHarmanPairCellSourceTuples endpoint P) := by
  intro cell hcell other hother hne
  change Disjoint (mtHarmanPairCellSourceTuples endpoint P cell)
    (mtHarmanPairCellSourceTuples endpoint P other)
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
    {t : ℕ} {endpoint : ℕ → ℕ} (_hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) :
    mtHarmanPairRectangularTuples (t := t) endpoint P E =
      (P.product P).filter fun q : ℕ × ℕ =>
        MTHarmanPairRectangular t endpoint E q.1 q.2 := by
  ext q
  rw [mtHarmanPairRectangularTuples, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨cell, hcell, hq⟩
    have hq' := Finset.mem_product.mp hq
    have hq₁ := Finset.mem_inter.mp hq'.1
    have hq₂ := Finset.mem_inter.mp hq'.2
    exact ⟨Finset.mem_product.mpr ⟨hq₁.2, hq₂.2⟩,
      cell.1, cell.2, hcell, hq₁.1, hq₂.1⟩
  · rintro ⟨hqP, i₁, i₂, hcell, hq₁, hq₂⟩
    have hqP' := Finset.mem_product.mp hqP
    refine ⟨(i₁, i₂), hcell, ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_inter.mpr ⟨hq₁, hqP'.1⟩,
        Finset.mem_inter.mpr ⟨hq₂, hqP'.2⟩⟩

/-- Sum of exact pair-cell convolutions across every active good rectangle. -/
def mtHarmanPairCellFamilySiftSum {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ := by
  classical
  exact ∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
    mtHarmanPairCellSiftSum
      (mtHarmanSourceBlock (t := t) endpoint P cell.1)
      (mtHarmanSourceBlock (t := t) endpoint P cell.2) z n

/-- The pair-cell family is exactly the rectangular projection, with no multiplicity loss. -/
theorem mtHarmanPairCellFamilySiftSum_eq
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (z n : ℕ) :
    mtHarmanPairCellFamilySiftSum (t := t) endpoint P E z n =
      ∑ q ∈ P.product P,
        if MTHarmanPairRectangular t endpoint E q.1 q.2 then
          if q.1 * q.2 ∣ n then (rho (n / q.1 / q.2) z : ℂ) else 0
        else 0 := by
  classical
  let f : ℕ × ℕ → ℂ := fun q =>
    if q.1 * q.2 ∣ n then (rho (n / q.1 / q.2) z : ℂ) else 0
  calc
    mtHarmanPairCellFamilySiftSum (t := t) endpoint P E z n =
        ∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
          ∑ q ∈ mtHarmanPairCellSourceTuples (t := t) endpoint P cell, f q := by
      unfold mtHarmanPairCellFamilySiftSum mtHarmanPairCellSiftSum
      apply Finset.sum_congr rfl
      intro cell hcell
      exact (Finset.sum_product
        (mtHarmanSourceBlock endpoint P cell.1)
        (mtHarmanSourceBlock endpoint P cell.2) f).symm
    _ = ∑ q ∈ mtHarmanPairRectangularTuples endpoint P E, f q := by
      unfold mtHarmanPairRectangularTuples
      exact (Finset.sum_biUnion
        (pairwiseDisjoint_mtHarmanPairCellSourceTuples (t := t) hmono P E)).symm
    _ = ∑ q ∈ (P.product P).filter fun q =>
        MTHarmanPairRectangular t endpoint E q.1 q.2, f q := by
      rw [mtHarmanPairRectangularTuples_eq_filter (t := t) hmono]
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

/-- The divisor-dependent prime window is the fixed prime interval filtered by divisibility. -/
theorem primeWindow_eq_primesIco_filter_dvd (n z D : ℕ) :
    primeWindow n z D = (primesIco z D).filter (fun q => q ∣ n) := by
  ext q
  simp only [mem_primeWindow, Finset.mem_filter, mem_primesIco]
  aesop

/-- Once `q₁` divides `n`, Harman's inner pair set is an exact filter of the fixed source
interval. -/
theorem harmanPairs_eq_primesIco_filter
    {z D E n q₁ : ℕ} (hq₁ : q₁ ∈ primeWindow n z D) :
    harmanPairs z E n q₁ =
      (primesIco z D).filter fun q₂ =>
        q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < (E : ℝ) ∧ q₁ * q₂ ∣ n := by
  ext q₂
  rw [harmanPairs, Finset.mem_filter, Finset.mem_filter]
  have hq₁' := mem_primeWindow.mp hq₁
  constructor
  · rintro ⟨hq₂, hgeom⟩
    have hq₂' := mem_primeWindow.mp hq₂
    refine ⟨mem_primesIco.mpr
      ⟨hq₂'.1.1, lt_trans hq₂'.1.2 hq₁'.1.2, hq₂'.2.1⟩,
        hq₂'.1.2, ?_, Nat.mul_dvd_of_dvd_div hq₁'.2.2 hq₂'.2.2⟩
    exact_mod_cast hgeom
  · rintro ⟨hq₂, hlt, hgeom, hdvd⟩
    have hq₂' := mem_primesIco.mp hq₂
    refine ⟨mem_primeWindow.mpr
      ⟨⟨hq₂'.1, hlt⟩, hq₂'.2.2, Nat.dvd_div_of_mul_dvd hdvd⟩, ?_⟩
    exact_mod_cast hgeom

/-- The exposed pair source is exactly Harman's original two-prime correction. -/
theorem mtHarmanAdmissiblePairSiftSum_primesIco
    (z D E n : ℕ) :
    mtHarmanAdmissiblePairSiftSum (primesIco z D) (E : ℝ) z n =
      (harmanS2 z D E n : ℂ) := by
  unfold mtHarmanAdmissiblePairSiftSum harmanS2
  push_cast
  rw [primeWindow_eq_primesIco_filter_dvd, Finset.sum_filter]
  calc
    (∑ q ∈ (primesIco z D).product (primesIco z D),
        if q.2 < q.1 ∧ (q.1 : ℝ) * (q.2 : ℝ) ^ 4 < (E : ℝ) ∧
            q.1 * q.2 ∣ n then
          (rho (n / q.1 / q.2) z : ℂ) else 0) =
        ∑ q₁ ∈ primesIco z D, ∑ q₂ ∈ primesIco z D,
          if q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < (E : ℝ) ∧
              q₁ * q₂ ∣ n then
            (rho (n / q₁ / q₂) z : ℂ) else 0 :=
      Finset.sum_product (primesIco z D) (primesIco z D) _
    _ = ∑ q₁ ∈ primesIco z D,
        if q₁ ∣ n then
          ∑ q₂ ∈ harmanPairs z E n q₁, (rho (n / q₁ / q₂) z : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      by_cases hdvd₁ : q₁ ∣ n
      · have hq₁win : q₁ ∈ primeWindow n z D := by
          rw [primeWindow_eq_primesIco_filter_dvd]
          exact Finset.mem_filter.mpr ⟨hq₁, hdvd₁⟩
        rw [if_pos hdvd₁, harmanPairs_eq_primesIco_filter hq₁win,
          Finset.sum_filter]
      · rw [if_neg hdvd₁]
        apply Finset.sum_eq_zero
        intro q₂ hq₂
        split_ifs with h
        · exact False.elim (hdvd₁ (dvd_trans (dvd_mul_right q₁ q₂) h.2.2))
        · rfl

/-- Literal nonrectangular pair remainder. -/
def mtHarmanPairNonrectangularError {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ := by
  classical
  exact ∑ q ∈ P.product P,
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
        mtHarmanPairNonrectangularError (t := t) endpoint P E z n := by
  classical
  rw [mtHarmanPairCellFamilySiftSum_eq (t := t) hmono]
  unfold mtHarmanAdmissiblePairSiftSum mtHarmanPairNonrectangularError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hrect : MTHarmanPairRectangular t endpoint E q.1 q.2
  · have hrect' := hrect
    obtain ⟨i₁, i₂, hcell, hq₁, hq₂⟩ := hrect
    have hadm := mtHarmanGoodPairCell_order_geometry
      hendpoint hmono (mem_mtHarmanActiveGoodPairCells.mp hcell).1 hq₁ hq₂
    by_cases hdvd : q.1 * q.2 ∣ n <;> simp [hrect', hadm.1, hadm.2, hdvd]
  · simp [hrect]

local instance instDecidableMTHarmanTripleRectangular
    {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) (q₁ q₂ q₃ : ℕ) :
    Decidable (MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃) :=
  Classical.propDecidable _

/-- Triple tuples attached to one source-restricted good cell. -/
def mtHarmanTripleCellSourceTuples {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (cell : (Fin t × Fin t) × Fin t) :
    Finset ((ℕ × ℕ) × ℕ) :=
  ((mtHarmanSourceBlock endpoint P cell.1.1).product
    (mtHarmanSourceBlock endpoint P cell.1.2)).product
      (mtHarmanSourceBlock endpoint P cell.2)

/-- Disjoint union of all source-restricted good triple rectangles. -/
def mtHarmanTripleRectangularTuples {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) : Finset ((ℕ × ℕ) × ℕ) :=
  (mtHarmanActiveGoodTripleCells (t := t) endpoint E).biUnion
    (mtHarmanTripleCellSourceTuples (t := t) endpoint P)

theorem pairwiseDisjoint_mtHarmanTripleCellSourceTuples
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) :
    (↑(mtHarmanActiveGoodTripleCells (t := t) endpoint E) :
      Set ((Fin t × Fin t) × Fin t)).PairwiseDisjoint
        (mtHarmanTripleCellSourceTuples endpoint P) := by
  intro cell hcell other hother hne
  change Disjoint (mtHarmanTripleCellSourceTuples endpoint P cell)
    (mtHarmanTripleCellSourceTuples endpoint P other)
  rw [Finset.disjoint_left]
  intro q hq hqOther
  have hq' := Finset.mem_product.mp hq
  have hqPair := Finset.mem_product.mp hq'.1
  have hqOther' := Finset.mem_product.mp hqOther
  have hqOtherPair := Finset.mem_product.mp hqOther'.1
  have hq₁ := (Finset.mem_inter.mp hqPair.1).1
  have hq₂ := (Finset.mem_inter.mp hqPair.2).1
  have hq₃ := (Finset.mem_inter.mp hq'.2).1
  have hqOther₁ := (Finset.mem_inter.mp hqOtherPair.1).1
  have hqOther₂ := (Finset.mem_inter.mp hqOtherPair.2).1
  have hqOther₃ := (Finset.mem_inter.mp hqOther'.2).1
  by_cases hfirst : cell.1.1 = other.1.1
  · by_cases hsecond : cell.1.2 = other.1.2
    · have hthird : cell.2 ≠ other.2 := by
        intro h
        exact hne (Prod.ext (Prod.ext hfirst hsecond) h)
      exact (Finset.disjoint_left.mp
        (mtAdjacentPrimeBlock_disjoint endpoint hmono cell.2 other.2 hthird))
          hq₃ hqOther₃
    · exact (Finset.disjoint_left.mp
        (mtAdjacentPrimeBlock_disjoint endpoint hmono cell.1.2 other.1.2 hsecond))
          hq₂ hqOther₂
  · exact (Finset.disjoint_left.mp
      (mtAdjacentPrimeBlock_disjoint endpoint hmono cell.1.1 other.1.1 hfirst))
        hq₁ hqOther₁

theorem mtHarmanTripleRectangularTuples_eq_filter
    {t : ℕ} {endpoint : ℕ → ℕ} (_hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) :
    mtHarmanTripleRectangularTuples (t := t) endpoint P E =
      ((P.product P).product P).filter fun q : (ℕ × ℕ) × ℕ =>
        MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2 := by
  ext q
  rw [mtHarmanTripleRectangularTuples, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨cell, hcell, hq⟩
    have hq' := Finset.mem_product.mp hq
    have hqPair := Finset.mem_product.mp hq'.1
    have hq₁ := Finset.mem_inter.mp hqPair.1
    have hq₂ := Finset.mem_inter.mp hqPair.2
    have hq₃ := Finset.mem_inter.mp hq'.2
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hq₁.2, hq₂.2⟩, hq₃.2⟩,
      cell.1.1, cell.1.2, cell.2, hcell, hq₁.1, hq₂.1, hq₃.1⟩
  · rintro ⟨hqP, i₁, i₂, i₃, hcell, hq₁, hq₂, hq₃⟩
    have hqP' := Finset.mem_product.mp hqP
    have hqPairP := Finset.mem_product.mp hqP'.1
    refine ⟨((i₁, i₂), i₃), hcell, ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_inter.mpr ⟨hq₁, hqPairP.1⟩,
          Finset.mem_inter.mpr ⟨hq₂, hqPairP.2⟩⟩,
        Finset.mem_inter.mpr ⟨hq₃, hqP'.2⟩⟩

/-- Sum of exact triple-cell convolutions across every active good rectangle. -/
def mtHarmanTripleCellFamilySiftSum {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ := by
  classical
  exact ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
    mtHarmanTripleCellSiftSum
      (mtHarmanSourceBlock endpoint P cell.1.1)
      (mtHarmanSourceBlock endpoint P cell.1.2)
      (mtHarmanSourceBlock endpoint P cell.2) z n

/-- The triple-cell family is exactly the rectangular projection, with no multiplicity loss. -/
theorem mtHarmanTripleCellFamilySiftSum_eq
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (z n : ℕ) :
    mtHarmanTripleCellFamilySiftSum (t := t) endpoint P E z n =
      ∑ q ∈ (P.product P).product P,
        if MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2 then
          if q.1.1 * q.1.2 * q.2 ∣ n then
            (rho (n / q.1.1 / q.1.2 / q.2) z : ℂ) else 0
        else 0 := by
  let f : (ℕ × ℕ) × ℕ → ℂ := fun q =>
    if q.1.1 * q.1.2 * q.2 ∣ n then
      (rho (n / q.1.1 / q.1.2 / q.2) z : ℂ) else 0
  calc
    mtHarmanTripleCellFamilySiftSum (t := t) endpoint P E z n =
        ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
          ∑ q ∈ mtHarmanTripleCellSourceTuples endpoint P cell, f q := by
      unfold mtHarmanTripleCellFamilySiftSum mtHarmanTripleCellSiftSum
      apply Finset.sum_congr rfl
      intro cell hcell
      let S₁ := mtHarmanSourceBlock endpoint P cell.1.1
      let S₂ := mtHarmanSourceBlock endpoint P cell.1.2
      let S₃ := mtHarmanSourceBlock endpoint P cell.2
      calc
        (∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃, f ((q₁, q₂), q₃)) =
            ∑ q₁q₂ ∈ S₁.product S₂,
              ∑ q₃ ∈ S₃, f (q₁q₂, q₃) := by
          exact (Finset.sum_product S₁ S₂
            (fun q₁q₂ => ∑ q₃ ∈ S₃, f (q₁q₂, q₃))).symm
        _ = ∑ q ∈ (S₁.product S₂).product S₃, f q := by
          exact (Finset.sum_product (S₁.product S₂) S₃ f).symm
    _ = ∑ q ∈ mtHarmanTripleRectangularTuples endpoint P E, f q := by
      unfold mtHarmanTripleRectangularTuples
      exact (Finset.sum_biUnion
        (pairwiseDisjoint_mtHarmanTripleCellSourceTuples
          (t := t) hmono P E)).symm
    _ = ∑ q ∈ ((P.product P).product P).filter fun q =>
        MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2, f q := by
      rw [mtHarmanTripleRectangularTuples_eq_filter (t := t) hmono]
    _ = ∑ q ∈ (P.product P).product P,
        if MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2 then f q else 0 := by
      rw [Finset.sum_filter]

/-- Literal triple term with all source predicates exposed. -/
def mtHarmanAdmissibleTripleSiftSum
    (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ :=
  ∑ q ∈ (P.product P).product P,
    if q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
        (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧
        q.1.1 * q.1.2 * q.2 ∣ n then
      (rho (n / q.1.1 / q.1.2 / q.2) z : ℂ)
    else 0

/-- For an admissible pair, Harman's third-prime window is an exact fixed-source filter. -/
theorem primeWindow_div_div_eq_primesIco_filter
    {z D E n q₁ q₂ : ℕ} (hq₁ : q₁ ∈ primeWindow n z D)
    (hq₂ : q₂ ∈ harmanPairs z E n q₁) :
    primeWindow (n / q₁ / q₂) z q₂ =
      (primesIco z D).filter fun q₃ => q₃ < q₂ ∧ q₁ * q₂ * q₃ ∣ n := by
  have hq₁' := mem_primeWindow.mp hq₁
  have hq₂filter := Finset.mem_filter.mp hq₂
  have hq₂' := mem_primeWindow.mp hq₂filter.1
  have hpairdvd : q₁ * q₂ ∣ n :=
    Nat.mul_dvd_of_dvd_div hq₁'.2.2 hq₂'.2.2
  ext q₃
  rw [Finset.mem_filter]
  constructor
  · intro hq₃
    have hq₃' := mem_primeWindow.mp hq₃
    refine ⟨mem_primesIco.mpr
      ⟨hq₃'.1.1, lt_trans hq₃'.1.2 (lt_trans hq₂'.1.2 hq₁'.1.2),
        hq₃'.2.1⟩, hq₃'.1.2, ?_⟩
    apply Nat.mul_dvd_of_dvd_div hpairdvd
    simpa [Nat.div_div_eq_div_mul] using hq₃'.2.2
  · rintro ⟨hq₃, hlt, hdvd⟩
    have hq₃' := mem_primesIco.mp hq₃
    apply mem_primeWindow.mpr
    refine ⟨⟨hq₃'.1, hlt⟩, hq₃'.2.2, ?_⟩
    simpa [Nat.div_div_eq_div_mul] using Nat.dvd_div_of_mul_dvd hdvd

/-- The exposed triple source is exactly Harman's original three-prime correction. -/
theorem mtHarmanAdmissibleTripleSiftSum_primesIco
    (z D E n : ℕ) :
    mtHarmanAdmissibleTripleSiftSum (primesIco z D) (E : ℝ) z n =
      (harmanS3 z D E n : ℂ) := by
  unfold mtHarmanAdmissibleTripleSiftSum harmanS3
  push_cast
  rw [primeWindow_eq_primesIco_filter_dvd, Finset.sum_filter]
  calc
    (∑ q ∈ ((primesIco z D).product (primesIco z D)).product (primesIco z D),
        if q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
            (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < (E : ℝ) ∧
            q.1.1 * q.1.2 * q.2 ∣ n then
          (rho (n / q.1.1 / q.1.2 / q.2) z : ℂ) else 0) =
        ∑ q₁q₂ ∈ (primesIco z D).product (primesIco z D),
          ∑ q₃ ∈ primesIco z D,
            if q₃ < q₁q₂.2 ∧ q₁q₂.2 < q₁q₂.1 ∧
                (q₁q₂.1 : ℝ) * (q₁q₂.2 : ℝ) ^ 4 < (E : ℝ) ∧
                q₁q₂.1 * q₁q₂.2 * q₃ ∣ n then
              (rho (n / q₁q₂.1 / q₁q₂.2 / q₃) z : ℂ) else 0 :=
      Finset.sum_product ((primesIco z D).product (primesIco z D)) (primesIco z D) _
    _ = ∑ q₁ ∈ primesIco z D, ∑ q₂ ∈ primesIco z D,
        ∑ q₃ ∈ primesIco z D,
          if q₃ < q₂ ∧ q₂ < q₁ ∧
              (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < (E : ℝ) ∧
              q₁ * q₂ * q₃ ∣ n then
            (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0 :=
      Finset.sum_product (primesIco z D) (primesIco z D) _
    _ = ∑ q₁ ∈ primesIco z D,
        if q₁ ∣ n then
          ∑ q₂ ∈ harmanPairs z E n q₁,
            ∑ q₃ ∈ primeWindow (n / q₁ / q₂) z q₂,
              (rho (n / q₁ / q₂ / q₃) z : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      by_cases hdvd₁ : q₁ ∣ n
      · have hq₁win : q₁ ∈ primeWindow n z D := by
          rw [primeWindow_eq_primesIco_filter_dvd]
          exact Finset.mem_filter.mpr ⟨hq₁, hdvd₁⟩
        rw [if_pos hdvd₁, harmanPairs_eq_primesIco_filter hq₁win,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro q₂ hq₂
        by_cases hpair : q₂ < q₁ ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < (E : ℝ) ∧ q₁ * q₂ ∣ n
        · have hq₂pair : q₂ ∈ harmanPairs z E n q₁ := by
            rw [harmanPairs_eq_primesIco_filter hq₁win]
            exact Finset.mem_filter.mpr ⟨hq₂, hpair⟩
          rw [if_pos hpair,
            primeWindow_div_div_eq_primesIco_filter hq₁win hq₂pair,
            Finset.sum_filter]
          simp only [hpair.1, hpair.2.1, true_and]
        · rw [if_neg hpair]
          apply Finset.sum_eq_zero
          intro q₃ hq₃
          split_ifs with h
          · exact False.elim (hpair ⟨h.2.1, h.2.2.1,
              dvd_trans (dvd_mul_right (q₁ * q₂) q₃) h.2.2.2⟩)
          · rfl
      · rw [if_neg hdvd₁]
        apply Finset.sum_eq_zero
        intro q₂ hq₂
        apply Finset.sum_eq_zero
        intro q₃ hq₃
        split_ifs with h
        · apply False.elim
          apply hdvd₁
          exact dvd_trans (by
            simp [Nat.mul_assoc]) h.2.2.2
        · rfl

/-- Literal nonrectangular triple remainder. -/
def mtHarmanTripleNonrectangularError {t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ) (z n : ℕ) : ℂ := by
  classical
  exact ∑ q ∈ (P.product P).product P,
    if q.2 < q.1.2 ∧ q.1.2 < q.1.1 ∧
        (q.1.1 : ℝ) * (q.1.2 : ℝ) ^ 4 < E ∧
        q.1.1 * q.1.2 * q.2 ∣ n ∧
        ¬MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2 then
      (rho (n / q.1.1 / q.1.2 / q.2) z : ℂ)
    else 0

/-- Exact triple rectangularization: source term equals good-cell family plus literal bad
support. -/
theorem mtHarmanAdmissibleTripleSiftSum_eq_cells_add_error
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (z n : ℕ) :
    mtHarmanAdmissibleTripleSiftSum P E z n =
      mtHarmanTripleCellFamilySiftSum (t := t) endpoint P E z n +
        mtHarmanTripleNonrectangularError (t := t) endpoint P E z n := by
  rw [mtHarmanTripleCellFamilySiftSum_eq (t := t) hmono]
  unfold mtHarmanAdmissibleTripleSiftSum mtHarmanTripleNonrectangularError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hrect : MTHarmanTripleRectangular t endpoint E q.1.1 q.1.2 q.2
  · have hrect' := hrect
    obtain ⟨i₁, i₂, i₃, hcell, hq₁, hq₂, hq₃⟩ := hrect
    have hadm := mtHarmanGoodTripleCell_orders_geometry
      hendpoint hmono (mem_mtHarmanActiveGoodTripleCells.mp hcell).1 hq₁ hq₂ hq₃
    by_cases hdvd : q.1.1 * q.1.2 * q.2 ∣ n <;>
      simp [hrect', hadm.1, hadm.2.1, hadm.2.2, hdvd]
  · simp [hrect]

end

end RHTower.Sieve
