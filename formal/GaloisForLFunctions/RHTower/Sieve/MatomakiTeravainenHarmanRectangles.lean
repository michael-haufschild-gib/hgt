import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanBoundary
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayerChains

/-!
# Exact rectangular cells for Harman pairs and triples

Distinct ordered aligned cells remove both prime-order predicates.  A cell whose upper pair
product lies below the Harman threshold removes the remaining coupled geometry predicate.  The
only tuples outside these literal rectangles are same-cell order collisions and the threshold
boundary fibre already estimated at paper scale.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Ordered pair cells on which `q₂<q₁` and `q₁q₂⁴<E` hold uniformly. -/
def mtHarmanGoodPairCells {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) :
    Finset (Fin t × Fin t) :=
  Finset.univ.filter fun cell =>
    cell.2.1 < cell.1.1 ∧
      mtAdjacentBlockUpperScale endpoint cell.1 *
        mtAdjacentBlockUpperScale endpoint cell.2 ^ (4 : ℕ) < E

theorem mem_mtHarmanGoodPairCells {t : ℕ} {endpoint : ℕ → ℕ} {E : ℝ}
    {i₁ i₂ : Fin t} :
    (i₁, i₂) ∈ mtHarmanGoodPairCells endpoint E ↔
      i₂.1 < i₁.1 ∧
        mtAdjacentBlockUpperScale endpoint i₁ *
          mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) < E := by
  simp [mtHarmanGoodPairCells]

/-- Ordered triple cells on which `q₃<q₂<q₁` and `q₁q₂⁴<E` hold uniformly. -/
def mtHarmanGoodTripleCells {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) :
    Finset ((Fin t × Fin t) × Fin t) :=
  Finset.univ.filter fun cell =>
    cell.2.1 < cell.1.2.1 ∧ cell.1.2.1 < cell.1.1.1 ∧
      mtAdjacentBlockUpperScale endpoint cell.1.1 *
        mtAdjacentBlockUpperScale endpoint cell.1.2 ^ (4 : ℕ) < E

theorem mem_mtHarmanGoodTripleCells {t : ℕ} {endpoint : ℕ → ℕ} {E : ℝ}
    {i₁ i₂ i₃ : Fin t} :
    ((i₁, i₂), i₃) ∈ mtHarmanGoodTripleCells endpoint E ↔
      i₃.1 < i₂.1 ∧ i₂.1 < i₁.1 ∧
        mtAdjacentBlockUpperScale endpoint i₁ *
          mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) < E := by
  simp [mtHarmanGoodTripleCells]

/-- Every prime pair chosen from one good cell satisfies both coupled source predicates. -/
theorem mtHarmanGoodPairCell_order_geometry
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {E : ℝ} {i₁ i₂ : Fin t}
    (hcell : (i₁, i₂) ∈ mtHarmanGoodPairCells endpoint E)
    {q₁ q₂ : ℕ}
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂) :
    q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E := by
  have hcell' := mem_mtHarmanGoodPairCells.mp hcell
  exact ⟨prime_lt_of_adjacentBlock_index_lt hmono hcell'.1 hq₁ hq₂,
    (adjacentBlock_product_le_upper hendpoint hq₁ hq₂).trans_lt hcell'.2⟩

/-- Every prime triple chosen from one good cell satisfies both prime orders and the coupled
source geometry. -/
theorem mtHarmanGoodTripleCell_orders_geometry
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {E : ℝ} {i₁ i₂ i₃ : Fin t}
    (hcell : ((i₁, i₂), i₃) ∈ mtHarmanGoodTripleCells endpoint E)
    {q₁ q₂ q₃ : ℕ}
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (hq₃ : q₃ ∈ mtAdjacentPrimeBlock endpoint i₃) :
    q₃ < q₂ ∧ q₂ < q₁ ∧ (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E := by
  have hcell' := mem_mtHarmanGoodTripleCells.mp hcell
  exact ⟨prime_lt_of_adjacentBlock_index_lt hmono hcell'.1 hq₂ hq₃,
    prime_lt_of_adjacentBlock_index_lt hmono hcell'.2.1 hq₁ hq₂,
    (adjacentBlock_product_le_upper hendpoint hq₁ hq₂).trans_lt hcell'.2.2⟩

/-- Nonempty good pair cells; these are exactly the pair rectangles that contribute a nonzero
piece. -/
def mtHarmanActiveGoodPairCells {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) :
    Finset (Fin t × Fin t) :=
  (mtHarmanGoodPairCells endpoint E).filter fun cell =>
    (mtAdjacentPrimeBlock endpoint cell.1).Nonempty ∧
      (mtAdjacentPrimeBlock endpoint cell.2).Nonempty

theorem mem_mtHarmanActiveGoodPairCells
    {t : ℕ} {endpoint : ℕ → ℕ} {E : ℝ} {i₁ i₂ : Fin t} :
    (i₁, i₂) ∈ mtHarmanActiveGoodPairCells endpoint E ↔
      (i₁, i₂) ∈ mtHarmanGoodPairCells endpoint E ∧
        (mtAdjacentPrimeBlock endpoint i₁).Nonempty ∧
          (mtAdjacentPrimeBlock endpoint i₂).Nonempty := by
  simp [mtHarmanActiveGoodPairCells]

/-- Nonempty good triple cells; these are exactly the triple rectangles that contribute a nonzero
piece. -/
def mtHarmanActiveGoodTripleCells {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ) :
    Finset ((Fin t × Fin t) × Fin t) :=
  (mtHarmanGoodTripleCells endpoint E).filter fun cell =>
    (mtAdjacentPrimeBlock endpoint cell.1.1).Nonempty ∧
      (mtAdjacentPrimeBlock endpoint cell.1.2).Nonempty ∧
        (mtAdjacentPrimeBlock endpoint cell.2).Nonempty

theorem mem_mtHarmanActiveGoodTripleCells
    {t : ℕ} {endpoint : ℕ → ℕ} {E : ℝ} {i₁ i₂ i₃ : Fin t} :
    ((i₁, i₂), i₃) ∈ mtHarmanActiveGoodTripleCells endpoint E ↔
      ((i₁, i₂), i₃) ∈ mtHarmanGoodTripleCells endpoint E ∧
        (mtAdjacentPrimeBlock endpoint i₁).Nonempty ∧
          (mtAdjacentPrimeBlock endpoint i₂).Nonempty ∧
            (mtAdjacentPrimeBlock endpoint i₃).Nonempty := by
  simp [mtHarmanActiveGoodTripleCells]

/-- Active good pair-cell count is at most the square of the active block count. -/
theorem card_mtHarmanActiveGoodPairCells_le {t : ℕ}
    (endpoint : ℕ → ℕ) (E : ℝ) :
    (mtHarmanActiveGoodPairCells (t := t) endpoint E).card ≤
      (mtActiveBlockIndices (mtAdjacentPrimeBlock (t := t) endpoint)).card ^ (2 : ℕ) := by
  have hsubset : mtHarmanActiveGoodPairCells (t := t) endpoint E ⊆
      (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)).product
        (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)) := by
    intro cell hcell
    have hactive := (mem_mtHarmanActiveGoodPairCells.mp hcell).2
    exact Finset.mem_product.mpr ⟨by
      simp [mtActiveBlockIndices, hactive.1], by
      simp [mtActiveBlockIndices, hactive.2]⟩
  calc
    (mtHarmanActiveGoodPairCells (t := t) endpoint E).card ≤
        ((mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)).product
          (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint))).card :=
      Finset.card_le_card hsubset
    _ = (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)).card ^ (2 : ℕ) := by
      let active : Finset (Fin t) :=
        mtActiveBlockIndices (mtAdjacentPrimeBlock (t := t) endpoint)
      change (active.product active).card = active.card ^ (2 : ℕ)
      calc
        (active.product active).card = active.card * active.card := by
          exact Finset.card_product active active
        _ = active.card ^ (2 : ℕ) := (pow_two active.card).symm

/-- Active good triple-cell count is at most the cube of the active block count. -/
theorem card_mtHarmanActiveGoodTripleCells_le {t : ℕ}
    (endpoint : ℕ → ℕ) (E : ℝ) :
    (mtHarmanActiveGoodTripleCells (t := t) endpoint E).card ≤
      (mtActiveBlockIndices (mtAdjacentPrimeBlock (t := t) endpoint)).card ^ (3 : ℕ) := by
  have hsubset : mtHarmanActiveGoodTripleCells (t := t) endpoint E ⊆
      ((mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)).product
        (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint))).product
          (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)) := by
    intro cell hcell
    have hactive := (mem_mtHarmanActiveGoodTripleCells.mp hcell).2
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨by
      simp [mtActiveBlockIndices, hactive.1], by
      simp [mtActiveBlockIndices, hactive.2.1]⟩, by
      simp [mtActiveBlockIndices, hactive.2.2]⟩
  calc
    (mtHarmanActiveGoodTripleCells (t := t) endpoint E).card ≤
        (((mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)).product
          (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint))).product
            (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint))).card :=
      Finset.card_le_card hsubset
    _ = (mtActiveBlockIndices (mtAdjacentPrimeBlock endpoint)).card ^ (3 : ℕ) := by
      let active : Finset (Fin t) :=
        mtActiveBlockIndices (mtAdjacentPrimeBlock (t := t) endpoint)
      change ((active.product active).product active).card = active.card ^ (3 : ℕ)
      calc
        ((active.product active).product active).card =
            (active.product active).card * active.card := by
          exact Finset.card_product (active.product active) active
        _ = (active.card * active.card) * active.card := by
          rw [show (active.product active).card = active.card * active.card by
            exact Finset.card_product active active]
        _ = active.card ^ (3 : ℕ) := by ring

/-- Every prime in the complete adjacent source interval belongs to one schedule block. -/
theorem exists_mem_mtAdjacentPrimeBlock_of_mem_primesIco
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {q : ℕ} (hq : q ∈ primesIco (endpoint 0) (endpoint t)) :
    ∃ i : Fin t, q ∈ mtAdjacentPrimeBlock endpoint i := by
  have hqUnion : q ∈
      (mtBlockPrefix (Fin.last t)).biUnion (mtAdjacentPrimeBlock endpoint) := by
    rw [mtAdjacentPrimeBlock_prefix_biUnion endpoint hmono]
    simpa using hq
  obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqUnion
  exact ⟨i, hqi⟩

/-- A pair lies in one literal nonempty good rectangle. -/
def MTHarmanPairRectangular (t : ℕ) (endpoint : ℕ → ℕ) (E : ℝ)
    (q₁ q₂ : ℕ) : Prop :=
  ∃ i₁ i₂ : Fin t,
    (i₁, i₂) ∈ mtHarmanActiveGoodPairCells endpoint E ∧
      q₁ ∈ mtAdjacentPrimeBlock endpoint i₁ ∧
        q₂ ∈ mtAdjacentPrimeBlock endpoint i₂

/-- A triple lies in one literal nonempty good rectangle. -/
def MTHarmanTripleRectangular (t : ℕ) (endpoint : ℕ → ℕ) (E : ℝ)
    (q₁ q₂ q₃ : ℕ) : Prop :=
  ∃ i₁ i₂ i₃ : Fin t,
    ((i₁, i₂), i₃) ∈ mtHarmanActiveGoodTripleCells endpoint E ∧
      q₁ ∈ mtAdjacentPrimeBlock endpoint i₁ ∧
        q₂ ∈ mtAdjacentPrimeBlock endpoint i₂ ∧
          q₃ ∈ mtAdjacentPrimeBlock endpoint i₃

/-- Exact pair classification: uniformly good rectangle, same-cell collision, or threshold
boundary fibre. -/
theorem matomakiTeravainen_admissiblePair_cellClassification
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {S : Finset ℕ} {i₁ i₂ : Fin t} {q₁ q₂ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁S : q₁ ∈ S)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (horder : q₂ < q₁)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E) :
    (i₁, i₂) ∈ mtHarmanGoodPairCells endpoint E ∨
      i₂ = i₁ ∨
        q₁ ∈ mtHarmanThresholdBoundaryFibre S δ E q₂ := by
  rcases adjacentBlock_eq_or_lt_of_prime_lt hmono hq₁ hq₂ horder with hsame | hidx
  · exact Or.inr (Or.inl hsame)
  · rcases adjacentBlock_good_or_thresholdBoundary hendpoint hq₁ hq₂ hgeometry with
      hgood | hboundary
    · exact Or.inl (mem_mtHarmanGoodPairCells.mpr ⟨hidx, hgood⟩)
    · exact Or.inr (Or.inr (adjacentBlock_thresholdBoundary_mem_harmanFibre
        hendpoint hδ hband hq₁S hq₁ hq₂ hgeometry hboundary.2))

/-- Exact triple classification: uniformly good rectangle, one of two same-cell order collisions,
or the same pair-threshold boundary fibre. -/
theorem matomakiTeravainen_admissibleTriple_cellClassification
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {S : Finset ℕ} {i₁ i₂ i₃ : Fin t} {q₁ q₂ q₃ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁S : q₁ ∈ S)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (hq₃ : q₃ ∈ mtAdjacentPrimeBlock endpoint i₃)
    (horder₂₁ : q₂ < q₁) (horder₃₂ : q₃ < q₂)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E) :
    ((i₁, i₂), i₃) ∈ mtHarmanGoodTripleCells endpoint E ∨
      i₂ = i₁ ∨ i₃ = i₂ ∨
        q₁ ∈ mtHarmanThresholdBoundaryFibre S δ E q₂ := by
  rcases matomakiTeravainen_admissiblePair_cellClassification
      hendpoint hmono hδ hband hq₁S hq₁ hq₂ horder₂₁ hgeometry with
    hgoodPair | hcollisionOrBoundary
  · rcases adjacentBlock_eq_or_lt_of_prime_lt hmono hq₂ hq₃ horder₃₂ with
      hsame | hidx₃₂
    · exact Or.inr (Or.inr (Or.inl hsame))
    · have hpair := mem_mtHarmanGoodPairCells.mp hgoodPair
      exact Or.inl (mem_mtHarmanGoodTripleCells.mpr ⟨hidx₃₂, hpair⟩)
  · rcases hcollisionOrBoundary with hsame | hboundary
    · exact Or.inr (Or.inl hsame)
    · exact Or.inr (Or.inr (Or.inr hboundary))

/-- Pair classification with empty rectangles removed. -/
theorem matomakiTeravainen_admissiblePair_activeCellClassification
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {S : Finset ℕ} {i₁ i₂ : Fin t} {q₁ q₂ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁S : q₁ ∈ S)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (horder : q₂ < q₁)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E) :
    (i₁, i₂) ∈ mtHarmanActiveGoodPairCells endpoint E ∨
      i₂ = i₁ ∨
        q₁ ∈ mtHarmanThresholdBoundaryFibre S δ E q₂ := by
  rcases matomakiTeravainen_admissiblePair_cellClassification
      hendpoint hmono hδ hband hq₁S hq₁ hq₂ horder hgeometry with
    hgood | hbad
  · exact Or.inl (mem_mtHarmanActiveGoodPairCells.mpr
      ⟨hgood, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩)
  · exact Or.inr hbad

/-- Triple classification with empty rectangles removed. -/
theorem matomakiTeravainen_admissibleTriple_activeCellClassification
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {S : Finset ℕ} {i₁ i₂ i₃ : Fin t} {q₁ q₂ q₃ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁S : q₁ ∈ S)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (hq₃ : q₃ ∈ mtAdjacentPrimeBlock endpoint i₃)
    (horder₂₁ : q₂ < q₁) (horder₃₂ : q₃ < q₂)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E) :
    ((i₁, i₂), i₃) ∈ mtHarmanActiveGoodTripleCells endpoint E ∨
      i₂ = i₁ ∨ i₃ = i₂ ∨
        q₁ ∈ mtHarmanThresholdBoundaryFibre S δ E q₂ := by
  rcases matomakiTeravainen_admissibleTriple_cellClassification
      hendpoint hmono hδ hband hq₁S hq₁ hq₂ hq₃
        horder₂₁ horder₃₂ hgeometry with hgood | hbad
  · exact Or.inl (mem_mtHarmanActiveGoodTripleCells.mpr
      ⟨hgood, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, ⟨q₃, hq₃⟩⟩)
  · exact Or.inr hbad

/-- Global pair support theorem: every admissible source-window pair outside the rectangular
family is a same-cell collision or belongs to the threshold-boundary fibre. -/
theorem matomakiTeravainen_admissiblePair_not_rectangular
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {q₁ q₂ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁ : q₁ ∈ primesIco (endpoint 0) (endpoint t))
    (hq₂ : q₂ ∈ primesIco (endpoint 0) (endpoint t))
    (horder : q₂ < q₁)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E)
    (hnot : ¬MTHarmanPairRectangular t endpoint E q₁ q₂) :
    (∃ i : Fin t,
      q₁ ∈ mtAdjacentPrimeBlock endpoint i ∧
        q₂ ∈ mtAdjacentPrimeBlock endpoint i) ∨
      q₁ ∈ mtHarmanThresholdBoundaryFibre
        (primesIco (endpoint 0) (endpoint t)) δ E q₂ := by
  obtain ⟨i₁, hq₁i⟩ := exists_mem_mtAdjacentPrimeBlock_of_mem_primesIco hmono hq₁
  obtain ⟨i₂, hq₂i⟩ := exists_mem_mtAdjacentPrimeBlock_of_mem_primesIco hmono hq₂
  rcases matomakiTeravainen_admissiblePair_activeCellClassification
      hendpoint hmono hδ hband hq₁ hq₁i hq₂i horder hgeometry with
    hgood | hbad
  · exact absurd ⟨i₁, i₂, hgood, hq₁i, hq₂i⟩ hnot
  · rcases hbad with hsame | hboundary
    · subst i₂
      exact Or.inl ⟨i₁, hq₁i, hq₂i⟩
    · exact Or.inr hboundary

/-- Global triple support theorem: every admissible source-window triple outside the rectangular
family is one of the two same-cell order collisions or belongs to the pair-threshold boundary
fibre. -/
theorem matomakiTeravainen_admissibleTriple_not_rectangular
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    {q₁ q₂ q₃ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁ : q₁ ∈ primesIco (endpoint 0) (endpoint t))
    (hq₂ : q₂ ∈ primesIco (endpoint 0) (endpoint t))
    (hq₃ : q₃ ∈ primesIco (endpoint 0) (endpoint t))
    (horder₂₁ : q₂ < q₁) (horder₃₂ : q₃ < q₂)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E)
    (hnot : ¬MTHarmanTripleRectangular t endpoint E q₁ q₂ q₃) :
    (∃ i : Fin t,
      q₁ ∈ mtAdjacentPrimeBlock endpoint i ∧
        q₂ ∈ mtAdjacentPrimeBlock endpoint i) ∨
      (∃ i : Fin t,
        q₂ ∈ mtAdjacentPrimeBlock endpoint i ∧
          q₃ ∈ mtAdjacentPrimeBlock endpoint i) ∨
        q₁ ∈ mtHarmanThresholdBoundaryFibre
          (primesIco (endpoint 0) (endpoint t)) δ E q₂ := by
  obtain ⟨i₁, hq₁i⟩ := exists_mem_mtAdjacentPrimeBlock_of_mem_primesIco hmono hq₁
  obtain ⟨i₂, hq₂i⟩ := exists_mem_mtAdjacentPrimeBlock_of_mem_primesIco hmono hq₂
  obtain ⟨i₃, hq₃i⟩ := exists_mem_mtAdjacentPrimeBlock_of_mem_primesIco hmono hq₃
  rcases matomakiTeravainen_admissibleTriple_activeCellClassification
      hendpoint hmono hδ hband hq₁ hq₁i hq₂i hq₃i
        horder₂₁ horder₃₂ hgeometry with hgood | hbad
  · exact absurd ⟨i₁, i₂, i₃, hgood, hq₁i, hq₂i, hq₃i⟩ hnot
  · rcases hbad with hsame₁₂ | hsame₂₃ | hboundary
    · subst i₂
      exact Or.inl ⟨i₁, hq₁i, hq₂i⟩
    · subst i₃
      exact Or.inr (Or.inl ⟨i₂, hq₂i, hq₃i⟩)
    · exact Or.inr (Or.inr hboundary)

end

end RHTower.Sieve
