import GaloisForLFunctions.HTGeometry.ProjectiveHorizonChartFixedField

/-!
# Separating horizon fields

The horizon field of a covector span determines the span.  This file proves the separation for
elementary spans and reduces the general statement to strict antitonicity in one direction.

A homogeneous jet coordinate `X̃_(i,l)` is invariant under the observer group of `ker e_i^*`,
because the transvections generating that group all have column `i` and therefore leave row `i`
standard.  It is moved by the observer group of any other elementary span, because the transvection
with row `i` and column `j` subtracts `X̃_(j,l)` from it.  Hence distinct elementary spans have
distinct horizon fields.

The general injectivity reduces to one step through the span-to-intersection law: if two horizon
fields agree, adding a missing direction to one span cannot change its horizon field.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Elementary transvection rows -/

/-- The inverse of an elementary transvection negates its coefficient. -/
theorem transvectionSL_inv {x j : n} (hx : x ≠ j) (c : K) :
    (transvectionSL x j hx c)⁻¹ = transvectionSL x j hx (-c) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show Matrix.transvection x j c * Matrix.transvection x j (-c) = 1
  rw [Matrix.transvection_mul_transvection_same _ _ hx]
  simp

omit [Fintype n] in
/-- Row `j` of an elementary transvection with column `j` is standard. -/
theorem transvection_row_of_col {x j : n} (hx : x ≠ j) (c : K) (m : n) :
    Matrix.transvection x j c j m = (1 : Matrix n n K) j m := by
  rw [Matrix.transvection]
  simp [hx]

omit [Fintype n] in
/-- Row `i` of the elementary transvection with row `i` and column `j`. -/
theorem transvection_row_self {i j : n} (c : K) (m : n) :
    Matrix.transvection i j c i m = (1 : Matrix n n K) i m + (if j = m then c else 0) := by
  rw [Matrix.transvection]
  simp [Matrix.single_apply]

/-! ## Elementary separation -/

/-- A homogeneous jet coordinate is invariant under the observer group of its own direction. -/
theorem freeCoordinate_mem_horizonField_self (i : n) (l : ℕ) :
    freeCoordinate K (n × ℕ) (i, l) ∈ horizonField (K := K) {i} := by
  rw [mem_horizonField_iff]
  rintro g ⟨j, hj, x, hx, c, rfl⟩
  have hji : j = i := hj
  subst hji
  rw [linearJetAction_freeCoordinate, transvectionSL_inv, Finset.sum_eq_single j]
  · rw [coe_transvectionSL, transvection_row_of_col hx, Matrix.one_apply_eq, map_one, one_mul]
  · intro m _ hm
    rw [coe_transvectionSL, transvection_row_of_col hx, Matrix.one_apply_ne (Ne.symm hm),
      map_zero, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

/-- A homogeneous jet coordinate is moved by the observer group of any other direction. -/
theorem freeCoordinate_notMem_horizonField_of_ne {i j : n} (hij : i ≠ j) (l : ℕ) :
    freeCoordinate K (n × ℕ) (i, l) ∉ horizonField (K := K) {j} := by
  intro hmem
  have hg : transvectionSL i j hij (1 : K) ∈ chartSubsetTransvectionSet ({j} : Set n) K :=
    ⟨j, Set.mem_singleton j, i, hij, 1, rfl⟩
  have hfix := (mem_horizonField_iff.1 hmem) _ hg
  rw [linearJetAction_freeCoordinate, transvectionSL_inv] at hfix
  have hsum : ∑ m, algebraMap K (HomogeneousJetField n K)
      (((transvectionSL i j hij (-1 : K) : SpecialLinearGroup n K) : Matrix n n K) i m) *
        freeCoordinate K (n × ℕ) (m, l) =
      freeCoordinate K (n × ℕ) (i, l) - freeCoordinate K (n × ℕ) (j, l) := by
    have hstep : ∀ m : n, algebraMap K (HomogeneousJetField n K)
        (((transvectionSL i j hij (-1 : K) : SpecialLinearGroup n K) : Matrix n n K) i m) *
          freeCoordinate K (n × ℕ) (m, l) =
        algebraMap K (HomogeneousJetField n K) ((1 : Matrix n n K) i m) *
            freeCoordinate K (n × ℕ) (m, l) -
          algebraMap K (HomogeneousJetField n K) (if j = m then 1 else 0) *
            freeCoordinate K (n × ℕ) (m, l) := by
      intro m
      rw [coe_transvectionSL, transvection_row_self, ← sub_mul]
      congr 2
      rw [← map_sub]
      congr 1
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun m _ => hstep m, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq, map_one, one_mul]
      · intro m _ hm
        rw [Matrix.one_apply_ne (Ne.symm hm), map_zero, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    · rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, map_one, one_mul]
      · intro m _ hm
        rw [if_neg (Ne.symm hm), map_zero, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ j) hcon
  rw [hsum] at hfix
  exact freeCoordinate_ne_zero j l (sub_eq_self.1 hfix)

/-- **Elementary separation.**  Distinct elementary covector spans have distinct horizon fields. -/
theorem horizonField_singleton_injective {i j : n}
    (h : horizonField (K := K) {i} = horizonField (K := K) {j}) : i = j := by
  by_contra hij
  exact freeCoordinate_notMem_horizonField_of_ne hij 0
    (h ▸ freeCoordinate_mem_horizonField_self i 0)

/-! ## Reduction of the general separation -/

/-- **Reduction to one step.**  The horizon-field assignment is injective as soon as adding one
missing direction always changes the horizon field. -/
theorem horizonField_injective_of_ne_insert
    (h : ∀ (t : Set n) (i : n), i ∉ t →
      horizonField (K := K) (insert i t) ≠ horizonField (K := K) t) :
    Function.Injective (horizonField (n := n) (K := K)) := by
  intro s t hst
  by_contra hne
  have hex : ∃ i, (i ∈ s ∧ i ∉ t) ∨ (i ∈ t ∧ i ∉ s) := by
    by_contra hcon
    apply hne
    ext x
    constructor
    · intro hx
      by_contra hxt
      exact hcon ⟨x, Or.inl ⟨hx, hxt⟩⟩
    · intro hx
      by_contra hxs
      exact hcon ⟨x, Or.inr ⟨hx, hxs⟩⟩
  obtain ⟨i, hi⟩ := hex
  rcases hi with ⟨his, hit⟩ | ⟨hit, his⟩
  · refine h t i hit ?_
    rw [Set.insert_eq, horizonField_union]
    refine le_antisymm inf_le_right (le_inf ?_ le_rfl)
    rw [← hst]
    exact horizonField_antitone (Set.singleton_subset_iff.2 his)
  · refine h s i his ?_
    rw [Set.insert_eq, horizonField_union]
    refine le_antisymm inf_le_right (le_inf ?_ le_rfl)
    rw [hst]
    exact horizonField_antitone (Set.singleton_subset_iff.2 hit)

end

end GaloisForLFunctions.HTGeometry
