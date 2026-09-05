import Mathlib

/-!
# Exact two-half-cell memory reduction from arXiv:2608.29060

For an antipodal exponential cell, even historical generations are positive contractions of the
current half-cell and odd generations are contractions of its first reflected copy. Convexity and
the origin therefore collapse infinite memory to exactly two half-cells. This module formalizes
that reduction and the resulting support-function formula without discretization.
-/

noncomputable section

open Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Union of all even exponential generations of a half-cell. -/
def bellmanShorelineEvenGenerations (rho : ℝ) (C : Set E) : Set E :=
  {x | ∃ (j : ℕ) (c : E), c ∈ C ∧ x = (rho⁻¹ ^ (2 * j)) • c}

/-- Union of all odd exponential generations, expressed as contractions of first reflection. -/
def bellmanShorelineOddGenerations (rho : ℝ) (C : Set E) : Set E :=
  {x | ∃ (j : ℕ) (c : E), c ∈ C ∧
    x = (rho⁻¹ ^ (2 * j)) • ((-rho⁻¹) • c)}

/-- Full normalized memory, split by generation parity. -/
def bellmanShorelineAllGenerations (rho : ℝ) (C : Set E) : Set E :=
  bellmanShorelineEvenGenerations rho C ∪ bellmanShorelineOddGenerations rho C

/-- Opposite half-cell discounted by one generation. -/
def bellmanShorelineReflectedHalfCell (rho : ℝ) (C : Set E) : Set E :=
  {x | ∃ c : E, c ∈ C ∧ x = (-rho⁻¹) • c}

/-- Existential and pointwise-scalar descriptions of reflected half-cell agree. -/
theorem bellmanShorelineReflectedHalfCell_eq_smul (rho : ℝ) (C : Set E) :
    bellmanShorelineReflectedHalfCell rho C = (-rho⁻¹) • C := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact Set.mem_smul_set.mpr ⟨c, hc, rfl⟩
  · intro hx
    obtain ⟨c, hc, hcx⟩ := Set.mem_smul_set.mp hx
    exact ⟨c, hc, hcx.symm⟩

/-- All even generations lie in current convex half-cell, and generation zero fills it. -/
theorem bellmanShorelineEvenGenerations_eq
    {rho : ℝ} (hrho : 1 < rho) {C : Set E}
    (hC : Convex ℝ C) (hzero : 0 ∈ C) :
    bellmanShorelineEvenGenerations rho C = C := by
  ext x
  constructor
  · rintro ⟨j, c, hc, rfl⟩
    apply hC.smul_mem_of_zero_mem hzero hc
    constructor
    · exact pow_nonneg (inv_nonneg.mpr (by linarith)) _
    · exact pow_le_one₀ (inv_nonneg.mpr (by linarith))
        (inv_le_one_of_one_le₀ (le_of_lt hrho))
  · intro hx
    exact ⟨0, x, hx, by simp⟩

/-- All odd generations lie in first reflected half-cell, and generation zero fills it. -/
theorem bellmanShorelineOddGenerations_eq
    {rho : ℝ} (hrho : 1 < rho) {C : Set E}
    (hC : Convex ℝ C) (hzero : 0 ∈ C) :
    bellmanShorelineOddGenerations rho C = bellmanShorelineReflectedHalfCell rho C := by
  ext x
  constructor
  · rintro ⟨j, c, hc, rfl⟩
    refine ⟨(rho⁻¹ ^ (2 * j)) • c, ?_, ?_⟩
    · apply hC.smul_mem_of_zero_mem hzero hc
      constructor
      · exact pow_nonneg (inv_nonneg.mpr (by linarith)) _
      · exact pow_le_one₀ (inv_nonneg.mpr (by linarith))
          (inv_le_one_of_one_le₀ (le_of_lt hrho))
    · simp only [smul_smul]
      rw [mul_comm]
  · rintro ⟨c, hc, rfl⟩
    exact ⟨0, c, hc, by simp⟩

/-- Infinite normalized memory is exactly current half-cell union first reflected half-cell. -/
theorem bellmanShorelineAllGenerations_eq_twoHalfCells
    {rho : ℝ} (hrho : 1 < rho) {C : Set E}
    (hC : Convex ℝ C) (hzero : 0 ∈ C) :
    bellmanShorelineAllGenerations rho C =
      C ∪ bellmanShorelineReflectedHalfCell rho C := by
  rw [bellmanShorelineAllGenerations,
    bellmanShorelineEvenGenerations_eq hrho hC hzero,
    bellmanShorelineOddGenerations_eq hrho hC hzero]

/-- Convex hull of infinite memory equals convex hull of two half-cells. -/
theorem bellmanShoreline_convexHull_allGenerations_eq_twoHalfCells
    {rho : ℝ} (hrho : 1 < rho) {C : Set E}
    (hC : Convex ℝ C) (hzero : 0 ∈ C) :
    convexHull ℝ (bellmanShorelineAllGenerations rho C) =
      convexHull ℝ (C ∪ bellmanShorelineReflectedHalfCell rho C) := by
  rw [bellmanShorelineAllGenerations_eq_twoHalfCells hrho hC hzero]

/-- Euclidean support function of a set. -/
def bellmanShorelineSupport
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (C : Set F) (n : F) : ℝ :=
  sSup ((fun x => inner ℝ n x) '' C)

/-- Positive physical rescaling commutes exactly with the support function. -/
theorem bellmanShorelineSupport_image_smul
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : ℝ} (ha : 0 < a) {C : Set F}
    (hcompact : IsCompact C) (hne : C.Nonempty) (n : F) :
    bellmanShorelineSupport ((fun x : F => a • x) '' C) n =
      a * bellmanShorelineSupport C n := by
  let S : Set ℝ := (fun x => inner ℝ n x) '' C
  have hSne : S.Nonempty := hne.image _
  have hSbdd : BddAbove S :=
    hcompact.bddAbove_image (continuous_const.inner continuous_id).continuousOn
  have himage :
      (fun x => inner ℝ n x) '' ((fun x : F => a • x) '' C) =
        (fun r : ℝ => a * r) '' S := by
    ext r
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨inner ℝ n c, ⟨c, hc, rfl⟩, by simp [real_inner_smul_right]⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨a • c, ⟨c, hc, rfl⟩, by simp [real_inner_smul_right]⟩
  rw [bellmanShorelineSupport, bellmanShorelineSupport, himage]
  exact ((OrderIso.mulLeft₀ a ha).map_csSup' hSne hSbdd).symm

/-- Taking convex hull does not alter a bounded nonempty set's support function. -/
theorem bellmanShorelineSupport_convexHull
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {C : Set F} (hne : C.Nonempty) (n : F)
    (hbdd : BddAbove ((fun x => inner ℝ n x) '' C)) :
    bellmanShorelineSupport (convexHull ℝ C) n = bellmanShorelineSupport C n := by
  have hbound : C ⊆ {x | inner ℝ n x ≤ bellmanShorelineSupport C n} := by
    intro x hx
    exact le_csSup hbdd ⟨x, hx, rfl⟩
  have hhull : convexHull ℝ C ⊆
      {x | inner ℝ n x ≤ bellmanShorelineSupport C n} :=
    convexHull_min hbound (convex_halfSpace_le (innerₗ F n).isLinear _)
  have hHullNe : (convexHull ℝ C).Nonempty := hne.convexHull
  have hbddHull : BddAbove ((fun x => inner ℝ n x) '' convexHull ℝ C) := by
    refine ⟨bellmanShorelineSupport C n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hhull hx
  apply le_antisymm
  · apply csSup_le (hHullNe.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact hhull hx
  · apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact le_csSup hbddHull ⟨x, subset_convexHull ℝ C hx, rfl⟩

/-- Support of discounted reflected half-cell is reflected support times discount. -/
theorem bellmanShorelineSupport_reflectedHalfCell
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {rho : ℝ} (hrho : 1 < rho) {C : Set F}
    (hcompact : IsCompact C) (hne : C.Nonempty) (n : F) :
    bellmanShorelineSupport (bellmanShorelineReflectedHalfCell rho C) n =
      rho⁻¹ * bellmanShorelineSupport C (-n) := by
  have hq : 0 < rho⁻¹ := inv_pos.mpr (by linarith)
  let S : Set ℝ := (fun x => inner ℝ (-n) x) '' C
  have hSne : S.Nonempty := hne.image _
  have hSbdd : BddAbove S :=
    hcompact.bddAbove_image (continuous_const.inner continuous_id).continuousOn
  have himage :
      (fun x => inner ℝ n x) '' bellmanShorelineReflectedHalfCell rho C =
        (fun r : ℝ => rho⁻¹ * r) '' S := by
    ext r
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨inner ℝ (-n) c, ⟨c, hc, rfl⟩, ?_⟩
      simp [real_inner_smul_right]
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨(-rho⁻¹) • c, ⟨c, hc, rfl⟩, ?_⟩
      simp [real_inner_smul_right]
  rw [bellmanShorelineSupport, bellmanShorelineSupport, himage]
  exact ((OrderIso.mulLeft₀ rho⁻¹ hq).map_csSup' hSne hSbdd).symm

/-- Support of infinite memory is maximum of current and first reflected half-cell supports. -/
theorem bellmanShorelineSupport_allGenerations
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {rho : ℝ} (hrho : 1 < rho) {C : Set F}
    (hC : Convex ℝ C) (hzero : 0 ∈ C) (hcompact : IsCompact C)
    (hne : C.Nonempty) (n : F) :
    bellmanShorelineSupport (bellmanShorelineAllGenerations rho C) n =
      max (bellmanShorelineSupport C n)
        (rho⁻¹ * bellmanShorelineSupport C (-n)) := by
  have hrefCompact : IsCompact (bellmanShorelineReflectedHalfCell rho C) := by
    rw [bellmanShorelineReflectedHalfCell_eq_smul]
    exact hcompact.smul _
  have hrefNe : (bellmanShorelineReflectedHalfCell rho C).Nonempty := by
    obtain ⟨c, hc⟩ := hne
    exact ⟨(-rho⁻¹) • c, c, hc, rfl⟩
  rw [bellmanShorelineAllGenerations_eq_twoHalfCells hrho hC hzero,
    bellmanShorelineSupport, Set.image_union,
    csSup_union
      (hcompact.bddAbove_image (continuous_const.inner continuous_id).continuousOn)
      (hne.image _)
      (hrefCompact.bddAbove_image (continuous_const.inner continuous_id).continuousOn)
      (hrefNe.image _),
    ← bellmanShorelineSupport, ← bellmanShorelineSupport,
    bellmanShorelineSupport_reflectedHalfCell hrho hcompact hne n]

/-- Paper's exact two-half-cell support formula for normalized convex memory hull. -/
theorem bellmanShorelineSupport_convexHull_allGenerations
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {rho : ℝ} (hrho : 1 < rho) {C : Set F}
    (hC : Convex ℝ C) (hzero : 0 ∈ C) (hcompact : IsCompact C)
    (hne : C.Nonempty) (n : F) :
    bellmanShorelineSupport
        (convexHull ℝ (bellmanShorelineAllGenerations rho C)) n =
      max (bellmanShorelineSupport C n)
        (rho⁻¹ * bellmanShorelineSupport C (-n)) := by
  rw [bellmanShorelineSupport_convexHull]
  · exact bellmanShorelineSupport_allGenerations hrho hC hzero hcompact hne n
  · rw [bellmanShorelineAllGenerations_eq_twoHalfCells hrho hC hzero]
    exact hne.mono Set.subset_union_left
  · rw [bellmanShorelineAllGenerations_eq_twoHalfCells hrho hC hzero, Set.image_union]
    apply BddAbove.union
    · exact hcompact.bddAbove_image
        (continuous_const.inner continuous_id).continuousOn
    · rw [bellmanShorelineReflectedHalfCell_eq_smul]
      exact (hcompact.smul _).bddAbove_image
        (continuous_const.inner continuous_id).continuousOn

/-- Algebraic core of antipodal support comparability for a two-half-cell memory. -/
theorem bellmanShoreline_inv_mul_reflectedMax_le
    {rho a b : ℝ} (hrho : 1 < rho) (ha : 0 ≤ a) :
    rho⁻¹ * max b (rho⁻¹ * a) ≤ max a (rho⁻¹ * b) := by
  have hq0 : 0 ≤ rho⁻¹ := (inv_pos.mpr (by linarith)).le
  have hq1 : rho⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt hrho)
  have hqa : rho⁻¹ * a ≤ a := mul_le_of_le_one_left ha hq1
  rw [mul_max_of_nonneg _ _ hq0]
  apply max_le
  · exact le_max_right _ _
  · calc
      rho⁻¹ * (rho⁻¹ * a) ≤ rho⁻¹ * a := mul_le_mul_of_nonneg_left hqa hq0
      _ ≤ a := hqa
      _ ≤ max a (rho⁻¹ * b) := le_max_left _ _

/-- Exact two-half-cell reduction forces antipodal support values to be comparable within
factor `rho` in both directions. -/
theorem bellmanShorelineSupport_allGenerations_antipodal
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {rho : ℝ} (hrho : 1 < rho) {C : Set F}
    (hC : Convex ℝ C) (hzero : 0 ∈ C) (hcompact : IsCompact C)
    (hne : C.Nonempty) (n : F) :
    rho⁻¹ * bellmanShorelineSupport (bellmanShorelineAllGenerations rho C) (-n) ≤
        bellmanShorelineSupport (bellmanShorelineAllGenerations rho C) n ∧
      rho⁻¹ * bellmanShorelineSupport (bellmanShorelineAllGenerations rho C) n ≤
        bellmanShorelineSupport (bellmanShorelineAllGenerations rho C) (-n) := by
  have hnonneg : ∀ u : F, 0 ≤ bellmanShorelineSupport C u := by
    intro u
    exact le_csSup
      (hcompact.bddAbove_image (continuous_const.inner continuous_id).continuousOn)
      ⟨0, hzero, by simp⟩
  constructor
  · rw [bellmanShorelineSupport_allGenerations hrho hC hzero hcompact hne,
      bellmanShorelineSupport_allGenerations hrho hC hzero hcompact hne, neg_neg]
    exact bellmanShoreline_inv_mul_reflectedMax_le hrho (hnonneg n)
  · rw [bellmanShorelineSupport_allGenerations hrho hC hzero hcompact hne,
      bellmanShorelineSupport_allGenerations hrho hC hzero hcompact hne, neg_neg]
    exact bellmanShoreline_inv_mul_reflectedMax_le hrho (hnonneg (-n))

end GaloisForLFunctions.HTGeometry

end
