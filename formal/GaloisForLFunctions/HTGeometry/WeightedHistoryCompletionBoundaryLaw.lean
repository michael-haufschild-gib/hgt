import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Data.DFinsupp.FiniteInfinite
import Mathlib.Data.ENNReal.Operations
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-!
# Weighted history completion and boundary action

Finite-support histories are dense in a product of compact coordinate groups.  A proper
coordinate length and a weight with finite bounded sublevels make the weighted action sublevels
finite.  The neighbourhood relaxation of that action agrees with the action on finite-support
histories and is infinite at every new product-completion point.
-/

open scoped DirectSum ENNReal NNReal
open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J : Type*} {K : J → Type*}
variable [∀ j, AddCommGroup (K j)] [∀ j, UniformSpace (K j)]

/-- Inclusion of finite-support histories into the full product. -/
def weightedHistoryInclusion : (⨁ j, K j) → ∀ j, K j :=
  DirectSum.coeFnAddMonoidHom K

theorem weightedHistoryInclusion_injective :
    Function.Injective (weightedHistoryInclusion (K := K)) := by
  intro x y h
  apply DFunLike.ext _ _
  intro j
  exact congrFun h j

/-- Finite-support histories are dense in the product topology. -/
theorem weightedHistoryInclusion_denseRange :
    DenseRange (weightedHistoryInclusion (K := K)) := by
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp hU x hxU
  classical
  let y : ⨁ j, K j := DirectSum.mk K I fun j => x j.1
  refine ⟨weightedHistoryInclusion y, ?_, ⟨y, rfl⟩⟩
  apply hpi
  intro j hj
  change y j ∈ u j
  rw [show y j = x j from DirectSum.mk_apply_of_mem hj]
  exact (hu j hj).2

/-- Uniform structure induced from the product completion. -/
def weightedHistoryUniformSpace : UniformSpace (⨁ j, K j) :=
  (Pi.uniformSpace K).comap (weightedHistoryInclusion (K := K))

local instance : UniformSpace (⨁ j, K j) := weightedHistoryUniformSpace

/-- The product is an abstract two-sided Hausdorff uniform completion of finite-support histories
for the uniform structure induced by the inclusion. -/
def weightedHistoryAbstractCompletion
    [∀ j, CompleteSpace (K j)] [∀ j, T0Space (K j)] :
    AbstractCompletion (⨁ j, K j) :=
  { space := ∀ j, K j
    coe := weightedHistoryInclusion
    uniformStruct := Pi.uniformSpace K
    complete := inferInstance
    separation := inferInstance
    isUniformInducing := by
      rw [isUniformInducing_iff_uniformSpace]
    dense := weightedHistoryInclusion_denseRange }

section Action

variable [DecidableEq J] [∀ j, DecidableEq (K j)]

/-- Exact assumptions used by weighted-history properness. -/
structure WeightedHistoryDatum where
  /-- Positive coordinate weights. -/
  weight : J → ℝ≥0
  /-- Proper coordinate lengths. -/
  length : ∀ j, K j → ℕ
  weight_pos : ∀ j : J, 0 < weight j
  weight_sublevel_finite : ∀ R : ℝ≥0, {j | weight j ≤ R}.Finite
  length_zero : ∀ j : J, length j 0 = 0
  length_pos : ∀ (j : J) x, x ≠ 0 → 0 < length j x
  length_ball_finite : ∀ (j : J) N, {x | length j x ≤ N}.Finite
  length_add_le : ∀ (j : J) x y, length j (x + y) ≤ length j x + length j y

variable (D : WeightedHistoryDatum (J := J) (K := K))

/-- Weighted source action on a finite-support history. -/
def weightedHistoryAction (x : ⨁ j, K j) : ℝ≥0 :=
  ∑ j ∈ x.support, D.weight j * D.length j (x j)

@[simp]
theorem weightedHistoryAction_zero : D.weightedHistoryAction 0 = 0 := by
  simp [weightedHistoryAction]

theorem weight_le_action_of_mem_support (x : ⨁ j, K j) {j : J} (hj : j ∈ x.support) :
    D.weight j ≤ D.weightedHistoryAction x := by
  have hlen : 1 ≤ D.length j (x j) := D.length_pos j (x j) (DFinsupp.mem_support_iff.mp hj)
  calc
    D.weight j ≤ D.weight j * D.length j (x j) := by
      simpa using mul_le_mul_left' hlen (D.weight j)
    _ ≤ ∑ i ∈ x.support, D.weight i * D.length i (x i) :=
      Finset.single_le_sum (fun i _ => mul_nonneg (D.weight i).2 (Nat.cast_nonneg _)) hj

theorem length_le_ceil_action_div_weight (x : ⨁ j, K j) {R : ℝ≥0}
    (hx : D.weightedHistoryAction x ≤ R) (j : J) :
    D.length j (x j) ≤ ⌈(R : ℝ) / (D.weight j : ℝ)⌉₊ := by
  by_cases hj : j ∈ x.support
  · have hterm : D.weight j * D.length j (x j) ≤ D.weightedHistoryAction x :=
      Finset.single_le_sum (fun i _ => mul_nonneg (D.weight i).2 (Nat.cast_nonneg _)) hj
    have hdiv : (D.length j (x j) : ℝ≥0) ≤ R / D.weight j := by
      rw [le_div_iff₀ (D.weight_pos j)]
      exact hterm.trans hx
    have hdivReal : (D.length j (x j) : ℝ) ≤ (R : ℝ) / (D.weight j : ℝ) := by
      exact_mod_cast hdiv
    exact_mod_cast hdivReal.trans (Nat.le_ceil _)
  · have hz : x j = 0 := by simpa [DFinsupp.mem_support_iff] using hj
    simp [hz, D.length_zero]

/-- Every bounded weighted-action sublevel is finite. -/
theorem weightedHistoryAction_sublevel_finite (R : ℝ≥0) :
    {x | D.weightedHistoryAction x ≤ R}.Finite := by
  classical
  let S : Finset J := (D.weight_sublevel_finite R).toFinset
  let B : ∀ j : S, Set (K j.1) := fun j =>
    {x | D.length j.1 x ≤ ⌈(R : ℝ) / (D.weight j.1 : ℝ)⌉₊}
  let encode : {x | D.weightedHistoryAction x ≤ R} → ∀ j : S, B j := fun x j =>
    ⟨x.1 j.1, D.length_le_ceil_action_div_weight x.1 x.2 j.1⟩
  have henc : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply DirectSum.ext
    intro j
    by_cases hj : j ∈ S
    · have hj' : (⟨j, hj⟩ : S) = ⟨j, hj⟩ := rfl
      exact congrArg Subtype.val (congrFun hxy ⟨j, hj⟩)
    · have hxnot : j ∉ x.1.support := by
        intro hjs
        have hw : D.weight j ≤ R := (D.weight_le_action_of_mem_support x.1 hjs).trans x.2
        exact hj (by simpa [S] using hw)
      have hynot : j ∉ y.1.support := by
        intro hjs
        have hw : D.weight j ≤ R := (D.weight_le_action_of_mem_support y.1 hjs).trans y.2
        exact hj (by simpa [S] using hw)
      have hx0 : x.1 j = 0 := by simpa [DFinsupp.mem_support_iff] using hxnot
      have hy0 : y.1 j = 0 := by simpa [DFinsupp.mem_support_iff] using hynot
      rw [hx0, hy0]
  have hB : ∀ j : S, Finite (B j) := fun j =>
    Set.Finite.toFinite
      (D.length_ball_finite j.1 ⌈(R : ℝ) / (D.weight j.1 : ℝ)⌉₊)
  letI (j : S) : Finite (B j) := hB j
  letI : Finite (∀ j : S, B j) := inferInstance
  letI : Finite {x | D.weightedHistoryAction x ≤ R} := Finite.of_injective encode henc
  exact Set.toFinite _

/-- Weighted action is subadditive. -/
theorem weightedHistoryAction_add_le (x y : ⨁ j, K j) :
    D.weightedHistoryAction (x + y) ≤ D.weightedHistoryAction x + D.weightedHistoryAction y := by
  classical
  let S := x.support ∪ y.support
  have hsupp : (x + y).support ⊆ S := by
    intro j hj
    rw [DFinsupp.mem_support_iff] at hj
    by_contra hnot
    simp only [Finset.mem_union, not_or, S] at hnot
    have hx0 : x j = 0 := by simpa [DFinsupp.mem_support_iff] using hnot.1
    have hy0 : y j = 0 := by simpa [DFinsupp.mem_support_iff] using hnot.2
    exact hj (by simp [hx0, hy0])
  calc
    D.weightedHistoryAction (x + y)
        ≤ ∑ j ∈ S, D.weight j * D.length j ((x + y) j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun i _ _ => by positivity)
    _ ≤ ∑ j ∈ S,
        (D.weight j * D.length j (x j) + D.weight j * D.length j (y j)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [DirectSum.add_apply, ← mul_add]
      exact mul_le_mul_left' (D.length_add_le j (x j) (y j)) _
    _ = D.weightedHistoryAction x + D.weightedHistoryAction y := by
      rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_subset (Finset.subset_union_left)
        intro j hjS hjx
        have hx0 : x j = 0 := by simpa [DFinsupp.mem_support_iff] using hjx
        simp [hx0, D.length_zero]
      · apply Finset.sum_subset (Finset.subset_union_right)
        intro j hjS hjy
        have hy0 : y j = 0 := by simpa [DFinsupp.mem_support_iff] using hjy
        simp [hy0, D.length_zero]

/-- Neighbourhood relaxation of the finite-support action in the product completion. -/
def weightedHistoryRelaxation (x : ∀ j, K j) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ U ∈ 𝓝 x,
    r ≤ sInf ((fun h : ⨁ j, K j => (D.weightedHistoryAction h : ℝ≥0∞)) ''
      ((weightedHistoryInclusion (K := K)) ⁻¹' U))}

theorem weightedHistoryRelaxation_eq_action (x : ⨁ j, K j) :
    D.weightedHistoryRelaxation (weightedHistoryInclusion x) = D.weightedHistoryAction x := by
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨U, hU, hr⟩
    have hxU : weightedHistoryInclusion x ∈ U := mem_of_mem_nhds hU
    exact hr.trans (sInf_le ⟨x, hxU, rfl⟩)
  · rw [← ENNReal.coe_le_coe]
    let low : Set (∀ j, K j) := weightedHistoryInclusion ''
      {h | D.weightedHistoryAction h < D.weightedHistoryAction x}
    have hsub : {h | D.weightedHistoryAction h < D.weightedHistoryAction x} ⊆
        {h | D.weightedHistoryAction h ≤ D.weightedHistoryAction x} :=
      fun _ h => h.le
    have hlowFinite : low.Finite :=
      ((D.weightedHistoryAction_sublevel_finite (D.weightedHistoryAction x)).subset hsub).image
        weightedHistoryInclusion
    have hxlow : weightedHistoryInclusion x ∉ low := by
      rintro ⟨h, hh, heq⟩
      have hxeq : h = x := weightedHistoryInclusion_injective heq
      exact (hh.trans_le (le_of_eq (congrArg D.weightedHistoryAction hxeq))).false
    let U := lowᶜ
    have hU : U ∈ 𝓝 (weightedHistoryInclusion x) :=
      hlowFinite.isClosed.isOpen_compl.mem_nhds hxlow
    apply le_sSup
    refine ⟨U, hU, ?_⟩
    apply le_sInf
    rintro q ⟨h, hh, rfl⟩
    rw [ENNReal.coe_le_coe]
    by_contra hnot
    have hlt : D.weightedHistoryAction h < D.weightedHistoryAction x := lt_of_not_ge hnot
    exact hh ⟨h, hlt, rfl⟩

/-- Every point added by product completion has infinite relaxed source action. -/
theorem weightedHistoryRelaxation_eq_top_of_not_mem_range
    {x : ∀ j, K j} (hx : x ∉ Set.range (weightedHistoryInclusion (K := K))) :
    D.weightedHistoryRelaxation x = ∞ := by
  rw [weightedHistoryRelaxation, sSup_eq_top]
  intro b hb
  let R : ℝ≥0 := b.toNNReal + 1
  let r : ℝ≥0∞ := R
  have hbr : b < r := by
    rw [show b = (b.toNNReal : ℝ≥0∞) from (ENNReal.coe_toNNReal (ne_of_lt hb)).symm]
    exact_mod_cast lt_add_one b.toNNReal
  refine ⟨r, ?_, hbr⟩
  change ∃ U ∈ 𝓝 x,
    r ≤ sInf ((fun h : ⨁ j, K j => (D.weightedHistoryAction h : ℝ≥0∞)) ''
      (weightedHistoryInclusion ⁻¹' U))
  ·
    let low : Set (∀ j, K j) := weightedHistoryInclusion ''
      {h | D.weightedHistoryAction h ≤ R}
    have hlowFinite : low.Finite :=
      (D.weightedHistoryAction_sublevel_finite R).image weightedHistoryInclusion
    have hxlow : x ∉ low := by
      intro h
      exact hx ⟨h.choose, h.choose_spec.1⟩
    let U := lowᶜ
    have hU : U ∈ 𝓝 x := hlowFinite.isClosed.isOpen_compl.mem_nhds hxlow
    refine ⟨U, hU, ?_⟩
    apply le_sInf
    rintro q ⟨h, hh, rfl⟩
    have hnot : ¬D.weightedHistoryAction h ≤ R := by
      intro hle
      exact hh ⟨h, hle, rfl⟩
    have hRlt : R < D.weightedHistoryAction h := lt_of_not_ge hnot
    change (R : ℝ≥0∞) ≤ (D.weightedHistoryAction h : ℝ≥0∞)
    rw [ENNReal.coe_le_coe]
    exact hRlt.le

/-- Complete weighted-history theorem: density, finite/compact sublevels, subadditivity, and exact
boundary relaxation. -/
theorem weightedHistory_completion_boundary_law
    [∀ j, CompleteSpace (K j)] [∀ j, T0Space (K j)] :
    DenseRange (weightedHistoryInclusion (K := K)) ∧
      (∀ R, {x | D.weightedHistoryAction x ≤ R}.Finite) ∧
      (∀ R, IsCompact {x | D.weightedHistoryAction x ≤ R}) ∧
      (∀ x y, D.weightedHistoryAction (x + y) ≤
        D.weightedHistoryAction x + D.weightedHistoryAction y) ∧
      (∀ h, D.weightedHistoryRelaxation (weightedHistoryInclusion h) =
        D.weightedHistoryAction h) ∧
      (∀ x, x ∉ Set.range (weightedHistoryInclusion (K := K)) →
        D.weightedHistoryRelaxation x = ∞) := by
  refine ⟨weightedHistoryInclusion_denseRange, D.weightedHistoryAction_sublevel_finite,
    fun R => (D.weightedHistoryAction_sublevel_finite R).isCompact,
    D.weightedHistoryAction_add_le, D.weightedHistoryRelaxation_eq_action,
    D.weightedHistoryRelaxation_eq_top_of_not_mem_range⟩

end Action

end

end GaloisForLFunctions.HTGeometry
