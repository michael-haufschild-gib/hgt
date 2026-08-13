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
variable [∀ j, AddCommGroup (K j)]

/-- Inclusion of finite-support histories into the full product. -/
def weightedHistoryInclusion (Gamma : ∀ j, AddSubgroup (K j)) :
    (⨁ j, Gamma j) → ∀ j, K j :=
  fun x j => x j

theorem weightedHistoryInclusion_injective (Gamma : ∀ j, AddSubgroup (K j)) :
    Function.Injective (weightedHistoryInclusion Gamma) := by
  intro x y h
  apply DirectSum.ext
  intro j
  apply Subtype.ext
  exact congrFun h j

/-- Finite-support histories are dense in the product topology. -/
theorem weightedHistoryInclusion_denseRange (Gamma : ∀ j, AddSubgroup (K j))
    [∀ j, UniformSpace (K j)]
    (hGamma : ∀ j, Dense (Gamma j : Set (K j))) :
    DenseRange (weightedHistoryInclusion Gamma) := by
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp hU x hxU
  classical
  choose k hkGamma hku using fun j : I =>
    (hGamma j.1).exists_mem_open (hu j.1 j.2).1 ⟨x j.1, (hu j.1 j.2).2⟩
  let y : ⨁ j, Gamma j := DirectSum.mk (fun j => Gamma j) I fun j => ⟨k j, hkGamma j⟩
  refine ⟨weightedHistoryInclusion Gamma y, ?_, ⟨y, rfl⟩⟩
  apply hpi
  intro j hj
  change ((y j : Gamma j) : K j) ∈ u j
  rw [show y j = ⟨k ⟨j, hj⟩, hkGamma ⟨j, hj⟩⟩ from DirectSum.mk_apply_of_mem hj]
  exact hku ⟨j, hj⟩

/-- Infinitely many nontrivial source coordinates produce an infinite-support product point, so
the finite-support inclusion is proper. -/
theorem weightedHistoryInclusion_not_surjective_of_infinite_nontrivial
    (Gamma : ∀ j, AddSubgroup (K j))
    (hInfinite : Set.Infinite {j | Nontrivial (Gamma j)}) :
    ¬ Function.Surjective (weightedHistoryInclusion Gamma) := by
  classical
  let g : ∀ j, Gamma j := fun j =>
    if hj : Nontrivial (Gamma j) then
      Classical.choose (by letI := hj; exact exists_ne (0 : Gamma j))
    else 0
  have hg : ∀ j, Nontrivial (Gamma j) → g j ≠ 0 := by
    intro j hj
    simp only [g, dif_pos hj]
    letI := hj
    exact Classical.choose_spec (exists_ne (0 : Gamma j))
  intro hsurj
  obtain ⟨h, hh⟩ := hsurj (fun j => (g j : K j))
  have hsubset : {j | Nontrivial (Gamma j)} ⊆ (h.support : Set J) := by
    intro j hj
    rw [Finset.mem_coe, DFinsupp.mem_support_iff]
    intro hz
    apply hg j hj
    exact Subtype.ext (by
      change (g j : K j) = (0 : K j)
      simpa [weightedHistoryInclusion, hz] using (congrFun hh j).symm)
  exact hInfinite (h.support.finite_toSet.subset hsubset)

/-- A proper dense finite-support subgroup is not closed in its product completion. -/
theorem weightedHistoryInclusion_not_isClosed_of_infinite_nontrivial
    (Gamma : ∀ j, AddSubgroup (K j)) [∀ j, UniformSpace (K j)]
    (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    (hInfinite : Set.Infinite {j | Nontrivial (Gamma j)}) :
    ¬ IsClosed (Set.range (weightedHistoryInclusion Gamma)) := by
  intro hclosed
  apply weightedHistoryInclusion_not_surjective_of_infinite_nontrivial Gamma hInfinite
  rw [← Set.range_eq_univ, ← (weightedHistoryInclusion_denseRange Gamma hGamma).closure_eq,
    hclosed.closure_eq]

section Completion

variable [∀ j, UniformSpace (K j)]

/-- Uniform structure induced from the product completion. -/
@[reducible] def weightedHistoryUniformSpace (Gamma : ∀ j, AddSubgroup (K j)) :
    UniformSpace (⨁ j, Gamma j) :=
  (Pi.uniformSpace K).comap (weightedHistoryInclusion Gamma)

local instance (Gamma : ∀ j, AddSubgroup (K j)) : UniformSpace (⨁ j, Gamma j) :=
  weightedHistoryUniformSpace Gamma

/-- The product is an abstract two-sided Hausdorff uniform completion of finite-support histories
for the uniform structure induced by the inclusion. -/
def weightedHistoryAbstractCompletion
    (Gamma : ∀ j, AddSubgroup (K j)) (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    [∀ j, CompleteSpace (K j)] [∀ j, T0Space (K j)] :
    AbstractCompletion (⨁ j, Gamma j) :=
  { space := ∀ j, K j
    coe := weightedHistoryInclusion Gamma
    uniformStruct := Pi.uniformSpace K
    complete := inferInstance
    separation := inferInstance
    isUniformInducing := by
      rw [isUniformInducing_iff_uniformSpace]
      rfl
    dense := weightedHistoryInclusion_denseRange Gamma hGamma }

/-- Source-form specialization: a product of compact Hausdorff coordinate groups is the uniform
completion of the dense finite-support subgroup. -/
def weightedHistoryCompactAbstractCompletion
    (Gamma : ∀ j, AddSubgroup (K j)) (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    [∀ j, CompactSpace (K j)] [∀ j, T2Space (K j)] :
    AbstractCompletion (⨁ j, Gamma j) :=
  weightedHistoryAbstractCompletion Gamma hGamma

/-- Compact-observer/open-history law: inclusion is dense but proper and nonclosed whenever
infinitely many source coordinates are nontrivial. -/
theorem restrictedHistory_compactObserver_openHistory
    (Gamma : ∀ j, AddSubgroup (K j)) (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    (hInfinite : Set.Infinite {j | Nontrivial (Gamma j)})
    [∀ j, CompactSpace (K j)] [∀ j, T2Space (K j)] :
    DenseRange (weightedHistoryInclusion Gamma) ∧
      ¬ Function.Surjective (weightedHistoryInclusion Gamma) ∧
      ¬ IsClosed (Set.range (weightedHistoryInclusion Gamma)) := by
  exact ⟨weightedHistoryInclusion_denseRange Gamma hGamma,
    weightedHistoryInclusion_not_surjective_of_infinite_nontrivial Gamma hInfinite,
    weightedHistoryInclusion_not_isClosed_of_infinite_nontrivial Gamma hGamma hInfinite⟩

end Completion

section Action

variable [DecidableEq J] [∀ j, DecidableEq (K j)]

/-- Exact assumptions used by weighted-history properness. -/
structure WeightedHistoryDatum (Gamma : ∀ j, AddSubgroup (K j)) where
  /-- Positive coordinate weights. -/
  weight : J → ℝ≥0
  /-- Proper coordinate lengths. -/
  length : ∀ j, Gamma j → ℕ
  weight_pos : ∀ j : J, 0 < weight j
  weight_sublevel_finite : ∀ R : ℝ≥0, {j | weight j ≤ R}.Finite
  length_zero : ∀ j : J, length j 0 = 0
  length_pos : ∀ (j : J) x, x ≠ 0 → 0 < length j x
  length_ball_finite : ∀ (j : J) N, {x | length j x ≤ N}.Finite
  length_add_le : ∀ (j : J) x y, length j (x + y) ≤ length j x + length j y
  length_neg : ∀ (j : J) x, length j (-x) = length j x

namespace WeightedHistoryDatum

variable {Gamma : ∀ j, AddSubgroup (K j)}
variable (D : WeightedHistoryDatum Gamma)

/-- Weighted source action on a finite-support history. -/
def weightedHistoryAction (x : ⨁ j, Gamma j) : ℝ≥0 :=
  ∑ j ∈ x.support, D.weight j * D.length j (x j)

@[simp]
theorem weightedHistoryAction_zero : D.weightedHistoryAction 0 = 0 := by
  simp [weightedHistoryAction]

theorem weight_le_action_of_mem_support (x : ⨁ j, Gamma j) {j : J} (hj : j ∈ x.support) :
    D.weight j ≤ D.weightedHistoryAction x := by
  have hlen : 1 ≤ D.length j (x j) := D.length_pos j (x j) (DFinsupp.mem_support_iff.mp hj)
  have hlen' : (1 : ℝ≥0) ≤ D.length j (x j) := by exact_mod_cast hlen
  calc
    D.weight j ≤ D.weight j * D.length j (x j) := by
      calc
        D.weight j = D.weight j * 1 := (mul_one _).symm
        _ ≤ D.weight j * D.length j (x j) := by gcongr
    _ ≤ ∑ i ∈ x.support, D.weight i * D.length i (x i) :=
      Finset.single_le_sum (s := x.support)
        (f := fun i => D.weight i * D.length i (x i)) (fun i _ => by positivity) hj

theorem length_le_ceil_action_div_weight (x : ⨁ j, Gamma j) {R : ℝ≥0}
    (hx : D.weightedHistoryAction x ≤ R) (j : J) :
    D.length j (x j) ≤ ⌈(R : ℝ) / (D.weight j : ℝ)⌉₊ := by
  by_cases hj : j ∈ x.support
  · have hterm : D.weight j * D.length j (x j) ≤ D.weightedHistoryAction x :=
      Finset.single_le_sum (s := x.support)
        (f := fun i => D.weight i * D.length i (x i)) (fun i _ => by positivity) hj
    have hdiv : (D.length j (x j) : ℝ≥0) ≤ R / D.weight j := by
      rw [le_div_iff₀ (D.weight_pos j)]
      simpa [mul_comm] using hterm.trans hx
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
  let B : ∀ j : S, Set (Gamma j.1) := fun j =>
    {x | D.length j.1 x ≤ ⌈(R : ℝ) / (D.weight j.1 : ℝ)⌉₊}
  let encode : {x | D.weightedHistoryAction x ≤ R} → ∀ j : S, B j := fun x j =>
    ⟨x.1 j.1, D.length_le_ceil_action_div_weight x.1 x.2 j.1⟩
  have henc : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply DirectSum.ext
    intro j
    by_cases hj : j ∈ S
    · exact congrArg Subtype.val (congrFun hxy ⟨j, hj⟩)
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
    @Finite.of_fintype (B j)
      (D.length_ball_finite j.1 ⌈(R : ℝ) / (D.weight j.1 : ℝ)⌉₊).fintype
  letI (j : S) : Finite (B j) := hB j
  letI : Finite (∀ j : S, B j) := inferInstance
  letI : Finite {x | D.weightedHistoryAction x ≤ R} := Finite.of_injective encode henc
  exact Set.toFinite _

/-- Weighted action is subadditive. -/
theorem weightedHistoryAction_add_le (x y : ⨁ j, Gamma j) :
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
      gcongr
      exact_mod_cast D.length_add_le j (x j) (y j)
    _ = D.weightedHistoryAction x + D.weightedHistoryAction y := by
      rw [Finset.sum_add_distrib]
      congr 1
      · symm
        apply Finset.sum_subset (Finset.subset_union_left)
        intro j hjS hjx
        have hx0 : x j = 0 := by simpa [DFinsupp.mem_support_iff] using hjx
        simp [hx0, D.length_zero]
      · symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro j hjS hjy
        have hy0 : y j = 0 := by simpa [DFinsupp.mem_support_iff] using hjy
        simp [hy0, D.length_zero]

variable [∀ j, UniformSpace (K j)]

local instance : UniformSpace (⨁ j, Gamma j) := weightedHistoryUniformSpace Gamma

/-- Neighbourhood relaxation of the finite-support action in the product completion. -/
def weightedHistoryRelaxation (x : ∀ j, K j) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ U ∈ 𝓝 x,
    r ≤ sInf ((fun h : ⨁ j, Gamma j => (D.weightedHistoryAction h : ℝ≥0∞)) ''
      ((weightedHistoryInclusion Gamma) ⁻¹' U))}

theorem weightedHistoryRelaxation_eq_action [∀ j, T0Space (K j)]
    (x : ⨁ j, Gamma j) :
    D.weightedHistoryRelaxation (weightedHistoryInclusion Gamma x) = D.weightedHistoryAction x := by
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨U, hU, hr⟩
    have hxU : weightedHistoryInclusion Gamma x ∈ U := mem_of_mem_nhds hU
    exact hr.trans (sInf_le ⟨x, hxU, rfl⟩)
  · change (D.weightedHistoryAction x : ℝ≥0∞) ≤ _
    let low : Set (∀ j, K j) := weightedHistoryInclusion Gamma ''
      {h | D.weightedHistoryAction h < D.weightedHistoryAction x}
    have hsub : {h | D.weightedHistoryAction h < D.weightedHistoryAction x} ⊆
        {h | D.weightedHistoryAction h ≤ D.weightedHistoryAction x} :=
      fun _ h => by simpa only [Set.mem_setOf_eq] using h.le
    have hlowFinite : low.Finite :=
      ((D.weightedHistoryAction_sublevel_finite (D.weightedHistoryAction x)).subset hsub).image
        (weightedHistoryInclusion Gamma)
    have hxlow : weightedHistoryInclusion Gamma x ∉ low := by
      rintro ⟨h, hh, heq⟩
      have hxeq : h = x := weightedHistoryInclusion_injective Gamma heq
      subst h
      have hxx : D.weightedHistoryAction x < D.weightedHistoryAction x := by
        simpa only [Set.mem_setOf_eq] using hh
      exact (lt_irrefl _ hxx)
    let U := lowᶜ
    have hU : U ∈ 𝓝 (weightedHistoryInclusion Gamma x) :=
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
    [∀ j, T0Space (K j)]
    {x : ∀ j, K j} (hx : x ∉ Set.range (weightedHistoryInclusion Gamma)) :
    D.weightedHistoryRelaxation x = ∞ := by
  rw [weightedHistoryRelaxation, sSup_eq_top]
  intro b hb
  let R : ℝ≥0 := b.toNNReal + 1
  let r : ℝ≥0∞ := R
  have hbr : b < r := by
    rw [show b = (b.toNNReal : ℝ≥0∞) from (ENNReal.coe_toNNReal (ne_of_lt hb)).symm]
    exact ENNReal.coe_lt_coe.mpr (lt_add_one b.toNNReal)
  refine ⟨r, ?_, hbr⟩
  change ∃ U ∈ 𝓝 x,
    r ≤ sInf ((fun h : ⨁ j, Gamma j => (D.weightedHistoryAction h : ℝ≥0∞)) ''
      (weightedHistoryInclusion Gamma ⁻¹' U))
  ·
    let low : Set (∀ j, K j) := weightedHistoryInclusion Gamma ''
      {h | D.weightedHistoryAction h ≤ R}
    have hlowFinite : low.Finite :=
      (D.weightedHistoryAction_sublevel_finite R).image (weightedHistoryInclusion Gamma)
    have hxlow : x ∉ low := by
      intro h
      exact hx ⟨h.choose, h.choose_spec.2⟩
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
    (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    [∀ j, CompleteSpace (K j)] [∀ j, T0Space (K j)] :
    DenseRange (weightedHistoryInclusion Gamma) ∧
      (∀ R, {x | D.weightedHistoryAction x ≤ R}.Finite) ∧
      (∀ R, IsCompact {x | D.weightedHistoryAction x ≤ R}) ∧
      (∀ x y, D.weightedHistoryAction (x + y) ≤
        D.weightedHistoryAction x + D.weightedHistoryAction y) ∧
      (∀ h, D.weightedHistoryRelaxation (weightedHistoryInclusion Gamma h) =
        D.weightedHistoryAction h) ∧
      (∀ x, x ∉ Set.range (weightedHistoryInclusion Gamma) →
        D.weightedHistoryRelaxation x = ∞) := by
  refine ⟨weightedHistoryInclusion_denseRange Gamma hGamma,
    D.weightedHistoryAction_sublevel_finite,
    fun R => (D.weightedHistoryAction_sublevel_finite R).isCompact,
    D.weightedHistoryAction_add_le, D.weightedHistoryRelaxation_eq_action,
    fun x hx => D.weightedHistoryRelaxation_eq_top_of_not_mem_range hx⟩

end WeightedHistoryDatum

end Action

end

end GaloisForLFunctions.HTGeometry
