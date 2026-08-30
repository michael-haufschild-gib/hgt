import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.DFinsupp.FiniteInfinite
import Mathlib.Data.ENNReal.Operations
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.UniformSpace.DiscreteUniformity

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

/-! ## Closed binary source witness -/

section BinaryRestrictedHistory

local instance weightedHistoryCompletionBoundaryLawLocalInst1 : UniformSpace (Fin 2) := ⊥

/-- Nonidentity element of the binary compact coordinate group. -/
def binaryHistoryOne : Fin 2 := ⟨1, by omega⟩

theorem binaryHistoryOne_ne_zero : binaryHistoryOne ≠ 0 := by decide

/-- Dense binary coordinate subgroup; it is the whole compact group. -/
abbrev binaryRestrictedGamma (_ : ℕ) : AddSubgroup (Fin 2) := ⊤

/-- Partial history with the first `N` binary coordinates activated. -/
def binaryRestrictedHistory (N : ℕ) : ⨁ j : ℕ, binaryRestrictedGamma j :=
  DirectSum.mk (fun j => binaryRestrictedGamma j) (Finset.range N) fun _ =>
    ⟨binaryHistoryOne, Set.mem_univ _⟩

theorem binaryRestrictedHistory_apply_of_lt (N j : ℕ) (hj : j < N) :
    ((binaryRestrictedHistory N j : binaryRestrictedGamma j) : Fin 2) = binaryHistoryOne := by
  rw [binaryRestrictedHistory, DirectSum.mk_apply_of_mem (Finset.mem_range.mpr hj)]

theorem binaryRestrictedHistory_apply_of_le (N j : ℕ) (hj : N ≤ j) :
    ((binaryRestrictedHistory N j : binaryRestrictedGamma j) : Fin 2) = 0 := by
  simp [binaryRestrictedHistory, DirectSum.mk, not_lt_of_ge hj]

/-- Support of the `N`-th partial history is exactly the first `N` coordinates. -/
theorem binaryRestrictedHistory_support (N : ℕ) :
    (binaryRestrictedHistory N).support = Finset.range N := by
  ext j
  rw [DFinsupp.mem_support_iff, Finset.mem_range]
  constructor
  · intro hj
    by_contra hn
    exact hj (Subtype.ext
      (binaryRestrictedHistory_apply_of_le N j (Nat.le_of_not_gt hn)))
  · intro hj hz
    have hvalue := binaryRestrictedHistory_apply_of_lt N j hj
    rw [hz] at hvalue
    exact binaryHistoryOne_ne_zero hvalue.symm

/-- Exact support cost of the partial history. -/
theorem binaryRestrictedHistory_supportCost (N : ℕ) :
    (binaryRestrictedHistory N).support.card = N := by
  rw [binaryRestrictedHistory_support, Finset.card_range]

/-- Every fixed finite-coordinate observer is eventually the constant activated packet. -/
theorem binaryRestrictedHistory_finiteObserver_eventually_constant (F : Finset ℕ) :
    ∃ N, ∀ M, N ≤ M → ∀ j ∈ F,
      ((binaryRestrictedHistory M j : binaryRestrictedGamma j) : Fin 2) = binaryHistoryOne := by
  refine ⟨∑ j ∈ F, (j + 1), fun M hM j hj =>
    binaryRestrictedHistory_apply_of_lt M j ?_⟩
  have hjN : j + 1 ≤ ∑ i ∈ F, (i + 1) :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (i + 1)) hj
  omega

/-- Partial histories converge coordinatewise, hence in the compact product, to the constant
infinite-support history. -/
theorem binaryRestrictedHistory_tendsto_infiniteHistory :
    Tendsto
      (fun N => weightedHistoryInclusion binaryRestrictedGamma (binaryRestrictedHistory N))
      atTop (𝓝 fun _ : ℕ => binaryHistoryOne) := by
  apply tendsto_pi_nhds.2
  intro j
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (j + 1)] with N hN
  exact (binaryRestrictedHistory_apply_of_lt N j (by omega)).symm

/-- The binary limit has infinite support and is not a restricted history. -/
theorem binaryInfiniteHistory_not_mem_range :
    (fun _ : ℕ => binaryHistoryOne) ∉
      Set.range (weightedHistoryInclusion binaryRestrictedGamma) := by
  rintro ⟨x, hx⟩
  have hall : ∀ j : ℕ, j ∈ x.support := by
    intro j
    rw [DFinsupp.mem_support_iff]
    intro hz
    have hj := congrFun hx j
    simp only [weightedHistoryInclusion] at hj
    rw [hz] at hj
    exact binaryHistoryOne_ne_zero hj.symm
  have hsub : Set.univ ⊆ (x.support : Set ℕ) := fun j _ => by
    simpa using hall j
  exact Set.infinite_univ (x.support.finite_toSet.subset hsub)

/-- Unconditional binary source capstone for compact observers and open lifted history. -/
theorem binaryRestrictedHistory_compactObserver_openHistory :
    DenseRange (weightedHistoryInclusion binaryRestrictedGamma) ∧
      ¬ Function.Surjective (weightedHistoryInclusion binaryRestrictedGamma) ∧
      ¬ IsClosed (Set.range (weightedHistoryInclusion binaryRestrictedGamma)) ∧
      (∀ F : Finset ℕ, ∃ N, ∀ M, N ≤ M → ∀ j ∈ F,
        ((binaryRestrictedHistory M j : binaryRestrictedGamma j) : Fin 2) =
          binaryHistoryOne) ∧
      (∀ N, (binaryRestrictedHistory N).support.card = N) ∧
      Tendsto
        (fun N => weightedHistoryInclusion binaryRestrictedGamma (binaryRestrictedHistory N))
        atTop (𝓝 fun _ : ℕ => binaryHistoryOne) ∧
      (fun _ : ℕ => binaryHistoryOne) ∉
        Set.range (weightedHistoryInclusion binaryRestrictedGamma) := by
  have hDense : ∀ j, Dense (binaryRestrictedGamma j : Set (Fin 2)) := by
    intro j
    simpa only [binaryRestrictedGamma, AddSubgroup.coe_top] using
      (dense_univ : Dense (Set.univ : Set (Fin 2)))
  have hInfinite : Set.Infinite {j | Nontrivial (binaryRestrictedGamma j)} := by
    have hnontrivial : ∀ j : ℕ, Nontrivial (binaryRestrictedGamma j) := fun _ => inferInstance
    have hset : {j | Nontrivial (binaryRestrictedGamma j)} = Set.univ := by
      exact Set.eq_univ_of_forall fun j => hnontrivial j
    rw [hset]
    exact Set.infinite_univ
  obtain ⟨hdense, hproper, hnonclosed⟩ :=
    restrictedHistory_compactObserver_openHistory binaryRestrictedGamma hDense hInfinite
  exact ⟨hdense, hproper, hnonclosed,
    binaryRestrictedHistory_finiteObserver_eventually_constant,
    binaryRestrictedHistory_supportCost,
    binaryRestrictedHistory_tendsto_infiniteHistory,
    binaryInfiniteHistory_not_mem_range⟩

end BinaryRestrictedHistory

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

local instance weightedHistoryCompletionBoundaryLawLocalInst2 : UniformSpace (⨁ j, Gamma j) := weightedHistoryUniformSpace Gamma

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

/-! ## Unconditional weighted binary source -/

section BinaryWeightedHistory

local instance weightedHistoryCompletionBoundaryLawLocalInst3 : UniformSpace (Fin 2) := ⊥
local instance weightedHistoryCompletionBoundaryLawLocalInst4 : UniformSpace (⨁ j : ℕ, binaryRestrictedGamma j) :=
  weightedHistoryUniformSpace binaryRestrictedGamma

/-- Proper symmetric binary coordinate length. -/
def binaryHistoryLength {j : ℕ} (x : binaryRestrictedGamma j) : ℕ :=
  if x = 0 then 0 else 1

/-- Closed weighted-history datum with linearly growing positive weights. -/
def binaryWeightedHistoryDatum : WeightedHistoryDatum binaryRestrictedGamma where
  weight j := j + 1
  length _ := binaryHistoryLength
  weight_pos j := by
    exact_mod_cast Nat.succ_pos j
  weight_sublevel_finite R := by
    refine (Set.finite_Iic ⌊(R : ℝ)⌋₊).subset ?_
    intro j hj
    apply Nat.le_floor
    have hjR : (j : ℝ≥0) ≤ R := by
      exact le_trans (by norm_num) hj
    exact_mod_cast hjR
  length_zero _ := by simp [binaryHistoryLength]
  length_pos _ x hx := by simp [binaryHistoryLength, hx]
  length_ball_finite _ _ := Set.toFinite _
  length_add_le _ x y := by
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
      simp [binaryHistoryLength, hx, hy]
    split <;> omega
  length_neg _ x := by simp [binaryHistoryLength]

/-- Unconditional exact completion-boundary action law on the binary compact product. -/
theorem binaryWeightedHistory_completion_boundary_law :
    DenseRange (weightedHistoryInclusion binaryRestrictedGamma) ∧
      (∀ R, {x | binaryWeightedHistoryDatum.weightedHistoryAction x ≤ R}.Finite) ∧
      (∀ R, IsCompact
        {x | binaryWeightedHistoryDatum.weightedHistoryAction x ≤ R}) ∧
      (∀ x y, binaryWeightedHistoryDatum.weightedHistoryAction (x + y) ≤
        binaryWeightedHistoryDatum.weightedHistoryAction x +
          binaryWeightedHistoryDatum.weightedHistoryAction y) ∧
      (∀ h, binaryWeightedHistoryDatum.weightedHistoryRelaxation
          (weightedHistoryInclusion binaryRestrictedGamma h) =
        binaryWeightedHistoryDatum.weightedHistoryAction h) ∧
      (∀ x, x ∉ Set.range (weightedHistoryInclusion binaryRestrictedGamma) →
        binaryWeightedHistoryDatum.weightedHistoryRelaxation x = ∞) := by
  have hDense : ∀ j, Dense (binaryRestrictedGamma j : Set (Fin 2)) := by
    intro j
    simpa only [binaryRestrictedGamma, AddSubgroup.coe_top] using
      (dense_univ : Dense (Set.univ : Set (Fin 2)))
  exact binaryWeightedHistoryDatum.weightedHistory_completion_boundary_law hDense

end BinaryWeightedHistory

end Action

end

end GaloisForLFunctions.HTGeometry
