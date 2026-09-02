import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Constructions

/-!
# Restricted-history completion for arbitrary groups

Finite-support histories in dense coordinate subgroups form a dense subgroup of the full product.
The product is their Hausdorff uniform completion. Infinitely many nontrivial coordinates make the
inclusion proper and nonclosed. For a countable coordinate family, partial histories have
eventually constant finite observations, linearly growing support, and an infinite-support product
limit outside the source.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J : Type*} {K : J → Type*}
variable [∀ j, Group (K j)]

/-- Finite-support subgroup of a dependent product of coordinate subgroups. -/
def multiplicativeRestrictedHistorySubgroup (Gamma : ∀ j, Subgroup (K j)) :
    Subgroup (∀ j, Gamma j) where
  carrier := {x | Set.Finite {j | x j ≠ 1}}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    refine (hx.union hy).subset ?_
    intro j hj
    simp only [Set.mem_setOf_eq, Set.mem_union] at hj ⊢
    by_cases hxj : x j = 1
    · right
      intro hyj
      exact hj (by simp [hxj, hyj])
    · exact Or.inl hxj
  inv_mem' {x} hx := by
    refine hx.subset ?_
    intro j hj
    simp only [Set.mem_setOf_eq] at hj ⊢
    simpa using hj

/-- Restricted product of the coordinate subgroups. -/
abbrev MultiplicativeRestrictedHistory (Gamma : ∀ j, Subgroup (K j)) :=
  multiplicativeRestrictedHistorySubgroup Gamma

/-- Finite support of a restricted history. -/
def multiplicativeRestrictedHistorySupport (Gamma : ∀ j, Subgroup (K j))
    (x : MultiplicativeRestrictedHistory Gamma) : Finset J :=
  x.property.toFinset

@[simp]
theorem mem_multiplicativeRestrictedHistorySupport_iff
    (Gamma : ∀ j, Subgroup (K j)) (x : MultiplicativeRestrictedHistory Gamma) (j : J) :
    j ∈ multiplicativeRestrictedHistorySupport Gamma x ↔ x.1 j ≠ 1 := by
  simp [multiplicativeRestrictedHistorySupport]

/-- Canonical inclusion into the product completion. -/
def multiplicativeRestrictedHistoryInclusion (Gamma : ∀ j, Subgroup (K j)) :
    MultiplicativeRestrictedHistory Gamma → ∀ j, K j :=
  fun x j => x.1 j

theorem multiplicativeRestrictedHistoryInclusion_injective
    (Gamma : ∀ j, Subgroup (K j)) :
    Function.Injective (multiplicativeRestrictedHistoryInclusion Gamma) := by
  intro x y h
  apply Subtype.ext
  funext j
  apply Subtype.ext
  exact congrFun h j

/-- Coordinatewise density gives density of finite-support histories in the full product. -/
theorem multiplicativeRestrictedHistoryInclusion_denseRange
    (Gamma : ∀ j, Subgroup (K j)) [∀ j, UniformSpace (K j)]
    (hGamma : ∀ j, Dense (Gamma j : Set (K j))) :
    DenseRange (multiplicativeRestrictedHistoryInclusion Gamma) := by
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp hU x hxU
  classical
  choose k hkGamma hku using fun j : I =>
    (hGamma j.1).exists_mem_open (hu j.1 j.2).1 ⟨x j.1, (hu j.1 j.2).2⟩
  let y : ∀ j, Gamma j := fun j =>
    if hj : j ∈ I then ⟨k ⟨j, hj⟩, hkGamma ⟨j, hj⟩⟩ else 1
  have hy : Set.Finite {j | y j ≠ 1} := by
    refine I.finite_toSet.subset ?_
    intro j hj
    simp only [Finset.mem_coe]
    by_contra hnot
    simp [y, hnot] at hj
  let yr : MultiplicativeRestrictedHistory Gamma := ⟨y, hy⟩
  refine ⟨multiplicativeRestrictedHistoryInclusion Gamma yr, ?_, ⟨yr, rfl⟩⟩
  apply hpi
  intro j hj
  change ((y j : Gamma j) : K j) ∈ u j
  have hjI : j ∈ I := hj
  have hyj : y j = ⟨k ⟨j, hj⟩, hkGamma ⟨j, hj⟩⟩ := by
    simp [y, hjI]
  rw [hyj]
  exact hku ⟨j, hj⟩

/-- Infinitely many nontrivial coordinates produce an infinite-support product point. -/
theorem multiplicativeRestrictedHistoryInclusion_not_surjective_of_infinite_nontrivial
    (Gamma : ∀ j, Subgroup (K j))
    (hInfinite : Set.Infinite {j | Nontrivial (Gamma j)}) :
    ¬ Function.Surjective (multiplicativeRestrictedHistoryInclusion Gamma) := by
  classical
  let g : ∀ j, Gamma j := fun j =>
    if hj : Nontrivial (Gamma j) then
      Classical.choose (by letI := hj; exact exists_ne (1 : Gamma j))
    else 1
  have hg : ∀ j, Nontrivial (Gamma j) → g j ≠ 1 := by
    intro j hj
    simp only [g, dif_pos hj]
    letI := hj
    exact Classical.choose_spec (exists_ne (1 : Gamma j))
  intro hsurj
  obtain ⟨h, hh⟩ := hsurj (fun j => (g j : K j))
  have hsubset : {j | Nontrivial (Gamma j)} ⊆ {j | h.1 j ≠ 1} := by
    intro j hj
    simp only [Set.mem_setOf_eq]
    intro hz
    apply hg j hj
    exact Subtype.ext (by
      change (g j : K j) = (1 : K j)
      simpa [multiplicativeRestrictedHistoryInclusion, hz] using (congrFun hh j).symm)
  exact hInfinite (h.property.subset hsubset)

/-- A proper dense restricted-history subgroup is not closed. -/
theorem multiplicativeRestrictedHistoryInclusion_not_isClosed_of_infinite_nontrivial
    (Gamma : ∀ j, Subgroup (K j)) [∀ j, UniformSpace (K j)]
    (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    (hInfinite : Set.Infinite {j | Nontrivial (Gamma j)}) :
    ¬ IsClosed (Set.range (multiplicativeRestrictedHistoryInclusion Gamma)) := by
  intro hclosed
  apply multiplicativeRestrictedHistoryInclusion_not_surjective_of_infinite_nontrivial
    Gamma hInfinite
  rw [← Set.range_eq_univ,
    ← (multiplicativeRestrictedHistoryInclusion_denseRange Gamma hGamma).closure_eq,
    hclosed.closure_eq]

/-- Uniform structure induced from the product completion. -/
@[reducible] def multiplicativeRestrictedHistoryUniformSpace
    (Gamma : ∀ j, Subgroup (K j)) [∀ j, UniformSpace (K j)] :
    UniformSpace (MultiplicativeRestrictedHistory Gamma) :=
  (Pi.uniformSpace K).comap (multiplicativeRestrictedHistoryInclusion Gamma)

section Completion

variable [∀ j, UniformSpace (K j)]

local instance (Gamma : ∀ j, Subgroup (K j)) :
    UniformSpace (MultiplicativeRestrictedHistory Gamma) :=
  multiplicativeRestrictedHistoryUniformSpace Gamma

/-- Full product as two-sided Hausdorff uniform completion of restricted histories. -/
def multiplicativeRestrictedHistoryAbstractCompletion
    (Gamma : ∀ j, Subgroup (K j)) (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    [∀ j, CompleteSpace (K j)] [∀ j, T0Space (K j)] :
    AbstractCompletion (MultiplicativeRestrictedHistory Gamma) :=
  { space := ∀ j, K j
    coe := multiplicativeRestrictedHistoryInclusion Gamma
    uniformStruct := Pi.uniformSpace K
    complete := inferInstance
    separation := inferInstance
    isUniformInducing := by
      rw [isUniformInducing_iff_uniformSpace]
      rfl
    dense := multiplicativeRestrictedHistoryInclusion_denseRange Gamma hGamma }

/-- Dense-completion, properness, and nonclosedness package for arbitrary compact Hausdorff
coordinate groups. -/
theorem multiplicativeRestrictedHistory_compactObserver_openHistory
    (Gamma : ∀ j, Subgroup (K j)) (hGamma : ∀ j, Dense (Gamma j : Set (K j)))
    (hInfinite : Set.Infinite {j | Nontrivial (Gamma j)})
    [∀ j, CompactSpace (K j)] [∀ j, T2Space (K j)] :
    DenseRange (multiplicativeRestrictedHistoryInclusion Gamma) ∧
      ¬ Function.Surjective (multiplicativeRestrictedHistoryInclusion Gamma) ∧
      ¬ IsClosed (Set.range (multiplicativeRestrictedHistoryInclusion Gamma)) := by
  exact ⟨multiplicativeRestrictedHistoryInclusion_denseRange Gamma hGamma,
    multiplicativeRestrictedHistoryInclusion_not_surjective_of_infinite_nontrivial Gamma hInfinite,
    multiplicativeRestrictedHistoryInclusion_not_isClosed_of_infinite_nontrivial
      Gamma hGamma hInfinite⟩

end Completion

section NaturalRestrictedHistory

variable {K : ℕ → Type*} [∀ n, Group (K n)]

/-- Partial history supported on the first `N` coordinates. -/
def multiplicativeRestrictedHistoryPartial (Gamma : ∀ n, Subgroup (K n))
    (g : ∀ n, Gamma n) (N : ℕ) : MultiplicativeRestrictedHistory Gamma := by
  refine ⟨(fun n => if n < N then g n else 1), ?_⟩
  refine (Finset.range N).finite_toSet.subset ?_
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  simp [hnot] at hn

theorem multiplicativeRestrictedHistoryPartial_apply_of_lt
    (Gamma : ∀ n, Subgroup (K n)) (g : ∀ n, Gamma n)
    (N n : ℕ) (hn : n < N) :
    (multiplicativeRestrictedHistoryPartial Gamma g N).1 n = g n := by
  simp [multiplicativeRestrictedHistoryPartial, hn]

theorem multiplicativeRestrictedHistoryPartial_apply_of_le
    (Gamma : ∀ n, Subgroup (K n)) (g : ∀ n, Gamma n)
    (N n : ℕ) (hn : N ≤ n) :
    (multiplicativeRestrictedHistoryPartial Gamma g N).1 n = 1 := by
  simp [multiplicativeRestrictedHistoryPartial, not_lt_of_ge hn]

theorem multiplicativeRestrictedHistoryPartial_support
    (Gamma : ∀ n, Subgroup (K n)) (g : ∀ n, Gamma n)
    (hg : ∀ n, g n ≠ 1) (N : ℕ) :
    multiplicativeRestrictedHistorySupport Gamma
        (multiplicativeRestrictedHistoryPartial Gamma g N) = Finset.range N := by
  ext n
  simp [multiplicativeRestrictedHistoryPartial, hg]

/-- Support cost of the `N`-th partial history is exactly `N`. -/
theorem multiplicativeRestrictedHistoryPartial_supportCost
    (Gamma : ∀ n, Subgroup (K n)) (g : ∀ n, Gamma n)
    (hg : ∀ n, g n ≠ 1) (N : ℕ) :
    (multiplicativeRestrictedHistorySupport Gamma
      (multiplicativeRestrictedHistoryPartial Gamma g N)).card = N := by
  rw [multiplicativeRestrictedHistoryPartial_support Gamma g hg N]
  simp

/-- Every fixed finite observer is eventually constant along the partial histories. -/
theorem multiplicativeRestrictedHistoryPartial_finiteObserver_eventually_constant
    (Gamma : ∀ n, Subgroup (K n)) (g : ∀ n, Gamma n) (F : Finset ℕ) :
    ∃ N, ∀ M, N ≤ M → ∀ n ∈ F,
      (multiplicativeRestrictedHistoryPartial Gamma g M).1 n = g n := by
  refine ⟨∑ n ∈ F, (n + 1), fun M hM n hn =>
    multiplicativeRestrictedHistoryPartial_apply_of_lt Gamma g M n ?_⟩
  have hnN : n + 1 ≤ ∑ j ∈ F, (j + 1) :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (j + 1)) hn
  omega

/-- Partial histories converge in the product to the full infinite-support history. -/
theorem multiplicativeRestrictedHistoryPartial_tendsto_infiniteHistory
    (Gamma : ∀ n, Subgroup (K n)) [∀ n, UniformSpace (K n)]
    (g : ∀ n, Gamma n) :
    Tendsto
      (fun N => multiplicativeRestrictedHistoryInclusion Gamma
        (multiplicativeRestrictedHistoryPartial Gamma g N))
      atTop (𝓝 fun n => (g n : K n)) := by
  apply tendsto_pi_nhds.2
  intro n
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (n + 1)] with N hN
  exact congrArg Subtype.val
    (multiplicativeRestrictedHistoryPartial_apply_of_lt Gamma g N n (by omega)) |>.symm

/-- A point nontrivial in every coordinate is not a restricted history. -/
theorem multiplicativeRestrictedInfiniteHistory_not_mem_range
    (Gamma : ∀ n, Subgroup (K n)) (g : ∀ n, Gamma n)
    (hg : ∀ n, g n ≠ 1) :
    (fun n => (g n : K n)) ∉
      Set.range (multiplicativeRestrictedHistoryInclusion Gamma) := by
  rintro ⟨x, hx⟩
  have hall : Set.univ ⊆ {n | x.1 n ≠ 1} := by
    intro n _
    simp only [Set.mem_setOf_eq]
    intro hn
    apply hg n
    exact Subtype.ext (by
      change (g n : K n) = (1 : K n)
      simpa [multiplicativeRestrictedHistoryInclusion, hn] using (congrFun hx n).symm)
  exact Set.infinite_univ (x.property.subset hall)

/-- Exact open-lift package for countably many arbitrary coordinate groups. -/
theorem multiplicativeRestrictedHistory_explicit_openLift
    (Gamma : ∀ n, Subgroup (K n)) [∀ n, UniformSpace (K n)]
    (g : ∀ n, Gamma n) (hg : ∀ n, g n ≠ 1) :
    (∀ F : Finset ℕ, ∃ N, ∀ M, N ≤ M → ∀ n ∈ F,
      (multiplicativeRestrictedHistoryPartial Gamma g M).1 n = g n) ∧
    (∀ N, (multiplicativeRestrictedHistorySupport Gamma
      (multiplicativeRestrictedHistoryPartial Gamma g N)).card = N) ∧
    Tendsto
      (fun N => multiplicativeRestrictedHistoryInclusion Gamma
        (multiplicativeRestrictedHistoryPartial Gamma g N))
      atTop (𝓝 fun n => (g n : K n)) ∧
    (fun n => (g n : K n)) ∉
      Set.range (multiplicativeRestrictedHistoryInclusion Gamma) := by
  exact ⟨multiplicativeRestrictedHistoryPartial_finiteObserver_eventually_constant Gamma g,
    multiplicativeRestrictedHistoryPartial_supportCost Gamma g hg,
    multiplicativeRestrictedHistoryPartial_tendsto_infiniteHistory Gamma g,
    multiplicativeRestrictedInfiniteHistory_not_mem_range Gamma g hg⟩

end NaturalRestrictedHistory

section EnumeratedRestrictedHistory

variable {J : Type*} {K : J → Type*} [∀ j, Group (K j)]

/-- First `N` coordinates of an arbitrary enumeration, as a finite set. -/
noncomputable def multiplicativeRestrictedHistoryEnumeratedSupport
    (e : ℕ → J) (N : ℕ) : Finset J := by
  classical
  exact (Finset.range N).image e

/-- Partial history supported on the first `N` entries of an arbitrary injective enumeration. -/
def multiplicativeRestrictedHistoryPartialAlong
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (g : ∀ j, Gamma j) (N : ℕ) :
    MultiplicativeRestrictedHistory Gamma := by
  classical
  refine ⟨(fun j => if j ∈ multiplicativeRestrictedHistoryEnumeratedSupport e N
      then g j else 1), ?_⟩
  exact (multiplicativeRestrictedHistoryEnumeratedSupport e N).finite_toSet.subset (by
    intro j hj
    simp only [Set.mem_setOf_eq] at hj
    simp only [Finset.mem_coe]
    by_contra hnot
    apply hj
    rw [if_neg hnot])

/-- Infinite-support product point determined by the enumerated nonidentity coordinates. -/
def multiplicativeRestrictedInfiniteHistoryAlong
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (g : ∀ j, Gamma j) : ∀ j, K j :=
  by
    classical
    exact fun j => if ∃ n, e n = j then g j else 1

theorem multiplicativeRestrictedHistoryPartialAlong_support
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (g : ∀ j, Gamma j)
    (hg : ∀ n, g (e n) ≠ 1) (N : ℕ) :
    multiplicativeRestrictedHistorySupport Gamma
      (multiplicativeRestrictedHistoryPartialAlong Gamma e g N) =
      multiplicativeRestrictedHistoryEnumeratedSupport e N := by
  classical
  ext j
  rw [mem_multiplicativeRestrictedHistorySupport_iff]
  change (if j ∈ multiplicativeRestrictedHistoryEnumeratedSupport e N then g j else 1) ≠ 1 ↔
    j ∈ multiplicativeRestrictedHistoryEnumeratedSupport e N
  by_cases hj : j ∈ multiplicativeRestrictedHistoryEnumeratedSupport e N
  · rw [if_pos hj]
    refine ⟨fun _ => hj, fun _ => ?_⟩
    unfold multiplicativeRestrictedHistoryEnumeratedSupport at hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
    exact hg n
  · simp [hj]

/-- The enumerated partial history has support cost exactly `N`. -/
theorem multiplicativeRestrictedHistoryPartialAlong_supportCost
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (he : Function.Injective e)
    (g : ∀ j, Gamma j) (hg : ∀ n, g (e n) ≠ 1) (N : ℕ) :
    (multiplicativeRestrictedHistorySupport Gamma
      (multiplicativeRestrictedHistoryPartialAlong Gamma e g N)).card = N := by
  classical
  rw [multiplicativeRestrictedHistoryPartialAlong_support Gamma e g hg N]
  unfold multiplicativeRestrictedHistoryEnumeratedSupport
  rw [Finset.card_image_of_injective _ he]
  simp

theorem multiplicativeRestrictedHistoryPartialAlong_eventually_apply
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (g : ∀ j, Gamma j) (j : J) :
    ∃ N, ∀ M, N ≤ M →
      ((multiplicativeRestrictedHistoryPartialAlong Gamma e g M).1 j : K j) =
        multiplicativeRestrictedInfiniteHistoryAlong Gamma e g j := by
  classical
  by_cases hj : ∃ n, e n = j
  · obtain ⟨n, hn⟩ := hj
    refine ⟨n + 1, fun M hM => ?_⟩
    have hnM : n < M := by omega
    have hmem : j ∈ multiplicativeRestrictedHistoryEnumeratedSupport e M := by
      unfold multiplicativeRestrictedHistoryEnumeratedSupport
      apply Finset.mem_image.mpr
      exact ⟨n, Finset.mem_range.mpr hnM, hn⟩
    change (↑(if j ∈ multiplicativeRestrictedHistoryEnumeratedSupport e M then g j else 1) : K j) =
      if ∃ n, e n = j then (g j : K j) else 1
    rw [if_pos hmem, if_pos ⟨n, hn⟩]
  · refine ⟨0, fun M hM => ?_⟩
    have hnot : j ∉ multiplicativeRestrictedHistoryEnumeratedSupport e M := by
      intro hmem
      unfold multiplicativeRestrictedHistoryEnumeratedSupport at hmem
      obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hmem
      exact hj ⟨n, heq⟩
    change (↑(if j ∈ multiplicativeRestrictedHistoryEnumeratedSupport e M then g j else 1) : K j) =
      if ∃ n, e n = j then (g j : K j) else 1
    rw [if_neg hnot, if_neg hj]
    rfl

/-- Every fixed finite observer is eventually constant along an arbitrary enumerated history. -/
theorem multiplicativeRestrictedHistoryPartialAlong_finiteObserver_eventually_constant
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (g : ∀ j, Gamma j) (F : Finset J) :
    ∃ N, ∀ M, N ≤ M → ∀ j ∈ F,
      ((multiplicativeRestrictedHistoryPartialAlong Gamma e g M).1 j : K j) =
        multiplicativeRestrictedInfiniteHistoryAlong Gamma e g j := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a F ha ih =>
      obtain ⟨Na, hNa⟩ :=
        multiplicativeRestrictedHistoryPartialAlong_eventually_apply Gamma e g a
      obtain ⟨NF, hNF⟩ := ih
      refine ⟨max Na NF, fun M hM j hj => ?_⟩
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hNa M ((le_max_left _ _).trans hM)
      · exact hNF M ((le_max_right _ _).trans hM) j hj

/-- Restriction of a history to one fixed finite-coordinate observer. -/
def multiplicativeRestrictedHistoryFiniteObserver
    (Gamma : ∀ j, Subgroup (K j)) (F : Finset J)
    (x : MultiplicativeRestrictedHistory Gamma) : ∀ j : F, K j.1 :=
  fun j => x.1 j.1

/-- No function of one fixed finite observer bounds support cost along the open history lift. -/
theorem multiplicativeRestrictedHistory_no_finiteObserver_supportCost_bound
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (he : Function.Injective e)
    (g : ∀ j, Gamma j) (hg : ∀ n, g (e n) ≠ 1)
    (F : Finset J) (φ : (∀ j : F, K j.1) → ℕ) :
    ¬ ∀ x : MultiplicativeRestrictedHistory Gamma,
      (multiplicativeRestrictedHistorySupport Gamma x).card ≤
        φ (multiplicativeRestrictedHistoryFiniteObserver Gamma F x) := by
  intro hbound
  obtain ⟨N, hN⟩ :=
    multiplicativeRestrictedHistoryPartialAlong_finiteObserver_eventually_constant
      Gamma e g F
  let terminalObserver : ∀ j : F, K j.1 := fun j =>
    multiplicativeRestrictedInfiniteHistoryAlong Gamma e g j.1
  let M := max N (φ terminalObserver + 1)
  have hNM : N ≤ M := le_max_left _ _
  have hobs :
      multiplicativeRestrictedHistoryFiniteObserver Gamma F
          (multiplicativeRestrictedHistoryPartialAlong Gamma e g M) =
        terminalObserver := by
    funext j
    exact hN M hNM j.1 j.2
  have hcost := multiplicativeRestrictedHistoryPartialAlong_supportCost
    Gamma e he g hg M
  have hb := hbound (multiplicativeRestrictedHistoryPartialAlong Gamma e g M)
  rw [hcost, hobs] at hb
  have hlarge : φ terminalObserver < M := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  omega

/-- Enumerated partial histories converge in the product to their infinite-support point. -/
theorem multiplicativeRestrictedHistoryPartialAlong_tendsto_infiniteHistory
    (Gamma : ∀ j, Subgroup (K j)) [∀ j, UniformSpace (K j)]
    (e : ℕ → J) (g : ∀ j, Gamma j) :
    Tendsto
      (fun N => multiplicativeRestrictedHistoryInclusion Gamma
        (multiplicativeRestrictedHistoryPartialAlong Gamma e g N))
      atTop (𝓝 (multiplicativeRestrictedInfiniteHistoryAlong Gamma e g)) := by
  apply tendsto_pi_nhds.2
  intro j
  obtain ⟨N, hN⟩ :=
    multiplicativeRestrictedHistoryPartialAlong_eventually_apply Gamma e g j
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (hN M hM).symm

/-- An injectively enumerated family of nonidentity coordinates has no finite-support preimage. -/
theorem multiplicativeRestrictedInfiniteHistoryAlong_not_mem_range
    (Gamma : ∀ j, Subgroup (K j)) (e : ℕ → J) (he : Function.Injective e)
    (g : ∀ j, Gamma j) (hg : ∀ n, g (e n) ≠ 1) :
    multiplicativeRestrictedInfiniteHistoryAlong Gamma e g ∉
      Set.range (multiplicativeRestrictedHistoryInclusion Gamma) := by
  rintro ⟨x, hx⟩
  have hsubset : Set.range e ⊆ {j | x.1 j ≠ 1} := by
    rintro j ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq]
    intro hz
    apply hg n
    apply Subtype.ext
    calc
      ((g (e n) : Gamma (e n)) : K (e n)) =
          multiplicativeRestrictedInfiniteHistoryAlong Gamma e g (e n) := by
        simp [multiplicativeRestrictedInfiniteHistoryAlong]
      _ = ((x.1 (e n) : Gamma (e n)) : K (e n)) := (congrFun hx (e n)).symm
      _ = 1 := congrArg Subtype.val hz
  exact (Set.infinite_range_of_injective he) (x.property.subset hsubset)

/-- Exact explicit open-lift package for any countably enumerated set of nontrivial coordinates. -/
theorem multiplicativeRestrictedHistory_explicit_openLift_along
    (Gamma : ∀ j, Subgroup (K j)) [∀ j, UniformSpace (K j)]
    (e : ℕ → J) (he : Function.Injective e)
    (g : ∀ j, Gamma j) (hg : ∀ n, g (e n) ≠ 1) :
    (∀ F : Finset J, ∃ N, ∀ M, N ≤ M → ∀ j ∈ F,
      ((multiplicativeRestrictedHistoryPartialAlong Gamma e g M).1 j : K j) =
        multiplicativeRestrictedInfiniteHistoryAlong Gamma e g j) ∧
    (∀ N, (multiplicativeRestrictedHistorySupport Gamma
      (multiplicativeRestrictedHistoryPartialAlong Gamma e g N)).card = N) ∧
    Tendsto
      (fun N => multiplicativeRestrictedHistoryInclusion Gamma
        (multiplicativeRestrictedHistoryPartialAlong Gamma e g N))
      atTop (𝓝 (multiplicativeRestrictedInfiniteHistoryAlong Gamma e g)) ∧
    multiplicativeRestrictedInfiniteHistoryAlong Gamma e g ∉
      Set.range (multiplicativeRestrictedHistoryInclusion Gamma) := by
  exact ⟨multiplicativeRestrictedHistoryPartialAlong_finiteObserver_eventually_constant
      Gamma e g,
    multiplicativeRestrictedHistoryPartialAlong_supportCost Gamma e he g hg,
    multiplicativeRestrictedHistoryPartialAlong_tendsto_infiniteHistory Gamma e g,
    multiplicativeRestrictedInfiniteHistoryAlong_not_mem_range Gamma e he g hg⟩

end EnumeratedRestrictedHistory

end

end GaloisForLFunctions.HTGeometry
