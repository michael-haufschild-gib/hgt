import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
# Steiner--Möbius interaction--observation duality

This module develops the exact Boolean-coordinate duality behind spectral causality. Zeta
features encode interaction modes supported on a finite site packet. Möbius probes are their
exact dual family. Filtering those modes by connected spanning cost therefore gives an exact,
not merely one-sided, classification of accessible and invisible modes.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators
open IncidenceAlgebra
open Module

/-! ## Möbius duality on every finite pointed poset -/

/-- Zeta feature indexed by an element of a finite pointed poset. -/
def posetZetaFeature
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [CommRing R]
    (index : P) : P → R :=
  fun state => zeta R index state

/-- Möbius probe dual to a zeta feature on a finite pointed poset. -/
def posetMobiusProbe
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [CommRing R]
    (index : P) (f : P → R) : R :=
  ∑ state ∈ Finset.Iic index, mu R state index * f state

theorem posetMobiusProbe_posetZetaFeature
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [CommRing R]
    (probeIndex featureIndex : P) :
    posetMobiusProbe (R := R) probeIndex
        (posetZetaFeature (R := R) featureIndex) =
      if featureIndex = probeIndex then 1 else 0 := by
  unfold posetMobiusProbe posetZetaFeature
  simp_rw [zeta_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Iic probeIndex).filter (featureIndex ≤ ·) =
        Finset.Icc featureIndex probeIndex := by
    ext state
    simp [and_comm]
  rw [hfilter, sum_Icc_mu_left]

/-- Möbius probing on a finite pointed poset as a linear functional. -/
def posetMobiusProbeLinear
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [CommRing R]
    (index : P) : (P → R) →ₗ[R] R where
  toFun := posetMobiusProbe index
  map_add' f g := by
    simp [posetMobiusProbe, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp [posetMobiusProbe, Finset.mul_sum, mul_left_comm, smul_eq_mul]

@[simp]
theorem posetMobiusProbeLinear_apply
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [CommRing R]
    (index : P) (f : P → R) :
    posetMobiusProbeLinear index f = posetMobiusProbe index f := rfl

theorem posetZetaFeature_linearIndependent
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [Field R] :
    LinearIndependent R
      (posetZetaFeature (P := P) (R := R) : P → P → R) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro index
  rw [Finsupp.linearCombination_apply] at hl
  have hprobe := congrArg
    (posetMobiusProbeLinear (R := R) index) hl
  simp only [Finsupp.sum, map_sum, map_smul, map_zero,
    posetMobiusProbeLinear_apply,
    posetMobiusProbe_posetZetaFeature] at hprobe
  simpa using hprobe

/-- Canonical zeta basis on every finite pointed poset. -/
noncomputable def posetZetaBasis
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [Field R] :
    Basis P R (P → R) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent
    (posetZetaFeature_linearIndependent (P := P) (R := R))

@[simp]
theorem posetZetaBasis_apply
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [Field R]
    (index : P) :
    posetZetaBasis (P := P) (R := R) index =
      posetZetaFeature (R := R) index := by
  classical
  exact congrFun
    (coe_basisOfPiSpaceOfLinearIndependent
      (posetZetaFeature_linearIndependent (P := P) (R := R))) index

theorem posetZetaBasis_repr
    {P R : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    [LocallyFiniteOrder P] [DecidableEq P] [DecidableLE P] [Field R]
    (f : P → R) (index : P) :
    (posetZetaBasis (P := P) (R := R)).repr f index =
      posetMobiusProbe index f := by
  classical
  have hexpand := (posetZetaBasis (P := P) (R := R)).sum_repr f
  have hprobe := congrArg
    (posetMobiusProbeLinear (R := R) index) hexpand
  simp only [map_sum, map_smul, posetZetaBasis_apply,
    posetMobiusProbeLinear_apply,
    posetMobiusProbe_posetZetaFeature] at hprobe
  simpa using hprobe

/-! ## Arbitrary finite local alphabets -/

/-- A finite local alphabet pointed at a reference value and ordered as a star: the reference is
below every value, while distinct non-reference values are incomparable. -/
structure AnchoredValue (A : Type*) (base : A) where
  val : A
deriving Fintype, DecidableEq

namespace AnchoredValue

variable {A : Type*} {base : A}

instance instLE : LE (AnchoredValue A base) :=
  ⟨fun x y => x.val = base ∨ x.val = y.val⟩

instance instPartialOrder : PartialOrder (AnchoredValue A base) where
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hxy with hx | hxy
    · exact Or.inl hx
    · rcases hyz with hy | hyz
      · exact Or.inl (hxy.trans hy)
      · exact Or.inr (hxy.trans hyz)
  le_antisymm x y hxy hyx := by
    rcases hxy with hx | hxy
    · rcases hyx with hy | hyx
      · cases x
        cases y
        simp only [mk.injEq]
        exact hx.trans hy.symm
      · cases x
        cases y
        simp only [mk.injEq]
        exact hyx.symm
    · cases x
      cases y
      simp only [mk.injEq]
      exact hxy

instance instOrderBot : OrderBot (AnchoredValue A base) where
  bot := ⟨base⟩
  bot_le _ := Or.inl rfl

@[simp]
theorem val_bot : (⊥ : AnchoredValue A base).val = base := rfl

@[simp]
theorem mk_le_mk {a b : A} :
    (AnchoredValue.mk a : AnchoredValue A base) ≤ AnchoredValue.mk b ↔
      a = base ∨ a = b := Iff.rfl

instance instDecidableLE [DecidableEq A] :
    DecidableLE (AnchoredValue A base) :=
  fun _ _ => inferInstanceAs (Decidable (_ = base ∨ _ = _))

instance instDecidableLT [DecidableEq A] :
    DecidableLT (AnchoredValue A base) :=
  fun x y => inferInstanceAs (Decidable (x ≤ y ∧ ¬ y ≤ x))

noncomputable instance instLocallyFiniteOrder
    [Fintype A] [DecidableEq A] :
    LocallyFiniteOrder (AnchoredValue A base) :=
  Fintype.toLocallyFiniteOrder

end AnchoredValue

/-- Product configurations over an arbitrary finite pointed local alphabet. -/
abbrev AnchoredConfiguration (V A : Type*) (base : A) :=
  V → AnchoredValue A base

instance anchoredConfigurationDecidableLE
    {V A : Type*} [Fintype V] [DecidableEq A] {base : A} :
    DecidableLE (AnchoredConfiguration V A base) :=
  fun x y => inferInstanceAs (Decidable (∀ i, x i ≤ y i))

/-- Coordinates on which an anchored configuration is non-reference. -/
def anchoredSupport
    {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
    {base : A} (index : AnchoredConfiguration V A base) : Finset V :=
  Finset.univ.filter fun i => index i ≠ ⊥

@[simp]
theorem mem_anchoredSupport
    {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
    {base : A} (index : AnchoredConfiguration V A base) (i : V) :
    i ∈ anchoredSupport index ↔ index i ≠ ⊥ := by
  simp [anchoredSupport]

/-- Reset every coordinate outside `support` to the reference value. -/
def anchoredReset
    {V A : Type*} [DecidableEq V] {base : A}
    (support : Finset V) (state : AnchoredConfiguration V A base) :
    AnchoredConfiguration V A base :=
  fun i => if i ∈ support then state i else ⊥

theorem anchoredSupport_anchoredReset_subset
    {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
    {base : A} (support : Finset V)
    (state : AnchoredConfiguration V A base) :
    anchoredSupport (anchoredReset support state) ⊆ support := by
  intro i hi
  by_contra hin
  have hnonzero := (mem_anchoredSupport _ _).mp hi
  exact hnonzero (by simp [anchoredReset, hin])

/-- Functions of arbitrary finite-alphabet configurations determined by coordinates in `support`. -/
def anchoredLocalSubmodule
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    Submodule R
      (AnchoredConfiguration V A base → R) where
  carrier := {f | ∀ state, f state = f (anchoredReset support state)}
  zero_mem' _ := rfl
  add_mem' {f g} hf hg state := by
    simp only [Pi.add_apply]
    rw [hf state, hg state]
  smul_mem' c f hf state := by
    simp only [Pi.smul_apply]
    rw [hf state]

/-- An anchored zeta mode is local on every site packet containing its non-reference support. -/
theorem posetZetaFeature_mem_anchoredLocalSubmodule
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    {index : AnchoredConfiguration V A base} {support : Finset V}
    (hsub : anchoredSupport index ⊆ support) :
    posetZetaFeature (R := R) index ∈
      anchoredLocalSubmodule support := by
  intro state
  unfold posetZetaFeature
  simp only [zeta_apply]
  have hiff :
      index ≤ state ↔ index ≤ anchoredReset support state := by
    constructor
    · intro h i
      by_cases hi : i ∈ support
      · simpa [anchoredReset, hi] using h i
      · have hibot : index i = ⊥ := by
          by_contra hne
          exact hi (hsub ((mem_anchoredSupport index i).2 hne))
        rw [hibot]
        exact bot_le
    · intro h i
      by_cases hi : i ∈ support
      · simpa [anchoredReset, hi] using h i
      · have hle := h i
        have hreset : anchoredReset support state i = ⊥ := by
          simp [anchoredReset, hi]
        rw [hreset] at hle
        have hibot : index i = ⊥ := le_bot_iff.mp hle
        rw [hibot]
        exact bot_le
  exact if_congr hiff rfl rfl

/-- Restriction of an anchored-local function to configurations supported in its local packet. -/
def anchoredLocalRestriction
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    anchoredLocalSubmodule (A := A) (base := base) (R := R) support →ₗ[R]
      ({index : AnchoredConfiguration V A base //
          anchoredSupport index ⊆ support} → R) where
  toFun f index := f.1 index.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem anchoredLocalRestriction_injective
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    Function.Injective
      (anchoredLocalRestriction (A := A) (base := base) (R := R) support) := by
  intro f g h
  apply Subtype.ext
  funext state
  rw [f.2 state, g.2 state]
  exact congrFun h
    ⟨anchoredReset support state,
      anchoredSupport_anchoredReset_subset support state⟩

/-- Interaction modes whose non-reference site support lies inside `support`. -/
noncomputable def anchoredSupportInteractionSubmodule
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    Submodule R (AnchoredConfiguration V A base → R) :=
  Submodule.span R
    (posetZetaBasis
      (P := AnchoredConfiguration V A base) (R := R) ''
        {index | anchoredSupport index ⊆ support})

theorem anchoredSupportInteractionSubmodule_finrank
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    Module.finrank R
        (anchoredSupportInteractionSubmodule
          (A := A) (base := base) (R := R) support) =
      Nat.card {index : AnchoredConfiguration V A base //
        anchoredSupport index ⊆ support} := by
  classical
  let family :
      {index : AnchoredConfiguration V A base //
          anchoredSupport index ⊆ support} →
        (AnchoredConfiguration V A base → R) :=
    fun index => posetZetaFeature index.1
  have hli : LinearIndependent R family := by
    exact
      (posetZetaFeature_linearIndependent
        (P := AnchoredConfiguration V A base) (R := R)).comp
          (fun index :
            {index : AnchoredConfiguration V A base //
              anchoredSupport index ⊆ support} => index.1)
          Subtype.val_injective
  have hrange :
      Set.range family =
        posetZetaBasis
          (P := AnchoredConfiguration V A base) (R := R) ''
            {index | anchoredSupport index ⊆ support} := by
    ext f
    constructor
    · rintro ⟨index, rfl⟩
      refine ⟨index.1, index.2, ?_⟩
      rw [posetZetaBasis_apply]
    · rintro ⟨index, hindex, rfl⟩
      refine ⟨(⟨index, hindex⟩ :
        {index : AnchoredConfiguration V A base //
          anchoredSupport index ⊆ support}), ?_⟩
      rw [posetZetaBasis_apply]
  unfold anchoredSupportInteractionSubmodule
  rw [← hrange]
  simpa [Nat.card_eq_fintype_card] using finrank_span_eq_card hli

/-- **Exact arbitrary-alphabet support decomposition.** Local functions are exactly the span of
anchored interaction modes whose supports lie in the local packet. -/
theorem anchoredSupportInteractionSubmodule_eq_anchoredLocalSubmodule
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    anchoredSupportInteractionSubmodule
        (A := A) (base := base) (R := R) support =
      anchoredLocalSubmodule support := by
  classical
  apply Submodule.eq_of_le_of_finrank_le
  · unfold anchoredSupportInteractionSubmodule
    apply Submodule.span_le.2
    rintro f ⟨index, hindex, rfl⟩
    rw [posetZetaBasis_apply]
    exact posetZetaFeature_mem_anchoredLocalSubmodule hindex
  · rw [anchoredSupportInteractionSubmodule_finrank]
    have hle :=
      (anchoredLocalRestriction
        (A := A) (base := base) (R := R) support).finrank_le_finrank_of_injective
          (anchoredLocalRestriction_injective
            (A := A) (base := base) (R := R) support)
    simpa [Module.finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card] using hle

/-- Boolean zeta feature indexed by a site packet: it asks whether every indexed site is active. -/
def booleanZetaFeature
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (sites : Finset V) : Finset V → R :=
  fun active => zeta R sites active

/-- Möbius probe dual to the Boolean zeta feature indexed by `sites`. -/
def booleanMobiusProbe
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (sites : Finset V) (f : Finset V → R) : R :=
  ∑ active ∈ Finset.Iic sites, mu R active sites * f active

/-- Möbius probes and zeta features are exactly biorthogonal. -/
theorem booleanMobiusProbe_booleanZetaFeature
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (probeSites featureSites : Finset V) :
    booleanMobiusProbe (R := R) probeSites
        (booleanZetaFeature (R := R) featureSites) =
      if featureSites = probeSites then 1 else 0 := by
  classical
  unfold booleanMobiusProbe booleanZetaFeature
  simp_rw [zeta_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Iic probeSites).filter (featureSites ≤ ·) =
        Finset.Icc featureSites probeSites := by
    ext active
    simp [and_comm]
  rw [hfilter, sum_Icc_mu_left]

theorem booleanMobiusProbe_add
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (sites : Finset V) (f g : Finset V → R) :
    booleanMobiusProbe sites (f + g) =
      booleanMobiusProbe sites f + booleanMobiusProbe sites g := by
  simp [booleanMobiusProbe, mul_add, Finset.sum_add_distrib]

theorem booleanMobiusProbe_smul
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (sites : Finset V) (c : R) (f : Finset V → R) :
    booleanMobiusProbe sites (c • f) =
      c * booleanMobiusProbe sites f := by
  simp [booleanMobiusProbe, Finset.mul_sum, mul_left_comm]

/-- Möbius probing as a linear functional. -/
def booleanMobiusProbeLinear
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (sites : Finset V) : (Finset V → R) →ₗ[R] R where
  toFun := booleanMobiusProbe sites
  map_add' := booleanMobiusProbe_add sites
  map_smul' c f := by
    simpa [smul_eq_mul] using booleanMobiusProbe_smul sites c f

@[simp]
theorem booleanMobiusProbeLinear_apply
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (sites : Finset V) (f : Finset V → R) :
    booleanMobiusProbeLinear sites f = booleanMobiusProbe sites f := rfl

/-- Boolean zeta features form a linearly independent family. -/
theorem booleanZetaFeature_linearIndependent
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R] :
    LinearIndependent R
      (booleanZetaFeature (V := V) (R := R) : Finset V → Finset V → R) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro sites
  rw [Finsupp.linearCombination_apply] at hl
  have hprobe := congrArg
    (booleanMobiusProbeLinear (R := R) sites) hl
  simp only [Finsupp.sum, map_sum, map_smul, map_zero,
    booleanMobiusProbeLinear_apply,
    booleanMobiusProbe_booleanZetaFeature] at hprobe
  simpa using hprobe

/-- Canonical Boolean zeta basis of all scalar functions on finite Boolean configurations. -/
noncomputable def booleanZetaBasis
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R] :
    Basis (Finset V) R (Finset V → R) :=
  by
    classical
    exact basisOfPiSpaceOfLinearIndependent
      (booleanZetaFeature_linearIndependent (V := V) (R := R))

@[simp]
theorem booleanZetaBasis_apply
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R] (sites : Finset V) :
    booleanZetaBasis (V := V) (R := R) sites =
      booleanZetaFeature (R := R) sites := by
  classical
  exact congrFun
    (coe_basisOfPiSpaceOfLinearIndependent
      (booleanZetaFeature_linearIndependent (V := V) (R := R))) sites

/-- The zeta-basis coordinate of a function is exactly its Möbius probe. -/
theorem booleanZetaBasis_repr
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (f : Finset V → R) (sites : Finset V) :
    (booleanZetaBasis (V := V) (R := R)).repr f sites =
      booleanMobiusProbe sites f := by
  classical
  have hexpand :=
    (booleanZetaBasis (V := V) (R := R)).sum_repr f
  have hprobe := congrArg
    (booleanMobiusProbeLinear (R := R) sites) hexpand
  simp only [map_sum, map_smul, booleanZetaBasis_apply,
    booleanMobiusProbeLinear_apply,
    booleanMobiusProbe_booleanZetaFeature] at hprobe
  simpa using hprobe

/-- Functions assembled only from Boolean interaction modes whose assigned cost is at most `r`. -/
noncomputable def costFilteredInteractionSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (cost : Finset V → WithTop ℕ) (r : WithTop ℕ) :
    Submodule R (Finset V → R) :=
  Submodule.span R
    (booleanZetaBasis (V := V) (R := R) '' {sites | cost sites ≤ r})

/-- **Exact interaction--observation duality.** Membership in a cost-filtered interaction space
is equivalent to annihilation by every Möbius probe above the cost threshold. -/
theorem mem_costFilteredInteractionSubmodule_iff
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (cost : Finset V → WithTop ℕ) (r : WithTop ℕ) (f : Finset V → R) :
    f ∈ costFilteredInteractionSubmodule cost r ↔
      ∀ sites, r < cost sites → booleanMobiusProbe sites f = 0 := by
  classical
  unfold costFilteredInteractionSubmodule
  rw [Module.Basis.mem_span_image]
  simp only [Finsupp.support_subset_iff, Set.mem_setOf_eq,
    booleanZetaBasis_repr]
  constructor
  · intro h sites hcost
    exact h sites (not_le_of_gt hcost)
  · intro h sites hcost
    exact h sites (lt_of_not_ge hcost)

/-- Exact dimension of a filtered Boolean interaction space. -/
theorem costFilteredInteractionSubmodule_finrank
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (cost : Finset V → WithTop ℕ) (r : WithTop ℕ) :
    Module.finrank R
        (costFilteredInteractionSubmodule (V := V) (R := R) cost r) =
      Fintype.card {sites : Finset V // cost sites ≤ r} := by
  classical
  let allowed := {sites : Finset V // cost sites ≤ r}
  let family : allowed → (Finset V → R) :=
    fun sites => booleanZetaFeature sites.1
  have hli : LinearIndependent R family := by
    exact (booleanZetaFeature_linearIndependent (V := V) (R := R)).comp
      (fun sites : allowed => sites.1) Subtype.val_injective
  have hrange :
      Set.range family =
        booleanZetaBasis (V := V) (R := R) '' {sites | cost sites ≤ r} := by
    ext f
    constructor
    · rintro ⟨sites, rfl⟩
      refine ⟨sites.1, sites.2, ?_⟩
      rw [booleanZetaBasis_apply]
    · rintro ⟨sites, hcost, rfl⟩
      refine ⟨(⟨sites, hcost⟩ : allowed), ?_⟩
      rw [booleanZetaBasis_apply]
  unfold costFilteredInteractionSubmodule
  rw [← hrange]
  exact finrank_span_eq_card hli

/-! ## Exact support locality -/

/-- Boolean functions whose value is completely determined by coordinates in `support`. -/
def booleanLocalSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) : Submodule R (Finset V → R) where
  carrier := {f | ∀ active, f active = f (active ∩ support)}
  zero_mem' active := rfl
  add_mem' {f g} hf hg active := by
    simp only [Pi.add_apply]
    rw [hf active, hg active]
  smul_mem' c f hf active := by
    simp only [Pi.smul_apply]
    rw [hf active]

/-- A zeta feature is local on every coordinate packet containing its index. -/
theorem booleanZetaFeature_mem_booleanLocalSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    {featureSites support : Finset V} (hsub : featureSites ⊆ support) :
    booleanZetaFeature (R := R) featureSites ∈
      booleanLocalSubmodule support := by
  intro active
  unfold booleanZetaFeature
  simp only [zeta_apply]
  have hiff :
      featureSites ⊆ active ↔ featureSites ⊆ active ∩ support := by
    constructor
    · exact fun h => Finset.subset_inter h hsub
    · exact fun h => h.trans Finset.inter_subset_left
  exact if_congr hiff rfl rfl

/-- Restriction of a local Boolean function to the subconfigurations of its support. -/
def booleanLocalRestriction
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) :
    booleanLocalSubmodule (R := R) support →ₗ[R]
      ({sites : Finset V // sites ⊆ support} → R) where
  toFun f sites := f.1 sites.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem booleanLocalRestriction_injective
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) :
    Function.Injective (booleanLocalRestriction (R := R) support) := by
  intro f g h
  apply Subtype.ext
  funext active
  rw [f.2 active, g.2 active]
  exact congrFun h ⟨active ∩ support, Finset.inter_subset_right⟩

/-- Interaction space generated by exactly those zeta modes supported inside `support`. -/
noncomputable def supportFilteredInteractionSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) : Submodule R (Finset V → R) :=
  Submodule.span R
    (booleanZetaBasis (V := V) (R := R) '' {sites | sites ⊆ support})

theorem supportFilteredInteractionSubmodule_finrank
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) :
    Module.finrank R
        (supportFilteredInteractionSubmodule (R := R) support) =
      Fintype.card {sites : Finset V // sites ⊆ support} := by
  classical
  let allowed := {sites : Finset V // sites ⊆ support}
  let family : allowed → (Finset V → R) :=
    fun sites => booleanZetaFeature sites.1
  have hli : LinearIndependent R family := by
    exact (booleanZetaFeature_linearIndependent (V := V) (R := R)).comp
      (fun sites : allowed => sites.1) Subtype.val_injective
  have hrange :
      Set.range family =
        booleanZetaBasis (V := V) (R := R) ''
          {sites | sites ⊆ support} := by
    ext f
    constructor
    · rintro ⟨sites, rfl⟩
      refine ⟨sites.1, sites.2, ?_⟩
      rw [booleanZetaBasis_apply]
    · rintro ⟨sites, hsites, rfl⟩
      refine ⟨(⟨sites, hsites⟩ : allowed), ?_⟩
      rw [booleanZetaBasis_apply]
  unfold supportFilteredInteractionSubmodule
  rw [← hrange]
  exact finrank_span_eq_card hli

/-- **Exact support decomposition.** A Boolean function is local on `support` iff it is a linear
combination of zeta modes indexed by subsets of `support`. -/
theorem supportFilteredInteractionSubmodule_eq_booleanLocalSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) :
    supportFilteredInteractionSubmodule (R := R) support =
      booleanLocalSubmodule support := by
  classical
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.2
    rintro f ⟨sites, hsites, rfl⟩
    rw [booleanZetaBasis_apply]
    exact booleanZetaFeature_mem_booleanLocalSubmodule hsites
  · rw [supportFilteredInteractionSubmodule_finrank]
    have hle :=
      (booleanLocalRestriction (R := R) support).finrank_le_finrank_of_injective
        (booleanLocalRestriction_injective (R := R) support)
    simpa [Module.finrank_fintype_fun_eq_card] using hle

/-! ## Connected interaction geometry -/

/-- A site packet is Steiner-eligible at depth `r` when some connected interaction subgraph with
at most `r` edges contains every site in the packet. -/
def SteinerEligible
    {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ)
    (sites : Finset V) : Prop :=
  ∃ H : G.Subgraph, H.Connected ∧
    Nat.card H.coe.edgeSet ≤ r ∧ (sites : Set V) ⊆ H.verts

/-! ### Universal finite-alphabet law -/

/-- Arbitrary-alphabet interaction modes selected by connected graph geometry at depth `r`. -/
noncomputable def anchoredSteinerInteractionSubmodule
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ) :
    Submodule R (AnchoredConfiguration V A base → R) :=
  Submodule.span R
    (posetZetaBasis
      (P := AnchoredConfiguration V A base) (R := R) ''
        {index | SteinerEligible G r (anchoredSupport index)})

/-- **Universal Steiner--Möbius duality.** For every finite graph and every finite pointed local
alphabet, membership in the connected interaction space is equivalent to annihilation by every
geometrically ineligible Möbius probe. -/
theorem mem_anchoredSteinerInteractionSubmodule_iff
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ)
    (f : AnchoredConfiguration V A base → R) :
    f ∈ anchoredSteinerInteractionSubmodule G r ↔
      ∀ index, ¬ SteinerEligible G r (anchoredSupport index) →
        posetMobiusProbe index f = 0 := by
  classical
  unfold anchoredSteinerInteractionSubmodule
  rw [Module.Basis.mem_span_image]
  simp only [Finsupp.support_subset_iff, Set.mem_setOf_eq,
    posetZetaBasis_repr]

/-- Exact number of arbitrary-alphabet interaction modes available at connected depth `r`. -/
theorem anchoredSteinerInteractionSubmodule_finrank
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ) :
    Module.finrank R
        (anchoredSteinerInteractionSubmodule
          (A := A) (base := base) (R := R) G r) =
      Nat.card {index : AnchoredConfiguration V A base //
        SteinerEligible G r (anchoredSupport index)} := by
  classical
  let family :
      {index : AnchoredConfiguration V A base //
          SteinerEligible G r (anchoredSupport index)} →
        (AnchoredConfiguration V A base → R) :=
    fun index => posetZetaFeature index.1
  have hli : LinearIndependent R family := by
    exact
      (posetZetaFeature_linearIndependent
        (P := AnchoredConfiguration V A base) (R := R)).comp
          (fun index :
            {index : AnchoredConfiguration V A base //
              SteinerEligible G r (anchoredSupport index)} => index.1)
          Subtype.val_injective
  have hrange :
      Set.range family =
        posetZetaBasis
          (P := AnchoredConfiguration V A base) (R := R) ''
            {index | SteinerEligible G r (anchoredSupport index)} := by
    ext f
    constructor
    · rintro ⟨index, rfl⟩
      refine ⟨index.1, index.2, ?_⟩
      rw [posetZetaBasis_apply]
    · rintro ⟨index, hindex, rfl⟩
      refine ⟨(⟨index, hindex⟩ :
        {index : AnchoredConfiguration V A base //
          SteinerEligible G r (anchoredSupport index)}), ?_⟩
      rw [posetZetaBasis_apply]
  unfold anchoredSteinerInteractionSubmodule
  rw [← hrange]
  simpa [Nat.card_eq_fintype_card] using finrank_span_eq_card hli

/-- Span of all arbitrary-alphabet functions local on connected clusters of depth at most `r`. -/
noncomputable def anchoredConnectedClusterLocalSubmodule
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ) :
    Submodule R (AnchoredConfiguration V A base → R) := by
  classical
  exact Submodule.span R {f |
    ∃ H : G.Subgraph, H.Connected ∧ Nat.card H.coe.edgeSet ≤ r ∧
      f ∈ anchoredLocalSubmodule H.verts.toFinset}

/-- **Universal connected-cluster/Steiner identity.** For every finite graph, finite local
alphabet, field, and depth, arbitrary connected-cluster functions span exactly the modes selected
by Steiner eligibility. -/
theorem anchoredConnectedClusterLocalSubmodule_eq_anchoredSteinerInteractionSubmodule
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ) :
    anchoredConnectedClusterLocalSubmodule
        (A := A) (base := base) (R := R) G r =
      anchoredSteinerInteractionSubmodule G r := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.2
    intro f hf
    obtain ⟨H, hconnected, hdepth, hlocal⟩ := hf
    rw [← anchoredSupportInteractionSubmodule_eq_anchoredLocalSubmodule] at hlocal
    apply
      (show anchoredSupportInteractionSubmodule
            (A := A) (base := base) (R := R) H.verts.toFinset ≤
          anchoredSteinerInteractionSubmodule G r by
        apply Submodule.span_le.2
        rintro mode ⟨index, hindex, rfl⟩
        apply Submodule.subset_span
        refine ⟨index, ?_, rfl⟩
        exact ⟨H, hconnected, hdepth, by simpa using hindex⟩)
    exact hlocal
  · apply Submodule.span_le.2
    rintro mode ⟨index, hindex, rfl⟩
    obtain ⟨H, hconnected, hdepth, hspan⟩ := hindex
    apply Submodule.subset_span
    refine ⟨H, hconnected, hdepth, ?_⟩
    rw [posetZetaBasis_apply]
    exact posetZetaFeature_mem_anchoredLocalSubmodule (by simpa using hspan)

/-- Master exact law for every finite graph and finite local alphabet: connected-generation and
Möbius-observation descriptions coincide at every interaction depth. -/
theorem mem_anchoredConnectedClusterLocalSubmodule_iff_mobius_invisible
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ)
    (f : AnchoredConfiguration V A base → R) :
    f ∈ anchoredConnectedClusterLocalSubmodule G r ↔
      ∀ index, ¬ SteinerEligible G r (anchoredSupport index) →
        posetMobiusProbe index f = 0 := by
  rw [
    anchoredConnectedClusterLocalSubmodule_eq_anchoredSteinerInteractionSubmodule]
  exact mem_anchoredSteinerInteractionSubmodule_iff G r f

/-- Exact interaction-mode space selected by connected graph geometry at depth `r`. -/
noncomputable def steinerInteractionSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (G : SimpleGraph V) (r : ℕ) : Submodule R (Finset V → R) :=
  Submodule.span R
    (booleanZetaBasis (V := V) (R := R) '' {sites | SteinerEligible G r sites})

/-- **Steiner--Möbius duality.** A function belongs to the depth-`r` connected interaction space
iff every Möbius probe that cannot be spanned by `r` interaction edges annihilates it. -/
theorem mem_steinerInteractionSubmodule_iff
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (G : SimpleGraph V) (r : ℕ) (f : Finset V → R) :
    f ∈ steinerInteractionSubmodule G r ↔
      ∀ sites, ¬ SteinerEligible G r sites →
        booleanMobiusProbe sites f = 0 := by
  classical
  unfold steinerInteractionSubmodule
  rw [Module.Basis.mem_span_image]
  simp only [Finsupp.support_subset_iff, Set.mem_setOf_eq,
    booleanZetaBasis_repr]

/-- Exact number of independent interaction modes available at connected depth `r`. -/
theorem steinerInteractionSubmodule_finrank
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (G : SimpleGraph V) (r : ℕ) :
    Module.finrank R (steinerInteractionSubmodule (R := R) G r) =
      Nat.card {sites : Finset V // SteinerEligible G r sites} := by
  classical
  let family :
      {sites : Finset V // SteinerEligible G r sites} → (Finset V → R) :=
    fun sites => booleanZetaFeature sites.1
  have hli : LinearIndependent R family := by
    exact (booleanZetaFeature_linearIndependent (V := V) (R := R)).comp
      (fun sites : {sites : Finset V // SteinerEligible G r sites} => sites.1)
      Subtype.val_injective
  have hrange :
      Set.range family =
        booleanZetaBasis (V := V) (R := R) ''
          {sites | SteinerEligible G r sites} := by
    ext f
    constructor
    · rintro ⟨sites, rfl⟩
      refine ⟨sites.1, sites.2, ?_⟩
      rw [booleanZetaBasis_apply]
    · rintro ⟨sites, hsites, rfl⟩
      refine ⟨(⟨sites, hsites⟩ :
        {sites : Finset V // SteinerEligible G r sites}), ?_⟩
      rw [booleanZetaBasis_apply]
  unfold steinerInteractionSubmodule
  rw [← hrange]
  simpa [Nat.card_eq_fintype_card] using finrank_span_eq_card hli

/-- Space spanned by all functions local on connected interaction clusters of depth at most `r`. -/
noncomputable def connectedClusterLocalSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (G : SimpleGraph V) (r : ℕ) : Submodule R (Finset V → R) := by
  classical
  exact Submodule.span R {f |
      ∃ H : G.Subgraph, H.Connected ∧ Nat.card H.coe.edgeSet ≤ r ∧
        f ∈ booleanLocalSubmodule H.verts.toFinset}

/-- **Exact connected-cluster/Steiner identity.** Spanning arbitrary functions local on connected
clusters of at most `r` edges produces exactly the interaction modes whose site packets admit such
a connected span. -/
theorem connectedClusterLocalSubmodule_eq_steinerInteractionSubmodule
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (G : SimpleGraph V) (r : ℕ) :
    connectedClusterLocalSubmodule (R := R) G r =
      steinerInteractionSubmodule G r := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.2
    intro f hf
    obtain ⟨H, hconnected, hdepth, hlocal⟩ := hf
    rw [← supportFilteredInteractionSubmodule_eq_booleanLocalSubmodule] at hlocal
    apply
      (show supportFilteredInteractionSubmodule (R := R) H.verts.toFinset ≤
          steinerInteractionSubmodule G r by
        apply Submodule.span_le.2
        rintro mode ⟨sites, hsites, rfl⟩
        apply Submodule.subset_span
        refine ⟨sites, ?_, rfl⟩
        exact ⟨H, hconnected, hdepth, by simpa using hsites⟩)
    exact hlocal
  · apply Submodule.span_le.2
    rintro mode ⟨sites, hsites, rfl⟩
    obtain ⟨H, hconnected, hdepth, hspan⟩ := hsites
    apply Submodule.subset_span
    refine ⟨H, hconnected, hdepth, ?_⟩
    rw [booleanZetaBasis_apply]
    exact booleanZetaFeature_mem_booleanLocalSubmodule (by simpa using hspan)

/-- Final exact form: connected-cluster locality and Möbius invisibility are annihilator-dual
descriptions of the same depth filtration. -/
theorem mem_connectedClusterLocalSubmodule_iff_mobius_invisible
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (G : SimpleGraph V) (r : ℕ) (f : Finset V → R) :
    f ∈ connectedClusterLocalSubmodule G r ↔
      ∀ sites, ¬ SteinerEligible G r sites →
        booleanMobiusProbe sites f = 0 := by
  rw [connectedClusterLocalSubmodule_eq_steinerInteractionSubmodule]
  exact mem_steinerInteractionSubmodule_iff G r f

end GaloisForLFunctions.HTGeometry
