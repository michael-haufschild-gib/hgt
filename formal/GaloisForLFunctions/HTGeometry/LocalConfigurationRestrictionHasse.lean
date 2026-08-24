import GaloisForLFunctions.HTGeometry.SteinerMobiusDuality

/-!
# Hasse gluing for finite local configuration functions

An anchored or Boolean function declared local on a finite support packet is completely determined by
its values on configurations carried by that packet.  Conversely, every arbitrary supported lookup
table extends uniquely by resetting or intersecting coordinates outside the packet.

Thus these restriction maps are exact linear equivalences, not merely injections.  The result gives
finite interaction, Möbius, and graphical-model constructions a canonical local-to-global gluing
interface without additional compatibility conditions.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Resetting a supported anchored configuration changes nothing. -/
theorem anchoredReset_eq_self_of_support_subset
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] {base : A}
    (support : Finset V) (index : AnchoredConfiguration V A base)
    (hindex : anchoredSupport index ⊆ support) :
    anchoredReset support index = index := by
  funext i
  by_cases hi : i ∈ support
  · simp [anchoredReset, hi]
  · have hzero : index i = ⊥ := by
      by_contra hne
      exact hi (hindex ((mem_anchoredSupport index i).2 hne))
    simp [anchoredReset, hi, hzero]

/-- Anchored reset is idempotent. -/
theorem anchoredReset_idempotent
    {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] {base : A}
    (support : Finset V) (index : AnchoredConfiguration V A base) :
    anchoredReset support (anchoredReset support index) = anchoredReset support index :=
  anchoredReset_eq_self_of_support_subset support _
    (anchoredSupport_anchoredReset_subset support index)

/-- Every table on supported anchored configurations extends to one local function. -/
theorem anchoredLocalRestriction_surjective
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    Function.Surjective
      (anchoredLocalRestriction (A := A) (base := base) (R := R) support) := by
  intro g
  let f : anchoredLocalSubmodule (A := A) (base := base) (R := R) support :=
    ⟨fun state ↦ g ⟨anchoredReset support state,
        anchoredSupport_anchoredReset_subset support state⟩, by
      intro state
      apply congrArg g
      apply Subtype.ext
      exact (anchoredReset_idempotent support state).symm⟩
  refine ⟨f, ?_⟩
  funext index
  change g ⟨anchoredReset support index.1,
      anchoredSupport_anchoredReset_subset support index.1⟩ = g index
  apply congrArg g
  apply Subtype.ext
  exact anchoredReset_eq_self_of_support_subset support index.1 index.2

/-- Anchored local functions are linearly equivalent to their supported tables. -/
noncomputable def anchoredLocalRestrictionHasseEquiv
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V) :
    anchoredLocalSubmodule (A := A) (base := base) (R := R) support ≃ₗ[R]
      ({index : AnchoredConfiguration V A base //
        anchoredSupport index ⊆ support} → R) :=
  LinearEquiv.ofBijective
    (anchoredLocalRestriction (A := A) (base := base) (R := R) support)
    ⟨anchoredLocalRestriction_injective support,
      anchoredLocalRestriction_surjective support⟩

/-- Every anchored local table has one unique global local-function realization. -/
theorem anchoredLocalRestriction_hasse_existsUnique
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (support : Finset V)
    (g : {index : AnchoredConfiguration V A base //
      anchoredSupport index ⊆ support} → R) :
    ∃! f : anchoredLocalSubmodule (A := A) (base := base) (R := R) support,
      anchoredLocalRestriction support f = g := by
  obtain ⟨f, hf⟩ := anchoredLocalRestriction_surjective support g
  refine ⟨f, hf, ?_⟩
  intro q hq
  exact anchoredLocalRestriction_injective support (hq.trans hf.symm)

/-- Every table on Boolean subconfigurations extends to one local Boolean function. -/
theorem booleanLocalRestriction_surjective
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) :
    Function.Surjective (booleanLocalRestriction (R := R) support) := by
  intro g
  let f : booleanLocalSubmodule (R := R) support :=
    ⟨fun active ↦ g ⟨active ∩ support, Finset.inter_subset_right⟩, by
      intro active
      apply congrArg g
      apply Subtype.ext
      simp⟩
  refine ⟨f, ?_⟩
  funext sites
  change g ⟨sites.1 ∩ support, Finset.inter_subset_right⟩ = g sites
  apply congrArg g
  apply Subtype.ext
  exact Finset.inter_eq_left.mpr sites.2

/-- Boolean local functions are linearly equivalent to their supported tables. -/
noncomputable def booleanLocalRestrictionHasseEquiv
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V) :
    booleanLocalSubmodule (R := R) support ≃ₗ[R]
      ({sites : Finset V // sites ⊆ support} → R) :=
  LinearEquiv.ofBijective (booleanLocalRestriction (R := R) support)
    ⟨booleanLocalRestriction_injective support,
      booleanLocalRestriction_surjective support⟩

/-- Every supported Boolean table has one unique global local-function realization. -/
theorem booleanLocalRestriction_hasse_existsUnique
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (support : Finset V)
    (g : {sites : Finset V // sites ⊆ support} → R) :
    ∃! f : booleanLocalSubmodule (R := R) support,
      booleanLocalRestriction support f = g := by
  obtain ⟨f, hf⟩ := booleanLocalRestriction_surjective support g
  refine ⟨f, hf, ?_⟩
  intro q hq
  exact booleanLocalRestriction_injective support (hq.trans hf.symm)

end GaloisForLFunctions.HTGeometry
