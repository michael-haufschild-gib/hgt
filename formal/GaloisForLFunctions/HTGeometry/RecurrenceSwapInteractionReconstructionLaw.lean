import GaloisForLFunctions.HTGeometry.LocalSpectralJetCausality
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.BooleanSubalgebra

/-!
# Recurrence-swap interaction reconstruction

A partial coordinate swap acts on two configurations. A mask is a universal
recurrence symmetry when the sum of their energies is invariant for every
pair. This file proves that the dynamical condition is exactly additive
separability across the corresponding coordinate cut and begins the Boolean
algebra of such cuts.
-/

open scoped BigOperators symmDiff

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- First output of swapping the coordinates in `mask` between `x` and `y`. -/
def dependentPartialSwapFirst
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (mask : Finset V) (x y : ∀ v, A v) : ∀ v, A v :=
  dependentUpdateOnFinset x y mask

/-- Second output of swapping the coordinates in `mask` between `x` and `y`. -/
def dependentPartialSwapSecond
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (mask : Finset V) (x y : ∀ v, A v) : ∀ v, A v :=
  dependentUpdateOnFinset y x mask

/-- A site mask preserves the two-history energy for every pair of
configurations. This is directly testable by a pair-resolved recurrence
kernel. -/
def IsUniversalRecurrenceSwap
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (mask : Finset V) : Prop :=
  ∀ x y,
    energy (dependentPartialSwapFirst mask x y) +
        energy (dependentPartialSwapSecond mask x y) =
      energy x + energy y

/-- Basepoint form of additive separation across one coordinate cut. -/
def IsAdditivelySeparableAcross
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (base : ∀ v, A v)
    (mask : Finset V) : Prop :=
  ∀ x,
    energy x + energy base =
      energy (dependentUpdateOnFinset base x mask) +
        energy (dependentUpdateOnFinset base x maskᶜ)

/-- Updating a basepoint by a previously updated configuration restricts
the active coordinates to the intersection. -/
theorem dependentUpdateOnFinset_compose
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (base x : ∀ v, A v) (s t : Finset V) :
    dependentUpdateOnFinset base
        (dependentUpdateOnFinset base x s) t =
      dependentUpdateOnFinset base x (s ∩ t) := by
  funext v
  by_cases hvs : v ∈ s <;>
    by_cases hvt : v ∈ t <;>
      simp [dependentUpdateOnFinset, hvs, hvt]

/-- Reversing the roles of the two configurations on a mask is the same as
updating the opposite mask. -/
theorem dependentUpdateOnFinset_swap_eq_compl
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (x y : ∀ v, A v) (mask : Finset V) :
    dependentUpdateOnFinset x y mask =
      dependentUpdateOnFinset y x maskᶜ := by
  funext v
  by_cases hv : v ∈ mask <;>
    simp [dependentUpdateOnFinset, hv]

/-- Restricting the first output of a partial swap back to the swapped mask
retains exactly the corresponding coordinates of the second input. -/
theorem dependentUpdateOnFinset_partialSwapFirst_self
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (base x y : ∀ v, A v) (mask : Finset V) :
    dependentUpdateOnFinset base
        (dependentPartialSwapFirst mask x y) mask =
      dependentUpdateOnFinset base y mask := by
  funext v
  by_cases hv : v ∈ mask <;>
    simp [dependentUpdateOnFinset, dependentPartialSwapFirst, hv]

/-- Restricting the first output of a partial swap to the complementary mask
retains exactly the corresponding coordinates of the first input. -/
theorem dependentUpdateOnFinset_partialSwapFirst_compl
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (base x y : ∀ v, A v) (mask : Finset V) :
    dependentUpdateOnFinset base
        (dependentPartialSwapFirst mask x y) maskᶜ =
      dependentUpdateOnFinset base x maskᶜ := by
  funext v
  by_cases hv : v ∈ mask <;>
    simp [dependentUpdateOnFinset, dependentPartialSwapFirst, hv]

/-- The analogous restriction law for the second partial-swap output. -/
theorem dependentUpdateOnFinset_partialSwapSecond_self
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (base x y : ∀ v, A v) (mask : Finset V) :
    dependentUpdateOnFinset base
        (dependentPartialSwapSecond mask x y) mask =
      dependentUpdateOnFinset base x mask := by
  funext v
  by_cases hv : v ∈ mask <;>
    simp [dependentUpdateOnFinset, dependentPartialSwapSecond, hv]

/-- Complementary restriction law for the second partial-swap output. -/
theorem dependentUpdateOnFinset_partialSwapSecond_compl
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (base x y : ∀ v, A v) (mask : Finset V) :
    dependentUpdateOnFinset base
        (dependentPartialSwapSecond mask x y) maskᶜ =
      dependentUpdateOnFinset base y maskᶜ := by
  funext v
  by_cases hv : v ∈ mask <;>
    simp [dependentUpdateOnFinset, dependentPartialSwapSecond, hv]

/-- **Swap/separability equivalence.** Universal preservation of the
two-history energy by a partial swap is exactly additive separability across
that cut. The basepoint is arbitrary. -/
theorem universalRecurrenceSwap_iff_additivelySeparableAcross
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (base : ∀ v, A v)
    (mask : Finset V) :
    IsUniversalRecurrenceSwap energy mask ↔
      IsAdditivelySeparableAcross energy base mask := by
  constructor
  · intro hswap x
    have h := hswap base x
    change
      energy (dependentUpdateOnFinset base x mask) +
          energy (dependentUpdateOnFinset x base mask) =
        energy base + energy x at h
    rw [dependentUpdateOnFinset_swap_eq_compl x base mask] at h
    change
      energy x + energy base =
        energy (dependentUpdateOnFinset base x mask) +
          energy (dependentUpdateOnFinset base x maskᶜ)
    linarith
  · intro hsep x y
    have hx := hsep x
    have hy := hsep y
    have hz :=
      hsep (dependentPartialSwapFirst mask x y)
    have hw :=
      hsep (dependentPartialSwapSecond mask x y)
    rw [dependentUpdateOnFinset_partialSwapFirst_self,
      dependentUpdateOnFinset_partialSwapFirst_compl] at hz
    rw [dependentUpdateOnFinset_partialSwapSecond_self,
      dependentUpdateOnFinset_partialSwapSecond_compl] at hw
    linarith

/-- Updating no coordinates leaves the base configuration unchanged. -/
theorem dependentUpdateOnFinset_empty
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (x y : ∀ v, A v) :
    dependentUpdateOnFinset x y ∅ = x := by
  funext v
  simp [dependentUpdateOnFinset]

/-- Updating every coordinate returns the alternative configuration. -/
theorem dependentUpdateOnFinset_univ
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (x y : ∀ v, A v) :
    dependentUpdateOnFinset x y Finset.univ = y := by
  funext v
  simp [dependentUpdateOnFinset]

/-- The empty mask is always a universal recurrence symmetry. -/
theorem isUniversalRecurrenceSwap_empty
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) :
    IsUniversalRecurrenceSwap energy ∅ := by
  intro x y
  change
    energy (dependentUpdateOnFinset x y ∅) +
        energy (dependentUpdateOnFinset y x ∅) =
      energy x + energy y
  rw [dependentUpdateOnFinset_empty, dependentUpdateOnFinset_empty]

/-- The full mask is always a universal recurrence symmetry. -/
theorem isUniversalRecurrenceSwap_univ
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) :
    IsUniversalRecurrenceSwap energy Finset.univ := by
  intro x y
  change
    energy (dependentUpdateOnFinset x y Finset.univ) +
        energy (dependentUpdateOnFinset y x Finset.univ) =
      energy x + energy y
  rw [dependentUpdateOnFinset_univ, dependentUpdateOnFinset_univ,
    add_comm]

/-- Universal recurrence symmetry is invariant under complementary masks. -/
theorem isUniversalRecurrenceSwap_compl_iff
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (mask : Finset V) :
    IsUniversalRecurrenceSwap energy maskᶜ ↔
      IsUniversalRecurrenceSwap energy mask := by
  constructor <;> intro h x y
  · have hxy := h x y
    change
      energy (dependentUpdateOnFinset x y maskᶜ) +
          energy (dependentUpdateOnFinset y x maskᶜ) =
        energy x + energy y at hxy
    rw [← dependentUpdateOnFinset_swap_eq_compl y x mask,
      ← dependentUpdateOnFinset_swap_eq_compl x y mask] at hxy
    simpa [IsUniversalRecurrenceSwap, dependentPartialSwapFirst,
      dependentPartialSwapSecond, add_comm] using hxy
  · have hxy := h x y
    change
      energy (dependentUpdateOnFinset x y mask) +
          energy (dependentUpdateOnFinset y x mask) =
        energy x + energy y at hxy
    rw [dependentUpdateOnFinset_swap_eq_compl y x mask,
      dependentUpdateOnFinset_swap_eq_compl x y mask] at hxy
    simpa [IsUniversalRecurrenceSwap, dependentPartialSwapFirst,
      dependentPartialSwapSecond, add_comm] using hxy

/-- Intersecting two additively separable cuts remains additively
separable. This is the nontrivial closure operation behind the recurrence
Boolean algebra. -/
theorem isAdditivelySeparableAcross_inter
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (base : ∀ v, A v)
    {s t : Finset V}
    (hs : IsAdditivelySeparableAcross energy base s)
    (ht : IsAdditivelySeparableAcross energy base t) :
    IsAdditivelySeparableAcross energy base (s ∩ t) := by
  intro x
  have hsx := hs x
  have hst_left := ht (dependentUpdateOnFinset base x s)
  have houtside :=
    hs (dependentUpdateOnFinset base x (s ∩ t)ᶜ)
  simp only [dependentUpdateOnFinset_compose] at hst_left houtside
  have h2 :
      s ∩ tᶜ = s \ t := by
    ext v
    simp
  have h5 :
      (s ∩ t)ᶜ ∩ s = s \ t := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  have h6 :
      (s ∩ t)ᶜ ∩ sᶜ = sᶜ := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_compl]
    tauto
  rw [h2] at hst_left
  rw [h5, h6] at houtside
  linarith

/-- Universal recurrence masks are closed under intersection. -/
theorem isUniversalRecurrenceSwap_inter
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ)
    {s t : Finset V}
    (hs : IsUniversalRecurrenceSwap energy s)
    (ht : IsUniversalRecurrenceSwap energy t) :
    IsUniversalRecurrenceSwap energy (s ∩ t) := by
  classical
  let base : ∀ v, A v := fun v => Classical.choice inferInstance
  rw [universalRecurrenceSwap_iff_additivelySeparableAcross
      energy base] at hs ht ⊢
  exact isAdditivelySeparableAcross_inter energy base hs ht

/-- Universal recurrence masks are closed under union. -/
theorem isUniversalRecurrenceSwap_union
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ)
    {s t : Finset V}
    (hs : IsUniversalRecurrenceSwap energy s)
    (ht : IsUniversalRecurrenceSwap energy t) :
    IsUniversalRecurrenceSwap energy (s ∪ t) := by
  have hcomplInter :
      IsUniversalRecurrenceSwap energy (sᶜ ∩ tᶜ) :=
    isUniversalRecurrenceSwap_inter energy
      ((isUniversalRecurrenceSwap_compl_iff energy s).2 hs)
      ((isUniversalRecurrenceSwap_compl_iff energy t).2 ht)
  have hcompl :
      IsUniversalRecurrenceSwap energy (sᶜ ∩ tᶜ)ᶜ :=
    (isUniversalRecurrenceSwap_compl_iff energy (sᶜ ∩ tᶜ)).2
      hcomplInter
  convert hcompl using 1
  ext v
  simp

/-- All universally energy-preserving partial-swap masks, equipped with
union, intersection, and complement. -/
def recurrenceSwapBooleanSubalgebra
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ) :
    BooleanSubalgebra (Finset V) where
  carrier := {mask | IsUniversalRecurrenceSwap energy mask}
  supClosed' := fun _ hs _ ht =>
    isUniversalRecurrenceSwap_union energy hs ht
  infClosed' := fun _ hs _ ht =>
    isUniversalRecurrenceSwap_inter energy hs ht
  compl_mem' := fun hs =>
    (isUniversalRecurrenceSwap_compl_iff energy _).2 hs
  bot_mem' := isUniversalRecurrenceSwap_empty energy

@[simp]
theorem mem_recurrenceSwapBooleanSubalgebra_iff
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ) (mask : Finset V) :
    mask ∈ recurrenceSwapBooleanSubalgebra energy ↔
      IsUniversalRecurrenceSwap energy mask :=
  Iff.rfl

/-- The atoms of the recurrence-swap algebra completely determine every
universal recurrence mask. Thus no information about the algebra is lost by
passing from all valid masks to its minimal nonempty masks. -/
theorem recurrenceSwapMask_eq_iff_same_atoms
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ)
    (s t : recurrenceSwapBooleanSubalgebra energy) :
    s = t ↔
      ∀ a : recurrenceSwapBooleanSubalgebra energy,
        IsAtom a → (a ≤ s ↔ a ≤ t) :=
  BooleanAlgebra.eq_iff_atom_le_iff

/-- Every nonempty universal recurrence mask contains a minimal nonempty
universal recurrence mask. These atoms are the irreducible additive
interaction blocks relative to the supplied coordinates. -/
theorem exists_recurrenceSwapAtom_le
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ)
    (mask : recurrenceSwapBooleanSubalgebra energy)
    (hmask : mask ≠ ⊥) :
    ∃ a : recurrenceSwapBooleanSubalgebra energy,
      IsAtom a ∧ a ≤ mask :=
  (eq_bot_or_exists_atom_le mask).resolve_left hmask

/-- Distinct irreducible recurrence blocks are disjoint. -/
theorem recurrenceSwapAtoms_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ)
    {a b : recurrenceSwapBooleanSubalgebra energy}
    (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Disjoint a b :=
  ha.disjoint_of_ne hb hab

/-- Every declared site lies in an irreducible recurrence block. Together
with pairwise disjointness, the atoms therefore partition the supplied site
set. -/
theorem exists_recurrenceSwapAtom_mem
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ) (v : V) :
    ∃ a : recurrenceSwapBooleanSubalgebra energy,
      IsAtom a ∧ v ∈ (a : Finset V) := by
  classical
  let atoms : Finset (recurrenceSwapBooleanSubalgebra energy) :=
    Finset.univ.filter IsAtom
  let atomUnion : recurrenceSwapBooleanSubalgebra energy :=
    atoms.sup id
  have hatomUnion :
      atomUnion = ⊤ := by
    apply BooleanAlgebra.eq_iff_atom_le_iff.2
    intro a ha
    constructor
    · exact fun _ => le_top
    · intro _
      exact Finset.le_sup (s := atoms) (f := id) (by simp [atoms, ha])
  have hv : v ∈ (atomUnion : Finset V) := by
    rw [hatomUnion]
    simp
  have hcoe :
      (atomUnion : Finset V) =
        atoms.sup (fun a => (a : Finset V)) := by
    dsimp [atomUnion]
    change
      (BooleanSubalgebra.subtype
        (recurrenceSwapBooleanSubalgebra energy)) (atoms.sup id) =
          atoms.sup (fun a => (a : Finset V))
    rw [map_finset_sup]
    rfl
  rw [hcoe] at hv
  rw [Finset.mem_sup] at hv
  obtain ⟨a, ha, hva⟩ := hv
  exact ⟨a, by simpa [atoms] using ha, hva⟩

/-- Each declared site belongs to exactly one irreducible recurrence block.
This is the canonical block assignment reconstructed by the recurrence-swap
algebra. -/
theorem existsUnique_recurrenceSwapAtom_mem
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    [∀ v, Nonempty (A v)]
    (energy : (∀ v, A v) → ℝ) (v : V) :
    ∃! a : recurrenceSwapBooleanSubalgebra energy,
      IsAtom a ∧ v ∈ (a : Finset V) := by
  obtain ⟨a, ha, hva⟩ :=
    exists_recurrenceSwapAtom_mem energy v
  refine ⟨a, ⟨ha, hva⟩, ?_⟩
  intro b hb
  by_contra hab
  have hdisjoint : Disjoint a b :=
    recurrenceSwapAtoms_disjoint energy ha hb.1 (Ne.symm hab)
  have hinter : v ∈ ((a ⊓ b : recurrenceSwapBooleanSubalgebra energy) :
      Finset V) := by
    simpa using And.intro hva hb.2
  have hbot : a ⊓ b = ⊥ := disjoint_iff.mp hdisjoint
  rw [hbot] at hinter
  simp at hinter

/-- Energy mismatch detected by a pair-resolved partial-swap recurrence
experiment. -/
def recurrenceSwapDetuning
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (mask : Finset V)
    (x y : ∀ v, A v) : ℝ :=
  energy (dependentPartialSwapFirst mask x y) +
      energy (dependentPartialSwapSecond mask x y) -
    (energy x + energy y)

/-- Infinite symmetric-time averaging of a pair-resolved recurrence kernel
returns one exactly when the chosen pair is invariant under the partial
swap, and zero otherwise. -/
theorem recurrenceSwapPhaseAverage_tendsto_indicator
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (mask : Finset V)
    (x y : ∀ v, A v) :
    Filter.Tendsto
      (fun T => symmetricPhaseAverage T
        (recurrenceSwapDetuning energy mask x y))
      Filter.atTop
      (nhds
        (if recurrenceSwapDetuning energy mask x y = 0
          then (1 : ℂ) else 0)) :=
  symmetricPhaseAverage_tendsto_resonanceIndicator
    (recurrenceSwapDetuning energy mask x y)

/-- **Operational inverse law.** A mask is an additive interaction cut
exactly when every pair-resolved partial-swap recurrence kernel converges to
one. Combined with the Boolean atom theorem, these limits reconstruct the
unique irreducible recurrence blocks relative to the supplied coordinates. -/
theorem isUniversalRecurrenceSwap_iff_all_phaseAverages_tendsto_one
    {V : Type*} [Fintype V] [DecidableEq V] {A : V → Type*}
    (energy : (∀ v, A v) → ℝ) (mask : Finset V) :
    IsUniversalRecurrenceSwap energy mask ↔
      ∀ x y,
        Filter.Tendsto
          (fun T => symmetricPhaseAverage T
            (recurrenceSwapDetuning energy mask x y))
          Filter.atTop (nhds (1 : ℂ)) := by
  constructor
  · intro h x y
    have hzero :
        recurrenceSwapDetuning energy mask x y = 0 := by
      dsimp [recurrenceSwapDetuning]
      rw [h x y]
      ring
    simpa only [hzero, if_pos] using
      recurrenceSwapPhaseAverage_tendsto_indicator energy mask x y
  · intro h x y
    have hindicator :=
      recurrenceSwapPhaseAverage_tendsto_indicator energy mask x y
    have hlimit :
        (if recurrenceSwapDetuning energy mask x y = 0
          then (1 : ℂ) else 0) = 1 :=
      tendsto_nhds_unique hindicator (h x y)
    have hzero :
        recurrenceSwapDetuning energy mask x y = 0 := by
      by_contra hne
      simp only [hne, if_false] at hlimit
      exact zero_ne_one hlimit
    exact sub_eq_zero.mp hzero

end

end GaloisForLFunctions.HTGeometry
