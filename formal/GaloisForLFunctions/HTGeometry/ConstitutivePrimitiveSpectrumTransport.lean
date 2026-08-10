import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalPrimitiveDegreeEscape
import Mathlib

/-!
# Primitive-spectrum transport

Local admission, dominated splitting, primitivity, and primitive-degree occurrence are invariant
under arbitrary relabelings of a failure system.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Transport a failure kernel through an equivalence of resource coordinates. -/
def transportFailureKernel {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (K : Finset α) : Finset β :=
  K.map e.toEmbedding

/-- Transport every failure kernel through an equivalence. -/
def transportFailureFamily {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) : Finset (Finset β) :=
  H.image (transportFailureKernel e)

/-- Transport a repair weight contravariantly along the inverse coordinate equivalence. -/
def transportRepairWeight {α : Type u} {β : Type v}
    (e : α ≃ β) (a : α → ℕ) : β → ℕ :=
  fun j => a (e.symm j)

/-- A transported kernel belongs to the transported family. -/
theorem transportFailureKernel_mem {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (K : Finset α) (hK : K ∈ H) :
    transportFailureKernel e K ∈ transportFailureFamily e H := by
  exact Finset.mem_image.mpr ⟨K, hK, rfl⟩

/-- Transported weights recover the original value at transported coordinates. -/
theorem transportRepairWeight_apply {α : Type u} {β : Type v}
    (e : α ≃ β) (a : α → ℕ) (i : α) :
    transportRepairWeight e a (e i) = a i := by
  simp [transportRepairWeight]

/-- Local admission transports forward through every coordinate equivalence. -/
theorem weightedLocalRepair_transport_forward {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (h : WeightedLocalRepair H m a) :
    WeightedLocalRepair (transportFailureFamily e H) m (transportRepairWeight e a) := by
  intro L hL
  rw [transportFailureFamily] at hL
  obtain ⟨K, hKH, rfl⟩ := Finset.mem_image.mp hL
  simpa [transportFailureKernel, transportRepairWeight] using h K hKH

/-- Local admission pulls back from every transported failure family. -/
theorem weightedLocalRepair_transport_backward {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) (b : β → ℕ)
    (h : WeightedLocalRepair (transportFailureFamily e H) m b) :
    WeightedLocalRepair H m (fun i => b (e i)) := by
  intro K hKH
  have h' := h (transportFailureKernel e K) (transportFailureKernel_mem e H K hKH)
  simpa [transportFailureKernel] using h'

/-- Local admission is exactly invariant under relabeling. -/
theorem weightedLocalRepair_transport_iff {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ) :
    WeightedLocalRepair H m a ↔
      WeightedLocalRepair (transportFailureFamily e H) m (transportRepairWeight e a) := by
  constructor
  · exact weightedLocalRepair_transport_forward e H m a
  · intro h
    have hb := weightedLocalRepair_transport_backward e H m (transportRepairWeight e a) h
    simpa [transportRepairWeight] using hb

/-- Dominated positive splitting transports forward through coordinate equivalences. -/
theorem weightedDominatedSplit_transport_forward {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (h : WeightedDominatedSplit H m a) :
    WeightedDominatedSplit (transportFailureFamily e H) m (transportRepairWeight e a) := by
  rcases h with ⟨m₁, m₂, a₁, a₂, hm₁, hm₂, hgrade, hlocal₁, hlocal₂, hdom⟩
  exact ⟨m₁, m₂, transportRepairWeight e a₁, transportRepairWeight e a₂,
    hm₁, hm₂, hgrade,
    weightedLocalRepair_transport_forward e H m₁ a₁ hlocal₁,
    weightedLocalRepair_transport_forward e H m₂ a₂ hlocal₂,
    fun j => hdom (e.symm j)⟩

/-- Dominated positive splitting pulls back from transported failure families. -/
theorem weightedDominatedSplit_transport_backward {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (h : WeightedDominatedSplit (transportFailureFamily e H) m (transportRepairWeight e a)) :
    WeightedDominatedSplit H m a := by
  rcases h with ⟨m₁, m₂, b₁, b₂, hm₁, hm₂, hgrade, hlocal₁, hlocal₂, hdom⟩
  refine ⟨m₁, m₂, (fun i => b₁ (e i)), (fun i => b₂ (e i)),
    hm₁, hm₂, hgrade, ?_, ?_, ?_⟩
  · exact weightedLocalRepair_transport_backward e H m₁ b₁ hlocal₁
  · exact weightedLocalRepair_transport_backward e H m₂ b₂ hlocal₂
  · intro i
    simpa [transportRepairWeight] using hdom (e i)

/-- Dominated positive splitting is exactly invariant under relabeling. -/
theorem weightedDominatedSplit_transport_iff {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ) :
    WeightedDominatedSplit H m a ↔
      WeightedDominatedSplit (transportFailureFamily e H) m (transportRepairWeight e a) := by
  exact ⟨weightedDominatedSplit_transport_forward e H m a,
    weightedDominatedSplit_transport_backward e H m a⟩

/-- Primitive laws are exactly invariant under resource relabeling. -/
theorem weightedPrimitiveRepair_transport_iff {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ) :
    WeightedPrimitiveRepair H m a ↔
      WeightedPrimitiveRepair (transportFailureFamily e H) m (transportRepairWeight e a) := by
  simp only [WeightedPrimitiveRepair, weightedLocalRepair_transport_iff e H m a,
    weightedDominatedSplit_transport_iff e H m a]

/-- A primitive degree occurs when some weight is primitive at that grade. -/
def PrimitiveDegreeOccurs {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (m : ℕ) : Prop :=
  ∃ a : α → ℕ, WeightedPrimitiveRepair H m a

/-- The set of occurring primitive degrees is exactly invariant under relabeling. -/
theorem primitiveDegreeOccurs_transport_iff {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (H : Finset (Finset α)) (m : ℕ) :
    PrimitiveDegreeOccurs H m ↔ PrimitiveDegreeOccurs (transportFailureFamily e H) m := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨transportRepairWeight e a,
      (weightedPrimitiveRepair_transport_iff e H m a).mp ha⟩
  · rintro ⟨b, hb⟩
    let a : α → ℕ := fun i => b (e i)
    have htrans : transportRepairWeight e a = b := by
      funext j
      simp [a, transportRepairWeight]
    have hb' : WeightedPrimitiveRepair (transportFailureFamily e H) m
        (transportRepairWeight e a) := by
      simpa [htrans] using hb
    exact ⟨a, (weightedPrimitiveRepair_transport_iff e H m a).mpr hb'⟩

/-- Closed capstone: primitive-degree occurrence is a relabeling invariant. -/
theorem primitiveSpectrumRelabelingMechanism_closed :
    ∀ (α : Type u) (β : Type v) (_ : DecidableEq α) (_ : DecidableEq β)
      (e : α ≃ β) (H : Finset (Finset α)) (m : ℕ),
      PrimitiveDegreeOccurs H m ↔ PrimitiveDegreeOccurs (transportFailureFamily e H) m := by
  intro α β instα instβ e H m
  letI : DecidableEq α := instα
  letI : DecidableEq β := instβ
  exact primitiveDegreeOccurs_transport_iff e H m

end GaloisForLFunctions.HTGeometry
