import GaloisForLFunctions.RHTower.XiPeripheralTargetCharts
import GaloisForLFunctions.HTGeometry.SubgroupCoverTopology
import GaloisForLFunctions.HTGeometry.PeripheralCoverComponent

/-!
# Peripheral components of the actual marked image cover

Connected components above the two explicit target charts form a countable
family of disjoint open regions. Retain precisely the components admitting an
exact positive power model, and choose one such model per retained component.
The remaining components have exponential models.
-/

open Topology Set Function
open scoped UpperHalfPlane

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

noncomputable section

abbrev MarkedImageCover (H : Subgroup (coveringDeckGroup markedUniversalCover)) :=
  SubgroupCover (E := ℍ) H

variable (H : Subgroup (coveringDeckGroup markedUniversalCover))

def markedImageProjection : MarkedImageCover H → Target :=
  subgroupCoverProjection markedUniversalCover_quotient H

theorem isCoveringMap_markedImageProjection : IsCoveringMap (markedImageProjection H) :=
  isCoveringMap_subgroupCoverProjection markedUniversalCover_quotient H

instance markedImageCoverT2Space : T2Space (MarkedImageCover H) :=
  t2Space_subgroupCover markedUniversalCover_quotient H

instance markedImageCoverSecondCountable : SecondCountableTopology (MarkedImageCover H) :=
  secondCountableTopology_subgroupCover markedUniversalCover_quotient H

def peripheralPreimage (b : Bool) : Set (MarkedImageCover H) :=
  markedImageProjection H ⁻¹' peripheralTarget b

theorem isOpen_peripheralPreimage (b : Bool) : IsOpen (peripheralPreimage H b) :=
  (isOpen_peripheralTarget b).preimage (isCoveringMap_markedImageProjection H).continuous

instance peripheralPreimageLocallyPathConnected (b : Bool) :
    LocallyPathConnectedSpace (peripheralPreimage H b) :=
  (isOpen_peripheralPreimage H b).locallyPathConnectedSpace

instance peripheralComponentsCountable (b : Bool) :
    Countable (ConnectedComponents (peripheralPreimage H b)) :=
  countable_connectedComponents_open (isOpen_peripheralPreimage H b)

abbrev PeripheralIndex := Σ b : Bool, ConnectedComponents (peripheralPreimage H b)

/-- A representative is chosen only to name the connected component, not to assume its model. -/
def peripheralRepresentative (j : PeripheralIndex H) : peripheralPreimage H j.1 :=
  (ConnectedComponents.surjective_coe j.2).choose

theorem peripheralRepresentative_component (j : PeripheralIndex H) :
    ConnectedComponents.mk (peripheralRepresentative H j) = j.2 :=
  (ConnectedComponents.surjective_coe j.2).choose_spec

abbrev PeripheralComponent (j : PeripheralIndex H) :=
  connectedComponent (peripheralRepresentative H j)

def peripheralRegion (j : PeripheralIndex H) : Set (MarkedImageCover H) :=
  Subtype.val '' connectedComponent (peripheralRepresentative H j)

theorem isOpen_peripheralRegion (j : PeripheralIndex H) : IsOpen (peripheralRegion H j) :=
  (isOpen_peripheralPreimage H j.1).isOpenMap_subtype_val _ isOpen_connectedComponent

/-- The component subtype and its region in the old cover have identical topology. -/
def peripheralComponentToRegion (j : PeripheralIndex H) :
    PeripheralComponent H j ≃ₜ peripheralRegion H j :=
  IsEmbedding.subtypeVal.homeomorphImage (connectedComponent (peripheralRepresentative H j))

@[simp] theorem peripheralComponentToRegion_val (j : PeripheralIndex H) (x : PeripheralComponent H j) :
    (peripheralComponentToRegion H j x).val = x.val.val := rfl

def peripheralComponentProjection (j : PeripheralIndex H) : PeripheralComponent H j → PuncturedUnitDisk :=
  fun x => peripheralTargetChart j.1 ⟨markedImageProjection H x.val.val, x.val.property⟩

theorem peripheralRegion_subset_preimage (j : PeripheralIndex H) :
    peripheralRegion H j ⊆ peripheralPreimage H j.1 := by
  rintro y ⟨x, _, rfl⟩
  exact x.property

/-- Distinct peripheral indices give disjoint open regions in the actual cover. -/
theorem disjoint_peripheralRegion : Pairwise (Disjoint on peripheralRegion H) := by
  intro i j hij
  by_cases hb : i.1 = j.1
  · obtain ⟨b, i⟩ := i
    obtain ⟨b', j⟩ := j
    dsimp at hb
    subst b'
    have hcc : connectedComponent (peripheralRepresentative H ⟨b, i⟩) ≠
        connectedComponent (peripheralRepresentative H ⟨b, j⟩) := by
      intro h
      have he := ConnectedComponents.coe_eq_coe.mpr h
      rw [peripheralRepresentative_component, peripheralRepresentative_component] at he
      exact hij (congrArg (Sigma.mk b) he)
    exact disjoint_image_of_injective Subtype.val_injective (connectedComponent_disjoint hcc)
  · apply Disjoint.mono (peripheralRegion_subset_preimage H i) (peripheralRegion_subset_preimage H j)
    exact (disjoint_peripheralTarget hb).preimage (markedImageProjection H)

/-- Data for a finite peripheral chart, including its exact projection formula. -/
structure PeripheralPowerChart (j : PeripheralIndex H) where
  degree : ℕ
  positive : 0 < degree
  homeomorph : PeripheralComponent H j ≃ₜ PuncturedUnitDisk
  projection : ∀ x, peripheralComponentProjection H j x =
    puncturedDiskPower degree positive (homeomorph x)

/-- Precisely the components which can be filled by a finite ramification point. -/
abbrev FinitePeripheralIndex := {j : PeripheralIndex H // Nonempty (PeripheralPowerChart H j)}

def chosenPeripheralPowerChart (i : FinitePeripheralIndex H) : PeripheralPowerChart H i.val :=
  Classical.choice i.property

/-- Every unfilled peripheral component is an exponential end. -/
theorem peripheralComponent_dichotomy (j : PeripheralIndex H) :
    (∃ D : PeripheralComponent H j ≃ₜ LogHalfPlane,
      ∀ x, peripheralComponentProjection H j x = puncturedDiskExp (D x)) ∨
      Nonempty (PeripheralPowerChart H j) := by
  rcases open_cover_component_classification (isCoveringMap_markedImageProjection H)
    (isOpen_peripheralTarget j.1) (peripheralTargetChart j.1) (peripheralRepresentative H j) with
    ⟨D, hD⟩ | ⟨n, hn, D, hD⟩
  · exact Or.inl ⟨D, hD⟩
  · exact Or.inr ⟨⟨n, hn, D, hD⟩⟩

/-- The selected power chart recovers the original complex projection. -/
theorem chosenPeripheralPowerChart_projection (i : FinitePeripheralIndex H)
    (x : PeripheralComponent H i.val) :
    (markedImageProjection H x.val.val : ℂ) = peripheralCenter i.val.1 +
      ((chosenPeripheralPowerChart H i).homeomorph x : ℂ) ^
        (chosenPeripheralPowerChart H i).degree / 4 := by
  have h := congrArg Subtype.val ((chosenPeripheralPowerChart H i).projection x)
  have hp := peripheralTargetChart_projection i.val.1
    ⟨markedImageProjection H x.val.val, x.val.property⟩
  change (peripheralComponentProjection H i.val x : ℂ) =
    ((chosenPeripheralPowerChart H i).homeomorph x : ℂ) ^
      (chosenPeripheralPowerChart H i).degree at h
  rw [← h]
  exact hp

end
end RHTower.XiMarkedMonodromy
