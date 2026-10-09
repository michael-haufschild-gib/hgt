import GaloisForLFunctions.RHTower.XiPeripheralComponents
import GaloisForLFunctions.HTGeometry.PuncturedDiskCapModel
import GaloisForLFunctions.HTGeometry.DisjointPointCapsFundamentalGroup

/-!
# The actual marked image cover with its finite peripheral caps

Assemble cap data from the actual component index and selected power charts.
The completed space is Hausdorff, second countable and path connected. Its
projection has exact polynomial cap formulas, adds fibers only over the marks,
and remains a covering away from them. The old body is onto on fundamental groups.

The global extended Xi lift and simple connectedness are separate obligations.
-/

open Topology Set Function
open scoped UpperHalfPlane
open DifferentialGeometry.Topology.VanKampen

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

noncomputable section

variable (H : Subgroup (coveringDeckGroup markedUniversalCover))

/-- Actual cap data for all finite peripheral components of the marked image cover. -/
def finitePeripheralCapData : PointCapData (MarkedImageCover H) UnitCapDisk (FinitePeripheralIndex H) where
  center := unitCapCenter
  region i := peripheralRegion H i.val
  isOpen_region i := isOpen_peripheralRegion H i.val
  disjoint_region _i _j hij := disjoint_peripheralRegion H (fun h => hij (Subtype.ext h))
  chart i := puncturedCapHomeomorph.trans
    ((chosenPeripheralPowerChart H i).homeomorph.symm.trans (peripheralComponentToRegion H i.val))

instance finitePeripheralCapPuncturedPathConnected :
    PathConnectedSpace {z : UnitCapDisk // z ≠ (finitePeripheralCapData H).center} := by
  change PathConnectedSpace {z : UnitCapDisk // z ≠ unitCapCenter}
  infer_instance

abbrev CappedMarkedCover := (finitePeripheralCapData H).Space

/-- Extend the actual projection by its marked value at every attached center. -/
def cappedMarkedProjection : CappedMarkedCover H → ℂ :=
  (finitePeripheralCapData H).extend (fun y => (markedImageProjection H y : ℂ))
    (fun i => peripheralCenter i.val.1)

@[simp] theorem cappedMarkedProjection_old (y : MarkedImageCover H) :
    cappedMarkedProjection H ((finitePeripheralCapData H).old y) = (markedImageProjection H y : ℂ) := rfl

/-- The completed projection has the exact polynomial formula in each full cap. -/
theorem cappedMarkedProjection_cap (i : FinitePeripheralIndex H) (z : UnitCapDisk) :
    cappedMarkedProjection H ((finitePeripheralCapData H).cap i z) =
      peripheralCenter i.val.1 + z.val ^ (chosenPeripheralPowerChart H i).degree / 4 := by
  by_cases hz : z = unitCapCenter
  · subst z
    have he := (finitePeripheralCapData H).cap_center i
    change (finitePeripheralCapData H).cap i unitCapCenter = (finitePeripheralCapData H).point i at he
    rw [he]
    change peripheralCenter i.val.1 =
      peripheralCenter i.val.1 + (0 : ℂ) ^ (chosenPeripheralPowerChart H i).degree / 4
    simp [(chosenPeripheralPowerChart H i).positive.ne']
  · rw [(finitePeripheralCapData H).cap_ne_center i hz]
    change (markedImageProjection H
      (peripheralComponentToRegion H i.val
        ((chosenPeripheralPowerChart H i).homeomorph.symm
          (puncturedCapHomeomorph ⟨z, hz⟩))).val : ℂ) = _
    rw [peripheralComponentToRegion_val, chosenPeripheralPowerChart_projection]
    simp only [Homeomorph.apply_symm_apply, puncturedCapHomeomorph_val]

theorem continuous_cappedMarkedProjection_cap (i : FinitePeripheralIndex H) :
    Continuous (cappedMarkedProjection H ∘ (finitePeripheralCapData H).cap i) := by
  have hc : Continuous (fun z : UnitCapDisk =>
      peripheralCenter i.val.1 + z.val ^ (chosenPeripheralPowerChart H i).degree / 4) := by fun_prop
  exact hc.congr fun z => (cappedMarkedProjection_cap H i z).symm

theorem continuous_cappedMarkedProjection : Continuous (cappedMarkedProjection H) :=
  (finitePeripheralCapData H).continuous_extend _ _
    (continuous_subtype_val.comp (isCoveringMap_markedImageProjection H).continuous)
    (continuous_cappedMarkedProjection_cap H)

instance cappedMarkedCoverT2Space : T2Space (CappedMarkedCover H) :=
  (finitePeripheralCapData H).t2Space_of_projection _ _
    (continuous_subtype_val.comp (isCoveringMap_markedImageProjection H).continuous)
    (continuous_cappedMarkedProjection_cap H)
    (fun y i => target_ne_peripheralCenter i.val.1 (markedImageProjection H y))

instance cappedMarkedCoverSecondCountable : SecondCountableTopology (CappedMarkedCover H) :=
  (finitePeripheralCapData H).secondCountableTopology

instance cappedMarkedCoverPathConnected : PathConnectedSpace (CappedMarkedCover H) :=
  (finitePeripheralCapData H).pathConnectedSpace

/-- The actual completed cover has no loops outside the image of its old body. -/
theorem cappedMarkedCover_body_fundamentalGroup_surjective
    (a : range (finitePeripheralCapData H).old) :
    Surjective (FundamentalGroup.map (subsetToAmbient (range (finitePeripheralCapData H).old)) a) :=
  (finitePeripheralCapData H).fundamentalGroup_body_surjective a

/-- The only added fibers are over the marked target values. -/
theorem cappedMarkedProjection_unmarked_iff (x : CappedMarkedCover H) :
    (cappedMarkedProjection H x ≠ 0 ∧ cappedMarkedProjection H x ≠ -1) ↔
      x ∈ range (finitePeripheralCapData H).old := by
  cases x with
  | inl y =>
    exact ⟨fun _ => ⟨y, rfl⟩, fun _ => (markedImageProjection H y).property⟩
  | inr i =>
    have hx : (PointCapData.point (finitePeripheralCapData H) i) ∉
        range (finitePeripheralCapData H).old := by
      rintro ⟨y, hy⟩
      change (Sum.inl y : MarkedImageCover H ⊕ FinitePeripheralIndex H) = Sum.inr i at hy
      cases hy
    change (peripheralCenter i.val.1 ≠ 0 ∧ peripheralCenter i.val.1 ≠ -1) ↔
      (finitePeripheralCapData H).point i ∈ range (finitePeripheralCapData H).old
    constructor
    · intro h
      cases i.val.1 <;> simp [peripheralCenter] at h
    · intro h
      exact (hx h).elim

/-- The old cover is precisely the unmarked part of the completed space. -/
def cappedMarkedUnmarkedHomeomorph : MarkedImageCover H ≃ₜ
    {x : CappedMarkedCover H // cappedMarkedProjection H x ≠ 0 ∧ cappedMarkedProjection H x ≠ -1} :=
  (finitePeripheralCapData H).isOpenEmbedding_old.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by ext x; exact (cappedMarkedProjection_unmarked_iff H x).symm))

@[simp] theorem cappedMarkedUnmarkedHomeomorph_val (y : MarkedImageCover H) :
    (cappedMarkedUnmarkedHomeomorph H y).val = (finitePeripheralCapData H).old y := rfl

/-- Restriction of the completed projection away from the marks remains an actual covering. -/
theorem isCoveringMap_cappedMarkedProjection_unmarked :
    IsCoveringMap (fun x : {x : CappedMarkedCover H //
        cappedMarkedProjection H x ≠ 0 ∧ cappedMarkedProjection H x ≠ -1} =>
      (⟨cappedMarkedProjection H x.val, x.property⟩ : Target)) := by
  have hc := (isCoveringMap_markedImageProjection H).comp_homeomorph
    (cappedMarkedUnmarkedHomeomorph H).symm
  convert hc using 1
  funext x
  apply Subtype.ext
  have hx := (cappedMarkedUnmarkedHomeomorph H).apply_symm_apply x
  have hv := congrArg Subtype.val hx
  rw [cappedMarkedUnmarkedHomeomorph_val] at hv
  change cappedMarkedProjection H x.val =
    (markedImageProjection H ((cappedMarkedUnmarkedHomeomorph H).symm x) : ℂ)
  rw [← hv, cappedMarkedProjection_old]

end
end RHTower.XiMarkedMonodromy
