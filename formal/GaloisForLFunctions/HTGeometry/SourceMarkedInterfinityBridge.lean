import GaloisForLFunctions.HTGeometry.SourceMarkedLawsonCompletion

/-!
# Source-marked exactness as Interfinity stable cohomology

A source-marked completion state remembers which literal source relations remain boundaries after
landing.  This module realizes that exact-source profile as the admissible-primitive profile of an
identity cochain slice.  Consequently:

* a retained source marker survives precisely when its Interfinity stable class is nonzero;
* source exactness loci are exactly stable death regions;
* the two-sided marked topology is the lower topology joined with the stable-death topology.

Thus provenance completion and stable-primitive geometry are not parallel analogies.  They are two
semicontinuous views of the same source-relation quotient.
-/

open Set Topology TopologicalSpace

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration
namespace SourceMarkedExFlag

open Interfinity

universe u v

variable {k : Type u} {V W : Type v} [Field k]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- Identity slice whose admissible primitives are the source relations still exact after landing. -/
def sourceExactnessSlice : CochainSlice k V V where
  d := LinearMap.id
  cocycles := ⊤
  range_le := le_top

@[simp] theorem sourceExactnessSlice_profile
    (s : SourceMarkedExFlag k V W) :
    (sourceExactnessSlice (k := k) (V := V)).profile
        (exactSourceProfile (k := k) (V := V) (W := W)) s =
      exactSourceProfile s := by
  simp [CochainSlice.profile, sourceExactnessSlice]

/-- Stable cohomology class of one retained source relation. -/
def sourceStableClass (s : SourceMarkedExFlag k V W) (x : V) :
    (sourceExactnessSlice (k := k) (V := V)).StableH (exactSourceProfile s) :=
  Submodule.Quotient.mk ⟨x, Submodule.mem_top⟩

/-- A source stable class vanishes exactly when its literal relation remains exact after landing. -/
theorem sourceStableClass_eq_zero_iff
    (s : SourceMarkedExFlag k V W) (x : V) :
    sourceStableClass s x = 0 ↔ x ∈ exactSourceProfile s := by
  rw [sourceStableClass, Submodule.Quotient.mk_eq_zero,
    CochainSlice.mem_stableBoundary_iff]
  simp [sourceExactnessSlice]

/-- Marker survival is precisely nonvanishing in Interfinity stable cohomology. -/
theorem sourceStableClass_ne_zero_iff_survival
    (s : SourceMarkedExFlag k V W) (x : V) :
    sourceStableClass s x ≠ 0 ↔ s ∈ survival x := by
  constructor
  · intro hclass hboundary
    apply hclass
    apply (sourceStableClass_eq_zero_iff s x).2
    exact hboundary
  · intro hsurvival hzero
    apply hsurvival
    exact (sourceStableClass_eq_zero_iff s x).1 hzero

/-- Exactness of a fixed source marker is its stable death region. -/
theorem sourceExactnessSlice_deathRegion_eq_exactAt (x : V) :
    (sourceExactnessSlice (k := k) (V := V)).deathRegion
        (exactSourceProfile (k := k) (V := V) (W := W)) x =
      exactAt x := by
  ext s
  constructor
  · rintro ⟨a, ha, hax⟩
    have : a = x := by simpa [sourceExactnessSlice] using hax
    exact (mem_exactSourceProfile_iff s x).1 (this ▸ ha)
  · intro hx
    exact ⟨x, (mem_exactSourceProfile_iff s x).2 hx, by rfl⟩

/-- Source exactness topology is literally the Interfinity Scott death topology. -/
theorem sourceExactnessTopology_eq_induced_scott :
    (sourceExactnessSlice (k := k) (V := V)).exactnessTopology
        (exactSourceProfile (k := k) (V := V) (W := W)) =
      induced exactSourceProfile (Topology.scott (Submodule k V) univ) := by
  rw [CochainSlice.exactnessTopology_eq_induced_scott]
  congr 1
  funext s
  exact sourceExactnessSlice_profile s

/-- Lawson marked completion joins loss-of-exactness with Interfinity acquisition-of-primitives. -/
theorem lawsonTopology_eq_lower_inf_interfinityExactness :
    lawsonTopology (k := k) (V := V) (W := W) =
      induced exactSourceProfile (Topology.lower (Submodule k V)) ⊓
        (sourceExactnessSlice (k := k) (V := V)).exactnessTopology
          (exactSourceProfile (k := k) (V := V) (W := W)) := by
  rw [lawsonTopology_eq_lower_scott_pullback,
    sourceExactnessTopology_eq_induced_scott]

end SourceMarkedExFlag
end BoundaryMigration
end GaloisForLFunctions.HTGeometry
