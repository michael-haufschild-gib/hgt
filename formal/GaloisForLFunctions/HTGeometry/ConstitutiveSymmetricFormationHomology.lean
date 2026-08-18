import GaloisForLFunctions.HTGeometry.LinearFamilyDefectSupermodularity

/-!
# Symmetric formation charge and observer-created overlap

Three subspaces carry a canonical distributivity quotient.  Its dimension is the symmetric
inclusion--exclusion defect.  When one subspace is an observer kernel, the same dimension is
exactly the overlap created by observation: the intersection of the two observed images modulo
the observed source intersection.  Thus vanishing formation charge is equivalent to exact
preservation of intersection, and under pairwise injectivity it is equivalent to joint
injectivity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Source directions in `U` that can be assembled from the other two formation legs. -/
def formationCore (U W Z : Submodule K V) : Submodule K V :=
  U ⊓ (W ⊔ Z)

/-- Pairwise gluing directions already generated before ternary fusion. -/
def formationBoundary (U W Z : Submodule K V) : Submodule K V :=
  (U ⊓ W) ⊔ (U ⊓ Z)

/-- Pairwise gluing lies inside the ternary core. -/
theorem formationBoundary_le_core (U W Z : Submodule K V) :
    formationBoundary U W Z ≤ formationCore U W Z := by
  apply sup_le
  · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)
  · exact le_inf inf_le_left (inf_le_right.trans le_sup_right)

/-- Pairwise gluing, regarded as a submodule of the ternary core. -/
def formationBoundaryInCore (U W Z : Submodule K V) :
    Submodule K (formationCore U W Z) :=
  (formationBoundary U W Z).comap (formationCore U W Z).subtype

/-- The first symmetric formation charge, in the chart privileging `U`. -/
abbrev FormationCharge (U W Z : Submodule K V) : Type _ :=
  ↥(formationCore U W Z) ⧸ formationBoundaryInCore U W Z

/-- Pulling the boundary into the core does not change its finite dimension. -/
theorem finrank_formationBoundaryInCore
    [FiniteDimensional K V] (U W Z : Submodule K V) :
    Module.finrank K (formationBoundaryInCore U W Z) =
      Module.finrank K (formationBoundary U W Z) := by
  rw [← Submodule.finrank_map_subtype_eq (formationCore U W Z)
      (formationBoundaryInCore U W Z),
    formationBoundaryInCore, Submodule.map_comap_subtype]
  rw [inf_eq_right.mpr (formationBoundary_le_core U W Z)]

/-- Symmetric inclusion--exclusion conservation for the formation charge. -/
theorem formationCharge_finrank_balance
    [FiniteDimensional K V] (U W Z : Submodule K V) :
    Module.finrank K (FormationCharge U W Z)
        + Module.finrank K ↥(U ⊔ W ⊔ Z)
        + Module.finrank K ↥(U ⊓ W)
        + Module.finrank K ↥(U ⊓ Z)
        + Module.finrank K ↥(W ⊓ Z)
      = Module.finrank K U
        + Module.finrank K W
        + Module.finrank K Z
        + Module.finrank K ↥(U ⊓ W ⊓ Z) := by
  have hq := Submodule.finrank_quotient_add_finrank
    (formationBoundaryInCore U W Z)
  have hB := finrank_formationBoundaryInCore U W Z
  have hUB := Submodule.finrank_sup_add_finrank_inf_eq
    (U ⊓ W) (U ⊓ Z)
  have hU := Submodule.finrank_sup_add_finrank_inf_eq U (W ⊔ Z)
  have hWZ := Submodule.finrank_sup_add_finrank_inf_eq W Z
  change Module.finrank K (FormationCharge U W Z) +
      Module.finrank K (formationBoundaryInCore U W Z) =
        Module.finrank K ↥(U ⊓ (W ⊔ Z)) at hq
  simp only [formationBoundary] at hB
  have htriple : (U ⊓ W) ⊓ (U ⊓ Z) = U ⊓ W ⊓ Z := by
    ext x
    simp [and_assoc, and_left_comm]
  have htotal : U ⊔ (W ⊔ Z) = U ⊔ W ⊔ Z := by
    exact sup_assoc U W Z |>.symm
  rw [htriple] at hUB
  rw [htotal] at hU
  rw [hB] at hq
  have hlocal :
      Module.finrank K (FormationCharge U W Z)
          + Module.finrank K ↥(U ⊓ W)
          + Module.finrank K ↥(U ⊓ Z)
        = Module.finrank K ↥(U ⊓ (W ⊔ Z))
          + Module.finrank K ↥(U ⊓ W ⊓ Z) := by
    calc
      Module.finrank K (FormationCharge U W Z)
            + Module.finrank K ↥(U ⊓ W)
            + Module.finrank K ↥(U ⊓ Z)
          = Module.finrank K (FormationCharge U W Z)
            + (Module.finrank K ↥(U ⊓ W) + Module.finrank K ↥(U ⊓ Z)) := by
              ac_rfl
      _ = Module.finrank K (FormationCharge U W Z)
            + (Module.finrank K ↥(U ⊓ W ⊔ U ⊓ Z)
              + Module.finrank K ↥(U ⊓ W ⊓ Z)) := by rw [hUB]
      _ = (Module.finrank K (FormationCharge U W Z)
            + Module.finrank K ↥(U ⊓ W ⊔ U ⊓ Z))
              + Module.finrank K ↥(U ⊓ W ⊓ Z) := by ac_rfl
      _ = Module.finrank K ↥(U ⊓ (W ⊔ Z))
              + Module.finrank K ↥(U ⊓ W ⊓ Z) := by
                exact congrArg (fun n => n + Module.finrank K ↥(U ⊓ W ⊓ Z)) hq
  calc
    Module.finrank K (FormationCharge U W Z)
          + Module.finrank K ↥(U ⊔ W ⊔ Z)
          + Module.finrank K ↥(U ⊓ W)
          + Module.finrank K ↥(U ⊓ Z)
          + Module.finrank K ↥(W ⊓ Z)
        = (Module.finrank K (FormationCharge U W Z)
            + Module.finrank K ↥(U ⊓ W)
            + Module.finrank K ↥(U ⊓ Z))
          + (Module.finrank K ↥(U ⊔ W ⊔ Z)
            + Module.finrank K ↥(W ⊓ Z)) := by ac_rfl
    _ = (Module.finrank K ↥(U ⊓ (W ⊔ Z))
            + Module.finrank K ↥(U ⊓ W ⊓ Z))
          + (Module.finrank K ↥(U ⊔ W ⊔ Z)
            + Module.finrank K ↥(W ⊓ Z)) := by rw [hlocal]
    _ = Module.finrank K ↥(U ⊓ W ⊓ Z)
          + ((Module.finrank K ↥(U ⊔ W ⊔ Z)
              + Module.finrank K ↥(U ⊓ (W ⊔ Z)))
            + Module.finrank K ↥(W ⊓ Z)) := by ac_rfl
    _ = Module.finrank K ↥(U ⊓ W ⊓ Z)
          + ((Module.finrank K U + Module.finrank K ↥(W ⊔ Z))
            + Module.finrank K ↥(W ⊓ Z)) := by rw [hU]
    _ = Module.finrank K ↥(U ⊓ W ⊓ Z)
          + (Module.finrank K U
            + (Module.finrank K ↥(W ⊔ Z) + Module.finrank K ↥(W ⊓ Z))) := by ac_rfl
    _ = Module.finrank K ↥(U ⊓ W ⊓ Z)
          + (Module.finrank K U + (Module.finrank K W + Module.finrank K Z)) := by rw [hWZ]
    _ = Module.finrank K U + Module.finrank K W + Module.finrank K Z
          + Module.finrank K ↥(U ⊓ W ⊓ Z) := by ac_rfl

private theorem finrank_map_add_finrank_inf_ker
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K V] (L : V →ₗ[K] Y) (W : Submodule K V) :
    Module.finrank K (W.map L) + Module.finrank K ↥(W ⊓ LinearMap.ker L)
      = Module.finrank K W := by
  have hrn := (L.domRestrict W).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
  have hEq : Module.finrank K ((LinearMap.ker L).comap W.subtype)
      = Module.finrank K ↥(W ⊓ LinearMap.ker L) := by
    rw [← Submodule.map_comap_subtype W (LinearMap.ker L)]
    exact (Submodule.equivMapOfInjective W.subtype (Submodule.injective_subtype W) _).finrank_eq
  rw [hEq] at hrn
  exact hrn

/-- Observer-created overlap is exactly conserved by the ternary formation charge. -/
theorem observerOverlap_finrank_conservation
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K V] [FiniteDimensional K Y]
    (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Module.finrank K (FormationCharge (LinearMap.ker L) W Z)
        + Module.finrank K ↥((W ⊓ Z).map L)
      = Module.finrank K ↥(W.map L ⊓ Z.map L) := by
  let U := LinearMap.ker L
  have hform := formationCharge_finrank_balance U W Z
  have hW := finrank_map_add_finrank_inf_ker L W
  have hZ := finrank_map_add_finrank_inf_ker L Z
  have hS := finrank_map_add_finrank_inf_ker L (W ⊔ Z)
  have hI := finrank_map_add_finrank_inf_ker L (W ⊓ Z)
  have htarget := Submodule.finrank_sup_add_finrank_inf_eq (W.map L) (Z.map L)
  rw [← Submodule.map_sup] at htarget
  have hK : Module.finrank K ↥(U ⊔ W ⊔ Z) + Module.finrank K ↥(U ⊓ (W ⊔ Z))
      = Module.finrank K U + Module.finrank K ↥(W ⊔ Z) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U (W ⊔ Z)
    rw [← sup_assoc] at h
    exact h
  have htriple : U ⊓ W ⊓ Z = (W ⊓ Z) ⊓ U := by
    ext x
    simp [and_assoc, and_left_comm, and_comm]
  have hKW : U ⊓ W = W ⊓ U := inf_comm U W
  have hKZ : U ⊓ Z = Z ⊓ U := inf_comm U Z
  have hKS : U ⊓ (W ⊔ Z) = (W ⊔ Z) ⊓ U := inf_comm U (W ⊔ Z)
  rw [htriple, hKW, hKZ] at hform
  rw [hKS] at hK
  dsimp [U] at hform hK
  omega

/-- Formation charge vanishes exactly when observation preserves the intersection of two legs. -/
theorem observerOverlap_charge_zero_iff
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K V] [FiniteDimensional K Y]
    (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Module.finrank K (FormationCharge (LinearMap.ker L) W Z) = 0 ↔
      (W ⊓ Z).map L = W.map L ⊓ Z.map L := by
  have hle : (W ⊓ Z).map L ≤ W.map L ⊓ Z.map L := by
    exact le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)
  have hbalance := observerOverlap_finrank_conservation L W Z
  constructor
  · intro hzero
    apply Submodule.eq_of_le_of_finrank_le hle
    omega
  · intro heq
    have hfin : Module.finrank K ↥((W ⊓ Z).map L) =
        Module.finrank K ↥(W.map L ⊓ Z.map L) :=
      congrArg (fun S : Submodule K Y => Module.finrank K S) heq
    omega

/-- Formation charge has rank zero exactly when its distributivity core is already generated by
the pairwise boundaries. -/
theorem formationCharge_finrank_zero_iff
    [FiniteDimensional K V] (U W Z : Submodule K V) :
    Module.finrank K (FormationCharge U W Z) = 0 ↔
      formationCore U W Z = formationBoundary U W Z := by
  rw [Module.finrank_zero_iff]
  constructor
  · intro h
    have htop : formationBoundaryInCore U W Z = ⊤ := by
      exact Submodule.Quotient.subsingleton_iff.mp h
    apply le_antisymm
    · intro x hx
      have hx' : (⟨x, hx⟩ : formationCore U W Z) ∈
          formationBoundaryInCore U W Z := by
        rw [htop]
        trivial
      exact hx'
    · exact formationBoundary_le_core U W Z
  · intro h
    rw [Submodule.Quotient.subsingleton_iff]
    apply le_antisymm le_top
    intro x hx
    change (x : V) ∈ formationBoundary U W Z
    rw [← h]
    exact x.2

/-- If each formation leg is separately observable, vanishing ternary charge is equivalent to
joint observability of their sum. -/
theorem formationCharge_zero_iff_jointInjective
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K V]
    (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (hW : Disjoint W (LinearMap.ker L))
    (hZ : Disjoint Z (LinearMap.ker L)) :
    Module.finrank K (FormationCharge (LinearMap.ker L) W Z) = 0 ↔
      Disjoint (W ⊔ Z) (LinearMap.ker L) := by
  rw [formationCharge_finrank_zero_iff]
  have hKW : LinearMap.ker L ⊓ W = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp hW
  have hKZ : LinearMap.ker L ⊓ Z = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp hZ
  rw [disjoint_iff, ← inf_comm]
  simp [formationCore, formationBoundary, hKW, hKZ]

end

end GaloisForLFunctions.HTGeometry
