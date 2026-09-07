import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.RepresentationTheory.Invariants

/-!
# Invariant functions on the upper half-plane and on `SL(2, ℝ)`

This file proves the algebraic homogeneous-space core of the classical Maass-to-automorphic
dictionary.  For every subgroup `Γ ≤ SL(2, ℝ)`, pullback along the orbit map `g ↦ g • I` gives a
linear equivalence between `Γ`-invariant complex-valued functions on the upper half-plane and
functions on `SL(2, ℝ)` that are left `Γ`-invariant and right invariant under the stabilizer of
`I`.

No smoothness, growth, cuspidality, square-integrability, Laplace/Casimir compatibility, or
adelic factorization is asserted here.
-/

namespace GaloisForLFunctions.RHTower

open UpperHalfPlane

noncomputable section

/-- The real special linear group acting on the upper half-plane. -/
abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The stabilizer of `I` in `SL(2, ℝ)`. -/
abbrev upperHalfPlaneStabilizer : Subgroup SL2R :=
  MulAction.stabilizer SL2R UpperHalfPlane.I

/-- Complex-valued functions on the upper half-plane invariant under `Γ`. -/
def upperHalfPlaneInvariantFunctions (Γ : Subgroup SL2R) : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | ∀ γ : Γ, ∀ z : ℍ, f ((γ : SL2R) • z) = f z}
  zero_mem' := by
    intro γ z
    rfl
  add_mem' := by
    intro f g hf hg γ z
    simp only [Pi.add_apply, hf γ z, hg γ z]
  smul_mem' := by
    intro c f hf γ z
    simp only [Pi.smul_apply, hf γ z]

/-- Functions on `SL(2, ℝ)` that are left `Γ`-invariant and right invariant under the stabilizer
of `I`. -/
def biInvariantFunctions (Γ : Subgroup SL2R) : Submodule ℂ (SL2R → ℂ) where
  carrier := {F |
    (∀ γ : Γ, ∀ g : SL2R, F ((γ : SL2R) * g) = F g) ∧
      ∀ k : upperHalfPlaneStabilizer, ∀ g : SL2R, F (g * (k : SL2R)) = F g}
  zero_mem' := by
    constructor <;> intro _ _ <;> rfl
  add_mem' := by
    intro F H hF hH
    constructor
    · intro γ g
      simp only [Pi.add_apply, hF.1 γ g, hH.1 γ g]
    · intro k g
      simp only [Pi.add_apply, hF.2 k g, hH.2 k g]
  smul_mem' := by
    intro c F hF
    constructor
    · intro γ g
      simp only [Pi.smul_apply, hF.1 γ g]
    · intro k g
      simp only [Pi.smul_apply, hF.2 k g]

@[simp]
theorem mem_upperHalfPlaneInvariantFunctions (Γ : Subgroup SL2R) (f : ℍ → ℂ) :
    f ∈ upperHalfPlaneInvariantFunctions Γ ↔
      ∀ γ : Γ, ∀ z : ℍ, f ((γ : SL2R) • z) = f z :=
  Iff.rfl

@[simp]
theorem mem_biInvariantFunctions (Γ : Subgroup SL2R) (F : SL2R → ℂ) :
    F ∈ biInvariantFunctions Γ ↔
      (∀ γ : Γ, ∀ g : SL2R, F ((γ : SL2R) * g) = F g) ∧
        ∀ k : upperHalfPlaneStabilizer, ∀ g : SL2R, F (g * (k : SL2R)) = F g :=
  Iff.rfl

/-- Pull a `Γ`-invariant function on the upper half-plane back along `g ↦ g • I`. -/
def liftInvariantFunction (Γ : Subgroup SL2R) :
    upperHalfPlaneInvariantFunctions Γ →ₗ[ℂ] biInvariantFunctions Γ where
  toFun f :=
    ⟨fun g ↦ f.1 (g • UpperHalfPlane.I), by
      constructor
      · intro γ g
        simpa only [mul_smul] using f.property γ (g • UpperHalfPlane.I)
      · intro k g
        change f.1 ((g * (k : SL2R)) • UpperHalfPlane.I) =
          f.1 (g • UpperHalfPlane.I)
        rw [mul_smul, MulAction.mem_stabilizer_iff.mp k.property]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A canonical stabilizer element comparing the chosen section at `γ • z` with `γ` times the
chosen section at `z`. -/
def sectionCocycle (γ : SL2R) (z : ℍ) : upperHalfPlaneStabilizer :=
  ⟨(UpperHalfPlane.toSL2R (γ • z))⁻¹ * γ * UpperHalfPlane.toSL2R z, by
    rw [MulAction.mem_stabilizer_iff]
    simp only [mul_smul, UpperHalfPlane.toSL2R_smul_I]
    rw [← UpperHalfPlane.toSL2R_smul_I (γ • z)]
    rw [← mul_smul]
    simp⟩

theorem sectionCocycle_identity (γ : SL2R) (z : ℍ) :
    UpperHalfPlane.toSL2R (γ • z) * (sectionCocycle γ z : SL2R) =
      γ * UpperHalfPlane.toSL2R z := by
  simp [sectionCocycle, mul_assoc]

/-- Restrict a bi-invariant function to the canonical section `z ↦ z.toSL2R`. -/
def descendBiInvariantFunction (Γ : Subgroup SL2R) :
    biInvariantFunctions Γ →ₗ[ℂ] upperHalfPlaneInvariantFunctions Γ where
  toFun F :=
    ⟨fun z ↦ F.1 (UpperHalfPlane.toSL2R z), by
      intro γ z
      calc
        F.1 (UpperHalfPlane.toSL2R ((γ : SL2R) • z)) =
            F.1 (UpperHalfPlane.toSL2R ((γ : SL2R) • z) *
              (sectionCocycle (γ : SL2R) z : SL2R)) :=
          (F.property.2 (sectionCocycle (γ : SL2R) z)
            (UpperHalfPlane.toSL2R ((γ : SL2R) • z))).symm
        _ = F.1 ((γ : SL2R) * UpperHalfPlane.toSL2R z) := by
          rw [sectionCocycle_identity]
        _ = F.1 (UpperHalfPlane.toSL2R z) := F.property.1 γ (UpperHalfPlane.toSL2R z)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem descend_liftInvariantFunction (Γ : Subgroup SL2R)
    (f : upperHalfPlaneInvariantFunctions Γ) :
    descendBiInvariantFunction Γ (liftInvariantFunction Γ f) = f := by
  ext z
  change f.1 (UpperHalfPlane.toSL2R z • UpperHalfPlane.I) = f.1 z
  exact congr_arg f.1 (UpperHalfPlane.toSL2R_smul_I z)

/-- A canonical stabilizer element comparing an arbitrary group element with the chosen section
through its image of `I`. -/
def orbitSectionCocycle (g : SL2R) : upperHalfPlaneStabilizer :=
  ⟨(UpperHalfPlane.toSL2R (g • UpperHalfPlane.I))⁻¹ * g, by
    rw [MulAction.mem_stabilizer_iff]
    rw [mul_smul]
    rw [← UpperHalfPlane.toSL2R_smul_I (g • UpperHalfPlane.I)]
    rw [← mul_smul]
    simp⟩

theorem orbitSectionCocycle_identity (g : SL2R) :
    UpperHalfPlane.toSL2R (g • UpperHalfPlane.I) * (orbitSectionCocycle g : SL2R) = g := by
  simp [orbitSectionCocycle]

@[simp]
theorem lift_descendBiInvariantFunction (Γ : Subgroup SL2R)
    (F : biInvariantFunctions Γ) :
    liftInvariantFunction Γ (descendBiInvariantFunction Γ F) = F := by
  ext g
  calc
    F.1 (UpperHalfPlane.toSL2R (g • UpperHalfPlane.I)) =
        F.1 (UpperHalfPlane.toSL2R (g • UpperHalfPlane.I) *
          (orbitSectionCocycle g : SL2R)) :=
      (F.property.2 (orbitSectionCocycle g)
        (UpperHalfPlane.toSL2R (g • UpperHalfPlane.I))).symm
    _ = F.1 g := by rw [orbitSectionCocycle_identity]

/-- **Classical homogeneous-space correspondence.** Pullback along `g ↦ g • I` is a linear
equivalence between `Γ`-invariant functions on `ℍ` and left-`Γ`, right-stabilizer-invariant
functions on `SL(2, ℝ)`. -/
def maassHomogeneousSpaceCorrespondence (Γ : Subgroup SL2R) :
    upperHalfPlaneInvariantFunctions Γ ≃ₗ[ℂ] biInvariantFunctions Γ :=
  { liftInvariantFunction Γ with
    invFun := descendBiInvariantFunction Γ
    left_inv := descend_liftInvariantFunction Γ
    right_inv := lift_descendBiInvariantFunction Γ }

@[simp]
theorem maassHomogeneousSpaceCorrespondence_apply (Γ : Subgroup SL2R)
    (f : upperHalfPlaneInvariantFunctions Γ) (g : SL2R) :
    (maassHomogeneousSpaceCorrespondence Γ f).1 g = f.1 (g • UpperHalfPlane.I) :=
  rfl

@[simp]
theorem maassHomogeneousSpaceCorrespondence_symm_apply (Γ : Subgroup SL2R)
    (F : biInvariantFunctions Γ) (z : ℍ) :
    ((maassHomogeneousSpaceCorrespondence Γ).symm F).1 z =
      F.1 (UpperHalfPlane.toSL2R z) :=
  rfl

/-- Left `Γ`-invariant functions on `SL(2, ℝ)`, before imposing a right `K`-type. -/
def automorphicFunctionSpace (Γ : Subgroup SL2R) : Submodule ℂ (SL2R → ℂ) where
  carrier := {F | ∀ γ : Γ, ∀ g : SL2R, F ((γ : SL2R) * g) = F g}
  zero_mem' := by
    intro γ g
    rfl
  add_mem' := by
    intro F H hF hH γ g
    simp only [Pi.add_apply, hF γ g, hH γ g]
  smul_mem' := by
    intro c F hF γ g
    simp only [Pi.smul_apply, hF γ g]

/-- Right translation by `h` on left `Γ`-invariant functions. -/
def automorphicRightTranslation (Γ : Subgroup SL2R) (h : SL2R) :
    automorphicFunctionSpace Γ →ₗ[ℂ] automorphicFunctionSpace Γ where
  toFun F :=
    ⟨fun g ↦ F.1 (g * h), by
      intro γ g
      change F.1 (((γ : SL2R) * g) * h) = F.1 (g * h)
      rw [mul_assoc]
      exact F.property γ (g * h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right regular representation of `SL(2, ℝ)` on left `Γ`-invariant functions. -/
def automorphicRightRegularRepresentation (Γ : Subgroup SL2R) :
    Representation ℂ SL2R (automorphicFunctionSpace Γ) where
  toFun := automorphicRightTranslation Γ
  map_one' := by
    ext F g
    change F.1 (g * 1) = F.1 g
    rw [mul_one]
  map_mul' h₁ h₂ := by
    ext F g
    change F.1 (g * (h₁ * h₂)) = F.1 ((g * h₁) * h₂)
    rw [mul_assoc]

@[simp]
theorem automorphicRightRegularRepresentation_apply (Γ : Subgroup SL2R)
    (h g : SL2R) (F : automorphicFunctionSpace Γ) :
    ((automorphicRightRegularRepresentation Γ) h F).1 g = F.1 (g * h) :=
  rfl

/-- The spherical vectors in the right regular representation on `Γ \ SL(2, ℝ)`. -/
def sphericalAutomorphicVectors (Γ : Subgroup SL2R) :
    Submodule ℂ (automorphicFunctionSpace Γ) :=
  Representation.invariants
    ((automorphicRightRegularRepresentation Γ).comp upperHalfPlaneStabilizer.subtype)

/-- A bi-invariant function is the same thing as a spherical vector in the right regular
representation on left `Γ`-invariant functions. -/
def biInvariantSphericalEquiv (Γ : Subgroup SL2R) :
    biInvariantFunctions Γ ≃ₗ[ℂ] sphericalAutomorphicVectors Γ where
  toFun F := by
    have hF := (mem_biInvariantFunctions Γ F.1).mp F.property
    refine ⟨⟨F.1, hF.1⟩, ?_⟩
    change ∀ k : upperHalfPlaneStabilizer,
      (automorphicRightRegularRepresentation Γ) (k : SL2R) ⟨F.1, hF.1⟩ = ⟨F.1, hF.1⟩
    intro k
    apply Subtype.ext
    funext g
    exact hF.2 k g
  invFun F := by
    refine ⟨F.1.1, ⟨F.1.property, ?_⟩⟩
    have hfixed : ∀ k : upperHalfPlaneStabilizer,
        (automorphicRightRegularRepresentation Γ) (k : SL2R) F.1 = F.1 := by
      exact F.property
    ·
      intro k g
      exact congr_arg (fun H : automorphicFunctionSpace Γ ↦ H.1 g) (hfixed k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Representation-theoretic homogeneous-space correspondence.** `Γ`-invariant functions on
the upper half-plane are linearly equivalent to the spherical vectors in the right regular
representation on functions on `Γ \ SL(2, ℝ)`. -/
def maassToSphericalAutomorphicCorrespondence (Γ : Subgroup SL2R) :
    upperHalfPlaneInvariantFunctions Γ ≃ₗ[ℂ] sphericalAutomorphicVectors Γ :=
  (maassHomogeneousSpaceCorrespondence Γ).trans (biInvariantSphericalEquiv Γ)

@[simp]
theorem maassToSphericalAutomorphicCorrespondence_apply (Γ : Subgroup SL2R)
    (f : upperHalfPlaneInvariantFunctions Γ) (g : SL2R) :
    (maassToSphericalAutomorphicCorrespondence Γ f).1.1 g =
      f.1 (g • UpperHalfPlane.I) :=
  rfl

end

end GaloisForLFunctions.RHTower
