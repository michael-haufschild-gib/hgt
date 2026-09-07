import GaloisForLFunctions.RHTower.RealUpperBorelPrincipalSeries

/-!
# Compact picture of the algebraic real principal series

Mathlib's upper-half-plane section gives a canonical Iwasawa decomposition
`g = b(g) k(g)` with `b(g) ∈ B` and `k(g) ∈ K`.  This file proves its Borel cocycle law and uses it
to identify algebraic coinduction from `B` with twisted functions on `K` under
`M = B ∩ K`.

Restriction to `K` and extension by `χσ(b(g)) φ(k(g))` are constructed as inverse complex-linear
maps.  This is the compact-picture bridge needed before identifying finite Fourier `K`-types with
the explicit spherical Harish-Chandra model.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Upper-Borel factor in the canonical Iwasawa decomposition of `g`. -/
def realIwasawaB (g : SL2R) : realUpperBorel :=
  ⟨UpperHalfPlane.toSL2R (g • UpperHalfPlane.I), by simp [realUpperBorel]⟩

/-- Stabilizer factor in the canonical Iwasawa decomposition of `g`. -/
def realIwasawaK (g : SL2R) : upperHalfPlaneStabilizer :=
  orbitSectionCocycle g

/-- Canonical algebraic Iwasawa decomposition `g = b(g) k(g)`. -/
theorem realIwasawaB_mul_realIwasawaK (g : SL2R) :
    (realIwasawaB g : SL2R) * (realIwasawaK g : SL2R) = g := by
  exact orbitSectionCocycle_identity g

/-- The intersection `M = B ∩ K`, represented as a subgroup of `K`. -/
def realSphericalM : Subgroup upperHalfPlaneStabilizer where
  carrier := {k | (k : SL2R) ∈ realUpperBorel}
  one_mem' := realUpperBorel.one_mem
  mul_mem' := fun ha hb ↦ realUpperBorel.mul_mem ha hb
  inv_mem' := fun ha ↦ realUpperBorel.inv_mem ha

/-- Inclusion of `M` into the upper Borel. -/
def realSphericalMToBorel : realSphericalM →* realUpperBorel where
  toFun m := ⟨((m : upperHalfPlaneStabilizer) : SL2R), m.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Inclusion of `M` into the stabilizer `K`. -/
def realSphericalMToK : realSphericalM →* upperHalfPlaneStabilizer :=
  realSphericalM.subtype

/-- Twisted functions on `K` forming the compact picture of exponent `σ`. -/
def realCompactPictureSpace (σ : ℝ) :
    Submodule ℂ (upperHalfPlaneStabilizer → ℂ) where
  carrier := {φ | ∀ m : realSphericalM, ∀ k : upperHalfPlaneStabilizer,
    φ (realSphericalMToK m * k) =
      realUpperBorelRpowCharacter σ (realSphericalMToBorel m) * φ k}
  zero_mem' := by intro m k; simp
  add_mem' := by
    intro φ ψ hφ hψ m k
    simp only [Pi.add_apply, hφ m k, hψ m k, mul_add]
  smul_mem' := by
    intro c φ hφ m k
    simp only [Pi.smul_apply, hφ m k, smul_eq_mul]
    ring

/-- Transition factor comparing Iwasawa decompositions of `bg` and `g`. -/
def realIwasawaTransition (b : realUpperBorel) (g : SL2R) : realSphericalM := by
  let k : upperHalfPlaneStabilizer := sectionCocycle (b : SL2R) (g • UpperHalfPlane.I)
  refine ⟨k, ?_⟩
  change (k : SL2R) ∈ realUpperBorel
  rw [realUpperBorel_mem_iff]
  change (((UpperHalfPlane.toSL2R ((b : SL2R) • (g • UpperHalfPlane.I)))⁻¹ *
    (b : SL2R) * UpperHalfPlane.toSL2R (g • UpperHalfPlane.I)) : SL2R) 1 0 = 0
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hb : (b : SL2R) 1 0 = 0 := b.property
  simp [hb]

/-- The `K` factors transform by left multiplication with the transition element. -/
theorem realIwasawaK_mul (b : realUpperBorel) (g : SL2R) :
    realIwasawaK ((b : SL2R) * g) =
      realSphericalMToK (realIwasawaTransition b g) * realIwasawaK g := by
  apply Subtype.ext
  simp [realIwasawaK, realIwasawaTransition, realSphericalMToK,
    orbitSectionCocycle, sectionCocycle, mul_smul, mul_assoc]

/-- The Borel factors and transition factor satisfy the corresponding cocycle identity. -/
theorem realIwasawaB_transition (b : realUpperBorel) (g : SL2R) :
    realIwasawaB ((b : SL2R) * g) * realSphericalMToBorel (realIwasawaTransition b g) =
      b * realIwasawaB g := by
  apply Subtype.ext
  simpa [realIwasawaB, realIwasawaTransition, realSphericalMToBorel, mul_smul] using
    sectionCocycle_identity (b : SL2R) (g • UpperHalfPlane.I)

@[simp]
theorem upperHalfPlane_toSL2R_I : UpperHalfPlane.toSL2R UpperHalfPlane.I = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [UpperHalfPlane.toSL2R]

@[simp]
theorem realIwasawaB_of_K (k : upperHalfPlaneStabilizer) :
    realIwasawaB (k : SL2R) = 1 := by
  apply Subtype.ext
  change UpperHalfPlane.toSL2R ((k : SL2R) • UpperHalfPlane.I) = 1
  rw [MulAction.mem_stabilizer_iff.mp k.property]
  exact upperHalfPlane_toSL2R_I

@[simp]
theorem realIwasawaK_of_K (k : upperHalfPlaneStabilizer) :
    realIwasawaK (k : SL2R) = k := by
  apply Subtype.ext
  simp [realIwasawaK, orbitSectionCocycle,
    MulAction.mem_stabilizer_iff.mp k.property]

/-- Restriction of the coinduced principal series to its compact picture. -/
def realPrincipalSeriesRestrictToK (σ : ℝ) :
    Representation.coindV realUpperBorel.subtype
        (realUpperBorelExponentRepresentation σ) →ₗ[ℂ]
      realCompactPictureSpace σ where
  toFun f := ⟨fun k ↦ f.1 (k : SL2R), by
    intro m k
    simpa [realSphericalMToK, realSphericalMToBorel,
      realUpperBorelExponentRepresentation] using
      f.property (realSphericalMToBorel m) (k : SL2R)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical extension of a compact-picture function through Iwasawa decomposition. -/
def realCompactPictureExtend (σ : ℝ) :
    realCompactPictureSpace σ →ₗ[ℂ]
      Representation.coindV realUpperBorel.subtype
        (realUpperBorelExponentRepresentation σ) where
  toFun φ := ⟨fun g ↦ realUpperBorelRpowCharacter σ (realIwasawaB g) *
      φ.1 (realIwasawaK g), by
    intro b g
    change realUpperBorelRpowCharacter σ (realIwasawaB ((b : SL2R) * g)) *
        φ.1 (realIwasawaK ((b : SL2R) * g)) =
      realUpperBorelRpowCharacter σ b *
        (realUpperBorelRpowCharacter σ (realIwasawaB g) * φ.1 (realIwasawaK g))
    rw [realIwasawaK_mul]
    rw [φ.property (realIwasawaTransition b g) (realIwasawaK g)]
    have hχ := congr_arg (realUpperBorelRpowCharacter σ)
      (realIwasawaB_transition b g)
    simp only [map_mul] at hχ
    rw [← mul_assoc, hχ, mul_assoc]⟩
  map_add' φ ψ := by
    ext g
    simp only [AddMemClass.coe_add, Pi.add_apply, mul_add]
  map_smul' c φ := by
    ext g
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp]
theorem realPrincipalSeriesRestrictToK_extend (σ : ℝ)
    (φ : realCompactPictureSpace σ) :
    realPrincipalSeriesRestrictToK σ (realCompactPictureExtend σ φ) = φ := by
  ext k
  simp [realPrincipalSeriesRestrictToK, realCompactPictureExtend]

@[simp]
theorem realCompactPictureExtend_restrictToK (σ : ℝ)
    (f : Representation.coindV realUpperBorel.subtype
      (realUpperBorelExponentRepresentation σ)) :
    realCompactPictureExtend σ (realPrincipalSeriesRestrictToK σ f) = f := by
  ext g
  change realUpperBorelRpowCharacter σ (realIwasawaB g) *
      f.1 (realIwasawaK g : SL2R) = f.1 g
  have h := f.property (realIwasawaB g) (realIwasawaK g : SL2R)
  change f.1 ((realIwasawaB g : SL2R) * (realIwasawaK g : SL2R)) =
    realUpperBorelRpowCharacter σ (realIwasawaB g) *
      f.1 (realIwasawaK g : SL2R) at h
  rw [realIwasawaB_mul_realIwasawaK] at h
  exact h.symm

/-- Algebraic compact-picture equivalence for the real principal series. -/
def algebraicRealPrincipalSeriesCompactPicture (σ : ℝ) :
    Representation.coindV realUpperBorel.subtype
        (realUpperBorelExponentRepresentation σ) ≃ₗ[ℂ]
      realCompactPictureSpace σ :=
  { realPrincipalSeriesRestrictToK σ with
    invFun := realCompactPictureExtend σ
    left_inv := realCompactPictureExtend_restrictToK σ
    right_inv := realPrincipalSeriesRestrictToK_extend σ }

end
end GaloisForLFunctions.RHTower
