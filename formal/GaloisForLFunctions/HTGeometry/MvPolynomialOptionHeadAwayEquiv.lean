import GaloisForLFunctions.HTGeometry.MvPolynomialProjectiveChartPrime
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Standard affine chart of a homogeneous polynomial ring

For the ordinary grading on `R[X₀, Xᵢ]`, the degree-zero part after inverting `X₀` is the
polynomial ring `R[Xᵢ]`.  This file constructs the canonical ring equivalence explicitly.

The forward map dehomogenizes by setting `X₀ = 1`; the inverse sends each affine coordinate to
`Xᵢ / X₀`.  Injectivity is proved by cross-multiplying two homogeneous fractions and reusing the
faithfulness of dehomogenization on a fixed homogeneous sector.
-/

namespace GaloisForLFunctions

open MvPolynomial HomogeneousLocalization

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable {R σ : Type*} [CommRing R]

/-- Ordinary total-degree grading on a polynomial ring with one distinguished coordinate. -/
abbrev optionHeadGrading : ℕ → Submodule R (MvPolynomial (Option σ) R) :=
  MvPolynomial.homogeneousSubmodule (Option σ) R

noncomputable instance optionHeadGradedAlgebra :
    GradedAlgebra (optionHeadGrading (R := R) (σ := σ)) :=
  MvPolynomial.gradedAlgebra

/-- Constants embedded into the distinguished affine chart. -/
def optionHeadBaseToAway :
    R →+* HomogeneousLocalization.Away
      (optionHeadGrading (R := R) (σ := σ)) (MvPolynomial.X none) where
  toFun r := HomogeneousLocalization.Away.mk
    (optionHeadGrading (R := R) (σ := σ))
    (MvPolynomial.isHomogeneous_X R (none : Option σ)) 0 (MvPolynomial.C r)
    (by simp)
  map_one' := by ext; simp [HomogeneousLocalization.Away.val_mk]
  map_mul' x y := by ext; simp [HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, Localization.mk_zero]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, Localization.add_mk, add_comm]

/-- Natural `R`-algebra structure on the distinguished affine chart. -/
noncomputable instance optionHeadAwayAlgebra :
    Algebra R (HomogeneousLocalization.Away
      (optionHeadGrading (R := R) (σ := σ)) (MvPolynomial.X none)) :=
  optionHeadBaseToAway.toAlgebra

/-- Affine coordinate `Xᵢ / X₀` in the chart where the distinguished coordinate is nonzero. -/
def optionHeadAffineCoordinate (i : σ) :
    HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := σ))
      (MvPolynomial.X none) :=
  HomogeneousLocalization.Away.mk
    (optionHeadGrading (R := R) (σ := σ))
    (MvPolynomial.isHomogeneous_X R (none : Option σ)) 1
    (MvPolynomial.X (some i)) (by simpa using MvPolynomial.isHomogeneous_X R (some i))

/-- Homomorphism from affine polynomials to the standard distinguished projective chart. -/
def optionHeadPolynomialToAway :
    MvPolynomial σ R →+*
      HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := σ))
        (MvPolynomial.X none) :=
  MvPolynomial.eval₂Hom optionHeadBaseToAway optionHeadAffineCoordinate

/-- Dehomogenization homomorphism from the standard distinguished projective chart. -/
def optionHeadAwayToPolynomial :
    HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := σ))
        (MvPolynomial.X none) →+* MvPolynomial σ R :=
  (Localization.awayLift optionHeadDehomogenize (MvPolynomial.X none) (by simp)).comp
    (algebraMap
      (HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := σ))
        (MvPolynomial.X none))
      (Localization.Away (MvPolynomial.X none)))

@[simp]
theorem optionHeadAwayToPolynomial_affineCoordinate (i : σ) :
    optionHeadAwayToPolynomial (R := R) (σ := σ) (optionHeadAffineCoordinate i) =
      MvPolynomial.X i := by
  change (Localization.awayLift optionHeadDehomogenize (MvPolynomial.X none) (by simp))
    (Localization.mk (MvPolynomial.X (some i))
      ⟨MvPolynomial.X none ^ 1, by use 1⟩) = _
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp [optionHeadDehomogenize]

@[simp]
theorem optionHeadAwayToPolynomial_base (r : R) :
    optionHeadAwayToPolynomial (R := R) (σ := σ)
      (optionHeadBaseToAway r) = MvPolynomial.C r := by
  change (Localization.awayLift optionHeadDehomogenize (MvPolynomial.X none) (by simp))
    (Localization.mk (MvPolynomial.C r)
      ⟨MvPolynomial.X none ^ 0, by exact Submonoid.one_mem _⟩) = _
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp [optionHeadDehomogenize]

/-- Dehomogenizing the canonical affine-coordinate substitution is the identity. -/
theorem optionHeadAwayToPolynomial_comp_polynomialToAway :
    (optionHeadAwayToPolynomial (R := R) (σ := σ)).comp optionHeadPolynomialToAway =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [optionHeadPolynomialToAway]
  · intro i
    simp [optionHeadPolynomialToAway]

/-- Formula for dehomogenizing a homogeneous fraction with denominator a power of `X₀`. -/
theorem optionHeadAwayToPolynomial_mk (n : ℕ) (a : MvPolynomial (Option σ) R)
    (ha : a ∈ optionHeadGrading (R := R) (σ := σ) (n • 1)) :
    optionHeadAwayToPolynomial (R := R) (σ := σ)
      (HomogeneousLocalization.Away.mk
        (optionHeadGrading (R := R) (σ := σ))
        (MvPolynomial.isHomogeneous_X R (none : Option σ)) n a ha) =
      optionHeadDehomogenize a := by
  change (Localization.awayLift optionHeadDehomogenize (MvPolynomial.X none) (by simp))
    (Localization.mk a ⟨MvPolynomial.X none ^ n, by use n⟩) = _
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp

variable [Nontrivial R]

/-- Dehomogenization is injective on the distinguished standard projective chart. -/
theorem optionHeadAwayToPolynomial_injective :
    Function.Injective (optionHeadAwayToPolynomial (R := R) (σ := σ)) := by
  intro z w hzw
  let hX : MvPolynomial.X (none : Option σ) ∈
      optionHeadGrading (R := R) (σ := σ) 1 :=
    MvPolynomial.isHomogeneous_X R (none : Option σ)
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (𝒜 := optionHeadGrading (R := R) (σ := σ)) hX z
  obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (𝒜 := optionHeadGrading (R := R) (σ := σ)) hX w
  rw [optionHeadAwayToPolynomial_mk, optionHeadAwayToPolynomial_mk] at hzw
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  apply eq_of_isHomogeneous_of_optionHeadDehomogenize_eq
  · simpa [add_comm] using
      ((MvPolynomial.isHomogeneous_X R (none : Option σ)).pow m).mul
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha)
  · simpa [add_comm] using
      ((MvPolynomial.isHomogeneous_X R (none : Option σ)).pow n).mul
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hb)
  · simpa [map_mul] using hzw

/-- Dehomogenization is bijective on the distinguished standard projective chart. -/
theorem optionHeadAwayToPolynomial_bijective :
    Function.Bijective (optionHeadAwayToPolynomial (R := R) (σ := σ)) := by
  refine ⟨optionHeadAwayToPolynomial_injective, ?_⟩
  intro p
  exact ⟨optionHeadPolynomialToAway p,
    RingHom.congr_fun optionHeadAwayToPolynomial_comp_polynomialToAway p⟩

/-- Canonical coordinate equivalence `(R[X₀, Xᵢ]_{X₀})₀ ≃ R[Xᵢ]`. -/
def optionHeadAwayRingEquiv :
    HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := σ))
        (MvPolynomial.X none) ≃+* MvPolynomial σ R :=
  RingEquiv.ofBijective optionHeadAwayToPolynomial optionHeadAwayToPolynomial_bijective

/-- Canonical affine-chart coordinate equivalence as an `R`-algebra equivalence. -/
def optionHeadAwayAlgEquiv :
    HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := σ))
        (MvPolynomial.X none) ≃ₐ[R] MvPolynomial σ R where
  __ := optionHeadAwayRingEquiv
  commutes' r := by
    change optionHeadAwayToPolynomial (optionHeadBaseToAway r) = MvPolynomial.C r
    exact optionHeadAwayToPolynomial_base r

/-! ## Swapping the two coordinates of a projective line -/

/-- Involution interchanging the two elements of `Option PUnit`. -/
def pUnitOptionSwap : Option PUnit ≃ Option PUnit where
  toFun
    | none => some PUnit.unit
    | some _ => none
  invFun
    | none => some PUnit.unit
    | some _ => none
  left_inv x := by rcases x with (_ | ⟨⟩) <;> rfl
  right_inv x := by rcases x with (_ | ⟨⟩) <;> rfl

@[simp]
theorem pUnitOptionSwap_none : pUnitOptionSwap none = some PUnit.unit := rfl

@[simp]
theorem pUnitOptionSwap_some : pUnitOptionSwap (some PUnit.unit) = none := rfl

/-- Coordinate swap as a graded endomorphism of the binary homogeneous polynomial ring. -/
def pUnitOptionSwapGradedHom {R : Type*} [CommRing R] :
    optionHeadGrading (R := R) (σ := PUnit) →+*ᵍ
      optionHeadGrading (R := R) (σ := PUnit) where
  __ := (MvPolynomial.renameEquiv R pUnitOptionSwap).toRingEquiv.toRingHom
  map_mem {i p} hp := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    exact hp.rename_isHomogeneous

@[simp]
theorem pUnitOptionSwapGradedHom_X_none {R : Type*} [CommRing R] :
    pUnitOptionSwapGradedHom (R := R) (MvPolynomial.X none) =
      MvPolynomial.X (some PUnit.unit) := by
  simp [pUnitOptionSwapGradedHom]

@[simp]
theorem pUnitOptionSwapGradedHom_X_some {R : Type*} [CommRing R] :
    pUnitOptionSwapGradedHom (R := R) (MvPolynomial.X (some PUnit.unit)) =
      MvPolynomial.X none := by
  simp [pUnitOptionSwapGradedHom]

/-- Coordinate swap is an involution as a graded ring homomorphism. -/
theorem pUnitOptionSwapGradedHom_comp_self {R : Type*} [CommRing R] :
    (pUnitOptionSwapGradedHom (R := R)).comp pUnitOptionSwapGradedHom =
      GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro p
  have hring :
      ((pUnitOptionSwapGradedHom (R := R)).comp
        pUnitOptionSwapGradedHom).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [pUnitOptionSwapGradedHom]
    · intro i
      rcases i with (_ | i)
      · simp [pUnitOptionSwapGradedHom]
      · rcases i with ⟨⟩
        simp [pUnitOptionSwapGradedHom]
  exact RingHom.congr_fun hring p

/-- Coordinate-swap homomorphism from the `X₁` chart to the `X₀` chart. -/
def pUnitOptionSwapAwayHom {R : Type*} [CommRing R] :
    HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := PUnit))
        (MvPolynomial.X (some PUnit.unit)) →+*
      HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := PUnit))
        (MvPolynomial.X none) := by
  apply HomogeneousLocalization.map (pUnitOptionSwapGradedHom (R := R))
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/-- Coordinate-swap homomorphism from the `X₀` chart to the `X₁` chart. -/
def pUnitOptionSwapAwayHomInv {R : Type*} [CommRing R] :
    HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := PUnit))
        (MvPolynomial.X none) →+*
      HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := PUnit))
        (MvPolynomial.X (some PUnit.unit)) := by
  apply HomogeneousLocalization.map (pUnitOptionSwapGradedHom (R := R))
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/-- Swapping homogeneous coordinates identifies the two standard affine projective-line charts. -/
def pUnitOptionSwapAwayRingEquiv {R : Type*} [CommRing R] :
    HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := PUnit))
        (MvPolynomial.X (some PUnit.unit)) ≃+*
      HomogeneousLocalization.Away (optionHeadGrading (R := R) (σ := PUnit))
        (MvPolynomial.X none) where
  toFun := pUnitOptionSwapAwayHom
  invFun := pUnitOptionSwapAwayHomInv
  left_inv z := by
    change HomogeneousLocalization.map _ _ (HomogeneousLocalization.map _ _ z) = z
    rw [HomogeneousLocalization.map_map]
    simp only [pUnitOptionSwapGradedHom_comp_self, HomogeneousLocalization.map_id,
      RingHom.id_apply]
  right_inv z := by
    change HomogeneousLocalization.map _ _ (HomogeneousLocalization.map _ _ z) = z
    rw [HomogeneousLocalization.map_map]
    simp only [pUnitOptionSwapGradedHom_comp_self, HomogeneousLocalization.map_id,
      RingHom.id_apply]
  map_add' x y := map_add _ x y
  map_mul' x y := map_mul _ x y

end

end GaloisForLFunctions
