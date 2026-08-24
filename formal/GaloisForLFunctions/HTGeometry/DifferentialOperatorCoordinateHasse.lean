import GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionFreeQuotient

/-!
# Coordinate Hasse principle for differential-operator modules

Deleting a finite set of coordinate places has kernel exactly the vectors supported on those
places. Every packet on the complementary places glues, uniquely modulo that finite support.
-/

namespace GaloisForLFunctions.HTGeometry
namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {κ : Type*} [DecidableEq κ]

/-- Simultaneous restriction to every coordinate outside a finite exceptional set. -/
def complementCoordinateHasseRestriction (C : Finset κ) :
    (κ → DiffOp K) →ₗ[DiffOp K]
      ({j : κ // j ∉ C} → DiffOp K) where
  toFun w j := w j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq κ] in
@[simp] theorem complementCoordinateHasseRestriction_apply
    (C : Finset κ) (w : κ → DiffOp K) (j : {j : κ // j ∉ C}) :
    complementCoordinateHasseRestriction C w j = w j.1 := by
  rfl

omit [DecidableEq κ] in
/-- Simultaneous invisibility off `C` is exactly support inside `C`. -/
theorem complementCoordinateHasseRestriction_ker (C : Finset κ) :
    LinearMap.ker (complementCoordinateHasseRestriction (K := K) C) =
      coordSupport C := by
  ext w
  constructor
  · intro hw j hj
    exact congrFun (LinearMap.mem_ker.mp hw) ⟨j, hj⟩
  · intro hw
    apply LinearMap.mem_ker.mpr
    funext j
    exact hw j.1 j.2

/-- Every complementary local packet extends to a global coordinate vector. -/
theorem complementCoordinateHasseRestriction_surjective (C : Finset κ) :
    Function.Surjective (complementCoordinateHasseRestriction (K := K) C) := by
  intro u
  refine ⟨fun j => if hj : j ∈ C then 0 else u ⟨j, hj⟩, ?_⟩
  funext j
  exact dif_neg j.2

/-- Quotient by the exceptional coordinate sector equals the complete complementary packet. -/
noncomputable def complementCoordinateHasseQuotientEquiv (C : Finset κ) :
    ((κ → DiffOp K) ⧸ coordSupport C) ≃ₗ[DiffOp K]
      ({j : κ // j ∉ C} → DiffOp K) :=
  (Submodule.quotEquivOfEq _ _
    (complementCoordinateHasseRestriction_ker (K := K) C).symm).trans
      ((complementCoordinateHasseRestriction (K := K) C).quotKerEquivOfSurjective
        (complementCoordinateHasseRestriction_surjective (K := K) C))

@[simp] theorem complementCoordinateHasseQuotientEquiv_mk
    (C : Finset κ) (w : κ → DiffOp K) :
    complementCoordinateHasseQuotientEquiv (K := K) C
        (Submodule.Quotient.mk w) =
      complementCoordinateHasseRestriction C w := by
  rfl

omit [DecidableEq κ] in
/-- Complementary places determine global vectors modulo exceptional support. -/
theorem complementCoordinate_congr_hasse_iff
    (C : Finset κ) (x y : κ → DiffOp K) :
    x - y ∈ coordSupport C ↔
      ∀ j : {j : κ // j ∉ C}, x j.1 = y j.1 := by
  rw [← complementCoordinateHasseRestriction_ker (K := K) C,
    LinearMap.mem_ker, map_sub, sub_eq_zero]
  constructor
  · intro h j
    exact congrFun h j
  · intro h
    funext j
    exact h j

omit [DecidableEq κ] in
/-- A quotient class vanishes iff every complementary local coordinate vanishes. -/
theorem complementCoordinateClass_eq_zero_hasse_iff
    (C : Finset κ) (w : κ → DiffOp K) :
    Submodule.Quotient.mk w =
        (0 : (κ → DiffOp K) ⧸ coordSupport C) ↔
      ∀ j : {j : κ // j ∉ C}, w j.1 = 0 := by
  rw [Submodule.Quotient.mk_eq_zero,
    ← complementCoordinateHasseRestriction_ker (K := K) C,
    LinearMap.mem_ker]
  constructor
  · intro h j
    exact congrFun h j
  · intro h
    funext j
    exact h j

omit [DecidableEq κ] in
/-- Every nonzero quotient class has a complementary coordinate witness. -/
theorem complementCoordinateClass_ne_zero_iff_exists_witness
    (C : Finset κ) (w : κ → DiffOp K) :
    Submodule.Quotient.mk w ≠
        (0 : (κ → DiffOp K) ⧸ coordSupport C) ↔
      ∃ j : {j : κ // j ∉ C}, w j.1 ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    have hall : ∀ j : {j : κ // j ∉ C}, w j.1 = 0 := by
      intro j
      by_contra hj
      exact hn ⟨j, hj⟩
    exact h (complementCoordinateClass_eq_zero_hasse_iff C w |>.2 hall)
  · rintro ⟨j, hj⟩ hzero
    exact hj (complementCoordinateClass_eq_zero_hasse_iff C w |>.1 hzero j)

/-- Every complementary packet has one unique quotient class. -/
theorem complementCoordinatePacket_existsUnique_globalClass
    (C : Finset κ) (u : {j : κ // j ∉ C} → DiffOp K) :
    ∃! x : (κ → DiffOp K) ⧸ coordSupport C,
      complementCoordinateHasseQuotientEquiv (K := K) C x = u := by
  refine ⟨(complementCoordinateHasseQuotientEquiv (K := K) C).symm u,
    (complementCoordinateHasseQuotientEquiv (K := K) C).apply_symm_apply u, ?_⟩
  intro y hy
  apply (complementCoordinateHasseQuotientEquiv (K := K) C).injective
  rw [hy, (complementCoordinateHasseQuotientEquiv (K := K) C).apply_symm_apply]

/-- Every complementary packet has a global representative, unique modulo exceptional support. -/
theorem complementCoordinatePacket_exists_global_unique_mod_support
    (C : Finset κ) (u : {j : κ // j ∉ C} → DiffOp K) :
    ∃ w : κ → DiffOp K,
      complementCoordinateHasseRestriction C w = u ∧
        ∀ z, complementCoordinateHasseRestriction C z = u ↔
          z - w ∈ coordSupport C := by
  obtain ⟨w, hw⟩ :=
    complementCoordinateHasseRestriction_surjective (K := K) C u
  refine ⟨w, hw, fun z => ?_⟩
  rw [← hw, ← sub_eq_zero, ← map_sub,
    ← LinearMap.mem_ker,
    complementCoordinateHasseRestriction_ker (K := K) C]

end
end DiffOp
end GaloisForLFunctions.HTGeometry
