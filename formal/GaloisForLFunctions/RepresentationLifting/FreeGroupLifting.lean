import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Free-group representations over successive ideal-power quotients

Reduction of general linear groups from `R / I^(n+2)` to `R / I^(n+1)` is surjective.
Entrywise lifts remain invertible because their determinants are units modulo a nilpotent
ideal. Lifting free generators then lifts every free-group representation.

This supplies actual representation lifts for the free-group setting of vanishing second
cohomology, using the reduction extension underlying Scavia's lifting obstruction.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

variable {R ι α : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Reduction of invertible matrices through one positive ideal-power step. -/
def idealPowerGLReduction (I : Ideal R) (n : ℕ) :
    (Matrix ι ι (R ⧸ I ^ (n + 2)))ˣ →* (Matrix ι ι (R ⧸ I ^ (n + 1)))ˣ :=
  Units.map (Ideal.Quotient.factorPowSucc I (n + 1)).mapMatrix.toMonoidHom

/-- Every invertible matrix lifts across a successive ideal-power quotient. -/
theorem idealPowerGLReduction_surjective (I : Ideal R) (n : ℕ) :
    Function.Surjective (idealPowerGLReduction (ι := ι) I n) := by
  intro u
  let q := Ideal.Quotient.factorPowSucc I (n + 1)
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective _
  let B : Matrix ι ι (R ⧸ I ^ (n + 2)) := fun i j =>
    Classical.choose (hq ((u : Matrix ι ι (R ⧸ I ^ (n + 1))) i j))
  have hB : q.mapMatrix B = (u : Matrix ι ι (R ⧸ I ^ (n + 1))) := by
    ext i j
    exact Classical.choose_spec (hq ((u : Matrix ι ι (R ⧸ I ^ (n + 1))) i j))
  have hdet : IsUnit B.det := by
    apply factorPowSucc.isUnit_of_isUnit_image (Nat.succ_pos n)
    rw [q.map_det, hB]
    exact (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr hdet
  refine ⟨hunit.unit, ?_⟩
  apply Units.ext
  change q.mapMatrix (hunit.unit : Matrix ι ι (R ⧸ I ^ (n + 2))) = _
  rw [hunit.unit_spec, hB]

/-- Every free-group representation lifts through every positive ideal-power step. -/
theorem freeGroup_representation_lifts (I : Ideal R) (n : ℕ)
    (ρ : FreeGroup α →* (Matrix ι ι (R ⧸ I ^ (n + 1)))ˣ) :
    ∃ ρ' : FreeGroup α →* (Matrix ι ι (R ⧸ I ^ (n + 2)))ˣ,
      (idealPowerGLReduction I n).comp ρ' = ρ := by
  let f : α → (Matrix ι ι (R ⧸ I ^ (n + 2)))ˣ := fun a =>
    Classical.choose (idealPowerGLReduction_surjective I n (ρ (FreeGroup.of a)))
  refine ⟨FreeGroup.lift f, ?_⟩
  apply FreeGroup.ext_hom
  intro a
  change idealPowerGLReduction I n (FreeGroup.lift f (FreeGroup.of a)) = _
  rw [FreeGroup.lift_apply_of]
  exact Classical.choose_spec (idealPowerGLReduction_surjective I n (ρ (FreeGroup.of a)))

/-- A chosen lift through one ideal-power step. -/
def freeGroupLiftStep (I : Ideal R) (n : ℕ)
    (ρ : FreeGroup α →* (Matrix ι ι (R ⧸ I ^ (n + 1)))ˣ) :
    FreeGroup α →* (Matrix ι ι (R ⧸ I ^ (n + 2)))ˣ :=
  Classical.choose (freeGroup_representation_lifts I n ρ)

theorem freeGroupLiftStep_reduces (I : Ideal R) (n : ℕ)
    (ρ : FreeGroup α →* (Matrix ι ι (R ⧸ I ^ (n + 1)))ˣ) :
    (idealPowerGLReduction I n).comp (freeGroupLiftStep I n ρ) = ρ :=
  Classical.choose_spec (freeGroup_representation_lifts I n ρ)

/-- A compatible tower lifting an initial representation through every positive ideal power. -/
def freeGroupLiftTower (I : Ideal R)
    (ρ : FreeGroup α →* (Matrix ι ι (R ⧸ I ^ 1))ˣ) :
    (n : ℕ) → FreeGroup α →* (Matrix ι ι (R ⧸ I ^ (n + 1)))ˣ
  | 0 => ρ
  | n + 1 => freeGroupLiftStep I n (freeGroupLiftTower I ρ n)

@[simp] theorem freeGroupLiftTower_zero (I : Ideal R)
    (ρ : FreeGroup α →* (Matrix ι ι (R ⧸ I ^ 1))ˣ) :
    freeGroupLiftTower I ρ 0 = ρ := rfl

/-- Successive representations in the tower reduce to one another. -/
theorem freeGroupLiftTower_compatible (I : Ideal R)
    (ρ : FreeGroup α →* (Matrix ι ι (R ⧸ I ^ 1))ˣ) (n : ℕ) :
    (idealPowerGLReduction I n).comp (freeGroupLiftTower I ρ (n + 1)) =
      freeGroupLiftTower I ρ n :=
  freeGroupLiftStep_reduces I n _

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.idealPowerGLReduction_surjective
#print axioms GaloisForLFunctions.RepresentationLifting.freeGroup_representation_lifts
#print axioms GaloisForLFunctions.RepresentationLifting.freeGroupLiftTower_compatible
