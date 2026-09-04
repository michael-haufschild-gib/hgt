import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Complex.Basic

/-!
# Cubic clock extension lifting obstruction

An ordinary linear quotient forgets ideal-valued changes of splitting.  Once source and
completion clocks are retained, the cube of the clock defines a finer lifting problem.  The
failure of a lift to intertwine the cubic clocks lands in the completion ideal.  Its class modulo
ideal-valued cubic changes of splitting is independent of the chosen lift, and it vanishes exactly
when an ideal correction makes the lift cubic-equivariant.
-/

namespace GaloisForLFunctions.HTGeometry


variable {X E : Type*}
variable [AddCommGroup X] [Module ℂ X]
variable [AddCommGroup E] [Module ℂ E]

/-- Third iterate of a linear clock. -/
def linearClockCube {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  D.comp (D.comp D)

@[simp]
theorem linearClockCube_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) (x : V) :
    linearClockCube D x = D (D (D x)) := by
  rfl

/-- A completion quotient carrying compatible source, total, and quotient clocks.  The quotient
landing is required to intertwine the cubes of the clocks; no lift is chosen in this datum. -/
structure CubicClockCompletion where
  ideal : Submodule ℂ E
  sourceClock : X →ₗ[ℂ] X
  totalClock : E →ₗ[ℂ] E
  quotientClock : (E ⧸ ideal) →ₗ[ℂ] (E ⧸ ideal)
  quotientLanding : X →ₗ[ℂ] (E ⧸ ideal)
  quotientClock_mkQ : ∀ y : E,
    quotientClock (ideal.mkQ y) = ideal.mkQ (totalClock y)
  quotientLanding_cubic :
    (linearClockCube quotientClock).comp quotientLanding =
      quotientLanding.comp (linearClockCube sourceClock)

namespace CubicClockCompletion

variable (C : CubicClockCompletion (X := X) (E := E))

/-- A linear lift of the fixed quotient landing. -/
structure Lift where
  toLinearMap : X →ₗ[ℂ] E
  mkQ_comp : C.ideal.mkQ.comp toLinearMap = C.quotientLanding

namespace Lift

variable {C : CubicClockCompletion (X := X) (E := E)}

/-- Ambient failure of a lift to intertwine the cubic source and completion clocks. -/
def ambientCubicDefect (F : C.Lift) : X →ₗ[ℂ] E :=
  (linearClockCube C.totalClock).comp F.toLinearMap -
    F.toLinearMap.comp (linearClockCube C.sourceClock)

@[simp]
theorem ambientCubicDefect_apply (F : C.Lift) (x : X) :
    F.ambientCubicDefect x =
      C.totalClock (C.totalClock (C.totalClock (F.toLinearMap x))) -
        F.toLinearMap (C.sourceClock (C.sourceClock (C.sourceClock x))) := by
  rfl

/-- The cubic defect of every quotient lift lands in the completion ideal. -/
theorem ambientCubicDefect_mem_ideal (F : C.Lift) (x : X) :
    F.ambientCubicDefect x ∈ C.ideal := by
  rw [← Submodule.Quotient.mk_eq_zero]
  change C.ideal.mkQ
      (C.totalClock (C.totalClock (C.totalClock (F.toLinearMap x))) -
        F.toLinearMap (C.sourceClock (C.sourceClock (C.sourceClock x)))) = 0
  rw [map_sub, ← C.quotientClock_mkQ, ← C.quotientClock_mkQ,
    ← C.quotientClock_mkQ]
  have hFx : C.ideal.mkQ (F.toLinearMap x) = C.quotientLanding x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun F.mkQ_comp x
  have hFcube :
      C.ideal.mkQ
          (F.toLinearMap (C.sourceClock (C.sourceClock (C.sourceClock x)))) =
        C.quotientLanding
          (C.sourceClock (C.sourceClock (C.sourceClock x))) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun F.mkQ_comp
      (C.sourceClock (C.sourceClock (C.sourceClock x)))
  rw [hFx, hFcube]
  have hlanding := LinearMap.congr_fun C.quotientLanding_cubic x
  simpa using sub_eq_zero.mpr hlanding

/-- Ideal-valued cubic lifting defect. -/
def cubicDefect (F : C.Lift) : X →ₗ[ℂ] C.ideal :=
  LinearMap.codRestrict C.ideal F.ambientCubicDefect F.ambientCubicDefect_mem_ideal

@[simp]
theorem ideal_subtype_cubicDefect (F : C.Lift) :
    C.ideal.subtype.comp F.cubicDefect = F.ambientCubicDefect := by
  rfl

/-- Inclusion of an ideal-valued correction into the total completion carrier. -/
def includeCorrection (H : X →ₗ[ℂ] C.ideal) : X →ₗ[ℂ] E :=
  C.ideal.subtype.comp H

/-- Compatibility with the quotient forces the total clock to preserve the completion ideal. -/
theorem totalClock_mem_ideal (z : C.ideal) : C.totalClock (z : E) ∈ C.ideal := by
  apply (Submodule.Quotient.mk_eq_zero C.ideal).mp
  change C.ideal.mkQ (C.totalClock (z : E)) = 0
  rw [← C.quotientClock_mkQ]
  have hz : C.ideal.mkQ (z : E) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact z.property
  rw [hz, map_zero]

/-- Clock induced on the completion ideal. -/
def idealClock : C.ideal →ₗ[ℂ] C.ideal :=
  LinearMap.codRestrict C.ideal (C.totalClock.domRestrict C.ideal)
    (totalClock_mem_ideal (C := C))

@[simp]
theorem idealClock_coe (z : C.ideal) :
    (idealClock (C := C) z : E) = C.totalClock z := by
  rfl

/-- Every ideal-valued correction has an ideal-valued cubic coboundary. -/
def cubicCoboundaryValue (H : X →ₗ[ℂ] C.ideal) : X →ₗ[ℂ] C.ideal :=
  (linearClockCube (idealClock (C := C))).comp H -
    H.comp (linearClockCube C.sourceClock)

/-- Cubic coboundary operator on ideal-valued changes of splitting. -/
def cubicCoboundary : (X →ₗ[ℂ] C.ideal) →ₗ[ℂ] (X →ₗ[ℂ] C.ideal) where
  toFun := cubicCoboundaryValue
  map_add' H K := by
    apply LinearMap.ext
    intro x
    simp only [cubicCoboundaryValue, LinearMap.sub_apply, LinearMap.comp_apply,
      linearClockCube_apply, LinearMap.add_apply, map_add]
    abel
  map_smul' r H := by
    apply LinearMap.ext
    intro x
    simp only [cubicCoboundaryValue, LinearMap.sub_apply, LinearMap.comp_apply,
      linearClockCube_apply, LinearMap.smul_apply, map_smul, smul_sub]
    rfl

/-- Cohomology space in which the cubic lifting obstruction lives. -/
abbrev CubicLiftingCohomology :=
  (X →ₗ[ℂ] C.ideal) ⧸ LinearMap.range (cubicCoboundary (C := C))

/-- Cubic source-equivariant deformation class of a chosen completion lift. -/
def cubicLiftingClass (F : C.Lift) : CubicLiftingCohomology (C := C) :=
  (LinearMap.range (cubicCoboundary (C := C))).mkQ F.cubicDefect

/-- Correct a lift by an arbitrary ideal-valued map. -/
def corrected (F : C.Lift) (H : X →ₗ[ℂ] C.ideal) : C.Lift where
  toLinearMap := F.toLinearMap + includeCorrection H
  mkQ_comp := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [map_add]
    have hF : C.ideal.mkQ (F.toLinearMap x) = C.quotientLanding x := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun F.mkQ_comp x
    rw [hF]
    have hzero : C.ideal.mkQ (H x : E) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (H x).property
    rw [includeCorrection, LinearMap.comp_apply, Submodule.coe_subtype, hzero, add_zero]

/-- Exact gauge law: changing a lift adds the cubic coboundary of the correction. -/
theorem cubicDefect_corrected (F : C.Lift) (H : X →ₗ[ℂ] C.ideal) :
    (F.corrected H).cubicDefect =
      F.cubicDefect + cubicCoboundary (C := C) H := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change
    C.totalClock
          (C.totalClock
            (C.totalClock (F.toLinearMap x + (H x : E)))) -
        (F.toLinearMap (C.sourceClock (C.sourceClock (C.sourceClock x))) +
          (H (C.sourceClock (C.sourceClock (C.sourceClock x))) : E)) =
      (C.totalClock (C.totalClock (C.totalClock (F.toLinearMap x))) -
          F.toLinearMap (C.sourceClock (C.sourceClock (C.sourceClock x)))) +
        (C.totalClock (C.totalClock (C.totalClock (H x : E))) -
          (H (C.sourceClock (C.sourceClock (C.sourceClock x))) : E))
  simp only [map_add]
  abel

/-- The cubic lifting class is independent of ideal-valued change of splitting. -/
theorem cubicLiftingClass_corrected (F : C.Lift) (H : X →ₗ[ℂ] C.ideal) :
    (F.corrected H).cubicLiftingClass = F.cubicLiftingClass := by
  rw [cubicLiftingClass, cubicLiftingClass, cubicDefect_corrected, map_add]
  have hcob :
      (LinearMap.range (cubicCoboundary (C := C))).mkQ
          (cubicCoboundary (C := C) H) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨H, rfl⟩
  rw [hcob, add_zero]

/-- Vanishing of the class is equivalent to existence of an ideal correction making the lift
exactly cubic-equivariant. -/
theorem cubicLiftingClass_eq_zero_iff (F : C.Lift) :
    F.cubicLiftingClass = 0 ↔
      ∃ H : X →ₗ[ℂ] C.ideal, (F.corrected H).cubicDefect = 0 := by
  constructor
  · intro hclass
    rw [cubicLiftingClass, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hclass
    obtain ⟨K, hK⟩ := hclass
    refine ⟨-K, ?_⟩
    rw [cubicDefect_corrected, map_neg, hK, add_neg_cancel]
  · rintro ⟨H, hzero⟩
    rw [← cubicLiftingClass_corrected F H]
    rw [cubicLiftingClass, hzero, map_zero]

/-- Exact cubic transgression identity.  Cubic source boundary, completed lift, and ideal anomaly
are three terms of one conservation law. -/
theorem cubicCompletion_transgression (F : C.Lift) (x : X) :
    linearClockCube C.totalClock (F.toLinearMap x) =
      F.toLinearMap (linearClockCube C.sourceClock x) +
        C.ideal.subtype (F.cubicDefect x) := by
  change C.totalClock (C.totalClock (C.totalClock (F.toLinearMap x))) =
    F.toLinearMap (C.sourceClock (C.sourceClock (C.sourceClock x))) +
      C.ideal.subtype (F.cubicDefect x)
  have hdef := congrArg (fun G : X →ₗ[ℂ] E => G x)
    (F.ideal_subtype_cubicDefect)
  change C.ideal.subtype (F.cubicDefect x) =
    C.totalClock (C.totalClock (C.totalClock (F.toLinearMap x))) -
      F.toLinearMap (C.sourceClock (C.sourceClock (C.sourceClock x))) at hdef
  rw [hdef]
  abel

end Lift

end CubicClockCompletion

/-! ## A split linear extension with nonzero cubic refinement -/

/-- Unipotent clock on a split two-coordinate completion. -/
def unipotentCompletionClock : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z := (z.1 + z.2, z.2)
  map_add' x y := by ext <;> simp [add_left_comm, add_comm]
  map_smul' r x := by ext <;> simp [mul_add]

/-- All scalar lifts of the second-coordinate quotient landing. -/
def unipotentCompletionLift (h : ℂ) : ℂ →ₗ[ℂ] (ℂ × ℂ) where
  toFun z := (h * z, z)
  map_add' x y := by ext <;> simp [mul_add]
  map_smul' r x := by ext <;> simp [mul_left_comm]

@[simp]
theorem unipotentCompletionClock_apply (z : ℂ × ℂ) :
    unipotentCompletionClock z = (z.1 + z.2, z.2) := by
  rfl

@[simp]
theorem unipotentCompletionLift_apply (h z : ℂ) :
    unipotentCompletionLift h z = (h * z, z) := by
  rfl

/-- The cube of the unipotent completion clock adds exactly three copies of the quotient
coordinate. -/
theorem linearClockCube_unipotentCompletionClock (z : ℂ × ℂ) :
    linearClockCube unipotentCompletionClock z = (z.1 + 3 * z.2, z.2) := by
  simp [linearClockCube]
  ring

/-- Every lift of the displayed scalar family has the same nonzero cubic defect. -/
theorem unipotentCompletionLift_cubicDefect (h z : ℂ) :
    linearClockCube unipotentCompletionClock (unipotentCompletionLift h z) -
        unipotentCompletionLift h (linearClockCube LinearMap.id z) =
      (3 * z, 0) := by
  rw [linearClockCube_unipotentCompletionClock]
  simp [linearClockCube]

/-- With identity clocks on source and ideal, every cubic splitting coboundary vanishes. -/
theorem identityClock_cubicCoboundary_zero (H : ℂ →ₗ[ℂ] ℂ) :
    (linearClockCube LinearMap.id).comp H -
        H.comp (linearClockCube LinearMap.id) = 0 := by
  apply LinearMap.ext
  intro z
  simp [linearClockCube]

/-- No scalar lift of the split second-coordinate quotient is cubic-equivariant. -/
theorem not_exists_unipotentCompletionLift_cubicEquivariant :
    ¬ ∃ h : ℂ,
      (linearClockCube unipotentCompletionClock).comp (unipotentCompletionLift h) =
        (unipotentCompletionLift h).comp (linearClockCube LinearMap.id) := by
  rintro ⟨h, heq⟩
  have hpoint := LinearMap.congr_fun heq (1 : ℂ)
  have hdef := unipotentCompletionLift_cubicDefect h 1
  rw [show linearClockCube unipotentCompletionClock (unipotentCompletionLift h 1) =
      unipotentCompletionLift h (linearClockCube LinearMap.id 1) by
        simpa [LinearMap.comp_apply] using hpoint] at hdef
  have hfirst := congrArg Prod.fst hdef
  norm_num at hfirst

end GaloisForLFunctions.HTGeometry

