/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.OmegaObstruction

/-!
# Cohomological Hasse exactness for section defects

The global one-cochain coboundary map, closed local two-cochains, and second constraint
cohomology form an exact right-surjective sequence.  Thus local section-defect data arise from one
global choice exactly when their cocycle lies in the coboundary range, equivalently when their
obstruction class vanishes.  This is a cohomological Hasse principle independent of arithmetic
places.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- Coboundary operator bundled as an additive map from global one-cochains to closed local
two-cochains. -/
def twoCoboundaryCocycleAddHom : (G → A) →+ twoCocycles (G := G) (A := A) where
  toFun := twoCoboundaryCocycle
  map_zero' := twoCoboundaryCocycle_zero
  map_add' := twoCoboundaryCocycle_add

@[simp] theorem twoCoboundaryCocycleAddHom_apply (b : G → A) :
    twoCoboundaryCocycleAddHom b = twoCoboundaryCocycle b := rfl

/-- Canonical additive obstruction map from cocycles to second constraint cohomology. -/
def obstructionClassAddHom :
    twoCocycles (G := G) (A := A) →+
      secondConstraintCohomology (G := G) (A := A) :=
  QuotientAddGroup.mk' (twoCoboundaries (G := G) (A := A))

@[simp] theorem obstructionClassAddHom_apply
    (omega : twoCocycles (G := G) (A := A)) :
    obstructionClassAddHom omega = obstructionClass omega := rfl

/-- Global one-cochains, closed local two-cochains, and obstruction classes are exact. -/
theorem twoCoboundaryCocycle_obstructionClass_exact :
    Function.Exact
      (twoCoboundaryCocycleAddHom (G := G) (A := A))
      (obstructionClassAddHom (G := G) (A := A)) := by
  intro omega
  change obstructionClass omega = 0 ↔
    omega ∈ Set.range (twoCoboundaryCocycleAddHom (G := G) (A := A))
  rw [obstructionClass_eq_zero_iff_exists_cochain]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.symm⟩

/-- Every second-cohomology obstruction class has a closed local cocycle representative. -/
theorem obstructionClassAddHom_surjective :
    Function.Surjective (obstructionClassAddHom (G := G) (A := A)) :=
  QuotientAddGroup.mk'_surjective (twoCoboundaries (G := G) (A := A))

/-- The cohomological local--global Hasse sequence is exact and right-surjective. -/
theorem omegaHasseSequence_exact_surjective :
    Function.Exact
        (twoCoboundaryCocycleAddHom (G := G) (A := A))
        (obstructionClassAddHom (G := G) (A := A)) ∧
      Function.Surjective (obstructionClassAddHom (G := G) (A := A)) :=
  ⟨twoCoboundaryCocycle_obstructionClass_exact,
    obstructionClassAddHom_surjective⟩

/-- Cocycles modulo globally induced coboundaries are exactly obstruction classes. -/
noncomputable def omegaHasseCocycleQuotientEquivObstruction :
    twoCocycles (G := G) (A := A) ⧸
        (twoCoboundaryCocycleAddHom (G := G) (A := A)).range ≃+
      secondConstraintCohomology (G := G) (A := A) := by
  have hker : (obstructionClassAddHom (G := G) (A := A)).ker =
      (twoCoboundaryCocycleAddHom (G := G) (A := A)).range := by
    have hexact := twoCoboundaryCocycle_obstructionClass_exact (G := G) (A := A)
    rw [AddMonoidHom.exact_iff] at hexact
    exact hexact
  exact (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (obstructionClassAddHom (G := G) (A := A))
      (obstructionClassAddHom_surjective (G := G) (A := A)))

/-- Evaluation of the Hasse quotient equivalence is the original obstruction class. -/
theorem omegaHasseCocycleQuotientEquivObstruction_mk
    (omega : twoCocycles (G := G) (A := A)) :
    omegaHasseCocycleQuotientEquivObstruction
        (QuotientAddGroup.mk omega) = obstructionClass omega := by
  simp [omegaHasseCocycleQuotientEquivObstruction]
  change QuotientAddGroup.kerLift
      (obstructionClassAddHom (G := G) (A := A))
      (QuotientAddGroup.mk omega) = obstructionClass omega
  rfl

/-- Section-defect Hasse criterion: local section data come from one global choice exactly when
their closed cocycle lies in the global coboundary range, equivalently when obstruction vanishes. -/
theorem SectionDefect.exists_global_choice_iff_cocycle_mem_coboundary_range
    (D : SectionDefect G A) :
    (∃ b : G → A, D.defect = twoCoboundary b) ↔
      D.cocycle ∈ (twoCoboundaryCocycleAddHom (G := G) (A := A)).range := by
  rw [← D.obstruction_eq_zero_iff_exists_global_choice]
  exact (twoCoboundaryCocycle_obstructionClass_exact (G := G) (A := A) D.cocycle)

end GaloisForLFunctions.RHTower
