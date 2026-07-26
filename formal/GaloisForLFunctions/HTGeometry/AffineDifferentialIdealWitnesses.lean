import GaloisForLFunctions.HTGeometry.ParameterizedPrimitiveMaximalIdeal
import GaloisForLFunctions.HTGeometry.DifferentialHopfIdeal
import GaloisForLFunctions.HTGeometry.PrimitiveSystemWitnesses

/-!
# Realizations of the affine differential ideal interfaces

The trivial and full ideals are affine differential ideals: the derivation and the affine actions fix
zero, and the affine actions are ring equivalences, so they detect the zero ideal exactly.  Scale-two
stability holds for the same two ideals.  Compatible additive cocycles are realized by the defect data
of an arbitrary tuple, through the compatible-primitive bridge already in the corpus.
-/

namespace GaloisForLFunctions

variable {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]

/-! ## Affine differential ideals -/

theorem isAffineDifferentialIdeal_top
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K) :
    IsAffineDifferentialIdeal S a (⊤ : Ideal (DifferentialPolynomial κ K)) := by
  refine ⟨fun P _ => Submodule.mem_top, fun i P => ?_⟩
  exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩

theorem isAffineDifferentialIdeal_bot
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K) :
    IsAffineDifferentialIdeal S a (⊥ : Ideal (DifferentialPolynomial κ K)) := by
  refine ⟨?_, ?_⟩
  · intro P hP
    rw [Ideal.mem_bot] at hP
    subst hP
    rw [map_zero]
    exact Ideal.zero_mem _
  · intro i P
    rw [Ideal.mem_bot, Ideal.mem_bot]
    constructor
    · intro h
      have hzero : (differentialPolynomialAffineEquiv S a i) P = 0 := h
      have := (differentialPolynomialAffineEquiv S a i).injective
        (by rw [hzero, map_zero] :
          (differentialPolynomialAffineEquiv S a i) P =
            (differentialPolynomialAffineEquiv S a i) 0)
      exact this
    · intro h
      rw [h, map_zero]

/-! ## Scale-two stability -/

theorem isDifferentialPolynomialScaleTwoStable_bot :
    IsDifferentialPolynomialScaleTwoStable (⊥ : Ideal (DifferentialPolynomial ι C)) := by
  intro P hP
  rw [Ideal.mem_bot] at hP
  subst hP
  rw [map_zero]
  exact Ideal.zero_mem _

theorem isDifferentialPolynomialScaleTwoStable_top :
    IsDifferentialPolynomialScaleTwoStable (⊤ : Ideal (DifferentialPolynomial ι C)) :=
  fun _ _ => Submodule.mem_top

/-! ## Compatible additive cocycles -/

/-- The defect data of an arbitrary tuple is a compatible additive cocycle. -/
theorem compatibleAdditiveCocycle_defect
    (S : CommutingDifferenceDifferentialField ι C K) (y : κ → K) :
    CompatibleAdditiveCocycle S (fun i k => S.defect i (y k)) :=
  CompatiblePrimitiveSystem.toCompatibleAdditiveCocycle S
    (compatiblePrimitiveSystem_defect S y)

end GaloisForLFunctions
