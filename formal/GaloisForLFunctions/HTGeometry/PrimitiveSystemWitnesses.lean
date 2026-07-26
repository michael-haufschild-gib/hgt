import GaloisForLFunctions.HTGeometry.ParameterizedPrimitiveQuotient
import GaloisForLFunctions.HTGeometry.ParameterizedPrimitiveAction

/-!
# Realizations of the compatible-primitive and quotient-ideal interfaces

Compatibility of a primitive system is a naming condition: the defect data of an arbitrary tuple is
compatible with itself, so the interface is realized by every tuple.  Over a field extension it
becomes a descent condition, satisfied by the zero tuple.  Stability of an ideal in the affine
differential quotient is realized by the trivial and full ideals, the trivial case because the
induced affine actions are ring equivalences.
-/

open scoped Differential

namespace GaloisForLFunctions

/-! ## Defect data -/

theorem CommutingDifferenceDifferentialField.defect_zero
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (i : ι) :
    S.defect i 0 = 0 := by
  rw [CommutingDifferenceDifferentialField.defect, map_zero, sub_zero]

/-- **Every tuple is a compatible primitive system for its own defect data.** -/
theorem compatiblePrimitiveSystem_defect
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (y : κ → K) :
    CompatiblePrimitiveSystem S y (fun i k => S.defect i (y k)) :=
  fun _ _ => rfl

/-- The zero tuple realizes the extension-compatibility interface. -/
theorem compatiblePrimitiveExtensionSystem_zero
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [Differential K] [Differential L]
    (SL : CommutingDifferenceDifferentialField ι C L) :
    CompatiblePrimitiveExtensionSystem SL (fun _ : κ => (0 : L))
      (fun _ _ => (0 : K)) := by
  intro i k
  rw [SL.defect_zero i, map_zero]

/-! ## Quotient affine differential ideals -/

theorem isQuotientAffineDifferentialIdeal_bot
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) :
    IsQuotientAffineDifferentialIdeal S a I hI ⊥ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Ideal.mem_bot] at hx
    subst hx
    rw [map_zero]
    exact Ideal.zero_mem _
  · intro i x
    rw [Ideal.mem_bot, Ideal.mem_bot]
    exact map_eq_zero_iff _
      (differentialPolynomialQuotientAffineEquiv S a I hI i).injective

theorem isQuotientAffineDifferentialIdeal_top
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K))
    (hI : IsAffineDifferentialIdeal S a I) :
    IsQuotientAffineDifferentialIdeal S a I hI ⊤ := by
  refine ⟨fun x _ => Submodule.mem_top, fun i x => ?_⟩
  simp

end GaloisForLFunctions
