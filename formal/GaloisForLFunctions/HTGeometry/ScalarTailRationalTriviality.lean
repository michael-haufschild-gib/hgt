import GaloisForLFunctions.HTGeometry.ScalarInfiniteScaleFixedField
import GaloisForLFunctions.HTGeometry.HypertranscendentalPow

/-!
# The current field meets the rational field of the amplitude only in constants

On the rank-one torsor the logarithmic-current field `F⟨q'/q⟩` and the ordinary rational field
`F(q)` of the amplitude are both subfields of `T`, and they intersect trivially: an element of the
current field is fixed by every constant rescaling of the amplitude, and a rational function of the
amplitude fixed by infinitely many rescalings is constant.

So the surviving velocity sector carries full differential transcendence degree while containing no
nonconstant rational function of the position.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {F T : Type*} [Field F] [Field T] [Algebra F T]
  [Differential F] [Differential T] [DifferentialAlgebra F T]
  [CharZero T]

/-- The successive natural-number units of a characteristic-zero field. -/
def natSuccUnit (F : Type*) [Field F] [CharZero F] (n : ℕ) : Fˣ :=
  Units.mk0 ((n : F) + 1) (Nat.cast_add_one_ne_zero n)

theorem natSuccUnit_injective (F : Type*) [Field F] [CharZero F] :
    Function.Injective (natSuccUnit F) := by
  intro m n hmn
  have hval : ((m : F) + 1) = ((n : F) + 1) := congrArg Units.val hmn
  exact Nat.cast_injective (add_right_cancel hval)

theorem infinite_range_natSuccUnit (F : Type*) [Field F] [CharZero F] :
    (Set.range (natSuccUnit F)).Infinite :=
  Set.infinite_range_of_injective (natSuccUnit_injective F)

/-- **The current field meets the rational field of the amplitude only in the constants.** -/
theorem scalarLogCurrentField_inf_adjoin_eq_bot
    (q : T) (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F] :
    scalarLogCurrentField F q ⊓ IntermediateField.adjoin F ({q} : Set T) = ⊥ := by
  have htr : Transcendental F q :=
    transcendental_of_differentialIndependent
      ((hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq)
  set A : IntermediateField F T := IntermediateField.adjoin F ({q} : Set T) with hA
  let e0 : RatFunc F ≃ₐ[F] A := RatFunc.algEquivOfTranscendental q htr
  let φ : RatFunc F →ₐ[F] T := A.val.comp e0.toAlgHom
  have hφX : φ RatFunc.X = q := by
    have hX := RatFunc.algEquivOfTranscendental_X (K := F) q htr
    simp only [φ, e0, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, IntermediateField.coe_val]
    rw [hX]
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hequiv : ∀ (u : Fˣ) (r : RatFunc F),
      scalarDifferentialScaleEquiv q hq hgen u (φ r) = φ (ratFuncUnitScaleAction u r) := by
    intro u
    have hcomp : (scalarDifferentialScaleEquiv q hq hgen u).toAlgHom.comp φ
        = φ.comp (ratFuncUnitScaleAction u).toAlgHom := by
      apply ratFunc_algHom_ext
      change scalarDifferentialScaleEquiv q hq hgen u (φ RatFunc.X)
        = φ (ratFuncUnitScaleAction u RatFunc.X)
      rw [hφX, ratFuncUnitScaleAction_apply_X, map_mul, hφX,
        scalarDifferentialScaleEquiv_apply_q]
      rw [AlgHom.commutes, mul_comm]
    exact fun r ↦ AlgHom.congr_fun hcomp r
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨hzL, hzA⟩ := hz
  obtain ⟨r, hr⟩ : ∃ r : RatFunc F, φ r = z := by
    refine ⟨e0.symm ⟨z, hzA⟩, ?_⟩
    change ((e0 (e0.symm ⟨z, hzA⟩) : A) : T) = z
    rw [AlgEquiv.apply_symm_apply]
  have hfix : ∀ u ∈ Set.range (natSuccUnit F), ratFuncUnitScaleAction u r = r := by
    rintro u -
    apply hφinj
    rw [← hequiv, hr]
    exact scalarDifferentialScaleEquiv_fixed_on_currentField q hq hq0 hgen hconst u ⟨z, hzL⟩
  obtain ⟨c, hc⟩ :=
    ratFuncUnitScale_fixed_eq_constant_of_infinite (infinite_range_natSuccUnit F) hfix
  have hzc : z = algebraMap F T c := by
    rw [← hr, hc]
    exact φ.commutes c
  rw [hzc]
  exact (⊥ : IntermediateField F T).algebraMap_mem c

end

end GaloisForLFunctions.HTGeometry
