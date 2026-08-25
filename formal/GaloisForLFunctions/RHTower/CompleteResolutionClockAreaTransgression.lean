import GaloisForLFunctions.RHTower.CompleteResolutionCofinalConditioningLaw
import GaloisForLFunctions.RHTower.DeningerRelationKernelTransgression

/-!
# Complete-source clock area survives only by cohomological degree shift

The complete Riemann source has two explicit label-sensitive reader directions.  Their source
inputs converge to zero, while their outputs span a two-dimensional clock plane and have nonzero
oriented area.  Consequently every closed linear relation retaining both clocks has full vertical
fibre.  This file proves the sharper descent consequence: every linear observer constant on the
output fibres of that relation is zero.

The lost orientation is not zero.  Its determinant defines a nonzero alternating normalized
two-cocycle on the same clock plane.  On a free rational presentation this cocycle becomes exact,
but every primitive has nonzero restriction to the presentation kernel.  Thus the first viable
post-collapse carrier is not another degree-zero quotient observer; it is a degree-one
relation-kernel transgression of degree-two source orientation.

This is an unconditional framework constraint, not an RH equivalence and not a construction of
the missing global arithmetic annihilation law.
-/

open Complex

namespace RHTower

noncomputable section

/-- Oriented area cocycle of the two persistent complete-source clocks. -/
def completeResolutionClockAreaCocycle :
    DeningerNormalizedCocycle (Multiplicative (ℂ × ℂ)) ℂ where
  f x :=
    x.1.toAdd.1 * x.2.toAdd.2 - x.1.toAdd.2 * x.2.toAdd.1
  cocycle g h j := by
    change
      ((g.toAdd + h.toAdd).1 * j.toAdd.2 -
          (g.toAdd + h.toAdd).2 * j.toAdd.1) +
        (g.toAdd.1 * h.toAdd.2 - g.toAdd.2 * h.toAdd.1) =
      (h.toAdd.1 * j.toAdd.2 - h.toAdd.2 * j.toAdd.1) +
        (g.toAdd.1 * (h.toAdd + j.toAdd).2 -
          g.toAdd.2 * (h.toAdd + j.toAdd).1)
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  one_fst g := by simp
  one_snd g := by simp

/-- The clock-area cocycle is alternating. -/
theorem completeResolutionClockAreaCocycle_alternating :
    completeResolutionClockAreaCocycle.IsAlternating := by
  intro x y
  change
    x.toAdd.1 * y.toAdd.2 - x.toAdd.2 * y.toAdd.1 =
      -(y.toAdd.1 * x.toAdd.2 - y.toAdd.2 * x.toAdd.1)
  ring

/-- Its value on the two actual persistent source-reader directions is nonzero. -/
theorem completeResolutionClockAreaCocycle_persistentOutputs :
    completeResolutionClockAreaCocycle.f
        (Multiplicative.ofAdd completeResolutionVerticalFirstOutput,
          Multiplicative.ofAdd completeResolutionVerticalSecondOutput) =
      -(1 / 18 : ℂ) := by
  simpa [completeResolutionClockAreaCocycle] using
    completeResolutionVerticalOutput_determinant

/-- The complete-source clock-area class is not zero. -/
theorem completeResolutionClockAreaCocycle_ne_zero :
    ¬ ∀ x y, completeResolutionClockAreaCocycle.f (x, y) = 0 := by
  intro hzero
  have h := hzero
    (Multiplicative.ofAdd completeResolutionVerticalFirstOutput)
    (Multiplicative.ofAdd completeResolutionVerticalSecondOutput)
  rw [completeResolutionClockAreaCocycle_persistentOutputs] at h
  norm_num at h

/-- A linear output observer descends through a relation when it is constant on each output
fibre over a fixed source. -/
def LinearRelationOutputDescends
    {𝕜 X Y Z : Type*} [Semiring 𝕜]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (R : Submodule 𝕜 (X × Y)) (q : Y →ₗ[𝕜] Z) : Prop :=
  ∀ x y₁ y₂, (x, y₁) ∈ R → (x, y₂) ∈ R → q y₁ = q y₂

/-- Full vertical fibre annihilates every fibre-descending linear output observer. -/
theorem linearRelationOutputDescends_eq_zero_of_fullVertical
    {𝕜 X Y Z : Type*} [Semiring 𝕜]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (R : Submodule 𝕜 (X × Y))
    (hvertical : ∀ y : Y, ((0 : X), y) ∈ R)
    (q : Y →ₗ[𝕜] Z) (hdescends : LinearRelationOutputDescends R q) :
    q = 0 := by
  ext y
  have h := hdescends 0 y 0 (hvertical y) R.zero_mem
  simpa using h

/-- Every linear observer descending through the closed complete-source two-clock relation is
zero. -/
theorem completeResolution_twoClock_descendedLinearObserver_eq_zero
    {Z : Type*} [AddCommMonoid Z] [Module ℂ Z]
    (R : Submodule ℂ (CompleteResolutionSourceSpace × (ℂ × ℂ)))
    (hclosed : IsClosed (R : Set (CompleteResolutionSourceSpace × (ℂ × ℂ))))
    (hfirst : ∀ K : ℕ,
      (completeResolutionVerticalFirstInput K,
        completeResolutionVerticalFirstOutput) ∈ R)
    (hsecond : ∀ K : ℕ,
      (completeResolutionVerticalSecondInput K,
        completeResolutionVerticalSecondOutput) ∈ R)
    (q : (ℂ × ℂ) →ₗ[ℂ] Z)
    (hdescends : LinearRelationOutputDescends R q) :
    q = 0 := by
  apply linearRelationOutputDescends_eq_zero_of_fullVertical R _ q hdescends
  intro y
  exact completeResolution_closedLinearRelation_fullVertical
    R hclosed hfirst hsecond y

/-- The nonzero clock area survives the collapse after one cohomological degree shift, as a
nonzero character on the relation kernel of a free rational presentation. -/
theorem exists_completeResolutionClockArea_nonzero_relationKernelTransgression :
    let basis := Module.Free.chooseBasis ℚ (ℂ × ℂ)
    let pi := deningerBauFreeMap (⇑basis)
    ∃ b : DeningerBau
        (FreeGroup (Module.Free.ChooseBasisIndex ℚ (ℂ × ℂ))) → ℂ,
      ((completeResolutionClockAreaCocycle.pullback pi).IsPrimitive b) ∧
      ¬ ∀ k : pi.ker, b k = 0 := by
  dsimp only
  let basis := Module.Free.chooseBasis ℚ (ℂ × ℂ)
  obtain ⟨b, hb, hvanish⟩ :=
    DeningerNormalizedCocycle.deningerBauFree_exists_alternating_kernelTransgression
      basis completeResolutionClockAreaCocycle
      completeResolutionClockAreaCocycle_alternating
  refine ⟨b, ?_, ?_⟩
  · simpa [basis] using hb
  · intro hzero
    exact completeResolutionClockAreaCocycle_ne_zero (hvanish.mp hzero)

end

end RHTower
