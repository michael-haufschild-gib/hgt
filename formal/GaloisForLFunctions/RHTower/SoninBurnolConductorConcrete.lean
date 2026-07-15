/-
# Concrete Burnol conductor reflection on the even Sonin carrier

On the even real `L²` carrier the cosine Fourier transform is an involution, and the Fourier
cutoff is literally the physical cutoff reflected by that involution.  This file specializes the
abstract Burnol conductor algebra to those existing concrete operators.

The results are source-side bridge identities.  They do not construct the unbounded logarithmic
position/conductor multipliers or prove the BMO bounded extension of their commutator.
-/
import GaloisForLFunctions.RHTower.SoninBurnolConductorReflection
import GaloisForLFunctions.RHTower.ConstrainedProlateOperator

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- The cosine Fourier transform squares to the identity on the even Sonin carrier. -/
theorem evenFourierTransform_mul_self :
    evenFourierTransform * evenFourierTransform = 1 := by
  apply ContinuousLinearMap.ext
  exact evenFourierTransform_involutive

/-- The concrete Fourier cutoff is the physical cutoff reflected by the involutive cosine
Fourier transform. -/
theorem evenFourierCutoff_eq_reflectedCutoff (a : ℝ) :
    evenFourierCutoff a =
      reflectedCutoff (evenIndicatorCutoff a) evenFourierTransform := by
  apply ContinuousLinearMap.ext
  intro f
  have hJinj : Function.Injective evenFourierTransform := by
    intro x y hxy
    rw [← evenFourierTransform_involutive x,
      ← evenFourierTransform_involutive y, hxy]
  apply hJinj
  simp only [reflectedCutoff, ContinuousLinearMap.mul_apply]
  rw [evenFourierTransform_involutive]
  apply Subtype.ext
  simp only [coe_evenFourierTransform_apply, coe_evenFourierCutoff_apply,
    fourierCutoff_apply, coe_evenIndicatorCutoff_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The Burnol conductor built from any bounded position channel commutes with concrete cosine
Fourier reflection. -/
theorem ccmCommutator_burnolConductor_evenFourierTransform
    (M : evenSubspace →L[ℂ] evenSubspace) :
    ccmCommutator (burnolConductor M evenFourierTransform)
      evenFourierTransform = 0 :=
  ccmCommutator_burnolConductor_reflection M evenFourierTransform
    evenFourierTransform_mul_self

/-- Concrete first half of Burnol cancellation: if the position channel commutes with the
physical cutoff, its Fourier-edge commutator is the conductor commutator. -/
theorem ccmCommutator_evenFourierCutoff_eq_conductor
    (a : ℝ) (M : evenSubspace →L[ℂ] evenSubspace)
    (hMP : ccmCommutator M (evenIndicatorCutoff a) = 0) :
    ccmCommutator M (evenFourierCutoff a) =
      ccmCommutator (burnolConductor M evenFourierTransform)
        (evenFourierCutoff a) := by
  rw [evenFourierCutoff_eq_reflectedCutoff]
  exact ccmCommutator_reflectedCutoff_eq_conductor M evenFourierTransform
    (evenIndicatorCutoff a) evenFourierTransform_mul_self hMP

/-- Concrete Burnol cancellation: the Fourier-edge position commutator is the cosine-Fourier
reflection of the physical conductor edge. -/
theorem ccmCommutator_evenFourierCutoff_eq_reflectedConductorEdge
    (a : ℝ) (M : evenSubspace →L[ℂ] evenSubspace)
    (hMP : ccmCommutator M (evenIndicatorCutoff a) = 0) :
    ccmCommutator M (evenFourierCutoff a) =
      evenFourierTransform *
        ccmCommutator (burnolConductor M evenFourierTransform)
          (evenIndicatorCutoff a) * evenFourierTransform := by
  rw [evenFourierCutoff_eq_reflectedCutoff]
  exact ccmCommutator_reflectedCutoff_eq_reflectedConductorEdge M
    evenFourierTransform (evenIndicatorCutoff a)
    evenFourierTransform_mul_self hMP

end RHTower
