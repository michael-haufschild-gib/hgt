import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilFinitePart
import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilSmoothBound

/-!
# Semiboundedness of Suzuki's complete restricted Weil form

The exact finite-part, scalar, visible-prime, and smooth source blocks admit explicit lower bounds
on Suzuki's literal smooth compactly supported core. This module combines those estimates and
proves semiboundedness of the complete source-locked quadratic form, with no analytic premise.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

def suzukiRestrictedWeilLowerBoundConstant (a : ℝ) : ℝ :=
  (1 / 2) * max (Real.log (a ^ 2)) 0 +
    |2 * suzukiWeilArchimedeanConstant + 1| +
    2 * (∑ n ∈ suzukiRestrictedWeilIndices a, primePairWeight n) +
    2 * a * suzukiWeilRemainderApertureBound a

theorem suzukiRestrictedWeilCore_pairing_eq_intervalEnergy
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    pairing u u = ∫ x in (-a.1)..a.1, u x ^ 2 := by
  have htest : ApertureTest a.1 u := by
    refine ⟨u.continuous, u.hasCompactSupport, ?_⟩
    intro x hx
    by_contra hne
    exact hx (u.support_subset_aperture hne)
  have hbridge := intervalIntegral_eq_integral_of_apertureTest a.property.le htest u
  rw [pairing]
  simpa [pow_two] using hbridge.symm

theorem suzukiRestrictedWeilScalarBlock_lowerBound
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    -|2 * suzukiWeilArchimedeanConstant + 1| *
        (∫ x in (-a.1)..a.1, u x ^ 2) ≤
      weilScalarBlock a.1 suzukiWeilArchimedeanConstant u u := by
  have hE : 0 ≤ ∫ x in (-a.1)..a.1, u x ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith [a.property])
      (fun x _ => sq_nonneg (u x))
  rw [weilScalarBlock]
  simp only [← pow_two]
  nlinarith [le_abs_self (2 * suzukiWeilArchimedeanConstant + 1)]

theorem suzukiRestrictedWeilForm_lowerBound
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    -(suzukiRestrictedWeilLowerBoundConstant a.1 *
        ∫ x in (-a.1)..a.1, u x ^ 2) ≤ suzukiRestrictedWeilForm a.1 u u := by
  let E : ℝ := ∫ x in (-a.1)..a.1, u x ^ 2
  have hfinite := suzukiWeilFinitePartBlock_lowerBound a u
  have hscalar := suzukiRestrictedWeilScalarBlock_lowerBound a u
  have hprime := suzukiRestrictedWeilPrimeBlock_lowerBound_core a.1 u
  rw [suzukiRestrictedWeilCore_pairing_eq_intervalEnergy a u] at hprime
  have hsmooth := suzukiRestrictedWeilSmoothBlock_lowerBound a u
  rw [suzukiRestrictedWeilForm_eq_fourBlocks]
  unfold suzukiRestrictedWeilLowerBoundConstant
  change -(((1 / 2) * max (Real.log (a.1 ^ 2)) 0 +
      |2 * suzukiWeilArchimedeanConstant + 1| +
      2 * (∑ n ∈ suzukiRestrictedWeilIndices a.1, primePairWeight n) +
      2 * a.1 * suzukiWeilRemainderApertureBound a.1) * E) ≤ _
  change -(1 / 2 * max (Real.log (a.1 ^ 2)) 0 * E) ≤ _ at hfinite
  change -|2 * suzukiWeilArchimedeanConstant + 1| * E ≤ _ at hscalar
  change -(2 * (∑ n ∈ suzukiRestrictedWeilIndices a.1, primePairWeight n)) * E ≤ _ at hprime
  change -(2 * a.1 * suzukiWeilRemainderApertureBound a.1 * E) ≤ _ at hsmooth
  linarith

end GaloisForLFunctions.RHTower

