import GaloisForLFunctions.HTGeometry.JuliaDefectSpectralEquilibrium
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivatives of the Julia compression profile

This module computes the exact quadratic jet of the Julia compression square.  The calculation is
kept separate from measure-theoretic moment arguments so it can be reused wherever the closed
hyperbolic profile appears.
-/

namespace HTGeometry

noncomputable section

private def juliaProfileNumerator (y : ℝ) : ℝ := Real.cosh (y / 2) ^ (2 : ℕ)
private def juliaProfileDenominator (y : ℝ) : ℝ := Real.sqrt (Real.cosh (2 * y))
private def juliaProfileNumeratorDeriv (y : ℝ) : ℝ :=
  Real.cosh (y / 2) * Real.sinh (y / 2)
private def juliaProfileDenominatorDeriv (y : ℝ) : ℝ :=
  Real.sinh (2 * y) / Real.sqrt (Real.cosh (2 * y))
private def juliaProfileClosedDeriv (y : ℝ) : ℝ :=
  (juliaProfileNumeratorDeriv y * juliaProfileDenominator y -
      juliaProfileNumerator y * juliaProfileDenominatorDeriv y) /
    juliaProfileDenominator y ^ (2 : ℕ)

private theorem hasDerivAt_juliaProfileNumerator (y : ℝ) :
    HasDerivAt juliaProfileNumerator (juliaProfileNumeratorDeriv y) y := by
  change HasDerivAt (fun z : ℝ => Real.cosh (z / 2) ^ (2 : ℕ))
    (Real.cosh (y / 2) * Real.sinh (y / 2)) y
  have hinner : HasDerivAt (fun z : ℝ => z / 2) (1 / 2 : ℝ) y :=
    (hasDerivAt_id y).div_const 2
  have h := ((Real.hasDerivAt_cosh (y / 2)).comp y hinner).pow 2
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

private theorem hasDerivAt_juliaProfileDenominator (y : ℝ) :
    HasDerivAt juliaProfileDenominator (juliaProfileDenominatorDeriv y) y := by
  change HasDerivAt (fun z : ℝ => Real.sqrt (Real.cosh (2 * z)))
    (Real.sinh (2 * y) / Real.sqrt (Real.cosh (2 * y))) y
  have hinner : HasDerivAt (fun z : ℝ => 2 * z) 2 y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul (2 : ℝ)
  have hcos := (Real.hasDerivAt_cosh (2 * y)).comp y hinner
  have hsqrt := hcos.sqrt (by
    change Real.cosh (2 * y) ≠ 0
    exact (Real.cosh_pos _).ne')
  refine (hsqrt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

private theorem hasDerivAt_juliaProfileClosed (y : ℝ) :
    HasDerivAt
      (fun z : ℝ => juliaProfileNumerator z / juliaProfileDenominator z)
      (juliaProfileClosedDeriv y) y := by
  have h := (hasDerivAt_juliaProfileNumerator y).div
    (hasDerivAt_juliaProfileDenominator y) (by
      simp [juliaProfileDenominator]
      positivity)
  change HasDerivAt
    (fun z : ℝ => juliaProfileNumerator z / juliaProfileDenominator z)
    ((juliaProfileNumeratorDeriv y * juliaProfileDenominator y -
      juliaProfileNumerator y * juliaProfileDenominatorDeriv y) /
      juliaProfileDenominator y ^ (2 : ℕ)) y
  exact h

private theorem deriv_juliaProfileClosed :
    deriv (fun z : ℝ => juliaProfileNumerator z / juliaProfileDenominator z) =
      juliaProfileClosedDeriv := by
  funext y
  exact (hasDerivAt_juliaProfileClosed y).deriv

private theorem hasDerivAt_juliaProfileNumeratorDeriv_zero :
    HasDerivAt juliaProfileNumeratorDeriv (1 / 2 : ℝ) 0 := by
  change HasDerivAt
    (fun z : ℝ => Real.cosh (z / 2) * Real.sinh (z / 2)) (1 / 2 : ℝ) 0
  have hi : HasDerivAt (fun z : ℝ => z / 2) (1 / 2 : ℝ) 0 :=
    (hasDerivAt_id 0).div_const 2
  have hc := (Real.hasDerivAt_cosh ((0 : ℝ) / 2)).comp 0 hi
  have hs := (Real.hasDerivAt_sinh ((0 : ℝ) / 2)).comp 0 hi
  have h := hc.mul hs
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num

private theorem hasDerivAt_juliaProfileDenominatorDeriv_zero :
    HasDerivAt juliaProfileDenominatorDeriv 2 0 := by
  change HasDerivAt
    (fun z : ℝ => Real.sinh (2 * z) / Real.sqrt (Real.cosh (2 * z))) 2 0
  have hi : HasDerivAt (fun z : ℝ => 2 * z) 2 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
  have hs := (Real.hasDerivAt_sinh (2 * (0 : ℝ))).comp 0 hi
  have hv := hasDerivAt_juliaProfileDenominator 0
  have h := hs.div hv (by norm_num [juliaProfileDenominator])
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num [juliaProfileDenominator]

private theorem hasDerivAt_juliaProfileClosedDeriv_zero :
    HasDerivAt juliaProfileClosedDeriv (-3 / 2 : ℝ) 0 := by
  have hu := hasDerivAt_juliaProfileNumerator 0
  have hv := hasDerivAt_juliaProfileDenominator 0
  have hu1 := hasDerivAt_juliaProfileNumeratorDeriv_zero
  have hv1 := hasDerivAt_juliaProfileDenominatorDeriv_zero
  have hnum := (hu1.mul hv).sub (hu.mul hv1)
  have hden := hv.pow 2
  have h := hnum.div hden (by norm_num [juliaProfileDenominator])
  change HasDerivAt
    (fun y : ℝ =>
      (juliaProfileNumeratorDeriv y * juliaProfileDenominator y -
        juliaProfileNumerator y * juliaProfileDenominatorDeriv y) /
        juliaProfileDenominator y ^ (2 : ℕ)) (-3 / 2 : ℝ) 0
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num [juliaProfileNumerator, juliaProfileDenominator,
    juliaProfileNumeratorDeriv, juliaProfileDenominatorDeriv]

/-- The Julia compression square has exact second derivative `-3/2` at the origin. -/
theorem iteratedDeriv_two_juliaCompressionSquareProfile :
    iteratedDeriv 2 juliaCompressionSquareProfile 0 = (-3 / 2 : ℝ) := by
  have heq : juliaCompressionSquareProfile = fun y : ℝ =>
      juliaProfileNumerator y / juliaProfileDenominator y := by
    funext y
    rw [juliaCompressionSquareProfile_eq_cosh_ratio]
    rfl
  rw [heq]
  simp only [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ']
  rw [deriv_juliaProfileClosed]
  exact hasDerivAt_juliaProfileClosedDeriv_zero.deriv

end

end HTGeometry
