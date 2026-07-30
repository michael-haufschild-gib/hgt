import GaloisForLFunctions.HTGeometry.PolynomialMovingPoleTaylor
import GaloisForLFunctions.HTGeometry.GammaPoleScaleUnitRelativeFreeness

/-!
# Polynomial coefficients in the moving Gamma pole chart

The Gamma unit families are indexed so that sequence index `N` represents the pole `1-N` and the
physical microscope scale is `reciprocalGammaFactorialScale (N-1)`.  This module reflects both
quantities exactly into the rational pole-position and factorial-scale germ interfaces.

For every `p ∈ ℂ[z]`, it then constructs the Laurent value relation

`p(1-N + s_(N-1)/T)`

and proves that its `T^(-b)` coefficient is the centered Hasse derivative of `p`, evaluated as a
rational function of `N`, times `s_(N-1)^b`.  The zero Laurent coefficient is a faithful evaluation
of `p`; hence the entire moving-coefficient transform is injective even though the ambient germ
ring may have zero divisors.  This closes the polynomial-coefficient Taylor interface needed by
the Gamma simple-pole diagonal descent, without asymptotic or numerical input.
-/

open Polynomial LaurentPolynomial

namespace GaloisForLFunctions

noncomputable section

def gammaPoleCenterRational : GammaPoleRationalBase :=
  1 - RatFunc.X

def gammaPoleCenterGerm : NatGerm :=
  ratNatEval gammaPoleCenterRational

def gammaPolePhysicalScaleGerm : NatGerm :=
  -reciprocalSignedFactorialGerm

/-- The abstract pole scale is exactly the shifted physical Gamma microscope scale. -/
theorem gammaPolePhysicalScaleGerm_eq_actual :
    gammaPolePhysicalScaleGerm =
      (fun N : ℕ => reciprocalGammaFactorialScale (N - 1) : NatGerm) := by
  rw [gammaPolePhysicalScaleGerm, reciprocalSignedFactorialGerm,
    ← Filter.Germ.coe_neg, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N => by
    rcases N with (_ | n)
    · simp [reciprocalSignedFactorialSequence,
        signedFactorialSequence, reciprocalGammaFactorialScale]
    · change -reciprocalSignedFactorialSequence (n + 1) =
        reciprocalGammaFactorialScale n
      rw [reciprocalSignedFactorialSequence_succ_eq_neg_scale]
      simp

theorem gammaPolePhysicalScaleGerm_ne_zero :
    gammaPolePhysicalScaleGerm ≠ 0 :=
  neg_ne_zero.mpr reciprocalSignedFactorialGerm_isUnit.ne_zero

def gammaPoleCenterRationalEval :
    Polynomial ℂ →+* GammaPoleRationalBase :=
  Polynomial.eval₂RingHom RatFunc.C gammaPoleCenterRational

@[simp] theorem gammaPoleCenterRationalEval_C (c : ℂ) :
    gammaPoleCenterRationalEval (Polynomial.C c) = RatFunc.C c := by
  simp [gammaPoleCenterRationalEval]

@[simp] theorem gammaPoleCenterRationalEval_X :
    gammaPoleCenterRationalEval Polynomial.X = gammaPoleCenterRational := by
  simp [gammaPoleCenterRationalEval]

theorem gammaPoleCenterRationalEval_eq_comp :
    gammaPoleCenterRationalEval =
      (algebraMap (Polynomial ℂ) GammaPoleRationalBase).comp
        (scaledTaylorAlgHom (1 : ℂ) (-1 : ℂ)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro c
    simp [gammaPoleCenterRationalEval, scaledTaylorAlgHom,
      polynomialDiagonalScaleAlgHom]
  · simp [gammaPoleCenterRationalEval, gammaPoleCenterRational,
      scaledTaylorAlgHom_apply, Polynomial.taylor_apply]
    ring

theorem gammaPoleCenterRationalEval_injective :
    Function.Injective gammaPoleCenterRationalEval := by
  rw [gammaPoleCenterRationalEval_eq_comp]
  exact (RatFunc.algebraMap_injective ℂ).comp
    (scaledTaylorAlgHom_injective (1 : ℂ) (-1 : ℂ) (by norm_num))

def gammaPoleCenterHasseRational (p : Polynomial ℂ) (b : ℕ) :
    GammaPoleRationalBase :=
  (Polynomial.hasseDeriv b (p.map RatFunc.C)).eval gammaPoleCenterRational

def gammaPoleMovingCoefficientLaurent :
    Polynomial ℂ →+* NatGerm[T;T⁻¹] :=
  (movingPoleTaylorLaurent
      gammaPoleCenterGerm gammaPolePhysicalScaleGerm).toRingHom.comp
    (Polynomial.mapRingHom complexNatGerm)

theorem gammaPoleMovingCoefficientLaurent_coeff_neg
    (p : Polynomial ℂ) (b : ℕ) :
    (gammaPoleMovingCoefficientLaurent p).coeff (-(b : ℤ)) =
      ratNatEval (gammaPoleCenterHasseRational p b) *
        gammaPolePhysicalScaleGerm ^ b := by
  rw [gammaPoleMovingCoefficientLaurent, RingHom.comp_apply]
  change (movingPoleTaylorLaurent gammaPoleCenterGerm
      gammaPolePhysicalScaleGerm (p.map complexNatGerm)).coeff (-(b : ℤ)) = _
  rw [movingPoleTaylorLaurent_coeff_neg]
  change (Polynomial.hasseDeriv b
      (p.map (ratNatEval.comp RatFunc.C))).eval
        (ratNatEval gammaPoleCenterRational) *
      gammaPolePhysicalScaleGerm ^ b = _
  rw [← Polynomial.map_map,
    hasseDeriv_eval_map ratNatEval (p.map RatFunc.C)
      gammaPoleCenterRational]
  rfl

theorem gammaPoleMovingCoefficientLaurent_coeff_zero
    (p : Polynomial ℂ) :
    (gammaPoleMovingCoefficientLaurent p).coeff 0 =
      ratNatEval (gammaPoleCenterRationalEval p) := by
  have h := gammaPoleMovingCoefficientLaurent_coeff_neg p 0
  simpa [gammaPoleCenterHasseRational,
    gammaPoleCenterRationalEval,
    Polynomial.eval₂_eq_eval_map] using h

theorem gammaPoleMovingCoefficientLaurent_coeff_zero_ne_zero
    {p : Polynomial ℂ} (hp : p ≠ 0) :
    (gammaPoleMovingCoefficientLaurent p).coeff 0 ≠ 0 := by
  rw [gammaPoleMovingCoefficientLaurent_coeff_zero]
  simpa using
    ratNatEval_injective.ne (gammaPoleCenterRationalEval_injective.ne hp)

theorem gammaPoleMovingCoefficientLaurent_injective :
    Function.Injective gammaPoleMovingCoefficientLaurent := by
  intro p q hpq
  apply gammaPoleCenterRationalEval_injective
  apply ratNatEval_injective
  rw [← gammaPoleMovingCoefficientLaurent_coeff_zero,
    ← gammaPoleMovingCoefficientLaurent_coeff_zero]
  exact congrArg (fun f : NatGerm[T;T⁻¹] => f.coeff 0) hpq

end

end GaloisForLFunctions
