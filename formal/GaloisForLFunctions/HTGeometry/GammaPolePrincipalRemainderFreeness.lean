import GaloisForLFunctions.HTGeometry.GammaPoleCovariantJetRealization
import GaloisForLFunctions.HTGeometry.GammaPoleUnitRelativeFreeness

/-!
# Relative freeness of the Gamma principal remainders

After its unique principal pole monomial is removed, the factorially normalized Gamma germ has a
canonical analytic remainder.  Its complete jet at the pole center is not merely explicit: across
the pole family it is a nonzero factorial rescaling of the positive Taylor coefficients of the
regular Gamma pole unit.  Consequently these finite-part jets remain algebraically independent
even over the full rational pole-position field `ℂ(n)`.

This is a lower-layer value reflection.  Principal-part subtraction does not collapse the free
analytic information hidden below the pole boundary.
-/

open Complex Filter

namespace GaloisForLFunctions

noncomputable section

local instance finitePartNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm := ratNatEval.toAlgebra

local instance finitePartComplexNatGermAlgebra :
    Algebra ℂ NatGerm := complexNatGerm.toAlgebra

/-- Across the pole label, the `m`th jet of the canonical regular remainder of Gamma itself. -/
def gammaPoleFinitePartJetGerm (m : ℕ) : NatGerm :=
  (fun N : ℕ => iteratedDeriv m
    (gammaPoleJetRegularRemainder (N - 1) 0) 0 : NatGerm)

/-- **Finite-part/unit value reflection.** The complete finite-part jet family is the positive
regular-unit coefficient family multiplied coordinatewise by the exact nonzero factor `-m!`. -/
theorem gammaPoleFinitePartJetGerm_eq_unitCoefficient (m : ℕ) :
    gammaPoleFinitePartJetGerm m =
      complexNatGerm (-(m.factorial : ℂ)) *
        gammaPoleUnitPositiveCoefficientGerm m := by
  rw [gammaPoleUnitPositiveCoefficientGerm_eq_actualTaylorCoefficient,
    complexNatGerm_eq_constGerm]
  change (↑(fun N : ℕ => iteratedDeriv m
      (gammaPoleJetRegularRemainder (N - 1) 0) 0) : NatGerm) =
    (↑(fun _N : ℕ => -(m.factorial : ℂ)) : NatGerm) *
      ↑(fun N : ℕ => (((m + 1).factorial : ℂ)⁻¹) *
        iteratedDeriv (m + 1) (gammaPoleRegularUnit (N - 1)) 0)
  rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N => by
    change iteratedDeriv m
      (gammaPoleJetRegularRemainder (N - 1) 0) 0 =
        -(m.factorial : ℂ) *
          ((((m + 1).factorial : ℂ)⁻¹) *
            iteratedDeriv (m + 1) (gammaPoleRegularUnit (N - 1)) 0)
    rw [iteratedDeriv_gammaPoleJetRegularRemainder_zero]
    simp only [pow_zero, neg_mul, one_mul, zero_add]
    rw [Nat.factorial_succ]
    have hm1 : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    have hmf : ((m.factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    field_simp
    push_cast
    ring

/-- **Relative finite-part freeness.** The analytic finite-part jets at all normalized Gamma poles
are algebraically independent over rational functions of the pole label. -/
theorem algebraicIndependent_gammaPoleFinitePartJetGerm_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase gammaPoleFinitePartJetGerm := by
  let u : ℕ → GammaPoleRationalBase :=
    fun m => RatFunc.C (-(m.factorial : ℂ))
  have hu : ∀ m, u m ≠ 0 := fun m => by
    dsimp [u]
    have hfac : ((m.factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    simpa only [map_zero] using
      RatFunc.C_injective.ne (neg_ne_zero.mpr hfac)
  have hx := algebraicIndependent_iff_injective_aeval.mp
    algebraicIndependent_gammaPoleUnitPositiveCoefficientGerm_over_ratFunc
  have hdiag := mvPolynomialDiagonalScaleRing_injective u hu
  have hcomp :
      MvPolynomial.eval₂Hom ratNatEval
        (fun m => algebraMap GammaPoleRationalBase NatGerm (u m) *
          gammaPoleUnitPositiveCoefficientGerm m) =
        (MvPolynomial.eval₂Hom ratNatEval
          gammaPoleUnitPositiveCoefficientGerm).comp
            (mvPolynomialDiagonalScaleRing u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [mvPolynomialDiagonalScaleRing]
    · intro m
      simp [mvPolynomialDiagonalScaleRing]
      rfl
  have hscaled : AlgebraicIndependent GammaPoleRationalBase
      (fun m => algebraMap GammaPoleRationalBase NatGerm (u m) *
        gammaPoleUnitPositiveCoefficientGerm m) := by
    rw [algebraicIndependent_iff_injective_aeval]
    change Function.Injective
      (MvPolynomial.eval₂Hom ratNatEval
        (fun m => algebraMap GammaPoleRationalBase NatGerm (u m) *
          gammaPoleUnitPositiveCoefficientGerm m))
    have hx' : Function.Injective
        (MvPolynomial.eval₂Hom ratNatEval
          gammaPoleUnitPositiveCoefficientGerm) := by
      change Function.Injective
        (MvPolynomial.aeval gammaPoleUnitPositiveCoefficientGerm)
      exact hx
    rw [hcomp]
    exact hx'.comp hdiag
  have hfamily :
      (fun m : ℕ => algebraMap GammaPoleRationalBase NatGerm (u m) *
        gammaPoleUnitPositiveCoefficientGerm m) =
        gammaPoleFinitePartJetGerm := by
    funext m
    dsimp [u]
    change complexNatGerm (-(m.factorial : ℂ)) *
      gammaPoleUnitPositiveCoefficientGerm m = gammaPoleFinitePartJetGerm m
    exact (gammaPoleFinitePartJetGerm_eq_unitCoefficient m).symm
  rwa [hfamily] at hscaled

/-- Rational-pole-position evaluation on the complete Gamma finite-part jet family. -/
def gammaPoleFinitePartJetRationalEval :
    MvPolynomial ℕ GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval gammaPoleFinitePartJetGerm

theorem gammaPoleFinitePartJetRationalEval_injective :
    Function.Injective gammaPoleFinitePartJetRationalEval := by
  have h := algebraicIndependent_iff_injective_aeval.mp
    algebraicIndependent_gammaPoleFinitePartJetGerm_over_ratFunc
  change Function.Injective
    (MvPolynomial.eval₂Hom ratNatEval gammaPoleFinitePartJetGerm)
  change Function.Injective
    (MvPolynomial.aeval gammaPoleFinitePartJetGerm) at h
  exact h

end

end GaloisForLFunctions
