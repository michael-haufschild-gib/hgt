import GaloisForLFunctions.HTGeometry.DirichletRationalIncrementIndependence
import GaloisForLFunctions.HTGeometry.ShiftedDigammaFamilyIncrement

/-!
# Shifted digamma jets in the Dirichlet coordinate

All shifts are literal translations of the rotated analytic digamma. Their jet increments
are the classical rational pole increments with the nonzero rotation factor `(-I)^j`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance dirichletShiftedDigammaDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance dirichletShiftedDigammaDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance dirichletShiftedDigammaComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- The actual upper-end germ of `psi(-I*z+lambda)`. -/
def shiftedRotDigammaMero (lam : ℂ) : upperEndMeroField :=
  upperEndTranslationMeroEquiv (Complex.I * lam) rotDigammaMero

theorem differentialJet_shiftedRotDigammaMero (lam : ℂ) (n : ℕ) :
    differentialJet n (shiftedRotDigammaMero lam) =
      upperEndTranslationMeroEquiv (Complex.I * lam) (rotDigammaJetMero n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [differentialJet_succ, ih]
      change (upperEndTranslationMeroEquiv (Complex.I * lam)
        (differentialJet n rotDigammaMero))′ =
        upperEndTranslationMeroEquiv (Complex.I * lam) (differentialJet (n + 1) rotDigammaMero)
      rw [differentialJet_succ, upperEndTranslationMeroEquiv_deriv]

theorem shiftedRotDigammaJet_shift (lam : ℂ) (n : ℕ) :
    upperEndTranslationMeroEquiv Complex.I (differentialJet n (shiftedRotDigammaMero lam)) =
      differentialJet n (shiftedRotDigammaMero lam) + dirDefectAt (-lam) n := by
  rw [differentialJet_shiftedRotDigammaMero, upperEndTranslationMeroEquiv_comm,
    upperEndTranslate_rotDigammaJetMero, map_add]
  simp only [dirDefectAt, dirTranslateAt, neg_neg, AlgEquiv.ofRingEquiv_apply]

theorem rotDefectConst_eq_rotation (n : ℕ) :
    rotDefectConst n = (-Complex.I) ^ n * ((-1 : ℂ) ^ n * (n.factorial : ℂ)) := by
  rw [rotDefectConst, pow_succ]
  calc
    _ = (Complex.I * (-Complex.I)) *
      ((-Complex.I) ^ n * ((-1 : ℂ) ^ n * (n.factorial : ℂ))) := by ring
    _ = _ := by simp

theorem dirDefectAt_eq_familyIncrement {r : ℕ} (lam : Fin r → ℂ) (i : Fin r) (n : ℕ) :
    dirDefectAt (-lam i) n = dirRatRealization
      (algebraMap ℂ (RatFunc ℂ) ((-Complex.I) ^ n) * familyIncrement lam i n) := by
  have hden : dirCoordAt (-lam i) ≠ 0 := by
    have h := aeval_dirCoordMero_ne_zero (Polynomial.X_add_C_ne_zero (lam i))
    simpa [dirCoordAt, map_neg] using h
  apply (mul_right_injective₀ (pow_ne_zero (n + 1) hden))
  dsimp only
  rw [mul_comm _ (dirDefectAt (-lam i) n)]
  rw [dirDefectAt_mul_pow, rotDefectConst_eq_rotation, map_mul]
  simp only [familyIncrement, map_mul, map_div₀, map_pow, map_add,
    dirRatRealization_const, dirRatRealization_C, dirRatRealization_X]
  have hcoord : dirCoordAt (-lam i) = dirCoordMero + algebraMap ℂ upperEndMeroField (lam i) := by
    simp [dirCoordAt]
  rw [← hcoord]
  field_simp

/-- Every shifted digamma jet has its explicit rational source increment. -/
theorem shiftedRotDigammaJet_rational_shift {r : ℕ}
    (lam : Fin r → ℂ) (i : Fin r) (n : ℕ) :
    upperEndTranslationMeroEquiv Complex.I (differentialJet n (shiftedRotDigammaMero (lam i))) =
      differentialJet n (shiftedRotDigammaMero (lam i)) + dirRatRealization
        (algebraMap ℂ (RatFunc ℂ) ((-Complex.I) ^ n) * familyIncrement lam i n) := by
  rw [shiftedRotDigammaJet_shift, dirDefectAt_eq_familyIncrement lam i n]

end

end GaloisForLFunctions.HTGeometry
