import GaloisForLFunctions.HTGeometry.GammaPoleMovingJetLaurent
import GaloisForLFunctions.HTGeometry.GammaPoleScaleDerivativeLaurentFreeness

/-!
# Symbolic moving-pole Gamma jet Laurent profile

This file lifts the polynomial-coefficient Gamma jet profile out of the germ
quotient and into a two-stage symbolic Laurent ring.  The outer Laurent degree
records pole order.  The inner Laurent degree records signed factorial-scale
exponent, and its coefficients are polynomials in the positive derivatives of
the regular Gamma unit over `ℂ(n)`.

The symbolic-to-actual map is injective by Laurent scale/derivative freeness.
It sends the symbolic coefficient Taylor transform and every universal jet
profile exactly to their actual Gamma germ counterparts.  Hence equality of
actual profiles is equivalent to equality of symbolic profiles.  This is the
faithful coefficient interface needed for the maximal-weight diagonal descent.
-/

open Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

abbrev GammaPoleScaleDerivativeSymbolic :=
  LaurentPolynomial (MvPolynomial ℕ GammaPoleRationalBase)

abbrev GammaPoleMovingJetSymbolic :=
  LaurentPolynomial GammaPoleScaleDerivativeSymbolic

def gammaPoleRationalScaleDerivativeInclude :
    GammaPoleRationalBase →+* GammaPoleScaleDerivativeSymbolic :=
  LaurentPolynomial.C.comp MvPolynomial.C

def gammaPoleComplexScaleDerivativeInclude :
    ℂ →+* GammaPoleScaleDerivativeSymbolic :=
  gammaPoleRationalScaleDerivativeInclude.comp RatFunc.C

def gammaPoleSymbolicScale : GammaPoleScaleDerivativeSymbolic :=
  LaurentPolynomial.T 1

def gammaPoleSymbolicPhysicalScale : GammaPoleScaleDerivativeSymbolic :=
  -gammaPoleSymbolicScale

def gammaPoleSymbolicUnitDerivativeBoundaryFamily :
    ℕ → GammaPoleScaleDerivativeSymbolic
  | 0 => 1
  | k + 1 => LaurentPolynomial.C (MvPolynomial.X k)

def gammaPoleSymbolicUnitDerivativeBoundaryEval :
    MvPolynomial ℕ ℂ →+* GammaPoleScaleDerivativeSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleComplexScaleDerivativeInclude
    gammaPoleSymbolicUnitDerivativeBoundaryFamily

/-- Symbolic moving-pole Taylor expansion of a polynomial coefficient. -/
def gammaPoleSymbolicMovingCoefficientLaurent :
    Polynomial ℂ →+* GammaPoleMovingJetSymbolic :=
  (movingPoleTaylorLaurent
      (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational)
      gammaPoleSymbolicPhysicalScale).toRingHom.comp
    (Polynomial.mapRingHom gammaPoleComplexScaleDerivativeInclude)

/-- The signed inverse-scale factor carried by the `j`-th derivative. -/
def gammaPoleSymbolicDerivativeScale
    (j : ℕ) : GammaPoleScaleDerivativeSymbolic :=
  -((-1 : GammaPoleScaleDerivativeSymbolic) ^ j *
    LaurentPolynomial.T (-(j : ℤ)))

def gammaPoleSymbolicDerivativeLaurentProfile
    (j : ℕ) : GammaPoleMovingJetSymbolic :=
  LaurentPolynomial.C (gammaPoleSymbolicDerivativeScale j) *
    Polynomial.toLaurent
      ((HTGeometry.universalSimplePoleJetProfile j).map
        gammaPoleSymbolicUnitDerivativeBoundaryEval)

/-- Complete symbolic moving-pole evaluation of a finite polynomial-coefficient
jet packet. -/
def gammaPoleSymbolicPolynomialJetLaurentEval (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      GammaPoleMovingJetSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleSymbolicMovingCoefficientLaurent
    (fun j : Fin (n + 1) =>
      gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ))

theorem gammaPoleSymbolicMovingCoefficientLaurent_coeff_neg
    (p : Polynomial ℂ) (b : ℕ) :
    gammaPoleSymbolicMovingCoefficientLaurent p (-(b : ℤ)) =
      gammaPoleRationalScaleDerivativeInclude
          (gammaPoleCenterHasseRational p b) *
        gammaPoleSymbolicPhysicalScale ^ b := by
  rw [gammaPoleSymbolicMovingCoefficientLaurent, RingHom.comp_apply]
  change movingPoleTaylorLaurent
      (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational)
      gammaPoleSymbolicPhysicalScale
      (p.map gammaPoleComplexScaleDerivativeInclude) (-(b : ℤ)) = _
  rw [movingPoleTaylorLaurent_coeff_neg]
  change (Polynomial.hasseDeriv b
      (p.map (gammaPoleRationalScaleDerivativeInclude.comp RatFunc.C))).eval
        (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational) *
      gammaPoleSymbolicPhysicalScale ^ b = _
  rw [← Polynomial.map_map,
    hasseDeriv_eval_map gammaPoleRationalScaleDerivativeInclude
      (p.map RatFunc.C) gammaPoleCenterRational]
  rfl

/-- Evaluate both symbolic boundary layers on the actual Gamma germ family. -/
def gammaPoleSymbolicToActual :
    GammaPoleMovingJetSymbolic →+* NatGerm[T;T⁻¹] :=
  AddMonoidAlgebra.mapRingHom ℤ
    gammaPoleScaleAndUnitDerivativeLaurentEval

theorem gammaPoleSymbolicToActual_injective :
    Function.Injective gammaPoleSymbolicToActual := by
  simpa [gammaPoleSymbolicToActual] using
    AddMonoidAlgebra.map_injective
      (M := ℤ) gammaPoleScaleAndUnitDerivativeLaurentEval.toAddMonoidHom
      gammaPoleScaleAndUnitDerivativeLaurentEval_injective

@[simp] theorem gammaPoleScaleAndUnitDerivativeLaurentEval_rationalInclude
    (q : GammaPoleRationalBase) :
    gammaPoleScaleAndUnitDerivativeLaurentEval
        (gammaPoleRationalScaleDerivativeInclude q) = ratNatEval q := by
  simp [gammaPoleScaleAndUnitDerivativeLaurentEval,
    gammaPoleUnitDerivativeRationalEval,
    gammaPoleRationalScaleDerivativeInclude]

@[simp] theorem gammaPoleScaleAndUnitDerivativeLaurentEval_symbolicScale :
    gammaPoleScaleAndUnitDerivativeLaurentEval gammaPoleSymbolicScale =
      reciprocalSignedFactorialGerm := by
  simp [gammaPoleScaleAndUnitDerivativeLaurentEval,
    gammaPoleSymbolicScale]

@[simp] theorem gammaPoleScaleAndUnitDerivativeLaurentEval_symbolicPhysicalScale :
    gammaPoleScaleAndUnitDerivativeLaurentEval gammaPoleSymbolicPhysicalScale =
      gammaPolePhysicalScaleGerm := by
  simp [gammaPoleSymbolicPhysicalScale, gammaPolePhysicalScaleGerm]

@[simp] theorem gammaPoleSymbolicToActual_C
    (a : GammaPoleScaleDerivativeSymbolic) :
    gammaPoleSymbolicToActual (LaurentPolynomial.C a) =
      LaurentPolynomial.C
        (gammaPoleScaleAndUnitDerivativeLaurentEval a) := by
  ext q
  by_cases hq : q = 0 <;>
    simp [gammaPoleSymbolicToActual, AddMonoidAlgebra.mapRingHom_apply, hq]

theorem gammaPoleSymbolicToActual_movingCoefficient
    (p : Polynomial ℂ) :
    gammaPoleSymbolicToActual
        (gammaPoleSymbolicMovingCoefficientLaurent p) =
      gammaPoleMovingCoefficientLaurent p := by
  ext q
  change gammaPoleScaleAndUnitDerivativeLaurentEval
      (gammaPoleSymbolicMovingCoefficientLaurent p q) =
    gammaPoleMovingCoefficientLaurent p q
  cases q with
  | ofNat b =>
      rcases b with (_ | b)
      · change gammaPoleScaleAndUnitDerivativeLaurentEval
          (gammaPoleSymbolicMovingCoefficientLaurent p (-(0 : ℤ))) =
            gammaPoleMovingCoefficientLaurent p (-(0 : ℤ))
        calc
          _ = gammaPoleScaleAndUnitDerivativeLaurentEval
              (gammaPoleRationalScaleDerivativeInclude
                  (gammaPoleCenterHasseRational p 0) *
                gammaPoleSymbolicPhysicalScale ^ 0) :=
            congrArg gammaPoleScaleAndUnitDerivativeLaurentEval
              (gammaPoleSymbolicMovingCoefficientLaurent_coeff_neg p 0)
          _ = ratNatEval (gammaPoleCenterHasseRational p 0) *
              gammaPolePhysicalScaleGerm ^ 0 := by simp
          _ = gammaPoleMovingCoefficientLaurent p (-(0 : ℤ)) :=
            (gammaPoleMovingCoefficientLaurent_coeff_neg p 0).symm
      · have hpos : (0 : ℤ) < Int.ofNat (b + 1) := by simp
        change gammaPoleScaleAndUnitDerivativeLaurentEval
            (movingPoleTaylorLaurent
              (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational)
              gammaPoleSymbolicPhysicalScale
              (p.map gammaPoleComplexScaleDerivativeInclude)
              (Int.ofNat (b + 1))) =
          movingPoleTaylorLaurent gammaPoleCenterGerm
            gammaPolePhysicalScaleGerm (p.map complexNatGerm)
              (Int.ofNat (b + 1))
        rw [movingPoleTaylorLaurent_coeff_pos _ _ _ _ hpos,
          movingPoleTaylorLaurent_coeff_pos _ _ _ _ hpos]
        simp
  | negSucc b =>
      change gammaPoleScaleAndUnitDerivativeLaurentEval
          (gammaPoleSymbolicMovingCoefficientLaurent p
            (-((b + 1 : ℕ) : ℤ))) =
        gammaPoleMovingCoefficientLaurent p (-((b + 1 : ℕ) : ℤ))
      rw [gammaPoleSymbolicMovingCoefficientLaurent_coeff_neg,
        gammaPoleMovingCoefficientLaurent_coeff_neg]
      simp

@[simp] theorem gammaPoleScaleAndUnitDerivativeLaurentEval_symbolicBoundaryFamily
    (k : ℕ) :
    gammaPoleScaleAndUnitDerivativeLaurentEval
        (gammaPoleSymbolicUnitDerivativeBoundaryFamily k) =
      gammaPoleUnitDerivativeBoundaryFamily k := by
  rcases k with (_ | k)
  · simp [gammaPoleSymbolicUnitDerivativeBoundaryFamily,
      gammaPoleUnitDerivativeBoundaryFamily]
  · simp [gammaPoleSymbolicUnitDerivativeBoundaryFamily,
      gammaPoleUnitDerivativeBoundaryFamily,
      gammaPoleScaleAndUnitDerivativeLaurentEval,
      gammaPoleUnitDerivativeRationalEval]

theorem gammaPoleScaleAndUnitDerivativeLaurentEval_boundaryEval :
    gammaPoleScaleAndUnitDerivativeLaurentEval.comp
        gammaPoleSymbolicUnitDerivativeBoundaryEval =
      gammaPoleUnitDerivativeBoundaryEval := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,
      gammaPoleSymbolicUnitDerivativeBoundaryEval,
      MvPolynomial.eval₂Hom_C,
      gammaPoleUnitDerivativeBoundaryEval]
    change gammaPoleScaleAndUnitDerivativeLaurentEval
        (gammaPoleRationalScaleDerivativeInclude (RatFunc.C c)) =
      complexNatGerm c
    rw [gammaPoleScaleAndUnitDerivativeLaurentEval_rationalInclude]
    rfl
  · intro k
    simp [gammaPoleSymbolicUnitDerivativeBoundaryEval,
      gammaPoleUnitDerivativeBoundaryEval]

@[simp] theorem gammaPoleSymbolicToActual_T (q : ℤ) :
    gammaPoleSymbolicToActual
        (LaurentPolynomial.T q : GammaPoleMovingJetSymbolic) =
      (LaurentPolynomial.T q : NatGerm[T;T⁻¹]) := by
  ext m
  change (AddMonoidAlgebra.mapRingHom ℤ
      gammaPoleScaleAndUnitDerivativeLaurentEval
        (LaurentPolynomial.T q)) m =
    (LaurentPolynomial.T q : NatGerm[T;T⁻¹]) m
  rw [AddMonoidAlgebra.mapRingHom_apply]
  by_cases hqm : q = m <;>
    simp [LaurentPolynomial.T_apply, hqm]

theorem gammaPoleSymbolicToActual_toLaurent
    (p : Polynomial GammaPoleScaleDerivativeSymbolic) :
    gammaPoleSymbolicToActual (Polynomial.toLaurent p) =
      Polynomial.toLaurent
        (p.map gammaPoleScaleAndUnitDerivativeLaurentEval) := by
  let lhs : Polynomial GammaPoleScaleDerivativeSymbolic →+*
      NatGerm[T;T⁻¹] :=
    gammaPoleSymbolicToActual.comp Polynomial.toLaurent
  let rhs : Polynomial GammaPoleScaleDerivativeSymbolic →+*
      NatGerm[T;T⁻¹] :=
    Polynomial.toLaurent.comp
      (Polynomial.mapRingHom gammaPoleScaleAndUnitDerivativeLaurentEval)
  have h : lhs = rhs := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [lhs, rhs]
    · simp [lhs, rhs]
  exact RingHom.congr_fun h p

@[simp] theorem gammaPoleScaleAndUnitDerivativeLaurentEval_derivativeScale
    (j : ℕ) :
    gammaPoleScaleAndUnitDerivativeLaurentEval
        (gammaPoleSymbolicDerivativeScale j) =
      -gammaPolePhysicalScaleGerm⁻¹ ^ j := by
  simp [gammaPoleSymbolicDerivativeScale,
    gammaPoleScaleAndUnitDerivativeLaurentEval,
    gammaPolePhysicalScaleGerm]
  rw [← inv_pow,
    show -reciprocalSignedFactorialGerm⁻¹ =
      (-1 : NatGerm) * reciprocalSignedFactorialGerm⁻¹ by ring,
    mul_pow]

theorem gammaPoleSymbolicToActual_derivativeProfile
    (j : ℕ) :
    gammaPoleSymbolicToActual
        (gammaPoleSymbolicDerivativeLaurentProfile j) =
      gammaPoleDerivativeLaurentProfile j := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile, map_mul,
    gammaPoleSymbolicToActual_C,
    gammaPoleScaleAndUnitDerivativeLaurentEval_derivativeScale,
    gammaPoleSymbolicToActual_toLaurent]
  rw [Polynomial.map_map,
    gammaPoleScaleAndUnitDerivativeLaurentEval_boundaryEval]
  rfl

@[simp] theorem gammaPoleSymbolicPolynomialJetLaurentEval_C
    (n : ℕ) (p : Polynomial ℂ) :
    gammaPoleSymbolicPolynomialJetLaurentEval n (MvPolynomial.C p) =
      gammaPoleSymbolicMovingCoefficientLaurent p := by
  simp [gammaPoleSymbolicPolynomialJetLaurentEval]

@[simp] theorem gammaPoleSymbolicPolynomialJetLaurentEval_X
    (n : ℕ) (j : Fin (n + 1)) :
    gammaPoleSymbolicPolynomialJetLaurentEval n (MvPolynomial.X j) =
      gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ) := by
  simp [gammaPoleSymbolicPolynomialJetLaurentEval]

/-- The symbolic two-stage Laurent profile evaluates exactly to the actual
Gamma germ profile. -/
theorem gammaPoleSymbolicToActual_polynomialJetLaurentEval
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    gammaPoleSymbolicToActual
        (gammaPoleSymbolicPolynomialJetLaurentEval n P) =
      gammaPolePolynomialJetLaurentEval n P := by
  let lhs : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+*
      NatGerm[T;T⁻¹] :=
    gammaPoleSymbolicToActual.comp
      (gammaPoleSymbolicPolynomialJetLaurentEval n)
  have h : lhs = gammaPolePolynomialJetLaurentEval n := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [lhs, gammaPoleSymbolicToActual_movingCoefficient]
    · intro j
      simp [lhs, gammaPoleSymbolicToActual_derivativeProfile]
  exact RingHom.congr_fun h P

/-- Actual equality reflects to equality of the symbolic Laurent profiles. -/
theorem gammaPolePolynomialJetLaurentEval_eq_iff_symbolic_eq
    (n : ℕ) (P Q : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    gammaPolePolynomialJetLaurentEval n P =
        gammaPolePolynomialJetLaurentEval n Q ↔
      gammaPoleSymbolicPolynomialJetLaurentEval n P =
        gammaPoleSymbolicPolynomialJetLaurentEval n Q := by
  rw [← gammaPoleSymbolicToActual_polynomialJetLaurentEval,
    ← gammaPoleSymbolicToActual_polynomialJetLaurentEval]
  exact gammaPoleSymbolicToActual_injective.eq_iff

end

end GaloisForLFunctions
