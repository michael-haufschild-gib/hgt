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
    (gammaPoleSymbolicMovingCoefficientLaurent p).coeff (-(b : ℤ)) =
      gammaPoleRationalScaleDerivativeInclude
          (gammaPoleCenterHasseRational p b) *
        gammaPoleSymbolicPhysicalScale ^ b := by
  rw [gammaPoleSymbolicMovingCoefficientLaurent, RingHom.comp_apply]
  change (movingPoleTaylorLaurent
      (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational)
      gammaPoleSymbolicPhysicalScale
      (p.map gammaPoleComplexScaleDerivativeInclude)).coeff (-(b : ℤ)) = _
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
  simpa [gammaPoleSymbolicToActual, AddMonoidAlgebra.coe_mapRingHom] using!
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
    simp [gammaPoleSymbolicToActual, AddMonoidAlgebra.coeff_mapRingHom, hq]

theorem gammaPoleSymbolicToActual_movingCoefficient
    (p : Polynomial ℂ) :
    gammaPoleSymbolicToActual
        (gammaPoleSymbolicMovingCoefficientLaurent p) =
      gammaPoleMovingCoefficientLaurent p := by
  ext q
  change gammaPoleScaleAndUnitDerivativeLaurentEval
      ((gammaPoleSymbolicMovingCoefficientLaurent p).coeff q) =
    (gammaPoleMovingCoefficientLaurent p).coeff q
  cases q with
  | ofNat b =>
      rcases b with (_ | b)
      · change gammaPoleScaleAndUnitDerivativeLaurentEval
          ((gammaPoleSymbolicMovingCoefficientLaurent p).coeff (-(0 : ℤ))) =
            (gammaPoleMovingCoefficientLaurent p).coeff (-(0 : ℤ))
        calc
          _ = gammaPoleScaleAndUnitDerivativeLaurentEval
              (gammaPoleRationalScaleDerivativeInclude
                  (gammaPoleCenterHasseRational p 0) *
                gammaPoleSymbolicPhysicalScale ^ 0) :=
            congrArg gammaPoleScaleAndUnitDerivativeLaurentEval
              (gammaPoleSymbolicMovingCoefficientLaurent_coeff_neg p 0)
          _ = ratNatEval (gammaPoleCenterHasseRational p 0) *
              gammaPolePhysicalScaleGerm ^ 0 := by simp
          _ = (gammaPoleMovingCoefficientLaurent p).coeff (-(0 : ℤ)) :=
            (gammaPoleMovingCoefficientLaurent_coeff_neg p 0).symm
      · have hpos : (0 : ℤ) < Int.ofNat (b + 1) := by simp
        change gammaPoleScaleAndUnitDerivativeLaurentEval
            ((movingPoleTaylorLaurent
              (gammaPoleRationalScaleDerivativeInclude gammaPoleCenterRational)
              gammaPoleSymbolicPhysicalScale
              (p.map gammaPoleComplexScaleDerivativeInclude)).coeff
                (Int.ofNat (b + 1))) =
          (movingPoleTaylorLaurent gammaPoleCenterGerm
            gammaPolePhysicalScaleGerm (p.map complexNatGerm)).coeff
              (Int.ofNat (b + 1))
        rw [movingPoleTaylorLaurent_coeff_pos _ _ _ _ hpos,
          movingPoleTaylorLaurent_coeff_pos _ _ _ _ hpos]
        simp
  | negSucc b =>
      change gammaPoleScaleAndUnitDerivativeLaurentEval
          ((gammaPoleSymbolicMovingCoefficientLaurent p).coeff
            (-((b + 1 : ℕ) : ℤ))) =
        (gammaPoleMovingCoefficientLaurent p).coeff (-((b + 1 : ℕ) : ℤ))
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
        (LaurentPolynomial.T q)).coeff m =
    (LaurentPolynomial.T q : NatGerm[T;T⁻¹]).coeff m
  rw [AddMonoidAlgebra.coeff_mapRingHom]
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

/-- The highest pole grade of the universal `j`-th simple-pole jet is
the `U₀` boundary term with its signed factorial coefficient. -/
theorem universalSimplePoleJetProfile_coeff_top (j : ℕ) :
    (HTGeometry.universalSimplePoleJetProfile j).coeff (j + 1) =
      MvPolynomial.C (((-1 : ℂ) ^ j) * (j.factorial : ℂ)) *
        MvPolynomial.X 0 := by
  rw [HTGeometry.universalSimplePoleJetProfile,
    Polynomial.coeff_X_mul,
    HTGeometry.universalSimplePoleRegularProfile,
    Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkle : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsub : j - k ≠ j := by omega
    simp [Polynomial.coeff_monomial, hsub]
  · simp

theorem gammaPoleSymbolicDerivativeLaurentProfile_coeff_top (j : ℕ) :
    (gammaPoleSymbolicDerivativeLaurentProfile j).coeff ((j + 1 : ℕ) : ℤ) =
      gammaPoleSymbolicDerivativeScale j *
        gammaPoleComplexScaleDerivativeInclude
          (((-1 : ℂ) ^ j) * (j.factorial : ℂ)) := by
  have hboundary :
      (((HTGeometry.universalSimplePoleJetProfile j).map
        gammaPoleSymbolicUnitDerivativeBoundaryEval).coeff (j + 1)) =
        gammaPoleComplexScaleDerivativeInclude
          (((-1 : ℂ) ^ j) * (j.factorial : ℂ)) := by
    rw [Polynomial.coeff_map, universalSimplePoleJetProfile_coeff_top]
    simp [gammaPoleSymbolicUnitDerivativeBoundaryEval,
      gammaPoleSymbolicUnitDerivativeBoundaryFamily]
  rw [gammaPoleSymbolicDerivativeLaurentProfile,
    ← LaurentPolynomial.smul_eq_C_mul]
  change gammaPoleSymbolicDerivativeScale j *
      (Polynomial.toLaurent
        ((HTGeometry.universalSimplePoleJetProfile j).map
          gammaPoleSymbolicUnitDerivativeBoundaryEval)).coeff
        ((j + 1 : ℕ) : ℤ) = _
  congr 1
  rw [LaurentPolynomial.coeff_toLaurent]
  change Finsupp.mapDomain (fun n : ℕ => (n : ℤ))
      ((HTGeometry.universalSimplePoleJetProfile j).map
        gammaPoleSymbolicUnitDerivativeBoundaryEval).toFinsupp.coeff
        ((j + 1 : ℕ) : ℤ) = _
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) :=
    Int.ofNat_injective
  rw [Finsupp.mapDomain_apply hinj]
  exact hboundary

/-- **Linear top-edge diagonal.** The outer grade `j+1`, scale grade `-j`,
boundary-constant coefficient of the symbolic `j`-th Gamma derivative is
exactly `-j!`. -/
theorem gammaPoleSymbolicDerivativeLaurentProfile_top_scale_boundary
    (j : ℕ) :
    MvPolynomial.coeff 0
        (((gammaPoleSymbolicDerivativeLaurentProfile j).coeff ((j + 1 : ℕ) : ℤ)).coeff
          (-(j : ℤ))) =
      RatFunc.C (-(j.factorial : ℂ)) := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile_coeff_top]
  have hsign : (-1 : GammaPoleRationalBase) ^ j *
      (-1 : GammaPoleRationalBase) ^ j = 1 := by
    rw [← mul_pow]
    simp
  have hinner :
      ((gammaPoleSymbolicDerivativeScale j *
        gammaPoleComplexScaleDerivativeInclude
          (((-1 : ℂ) ^ j) * (j.factorial : ℂ))) :
        GammaPoleScaleDerivativeSymbolic).coeff (-(j : ℤ)) =
        MvPolynomial.C (RatFunc.C (-(j.factorial : ℂ))) := by
    have hscaleCoeff :
        (gammaPoleSymbolicDerivativeScale j).coeff (-(j : ℤ)) =
          -MvPolynomial.C ((-1 : GammaPoleRationalBase) ^ j) := by
      rw [gammaPoleSymbolicDerivativeScale]
      have hpow :
          (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
            LaurentPolynomial.C
              (MvPolynomial.C ((-1 : GammaPoleRationalBase) ^ j)) := by
        calc
          (-1 : GammaPoleScaleDerivativeSymbolic) ^ j =
              (gammaPoleRationalScaleDerivativeInclude
                (-1 : GammaPoleRationalBase)) ^ j := by
            simp [gammaPoleRationalScaleDerivativeInclude]
          _ = gammaPoleRationalScaleDerivativeInclude
              ((-1 : GammaPoleRationalBase) ^ j) := by rw [map_pow]
          _ = _ := rfl
      rw [hpow]
      change
        (-(LaurentPolynomial.C
            (MvPolynomial.C ((-1 : GammaPoleRationalBase) ^ j)) *
          LaurentPolynomial.T (-(j : ℤ))) :
          GammaPoleScaleDerivativeSymbolic).coeff (-(j : ℤ)) =
            -MvPolynomial.C ((-1 : GammaPoleRationalBase) ^ j)
      rw [AddMonoidAlgebra.coeff_neg]
      rw [← LaurentPolynomial.single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_single]
      simp
    rw [mul_comm]
    change
      ((LaurentPolynomial.C
        (MvPolynomial.C (RatFunc.C (((-1 : ℂ) ^ j) * (j.factorial : ℂ)))) *
          gammaPoleSymbolicDerivativeScale j) :
        GammaPoleScaleDerivativeSymbolic).coeff (-(j : ℤ)) =
          MvPolynomial.C (RatFunc.C (-(j.factorial : ℂ)))
    rw [← LaurentPolynomial.smul_eq_C_mul]
    change
      MvPolynomial.C
          (RatFunc.C (((-1 : ℂ) ^ j) * (j.factorial : ℂ))) *
        (gammaPoleSymbolicDerivativeScale j).coeff (-(j : ℤ)) =
          MvPolynomial.C (RatFunc.C (-(j.factorial : ℂ)))
    rw [hscaleCoeff]
    rw [mul_neg]
    have hbase :
        -(RatFunc.C (((-1 : ℂ) ^ j) * (j.factorial : ℂ)) *
            (-1 : GammaPoleRationalBase) ^ j) =
          RatFunc.C (-(j.factorial : ℂ)) := by
      have hpowK : (-1 : GammaPoleRationalBase) ^ j =
          RatFunc.C ((-1 : ℂ) ^ j) := by
        calc
          (-1 : GammaPoleRationalBase) ^ j =
              (RatFunc.C (-1 : ℂ)) ^ j := by simp
          _ = RatFunc.C ((-1 : ℂ) ^ j) := by rw [map_pow]
      have hsignC : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
        rw [← mul_pow]
        simp
      have hcomplex :
          -((((-1 : ℂ) ^ j) * (j.factorial : ℂ)) * (-1 : ℂ) ^ j) =
            -(j.factorial : ℂ) := by
        congr 1
        calc
          (((-1 : ℂ) ^ j) * (j.factorial : ℂ)) * (-1 : ℂ) ^ j =
              ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * (j.factorial : ℂ) := by ring
          _ = (j.factorial : ℂ) := by rw [hsignC, one_mul]
      calc
        _ = -(RatFunc.C ((((-1 : ℂ) ^ j) * (j.factorial : ℂ)) *
            (-1 : ℂ) ^ j)) := by rw [hpowK, ← map_mul]
        _ = RatFunc.C (-(j.factorial : ℂ)) := by
          rw [← map_neg, hcomplex]
    simpa only [map_mul, map_neg] using
      congrArg (MvPolynomial.C : GammaPoleRationalBase →+*
        MvPolynomial ℕ GammaPoleRationalBase) hbase
  calc
    _ = MvPolynomial.coeff 0
        (MvPolynomial.C (RatFunc.C (-(j.factorial : ℂ)))) :=
      congrArg (MvPolynomial.coeff 0) hinner
    _ = RatFunc.C (-(j.factorial : ℂ)) :=
      MvPolynomial.coeff_zero_C _

end

end GaloisForLFunctions
