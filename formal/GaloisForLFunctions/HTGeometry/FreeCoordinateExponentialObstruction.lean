import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import Mathlib.FieldTheory.Differential.Basic

/-!
# No rational exponential eigenfunctions of a free coordinate derivative

A nonzero rational function in free coordinates cannot be an eigenvector of a coordinate
derivation with nonzero scalar eigenvalue.  The proof uses a reduced numerator and denominator:
relative primality forces each to divide its own partial derivative, while strict total-degree
drop forces both derivatives to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial
open scoped Differential

/-- Regard a derivation over any coefficient ring as the underlying integer derivation of a
differential ring. -/
@[reducible] def differentialOfDerivation
    {C R : Type*} [CommRing C] [CommRing R] [Algebra C R]
    (D : Derivation C R R) : Differential R where
  deriv := Derivation.mk'
    D.toAddMonoidHom.toIntLinearMap
    (by
      intro x y
      change D (x * y) = x * D y + y * D x
      exact D.leibniz x y)

@[simp] theorem differentialOfDerivation_apply
    {C R : Type*} [CommRing C] [CommRing R] [Algebra C R]
    (D : Derivation C R R) (x : R) :
    letI := differentialOfDerivation D
    x′ = D x := rfl

/-- A free-coordinate derivation has no nonzero rational eigenfunction with nonzero scalar
eigenvalue. -/
theorem freeCoordinateDerivation_eq_const_mul_self_forces_zero
    {C σ : Type*} [Field C] [CharZero C] (i : σ)
    {c : C} (hc : c ≠ 0) {f : FreeCoordinateRationalField C σ}
    (hf : freeCoordinateDerivation C σ i f =
      algebraMap C (FreeCoordinateRationalField C σ) c * f) :
    f = 0 := by
  by_contra hf0
  let P := MvPolynomial σ C
  let F := FreeCoordinateRationalField C σ
  let p : P := IsFractionRing.num P f
  let q : P := IsFractionRing.den P f
  have hq : q ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den P f).property
  have hqF : algebraMap P F q ≠ 0 := by
    simpa using (IsFractionRing.injective P F).ne hq
  have hrel : algebraMap P F p = f * algebraMap P F q := by
    exact (div_eq_iff hqF).mp (IsFractionRing.mk'_num_den' P f)
  have hp : p ≠ 0 := by
    intro hp0
    rw [hp0, map_zero] at hrel
    exact hf0 ((mul_eq_zero.mp hrel.symm).resolve_right hqF)
  have hcoprime : IsRelPrime p q := by
    simpa only [p, q] using IsFractionRing.num_den_reduced P f
  have hderiv := congrArg (freeCoordinateDerivation C σ i) hrel
  rw [freeCoordinateDerivation_algebraMap, Derivation.leibniz,
    freeCoordinateDerivation_algebraMap, hf] at hderiv
  simp only [smul_eq_mul] at hderiv
  have hcrossF :
      algebraMap P F (MvPolynomial.pderiv i p * q) =
        algebraMap P F
          (p * (MvPolynomial.C c * q + MvPolynomial.pderiv i q)) := by
    simp only [map_mul, map_add]
    rw [show algebraMap P F (MvPolynomial.C c) = algebraMap C F c by
      exact IsScalarTower.algebraMap_apply C P F c]
    calc
      algebraMap P F (MvPolynomial.pderiv i p) * algebraMap P F q =
          (f * algebraMap P F (MvPolynomial.pderiv i q) +
            algebraMap P F q * (algebraMap C F c * f)) *
              algebraMap P F q := by rw [hderiv]
      _ = (f * algebraMap P F q) *
          (algebraMap C F c * algebraMap P F q +
            algebraMap P F (MvPolynomial.pderiv i q)) := by ring
      _ = algebraMap P F p *
          (algebraMap C F c * algebraMap P F q +
            algebraMap P F (MvPolynomial.pderiv i q)) := by
            rw [hrel]
  have hcross :
      MvPolynomial.pderiv i p * q =
        p * (MvPolynomial.C c * q + MvPolynomial.pderiv i q) :=
    (IsFractionRing.injective P F) hcrossF
  have hpdiv : p ∣ MvPolynomial.pderiv i p := by
    apply hcoprime.dvd_of_dvd_mul_right
    exact ⟨MvPolynomial.C c * q + MvPolynomial.pderiv i q, hcross⟩
  have hpderiv : MvPolynomial.pderiv i p = 0 :=
    mvPolynomial_pderiv_eq_zero_of_self_dvd p i hpdiv
  have hqrelation : MvPolynomial.pderiv i q = -(MvPolynomial.C c * q) := by
    rw [hpderiv, zero_mul] at hcross
    have hsum : MvPolynomial.C c * q + MvPolynomial.pderiv i q = 0 := by
      exact (mul_eq_zero.mp hcross.symm).resolve_left hp
    linear_combination hsum
  have hqdiv : q ∣ MvPolynomial.pderiv i q := by
    exact ⟨-MvPolynomial.C c, by rw [hqrelation]; ring⟩
  have hqderiv : MvPolynomial.pderiv i q = 0 :=
    mvPolynomial_pderiv_eq_zero_of_self_dvd q i hqdiv
  rw [hqderiv] at hqrelation
  have hcC : MvPolynomial.C c ≠ (0 : P) := MvPolynomial.C_ne_zero.mpr hc
  exact (mul_ne_zero hcC hq) (neg_eq_zero.mp hqrelation.symm)

/-- An element algebraic over a free rational coordinate field cannot solve `x' = x` in a
differential field extension. -/
theorem ne_self_of_isAlgebraic_freeCoordinateDerivation
    {C σ L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
    [Algebra (FreeCoordinateRationalField C σ) L]
    [IsScalarTower C (FreeCoordinateRationalField C σ) L]
    (i : σ) (D : Derivation C L L)
    (hD : ∀ a : FreeCoordinateRationalField C σ,
      D (algebraMap (FreeCoordinateRationalField C σ) L a) =
        algebraMap (FreeCoordinateRationalField C σ) L
          (freeCoordinateDerivation C σ i a))
    {x : L} (hxalg : IsAlgebraic (FreeCoordinateRationalField C σ) x)
    (hx0 : x ≠ 0) :
    D x ≠ x := by
  letI : Differential (FreeCoordinateRationalField C σ) :=
    differentialOfDerivation (freeCoordinateDerivation C σ i)
  letI : Differential L :=
    differentialOfDerivation D
  letI : DifferentialAlgebra (FreeCoordinateRationalField C σ) L :=
    ⟨by
      intro a
      change D (algebraMap (FreeCoordinateRationalField C σ) L a) =
        algebraMap (FreeCoordinateRationalField C σ) L
          (freeCoordinateDerivation C σ i a)
      exact hD a⟩
  let F := FreeCoordinateRationalField C σ
  intro hx
  let p : F[X] := minpoly F x
  let n := p.natDegree
  let q : F[X] := Differential.mapCoeffs p + X * derivative p
  let r : F[X] := q - Polynomial.C (n : F) * p
  have hp0 : p ≠ 0 := minpoly.ne_zero hxalg.isIntegral
  have hpd : 0 < n := (minpoly.irreducible hxalg.isIntegral).natDegree_pos
  have hpmonic : p.Monic := minpoly.monic hxalg.isIntegral
  have hqeval : aeval x q = 0 := by
    have hchain := Differential.deriv_aeval_eq (A := F) x p
    have hprel : aeval x p = 0 := minpoly.aeval F x
    have hx' : x′ = x := by
      change D x = x
      exact hx
    rw [hprel, map_zero, hx'] at hchain
    simpa only [q, map_add, map_mul, aeval_X, mul_comm] using hchain.symm
  have hpq : p ∣ q := minpoly.dvd F x hqeval
  have hpr : p ∣ r := by
    apply dvd_sub hpq
    exact ⟨Polynomial.C (n : F), by ring⟩
  have hEulerCoeff : ∀ m : ℕ,
      (X * derivative p).coeff m = (m : F) * p.coeff m := by
    intro m
    cases m with
    | zero => simp
    | succ m =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
        push_cast
        ring
  have hrle : r.natDegree ≤ n - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hnm : n ≤ m := by omega
    simp only [r, q, coeff_sub, coeff_add, Differential.coeff_mapCoeffs,
      Polynomial.coeff_C_mul, hEulerCoeff]
    by_cases hmn : m = n
    · subst m
      rw [hpmonic.coeff_natDegree]
      simp
    · have hlt : n < m := lt_of_le_of_ne hnm (Ne.symm hmn)
      simp [coeff_eq_zero_of_natDegree_lt hlt]
  have hrlt : r.natDegree < p.natDegree := by
    change r.natDegree < n
    omega
  have hr0 : r = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hpr hrlt
  have hcoeff := congrArg (fun s : F[X] ↦ s.coeff 0) hr0
  simp only [r, q, coeff_sub, coeff_add, Differential.coeff_mapCoeffs,
    Polynomial.coeff_C_mul, hEulerCoeff, Nat.cast_zero, zero_mul, add_zero,
    coeff_zero] at hcoeff
  have heigen : freeCoordinateDerivation C σ i (p.coeff 0) =
      algebraMap C F (n : C) * p.coeff 0 := by
    change (p.coeff 0)′ = algebraMap C F (n : C) * p.coeff 0
    rw [map_natCast]
    linear_combination hcoeff
  have hnC : (n : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hpd)
  have hpcoeff0 : p.coeff 0 = 0 :=
    freeCoordinateDerivation_eq_const_mul_self_forces_zero i hnC heigen
  exact (minpoly.coeff_zero_ne_zero hxalg.isIntegral hx0) hpcoeff0

end

end GaloisForLFunctions.HTGeometry
