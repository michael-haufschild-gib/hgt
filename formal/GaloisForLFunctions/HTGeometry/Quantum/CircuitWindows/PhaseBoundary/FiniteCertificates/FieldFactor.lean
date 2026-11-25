import GaloisForLFunctions.HTGeometry.DifferentialLurothVariableSupport
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.LiftCertificate

/-! # Specialization of a simple factor over a characteristic-zero field -/

open Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section
variable {A : Type*} [CommRing A]

/-- A factorization after clearing denominators in the coefficient image. -/
structure FactorChoice (A : Type*) [CommRing A] where
  den : A
  factor : A[X]
  quotient : A[X]

def FactorChoice.remainder (c : FactorChoice A) (p : A[X]) :=
  C c.den*p-c.factor*c.quotient

/-- The factor cuts out a simple zero of the specialized polynomial.
All four tests involve only finitely many coefficient values. -/
def FactorChoice.serves {K : Type*} [Field K] (c : FactorChoice A) (p : A[X]) (φ : A →+* K) (y : K) : Prop :=
  φ c.den≠0 ∧ (c.remainder p).map φ=0 ∧ c.factor.eval₂ φ y=0 ∧ c.factor.derivative.eval₂ φ y≠0

/-- A root of a nonzero specialization admits a simple factor over
the image fraction field, lifted with its cofactor to the base ring. -/
theorem exists_factor {K : Type*} [Field K] [CharZero K] (φ : A →+* K) (p : A[X]) (y : K)
    (hr : p.eval₂ φ y=0) (hn : p.map φ≠0) : ∃ c : FactorChoice A, c.serves p φ y := by
  classical
  let R := φ.range
  let F := FractionRing R
  let j : F →+* K := IsFractionRing.lift (K:=F) (g:=R.subtype) Subtype.val_injective
  letI : Algebra F K := j.toAlgebra
  let η : A →+* F := (algebraMap R F).comp φ.rangeRestrict
  have hcomp : (algebraMap F K).comp η=φ := by
    ext a
    exact IsFractionRing.lift_algebraMap (K:=F) (g:=R.subtype) Subtype.val_injective (φ.rangeRestrict a)
  have eval (P : A[X]) : aeval y (P.map η)=P.eval₂ φ y := by
    rw [aeval_def,eval₂_map,hcomp]
  have hi : IsIntegral F y := IsAlgebraic.isIntegral ⟨p.map η,fun hz => hn (by
    rw [←hcomp,←Polynomial.map_map,hz,Polynomial.map_zero]),(eval p).trans hr⟩
  let M := minpoly F y
  obtain ⟨T,hT⟩ := minpoly.dvd F y ((eval p).trans hr)
  have clear (Z : F[X]) : ∃ a : A, φ a≠0 ∧ ∃ W : A[X], W.map η=C (η a)*Z := by
    obtain ⟨d,Q,hQ⟩ := exists_polynomial_fraction_clear (R:=R) Z
    obtain ⟨a,ha⟩ := φ.rangeRestrict_surjective (d:R)
    obtain ⟨W,hW⟩ := Polynomial.map_surjective φ.rangeRestrict φ.rangeRestrict_surjective Q
    have hne : φ a≠0 := by
      intro hz
      have hh : φ.rangeRestrict a=0 := Subtype.ext hz
      rw [ha] at hh
      exact (mem_nonZeroDivisors_iff_ne_zero.mp d.property) hh
    refine ⟨a,hne,W,?_⟩
    change W.map ((algebraMap R F).comp φ.rangeRestrict)=C (algebraMap R F (φ.rangeRestrict a))*Z
    rwa [←Polynomial.map_map,hW,ha]
  obtain ⟨a,ha,P,hP⟩ := clear M
  obtain ⟨b,hb,Q,hQ⟩ := clear T
  refine ⟨⟨a*b,P,Q⟩,by rw [map_mul]; exact mul_ne_zero ha hb,?_,?_,?_⟩
  · let S := C (a*b)*p-P*Q
    have hz : S.map η=0 := by
      simp only [S,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,hP,hQ,hT,map_mul]
      dsimp only [M]
      ring
    change S.map φ=0
    rw [←hcomp,←Polynomial.map_map,hz,Polynomial.map_zero]
  · change P.eval₂ φ y=0
    rw [←eval,hP,map_mul,minpoly.aeval,mul_zero]
  · change P.derivative.eval₂ φ y≠0
    rw [←eval,←Polynomial.derivative_map,hP,Polynomial.derivative_C_mul,map_mul,aeval_C]
    have hne : algebraMap F K (η a)≠0 := by
      change ((algebraMap F K).comp η) a≠0
      rwa [hcomp]
    exact mul_ne_zero hne ((minpoly.irreducible hi).separable.aeval_derivative_ne_zero (minpoly.aeval F y))

#print axioms exists_factor
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
