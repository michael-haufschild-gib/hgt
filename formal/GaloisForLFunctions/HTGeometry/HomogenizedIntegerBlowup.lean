import GaloisForLFunctions.HTGeometry.HomogenizedMonoidProjectiveBlowup
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.PNat.Basic

/-!
# Prime coordinates of the integer-marked blowup

Unique prime factorization identifies positive integers, written additively under
multiplication, with finitely supported prime-exponent vectors. Transporting the monoid
algebra through this equivalence identifies the full native blowup with
`Spec R[x_p | p prime][T]`. The marked homogeneous fraction for each prime maps to the
corresponding polynomial variable, so the equivalence retains the arithmetic labels.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.HomogenizedIntegerBlowup

/-- Positive integers form the free commutative additive monoid on the primes. -/
def primeExponentEquiv : Additive ℕ+ ≃+ (Nat.Primes →₀ ℕ) where
  toEquiv := Nat.factorizationEquiv.trans (Finsupp.restrictSupportEquiv {p | Nat.Prime p} ℕ)
  map_add' m n := by
    change Finsupp.subtypeDomain Nat.Prime ((m.toMul * n.toMul : ℕ+) : ℕ).factorization =
      Finsupp.subtypeDomain Nat.Prime (m.toMul : ℕ).factorization +
        Finsupp.subtypeDomain Nat.Prime (n.toMul : ℕ).factorization
    rw [PNat.mul_coe]
    exact (congrArg (Finsupp.subtypeDomain Nat.Prime)
      (Nat.factorization_mul m.toMul.2.ne' n.toMul.2.ne')).trans Finsupp.subtypeDomain_add

theorem primeExponentEquiv_apply (n : Additive ℕ+) (p : Nat.Primes) :
    primeExponentEquiv n p = (n.toMul : ℕ).factorization p := rfl

theorem primeExponentEquiv_prime (p : Nat.Primes) :
    primeExponentEquiv (Additive.ofMul (⟨p,p.2.pos⟩ : ℕ+)) = Finsupp.single p 1 := by
  change Finsupp.subtypeDomain Nat.Prime (p : ℕ).factorization = Finsupp.single p 1
  calc
    _ = Finsupp.subtypeDomain Nat.Prime (Finsupp.single (p : ℕ) 1) :=
      congrArg _ p.2.factorization
    _ = Finsupp.subtypeDomain Nat.Prime (Finsupp.single p 1).extendDomain :=
      congrArg _ (Finsupp.extendDomain_single p 1).symm
    _ = _ := Finsupp.subtypeDomain_extendDomain _

variable (R : Type*) [CommRing R]

/-- The positive-integer monoid algebra is the prime-variable polynomial algebra. -/
def primeCoordinateEquiv : AddMonoidAlgebra R (Additive ℕ+) ≃ₐ[R] MvPolynomial Nat.Primes R :=
  AddMonoidAlgebra.domCongr R R primeExponentEquiv

theorem primeCoordinateEquiv_single (n : Additive ℕ+) (r : R) :
    primeCoordinateEquiv R (AddMonoidAlgebra.single n r) =
      MvPolynomial.monomial (primeExponentEquiv n) r := by
  exact AddMonoidAlgebra.domCongr_single primeExponentEquiv n r

theorem primeCoordinateEquiv_prime (p : Nat.Primes) :
    primeCoordinateEquiv R (AddMonoidAlgebra.single (Additive.ofMul (⟨p,p.2.pos⟩ : ℕ+)) 1) =
      MvPolynomial.X p := by
  rw [primeCoordinateEquiv_single,primeExponentEquiv_prime]
  rfl

/-- Extend the prime-coordinate equivalence while preserving the homogenizer. -/
def primePolynomialEquiv : Polynomial (AddMonoidAlgebra R (Additive ℕ+)) ≃ₐ[R]
    Polynomial (MvPolynomial Nat.Primes R) := Polynomial.mapAlgEquiv (primeCoordinateEquiv R)

open HomogenizedMonoidAlgebra

/-- The native integer-marked chart in prime polynomial coordinates. -/
def nativePrimeChartEquiv : NativeChart R (Additive ℕ+) ≃+* Polynomial (MvPolynomial Nat.Primes R) :=
  (nativeChartPolynomialEquiv R (Additive ℕ+)).trans (primePolynomialEquiv R).toRingEquiv

theorem nativePrimeChartEquiv_mark (p : Nat.Primes) :
    nativePrimeChartEquiv R (nativeFraction R (Additive ℕ+) 1
      (qVar R (Additive ℕ+) (Additive.ofMul (⟨p,p.2.pos⟩ : ℕ+)))
        (by rw [Submodule.pow_one]; exact qVar_mem_vertexIdeal R (Additive ℕ+) _)) =
          Polynomial.C (MvPolynomial.X p) := by
  change primePolynomialEquiv R (nativeChartPolynomialEquiv R (Additive ℕ+) _) = _
  rw [nativeChartPolynomialEquiv_mark]
  change Polynomial.map (primeCoordinateEquiv R).toRingHom (Polynomial.C _) = _
  rw [Polynomial.map_C]
  exact congrArg Polynomial.C (primeCoordinateEquiv_prime R p)

open CategoryTheory

/-- The full native integer-marked blowup is affine space in the prime marks and homogenizer. -/
def projIsoPrimePolynomialChart :
    AlgebraicGeometry.Proj (reesGrade R (Additive ℕ+)) ≅
      AlgebraicGeometry.Spec (.of (Polynomial (MvPolynomial Nat.Primes R))) :=
  projIsoPolynomialChart R (Additive ℕ+) ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso
    (primePolynomialEquiv R).symm.toRingEquiv.toCommRingCatIso.op

end GaloisForLFunctions.HTGeometry.HomogenizedIntegerBlowup
