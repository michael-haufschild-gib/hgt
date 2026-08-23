import GaloisForLFunctions.HTGeometry.MonicRootClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Residue fields of an integral closure in an algebraically closed field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §3: for `X` the
normalization of `X₀` in an algebraic closure `K` of the function field of `X₀`, and `x` a point
of `X` over `x₀`, the residue field `κ (x)` is an algebraic closure of `κ (x₀)`.

Algebraicity is the residue-field shadow of integrality; algebraic closedness comes from the
integral closure being monic-root closed, a property inherited by quotients and passing to
fraction fields.  Together these are exactly the hypothesis `IsAlgClosure` under which
Corollary 3.1 describes `Hom (W_rat (κ (x₀)) , C)`.
-/

namespace RHTower

open HTGeometry

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P]
variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [Algebra (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
  [IsFractionRing (A ⧸ P) K] [IsFractionRing (B ⧸ Q) L]

omit [P.IsPrime] [Q.IsPrime] [IsFractionRing (A ⧸ P) K] in
include P Q in
/-- The residue field extension of an integral ring extension is algebraic. -/
theorem deningerResidue_isAlgebraic [Algebra.IsIntegral A B] : Algebra.IsAlgebraic K L := by
  haveI : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  exact isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L

include Q in
/-- The residue fields of a monic-root closed ring are algebraically closed. -/
theorem deningerResidue_isAlgClosed (h : IsMonicRootClosed B) : IsAlgClosed L :=
  (h.quotient Q).isAlgClosed_fractionRing L

omit [P.IsPrime] [IsFractionRing (A ⧸ P) K] in
include P Q in
/-- The residue field at a prime of a monic-root closed integral extension is an algebraic closure
of the residue field below. -/
theorem deningerResidue_isAlgClosure [Algebra.IsIntegral A B] (h : IsMonicRootClosed B) :
    IsAlgClosure K L := by
  haveI := deningerResidue_isAlgClosed Q L h
  haveI := deningerResidue_isAlgebraic P Q K L
  exact ⟨‹_›, ‹_›⟩

section IntegralClosure

variable {A C : Type*} [CommRing A] [Field C] [Algebra A C] [IsAlgClosed C]
variable (P : Ideal A) (Q : Ideal (integralClosure A C)) [Q.IsPrime] [Q.LiesOver P]
variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [Algebra (integralClosure A C ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (integralClosure A C ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
  [IsFractionRing (integralClosure A C ⧸ Q) L]

include P Q in
/-- **Deninger, §3.**  For the integral closure of `A` in an algebraically closed field, the
residue field at a prime `Q` is an algebraic closure of the residue field at the prime below. -/
theorem deningerIntegralClosureResidue_isAlgClosure : IsAlgClosure K L :=
  deningerResidue_isAlgClosure P Q K L (isMonicRootClosed_integralClosure A C)

end IntegralClosure

end RHTower
