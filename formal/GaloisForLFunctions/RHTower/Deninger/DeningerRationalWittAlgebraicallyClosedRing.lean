import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittAlgebraicallyClosedPresentation
import Mathlib.Algebra.Ring.TransferInstance

/-!
# Literal rational-Witt ring over an algebraically closed field

The localized rational-function carrier uses multiplication for Witt addition.  Consequently its
existing multiplicative type cannot also use Lean's multiplication symbol for Witt multiplication.
This module introduces a one-field wrapper around that literal carrier and transports the
commutative-ring structure across the proved equivalence with `ℤ[Kˣ]`.

This is not a presentation alias: `additiveVal` is an actual element of the localized-polynomial
kernel.  The resulting ring addition is proved to be literal multiplication of rational functions,
and its Teichmüller elements satisfy `[a] * [b] = [ab]` for all `a,b : K`.
-/

namespace RHTower

noncomputable section

/-- Rational-Witt ring carrier whose values are literal normalized rational functions. -/
@[ext] structure DeningerRationalWittRing (K : Type*) [Field K] where
  additiveVal : Additive (DeningerRationalWittAdditive K)

/-- Underlying equivalence used to transport the ring structure from the reduced monoid algebra. -/
noncomputable def deningerRationalWittRingCarrierEquiv
    (K : Type*) [Field K] [IsAlgClosed K] :
    DeningerRationalWittRing K ≃ MonoidAlgebra ℤ Kˣ where
  toFun w :=
    (deningerRationalWittReducedMonoidAlgebraAddEquiv K).symm w.additiveVal
  invFun x :=
    ⟨deningerRationalWittReducedMonoidAlgebraAddEquiv K x⟩
  left_inv w := by ext; simp
  right_inv x := by simp

/-- Commutative Witt-ring structure on the literal rational-function carrier. -/
noncomputable instance deningerRationalWittRingCommRing
    (K : Type*) [Field K] [IsAlgClosed K] :
    CommRing (DeningerRationalWittRing K) :=
  (deningerRationalWittRingCarrierEquiv K).commRing

/-- Exact ring comparison with the reduced monoid algebra over an algebraically closed field. -/
noncomputable def deningerRationalWittReducedMonoidAlgebraRingEquiv
    (K : Type*) [Field K] [IsAlgClosed K] :
    MonoidAlgebra ℤ Kˣ ≃+* DeningerRationalWittRing K :=
  (Equiv.ringEquiv (deningerRationalWittRingCarrierEquiv K)).symm

theorem deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal
    {K : Type*} [Field K] [IsAlgClosed K]
    (x : MonoidAlgebra ℤ Kˣ) :
    (deningerRationalWittReducedMonoidAlgebraRingEquiv K x).additiveVal =
      deningerRationalWittReducedMonoidAlgebraToAdditive K x := by
  rfl

/-- Literal Teichmüller element in the rational-Witt ring wrapper. -/
noncomputable def deningerRationalWittRingTeichmuller
    {K : Type*} [Field K] [IsAlgClosed K]
    (a : K) : DeningerRationalWittRing K :=
  ⟨Additive.ofMul (deningerRationalWittTeichmuller a)⟩

theorem deningerRationalWittRingTeichmuller_unit
    {K : Type*} [Field K] [IsAlgClosed K] (a : Kˣ) :
    deningerRationalWittRingTeichmuller (a : K) =
      deningerRationalWittReducedMonoidAlgebraRingEquiv K
        (MonoidAlgebra.single a 1) := by
  apply DeningerRationalWittRing.ext
  rw [deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal]
  simp
  rfl

/-- Teichmüller multiplication on nonzero field elements. -/
theorem deningerRationalWittRingTeichmuller_mul_units
    {K : Type*} [Field K] [IsAlgClosed K] (a b : Kˣ) :
    deningerRationalWittRingTeichmuller (a : K) *
        deningerRationalWittRingTeichmuller (b : K) =
      deningerRationalWittRingTeichmuller ((a * b : Kˣ) : K) := by
  rw [deningerRationalWittRingTeichmuller_unit,
    deningerRationalWittRingTeichmuller_unit,
    deningerRationalWittRingTeichmuller_unit]
  rw [← map_mul, MonoidAlgebra.single_mul_single, one_mul]

@[simp] theorem deningerRationalWittRingTeichmuller_zero
    {K : Type*} [Field K] [IsAlgClosed K] :
    deningerRationalWittRingTeichmuller (0 : K) = 0 := by
  calc
    deningerRationalWittRingTeichmuller (0 : K) =
        deningerRationalWittReducedMonoidAlgebraRingEquiv K 0 := by
      apply DeningerRationalWittRing.ext
      rw [deningerRationalWittReducedMonoidAlgebraRingEquiv_additiveVal]
      change Additive.ofMul (deningerRationalWittTeichmuller (0 : K)) =
        Additive.ofMul 1
      congr 1
      apply Subtype.ext
      apply Units.ext
      change (deningerRationalWittTeichmullerUnit (0 : K) :
        DeningerRationalWittLocalization K) = 1
      rw [deningerRationalWittTeichmullerUnit_val]
      simp [deningerRationalWittTeichmullerPolynomial]
    _ = 0 :=
      map_zero (deningerRationalWittReducedMonoidAlgebraRingEquiv K)

/-- Full Teichmüller multiplication law, including zero atoms. -/
theorem deningerRationalWittRingTeichmuller_mul
    {K : Type*} [Field K] [IsAlgClosed K] (a b : K) :
    deningerRationalWittRingTeichmuller a *
        deningerRationalWittRingTeichmuller b =
      deningerRationalWittRingTeichmuller (a * b) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  let ua : Kˣ := Units.mk0 a ha
  let ub : Kˣ := Units.mk0 b hb
  change deningerRationalWittRingTeichmuller (ua : K) *
      deningerRationalWittRingTeichmuller (ub : K) =
    deningerRationalWittRingTeichmuller ((ua * ub : Kˣ) : K)
  exact deningerRationalWittRingTeichmuller_mul_units ua ub

/-- Witt addition is literal multiplication of normalized rational functions. -/
theorem deningerRationalWittRing_additiveVal_add
    {K : Type*} [Field K] [IsAlgClosed K]
    (x y : DeningerRationalWittRing K) :
    (x + y).additiveVal = x.additiveVal + y.additiveVal := by
  apply (deningerRationalWittReducedMonoidAlgebraAddEquiv K).symm.injective
  rw [map_add]
  change deningerRationalWittRingCarrierEquiv K (x + y) =
    deningerRationalWittRingCarrierEquiv K x +
      deningerRationalWittRingCarrierEquiv K y
  exact map_add (Equiv.ringEquiv
    (deningerRationalWittRingCarrierEquiv K)) x y

/-- Closed arithmetic-closure rational-Witt ring comparison. -/
noncomputable def deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv
    (p : Nat.Primes) :
    MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ ≃+*
      DeningerRationalWittRing (DeningerPrimeArithmeticClosure p) :=
  deningerRationalWittReducedMonoidAlgebraRingEquiv
    (DeningerPrimeArithmeticClosure p)

end

end RHTower
