import GaloisForLFunctions.HTGeometry.PrimeSeparatedDeterminantCoefficient
import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField

/-!
# Separated prime-ray packets for arbitrary prime-power profile jets

This module isolates the lightweight Jacobian core for positive-prime-power sources with
uncontrolled valuation tails.  A nonsingular scalar packet read at distinct prime rays makes the
arithmetic-function Jacobian nonsingular and gives algebraic independence over the common kernel
of the selected prime derivations.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix
open scoped Differential

noncomputable section

/-- Support on positive prime powers, without any finiteness restriction on valuation depth. -/
def PrimeProfileSupportedOnPositivePrimePowers (f : ArithmeticFunction ℂ) : Prop :=
  ∀ ⦃n : ℕ⦄, f n ≠ 0 →
    ∃ (p : Nat.Primes) (e : ℕ), n = (p : ℕ) ^ (e + 1)

/-- The explicit logarithmic coefficient jet, kept local to the profile packet theory so this
leaf does not import the much broader valuation-echelon development. -/
def primeProfileRotatedLogJet (k : ℕ) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ where
  toFun n := (Complex.I * (Real.log n : ℂ)) ^ k * f n
  map_zero' := by simp

@[simp]
theorem primeProfileRotatedLogJet_apply
    (k : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    primeProfileRotatedLogJet k f n =
      (Complex.I * (Real.log n : ℂ)) ^ k * f n :=
  rfl

/-- Prime derivation of a profile jet stays on the selected prime ray. -/
theorem primeDeriv_primeProfileRotatedLogJet_supportedOnPrimeRay
    (f : ArithmeticFunction ℂ)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers f)
    (q : Nat.Primes) (k : ℕ) :
    SupportedOnPrimeRay q (primeDeriv q.1 (primeProfileRotatedLogJet k f)) := by
  intro n hn
  have hvalue : f (n * q) ≠ 0 := by
    intro hzero
    apply hn
    rw [primeDeriv_apply, primeProfileRotatedLogJet_apply, hzero, mul_zero, mul_zero]
  obtain ⟨p, e, hp⟩ := hsupport hvalue
  have hqdvd : (q : ℕ) ∣ (p : ℕ) ^ (e + 1) := by
    rw [← hp]
    exact ⟨n, by ring⟩
  have hpq : q = p := by
    apply Subtype.ext
    exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqdvd
  subst p
  refine ⟨e, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right q.2.pos
  calc
    n * q = (q : ℕ) ^ (e + 1) := hp
    _ = (q : ℕ) ^ e * q := by rw [pow_succ]

/-- The explicit finite jet family of a positive-prime-power source packet. -/
def primeProfileJetSource
    {I : Type*} (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (x : I × Fin (m + 1)) : ArithmeticFunction ℂ :=
  primeProfileRotatedLogJet x.2 (g x.1)

/-- The scalar Jacobian read at one selected valuation coordinate on each prime ray. -/
def primeProfileJetPacketMatrix
    {I : Type*}
    (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (q : I × Fin (m + 1) → Nat.Primes)
    (e : I × Fin (m + 1) → ℕ) :
    Matrix (I × Fin (m + 1)) (I × Fin (m + 1)) ℂ :=
  fun row col =>
    primeDeriv (q row).1 (primeProfileJetSource g m col)
      ((q row : ℕ) ^ e row)

/-- Every finite jet rectangle has a nonsingular separated-prime packet outside every finite set
of forbidden prime directions. -/
def CofinitePrimeProfileJetPacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I → ArithmeticFunction ℂ) : Prop :=
  ∀ (m : ℕ) (forbidden : Set Nat.Primes), forbidden.Finite →
    ∃ (q : I × Fin (m + 1) → Nat.Primes)
      (e : I × Fin (m + 1) → ℕ),
      Function.Injective q ∧
      (∀ row, q row ∉ forbidden) ∧
      (primeProfileJetPacketMatrix g m q e).det ≠ 0

/-- The arithmetic-function Jacobian of one explicit profile-jet packet. -/
def primeProfileJetArithmeticJacobian
    {I : Type*}
    (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (q : I × Fin (m + 1) → Nat.Primes) :
    Matrix (I × Fin (m + 1)) (I × Fin (m + 1)) (ArithmeticFunction ℂ) :=
  fun row col => primeDeriv (q row).1 (primeProfileJetSource g m col)

/-- A nonsingular scalar packet makes the full arithmetic-function Jacobian nonsingular. -/
theorem primeProfileJetArithmeticJacobian_det_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (m : ℕ) (q : I × Fin (m + 1) → Nat.Primes)
    (e : I × Fin (m + 1) → ℕ) (hq : Function.Injective q)
    (hdet : (primeProfileJetPacketMatrix g m q e).det ≠ 0) :
    (primeProfileJetArithmeticJacobian g m q).det ≠ 0 := by
  apply primeRayMatrix_det_ne_zero q hq e
  · intro row col
    exact primeDeriv_primeProfileRotatedLogJet_supportedOnPrimeRay
      (g col.1) (hsupport col.1) (q row) col.2
  · exact hdet

/-- The packet Jacobian embedded into the arithmetic-function fraction field. -/
def fractionPrimeProfileJetJacobian
    {I : Type*}
    (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (q : I × Fin (m + 1) → Nat.Primes) :
    Matrix (I × Fin (m + 1)) (I × Fin (m + 1))
      arithmeticFunctionFractionField :=
  fun row col =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeProfileJetArithmeticJacobian g m q row col)

theorem fractionPrimeProfileJetJacobian_apply
    {I : Type*}
    (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (q : I × Fin (m + 1) → Nat.Primes)
    (row col : I × Fin (m + 1)) :
    fractionPrimeProfileJetJacobian g m q row col =
      primeFractionDerivation (q row)
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeProfileJetSource g m col)) := by
  rw [fractionPrimeProfileJetJacobian, primeProfileJetArithmeticJacobian,
    primeFractionDerivation_algebraMap]

/-- A nonsingular arithmetic profile packet remains nonsingular in the fraction field. -/
theorem fractionPrimeProfileJetJacobian_det_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (m : ℕ) (q : I × Fin (m + 1) → Nat.Primes)
    (e : I × Fin (m + 1) → ℕ) (hq : Function.Injective q)
    (hdet : (primeProfileJetPacketMatrix g m q e).det ≠ 0) :
    (fractionPrimeProfileJetJacobian g m q).det ≠ 0 := by
  have hsource := primeProfileJetArithmeticJacobian_det_ne_zero
    g hsupport m q e hq hdet
  change ((algebraMap (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField).mapMatrix
      (primeProfileJetArithmeticJacobian g m q)).det ≠ 0
  rw [← RingHom.map_det]
  intro hzero
  apply hsource
  apply FaithfulSMul.algebraMap_injective (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField
  simpa using hzero

end


end GaloisForLFunctions.HTGeometry
