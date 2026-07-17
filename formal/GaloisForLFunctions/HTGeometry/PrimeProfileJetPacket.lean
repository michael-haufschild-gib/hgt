import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon
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

/-- The explicit finite jet family of a positive-prime-power source packet. -/
def primeProfileJetSource
    {I : Type*} (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (x : I × Fin (m + 1)) : ArithmeticFunction ℂ :=
  rotatedLogArithmeticJet x.2 (g x.1)

/-- The scalar Jacobian read at one selected valuation coordinate on each separated prime ray. -/
def primeProfileJetPacketMatrix
    {I : Type*} [Fintype I]
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
    {I : Type*} [Fintype I]
    (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (q : I × Fin (m + 1) → Nat.Primes) :
    Matrix (I × Fin (m + 1)) (I × Fin (m + 1)) (ArithmeticFunction ℂ) :=
  fun row col => primeDeriv (q row).1 (primeProfileJetSource g m col)

/-- A nonsingular scalar packet makes the full arithmetic-function Jacobian nonsingular. -/
theorem primeProfileJetArithmeticJacobian_det_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, SupportedOnPositivePrimePowers (g i))
    (m : ℕ) (q : I × Fin (m + 1) → Nat.Primes)
    (e : I × Fin (m + 1) → ℕ) (hq : Function.Injective q)
    (hdet : (primeProfileJetPacketMatrix g m q e).det ≠ 0) :
    (primeProfileJetArithmeticJacobian g m q).det ≠ 0 := by
  apply primeRayMatrix_det_ne_zero q hq e
  · intro row col
    exact primeDeriv_rotatedLogArithmeticJet_supportedOnPrimeRay
      (g col.1) (hsupport col.1) (q row) col.2
  · exact hdet

/-- The packet Jacobian embedded into the arithmetic-function fraction field. -/
def fractionPrimeProfileJetJacobian
    {I : Type*} [Fintype I]
    (g : I → ArithmeticFunction ℂ) (m : ℕ)
    (q : I × Fin (m + 1) → Nat.Primes) :
    Matrix (I × Fin (m + 1)) (I × Fin (m + 1))
      arithmeticFunctionFractionField :=
  fun row col =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeProfileJetArithmeticJacobian g m q row col)

theorem fractionPrimeProfileJetJacobian_apply
    {I : Type*} [Fintype I]
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
    (hsupport : ∀ i, SupportedOnPositivePrimePowers (g i))
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

/-- One separated packet gives algebraic independence over the common kernel of its selected
prime derivations. -/
theorem algebraicIndependent_fractionPrimeProfileJets_over_commonKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, SupportedOnPositivePrimePowers (g i))
    (m : ℕ) (q : I × Fin (m + 1) → Nat.Primes)
    (e : I × Fin (m + 1) → ℕ) (hq : Function.Injective q)
    (hdet : (primeProfileJetPacketMatrix g m q e).det ≠ 0) :
    AlgebraicIndependent (primeCommonKernelField q)
      (fun col => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (primeProfileJetSource g m col)) := by
  let M := fractionPrimeProfileJetJacobian g m q
  have hM : M.det ≠ 0 :=
    fractionPrimeProfileJetJacobian_det_ne_zero
      g hsupport m q e hq hdet
  refine algebraicIndependent_of_domain_jacobian
    (K := primeCommonKernelField q)
    (R := arithmeticFunctionFractionField)
    (fun col => algebraMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField (primeProfileJetSource g m col))
    (fun row => primeCommonKernelDerivation q row)
    (fun row x y => map_add (primeCommonKernelDerivation q row) x y)
    (fun row x y => by
      simpa only [Algebra.smul_def] using
        (primeCommonKernelDerivation q row).leibniz x y)
    (fun row c => (primeCommonKernelDerivation q row).map_algebraMap c)
    M hM ?_
  intro row col
  exact (fractionPrimeProfileJetJacobian_apply g m q row col).symm

end


end GaloisForLFunctions.HTGeometry
