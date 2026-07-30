import GaloisForLFunctions.HTGeometry.PrimePowerArithmeticColumn

/-!
# Finite prime-power packets

This file converts the prime-power lowering law and block coefficient identity into algebraic
independence.  The exponent map may be nonconstant.  Cross-exponent entries are present in the
full arithmetic Jacobian, but the distinguished prime-power coefficient sees only the diagonal
exponent blocks.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix

noncomputable section

/-- Scalar masses of the prime-power Jacobian. -/
def primePowerPacketCoefficientMatrix
    {I : Type*} (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) : Matrix I I ℂ :=
  fun i j => (((e j + 1 : ℕ) : ℂ) * a j (q i))

/-- The actual arithmetic-function Jacobian of a prime-power packet. -/
def primePowerPacketJacobian
    {I : Type*} (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) : Matrix I I (ArithmeticFunction ℂ) :=
  primePowerPointMassMatrix q e (primePowerPacketCoefficientMatrix e a q)

theorem primePowerPacketJacobian_apply
    {I : Type*} (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) (i j : I) :
    primePowerPacketJacobian e a q i j =
      primeDeriv (q i).1 (arithmeticOfPrimePowerColumn (e j) (a j)) := by
  rw [primeDeriv_arithmeticOfPrimePowerColumn]
  rfl

/-- **Finite prime-power packet criterion over `ℂ`.**  A nonzero exponent-block evaluation
determinant makes the full family of power-supported arithmetic columns algebraically independent.
-/
theorem algebraicIndependent_arithmeticPrimePowerColumns_of_packet
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (hdet : (primePowerBlockMatrix e
      (primePowerPacketCoefficientMatrix e a q)).det ≠ 0) :
    AlgebraicIndependent ℂ
      (fun j => arithmeticOfPrimePowerColumn (e j) (a j)) := by
  let M := primePowerPacketJacobian e a q
  have hM : M.det ≠ 0 := by
    exact primePowerPointMassMatrix_det_ne_zero q hq e
      (primePowerPacketCoefficientMatrix e a q) hdet
  refine algebraicIndependent_of_domain_jacobian
    (K := ℂ) (R := ArithmeticFunction ℂ)
    (fun j => arithmeticOfPrimePowerColumn (e j) (a j))
    (fun i => primeDeriv (q i).1)
    (fun i => primeDeriv_add (q i).1)
    (fun i => primeDeriv_mul (q i).1 (q i).2)
    (fun i => primeDeriv_algebraMap (q i).1 (q i).2)
    M hM ?_
  intro i j
  exact (primePowerPacketJacobian_apply e a q i j).symm

/-- The arithmetic packet Jacobian embedded in the fraction field. -/
def fractionPrimePowerPacketJacobian
    {I : Type*} (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) : Matrix I I arithmeticFunctionFractionField :=
  fun i j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
    (primePowerPacketJacobian e a q i j)

theorem fractionPrimePowerPacketJacobian_apply
    {I : Type*} (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) (i j : I) :
    fractionPrimePowerPacketJacobian e a q i j =
      primeFractionDerivation (q i)
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimePowerColumn (e j) (a j))) := by
  rw [fractionPrimePowerPacketJacobian]
  rw [primePowerPacketJacobian_apply]
  rw [primeFractionDerivation_algebraMap]

/-- A nonzero arithmetic packet determinant remains nonzero in the fraction field. -/
theorem fractionPrimePowerPacketJacobian_det_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (hdet : (primePowerBlockMatrix e
      (primePowerPacketCoefficientMatrix e a q)).det ≠ 0) :
    (fractionPrimePowerPacketJacobian e a q).det ≠ 0 := by
  have hsource : (primePowerPacketJacobian e a q).det ≠ 0 :=
    primePowerPointMassMatrix_det_ne_zero q hq e
      (primePowerPacketCoefficientMatrix e a q) hdet
  change ((algebraMap (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField).mapMatrix
      (primePowerPacketJacobian e a q)).det ≠ 0
  rw [← RingHom.map_det]
  intro hzero
  apply hsource
  apply FaithfulSMul.algebraMap_injective (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField
  simpa using hzero

/-- **Finite prime-power packet criterion over the packet common kernel.**  This is the local
theorem consumed by the dynamic finite-prime coefficient argument: coefficients killed by every
chosen prime derivation do not reduce the independence of the dilation layers. -/
theorem algebraicIndependent_fractionPrimePowerColumns_over_commonKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (hdet : (primePowerBlockMatrix e
      (primePowerPacketCoefficientMatrix e a q)).det ≠ 0) :
    AlgebraicIndependent (primeCommonKernelField q)
      (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimePowerColumn (e j) (a j))) := by
  let M := fractionPrimePowerPacketJacobian e a q
  have hM : M.det ≠ 0 :=
    fractionPrimePowerPacketJacobian_det_ne_zero e a q hq hdet
  refine algebraicIndependent_of_domain_jacobian
    (K := primeCommonKernelField q)
    (R := arithmeticFunctionFractionField)
    (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimePowerColumn (e j) (a j)))
    (fun i => primeCommonKernelDerivation q i)
    (fun i x y => map_add (primeCommonKernelDerivation q i) x y)
    (fun i x y => by
      simpa only [Algebra.smul_def] using!
        (primeCommonKernelDerivation q i).leibniz x y)
    (fun i c => (primeCommonKernelDerivation q i).map_algebraMap c)
    M hM ?_
  intro i j
  exact (fractionPrimePowerPacketJacobian_apply e a q i j).symm

end

end GaloisForLFunctions.HTGeometry
