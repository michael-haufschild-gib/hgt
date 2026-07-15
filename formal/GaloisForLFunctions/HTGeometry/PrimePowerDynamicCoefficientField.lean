import GaloisForLFunctions.HTGeometry.PrimePowerPacketJacobian

/-!
# Dynamic coefficient fields for prime-power packets

A polynomial over the finite-prime coefficient field exposes only finitely many active prime
directions.  The cofinite packet property below says that the exponent-block Jacobian can be made
nonsingular outside every such finite set.  The resulting independence theorem is therefore over
the full intrinsic finite-prime field, not merely over the complex constants.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix

noncomputable section

/-- Every finite forbidden set admits a globally distinct prime packet with nonzero exponent-block
Jacobian determinant. -/
def CofinitePrimePowerPacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (a : I → Nat.Primes → ℂ) : Prop :=
  ∀ forbidden : Set Nat.Primes, forbidden.Finite →
    ∃ q : I → Nat.Primes,
      Function.Injective q ∧
      (∀ i, q i ∉ forbidden) ∧
      (primePowerBlockMatrix e
        (primePowerPacketCoefficientMatrix e a q)).det ≠ 0

/-- A cofinite packet already yields algebraic independence over `ℂ`. -/
theorem algebraicIndependent_arithmeticPrimePowerColumns_of_cofinitePacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (hpacket : CofinitePrimePowerPacket e a) :
    AlgebraicIndependent ℂ
      (fun j => arithmeticOfPrimePowerColumn (e j) (a j)) := by
  obtain ⟨q, hq, havoid, hdet⟩ :=
    hpacket ∅ Set.finite_empty
  exact algebraicIndependent_arithmeticPrimePowerColumns_of_packet
    e a q hq hdet

/-- **Dynamic finite-prime prime-power theorem.**  A family with cofinite nonsingular
exponent-block packets remains algebraically independent over the entire finite-prime coefficient
field. -/
theorem algebraicIndependent_fractionPrimePowerColumns_over_finitePrimeCoefficientField
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (a : I → Nat.Primes → ℂ)
    (hpacket : CofinitePrimePowerPacket e a) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimePowerColumn (e j) (a j))) := by
  rw [algebraicIndependent_iff]
  intro P hPeval
  by_contra hPne
  have hPne' : P ≠ 0 := hPne
  obtain ⟨q, hq, havoid, hdet⟩ :=
    hpacket (polynomialPrimeActivity P) (polynomialPrimeActivity_finite P)
  have hAIK : AlgebraicIndependent (primeCommonKernelField q)
      (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimePowerColumn (e j) (a j))) :=
    algebraicIndependent_fractionPrimePowerColumns_over_commonKernel
      e a q hq hdet
  let Q : MvPolynomial I (primeCommonKernelField q) :=
    liftPolynomialToPrimeCommonKernel q P havoid
  have hQne : Q ≠ 0 :=
    liftPolynomialToPrimeCommonKernel_ne_zero q P havoid hPne'
  have hmap := map_liftPolynomialToPrimeCommonKernel q P havoid
  let g : I → arithmeticFunctionFractionField := fun j =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimePowerColumn (e j) (a j))
  have heval := congrArg (MvPolynomial.eval g) hmap
  have hQeval : MvPolynomial.aeval g Q = 0 := by
    have heq : MvPolynomial.aeval g Q = MvPolynomial.aeval g P := by
      simpa [Q, g, MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hPeval
  exact hQne (hAIK.eq_zero_of_aeval_eq_zero Q hQeval)

end

end GaloisForLFunctions.HTGeometry
