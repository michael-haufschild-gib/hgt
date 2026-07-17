import GaloisForLFunctions.HTGeometry.PrimeProfileJetCommonKernel
import GaloisForLFunctions.HTGeometry.PrimePowerDynamicCoefficientField
import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField

/-!
# Dynamic finite-prime descent for arbitrary prime-power profile jets

If every finite jet rectangle admits a nonsingular separated-prime packet outside every finite
set of prime directions, then the whole differential family is independent over the intrinsic
finite-prime coefficient field.  This leaf contains only the common-kernel descent; the packet
Jacobian is isolated in `PrimeProfileJetPacket` so both results can be checked and cached
independently.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

/-- The local profile coefficient jet advances by one rotated logarithmic derivation. -/
theorem primeProfileRotatedLogJet_succ (k : ℕ) (f : ArithmeticFunction ℂ) :
    Complex.I • logWeight (primeProfileRotatedLogJet k f) =
      primeProfileRotatedLogJet (k + 1) f := by
  ext n
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, logWeight_apply,
    primeProfileRotatedLogJet_apply, pow_succ]
  ring

/-- Differential jets in the arithmetic-function fraction field are the explicit profile
coefficient jets. -/
@[simp]
theorem differentialJet_algebraMap_primeProfileRotatedLogJet
    (k : ℕ) (f : ArithmeticFunction ℂ) :
    GaloisForLFunctions.differentialJet k
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeProfileRotatedLogJet k f) := by
  induction k with
  | zero =>
      have hzero : primeProfileRotatedLogJet 0 f = f := by
        ext n
        simp [primeProfileRotatedLogJet]
      simp [hzero]
  | succ k ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih,
        arithmeticFunctionFractionField_deriv_apply,
        rotatedLogFractionDerivation_algebraMap,
        primeProfileRotatedLogJet_succ]

/-- **Dynamic finite-prime profile-jet theorem.** Cofinite separated packets keep every finite
jet rectangle algebraically independent over the whole intrinsic finite-prime coefficient field. -/
theorem algebraicIndependent_fractionPrimeProfileJets_over_finitePrimeCoefficientField
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (hpacket : CofinitePrimeProfileJetPacket g) (m : ℕ) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun col : I × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeProfileJetSource g m col)) := by
  rw [algebraicIndependent_iff]
  intro P hPeval
  by_contra hPne
  have hPne' : P ≠ 0 := hPne
  obtain ⟨q, e, hq, havoid, hdet⟩ :=
    hpacket m (polynomialPrimeActivity P) (polynomialPrimeActivity_finite P)
  have hAIK : AlgebraicIndependent (primeCommonKernelField q)
      (fun col : I × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeProfileJetSource g m col)) :=
    algebraicIndependent_fractionPrimeProfileJets_over_commonKernel
      g hsupport m q e hq hdet
  let Q : MvPolynomial (I × Fin (m + 1)) (primeCommonKernelField q) :=
    liftPolynomialToPrimeCommonKernel q P havoid
  have hQne : Q ≠ 0 :=
    liftPolynomialToPrimeCommonKernel_ne_zero q P havoid hPne'
  have hmap := map_liftPolynomialToPrimeCommonKernel q P havoid
  let y : I × Fin (m + 1) → arithmeticFunctionFractionField := fun col =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeProfileJetSource g m col)
  have heval := congrArg (MvPolynomial.eval y) hmap
  have hQeval : MvPolynomial.aeval y Q = 0 := by
    have heq : MvPolynomial.aeval y Q = MvPolynomial.aeval y P := by
      simpa [Q, y, MvPolynomial.aeval_def, MvPolynomial.eval_map] using heval
    exact heq.trans hPeval
  exact hQne (hAIK.eq_zero_of_aeval_eq_zero Q hQeval)

/-- **Prime-profile differential independence over the Euler coefficient field.**  A cofinite
profile-jet packet at every finite order gives independence of the complete differential tower. -/
theorem differentialIndependent_fractionPrimeProfiles_over_finitePrimeCoefficientField
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (g : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (hpacket : CofinitePrimeProfileJetPacket g) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g i)) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_algebraMap_primeProfileRotatedLogJet]
  let y : I → ℕ → arithmeticFunctionFractionField := fun i k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeProfileRotatedLogJet k (g i))
  apply algebraicIndependent_prod_nat_of_fin y
  intro m
  simpa only [y, primeProfileJetSource] using
    algebraicIndependent_fractionPrimeProfileJets_over_finitePrimeCoefficientField
      g hsupport hpacket m

end


end GaloisForLFunctions.HTGeometry
