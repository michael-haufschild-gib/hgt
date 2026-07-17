import GaloisForLFunctions.HTGeometry.PrimeProfileJetPacket

/-!
# Common-kernel independence for one prime-profile jet packet

This leaf converts the separated prime-ray determinant into algebraic independence over the
common kernel of the chosen prime derivations.  It is kept separate from the packet construction
to minimize elaboration and cache each stage independently.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- One separated packet gives algebraic independence over the common kernel of its selected
prime derivations. -/
theorem algebraicIndependent_fractionPrimeProfileJets_over_commonKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
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
