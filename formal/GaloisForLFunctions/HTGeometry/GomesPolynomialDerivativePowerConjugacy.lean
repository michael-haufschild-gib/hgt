import GaloisForLFunctions.HTGeometry.GomesDividedMonomialResidueChains
import GaloisForLFunctions.HTGeometry.GomesRepeatedOperatorCommutant

/-!
# Higher differentiation is conjugate to repeated differentiation

Residue-chain coordinates identify the actual m-th polynomial derivative with m
copies of the first derivative. This is an algebraic conjugacy on all polynomials.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- Residue-chain coordinates intertwine every positive derivative power with repeated differentiation. -/
theorem gomesPolynomialResidueChainEquiv_intertwines (m : ℕ) [NeZero m] :
    (gomesPolynomialResidueChainEquiv K m).toLinearMap.comp
      (Polynomial.derivative ^ m : Module.End K K[X]) =
        (gomesRepeatedEndomorphism K (Fin m) Polynomial.derivative).comp
          (gomesPolynomialResidueChainEquiv K m).toLinearMap := by
  apply ((gomesDividedMonomialBasis K).reindex (Nat.divModEquiv m)).ext
  rintro ⟨n, r⟩
  rw [Module.Basis.reindex_apply, Nat.divModEquiv_symm_apply]
  change gomesPolynomialResidueChainEquiv K m
      ((Polynomial.derivative ^ m : Module.End K K[X])
        (gomesDividedMonomialBasis K (n * m + r.val))) =
    gomesRepeatedEndomorphism K (Fin m) Polynomial.derivative
      (gomesPolynomialResidueChainEquiv K m (gomesDividedMonomialBasis K (n * m + r.val)))
  rw [gomesPolynomialResidueChainEquiv_basis, gomesRepeatedEndomorphism_single]
  cases n with
  | zero =>
      rw [Nat.zero_mul, Nat.zero_add, gomesDividedMonomialBasis_derivative_pow_residue_zero,
        map_zero, gomesDividedMonomialBasis_derivative_zero, Pi.single_zero]
  | succ n =>
      rw [gomesDividedMonomialBasis_derivative_pow_residue_succ,
        gomesPolynomialResidueChainEquiv_basis, gomesDividedMonomialBasis_derivative_succ]

/-- Conjugation transports the full higher derivative to a finite repetition of the first derivative. -/
theorem gomesPolynomialResidueChainEquiv_conjugacy (m : ℕ) [NeZero m] :
    (gomesPolynomialResidueChainEquiv K m).conjAlgEquiv K
      (Polynomial.derivative ^ m : Module.End K K[X]) =
        gomesRepeatedEndomorphism K (Fin m) Polynomial.derivative := by
  apply LinearMap.ext
  intro P
  change gomesPolynomialResidueChainEquiv K m
    ((Polynomial.derivative ^ m : Module.End K K[X])
      ((gomesPolynomialResidueChainEquiv K m).symm P)) = _
  have h := congrArg (fun L : K[X] →ₗ[K] (Fin m → K[X]) =>
    L ((gomesPolynomialResidueChainEquiv K m).symm P))
      (gomesPolynomialResidueChainEquiv_intertwines K m)
  change gomesPolynomialResidueChainEquiv K m
    ((Polynomial.derivative ^ m : Module.End K K[X])
      ((gomesPolynomialResidueChainEquiv K m).symm P)) =
        gomesRepeatedEndomorphism K (Fin m) Polynomial.derivative
          (gomesPolynomialResidueChainEquiv K m ((gomesPolynomialResidueChainEquiv K m).symm P)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

end GaloisForLFunctions.HTGeometry
