import GaloisForLFunctions.HTGeometry.GomesDividedMonomialBasis
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Residue chains of divided monomials

The m-th derivative lowers the divided-monomial index by m. Grouping indices by
quotient and remainder gives m independent copies of the original derivative chain.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- Every derivative power has an exact lowering formula on all divided monomials. -/
theorem gomesDividedMonomialBasis_derivative_pow (m n : ℕ) :
    (Polynomial.derivative ^ m : Module.End K K[X]) (gomesDividedMonomialBasis K n) =
      if m ≤ n then gomesDividedMonomialBasis K (n - m) else 0 := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
      cases n with
      | zero =>
          rw [pow_succ, Module.End.mul_apply, gomesDividedMonomialBasis_derivative_zero, map_zero]
          simp
      | succ n =>
          rw [pow_succ, Module.End.mul_apply, gomesDividedMonomialBasis_derivative_succ, ih]
          simp only [Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub]

/-- Derivative powers lower an index containing a full extra block exactly. -/
theorem gomesDividedMonomialBasis_derivative_pow_add (n m : ℕ) :
    (Polynomial.derivative ^ m : Module.End K K[X]) (gomesDividedMonomialBasis K (n + m)) =
      gomesDividedMonomialBasis K n := by
  rw [gomesDividedMonomialBasis_derivative_pow, if_pos (Nat.le_add_left m n), Nat.add_sub_cancel]

/-- Each residue-chain bottom is killed by its full derivative block. -/
theorem gomesDividedMonomialBasis_derivative_pow_residue_zero (m : ℕ) (r : Fin m) :
    (Polynomial.derivative ^ m : Module.End K K[X]) (gomesDividedMonomialBasis K r.val) = 0 := by
  rw [gomesDividedMonomialBasis_derivative_pow, if_neg (Nat.not_le.mpr r.is_lt)]

/-- Within each residue class the full derivative block lowers the chain counter by one. -/
theorem gomesDividedMonomialBasis_derivative_pow_residue_succ (m n : ℕ) (r : Fin m) :
    (Polynomial.derivative ^ m : Module.End K K[X])
      (gomesDividedMonomialBasis K ((n + 1) * m + r.val)) =
        gomesDividedMonomialBasis K (n * m + r.val) := by
  rw [Nat.succ_mul, Nat.add_right_comm, gomesDividedMonomialBasis_derivative_pow_add]

/-- Divided monomials in each component give a basis for the finite product of polynomial spaces. -/
def gomesPolynomialChainBasis (m : ℕ) : Module.Basis (ℕ × Fin m) K (Fin m → K[X]) :=
  (gomesDividedMonomialBasis K).smulTower (Pi.basisFun K[X] (Fin m))

/-- A chain basis element is one divided monomial in exactly one component. -/
theorem gomesPolynomialChainBasis_apply (m n : ℕ) (r : Fin m) :
    gomesPolynomialChainBasis K m (n, r) = Pi.single r (gomesDividedMonomialBasis K n) := by
  rw [gomesPolynomialChainBasis, Module.Basis.smulTower_apply, Pi.basisFun_apply]
  ext i
  by_cases h : r = i
  · subst i
    simp [smul_eq_mul]
  · simp [Ne.symm h]

/-- Grouping divided monomial indices by quotient and remainder gives the residue-chain coordinates. -/
def gomesPolynomialResidueChainEquiv (m : ℕ) [NeZero m] : K[X] ≃ₗ[K] (Fin m → K[X]) :=
  (gomesDividedMonomialBasis K).equiv (gomesPolynomialChainBasis K m) (Nat.divModEquiv m)

/-- Residue-chain coordinates preserve the counter and residue on every divided monomial. -/
theorem gomesPolynomialResidueChainEquiv_basis (m : ℕ) [NeZero m] (n : ℕ) (r : Fin m) :
    gomesPolynomialResidueChainEquiv K m (gomesDividedMonomialBasis K (n * m + r.val)) =
      Pi.single r (gomesDividedMonomialBasis K n) := by
  change (gomesDividedMonomialBasis K).equiv (gomesPolynomialChainBasis K m) (Nat.divModEquiv m)
    (gomesDividedMonomialBasis K ((Nat.divModEquiv m).symm (n, r))) = _
  rw [Module.Basis.equiv_apply, Equiv.apply_symm_apply, gomesPolynomialChainBasis_apply]

end GaloisForLFunctions.HTGeometry
