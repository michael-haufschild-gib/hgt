import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirichletMeanValueBridge
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifier

/-!
# Displaced finite detector with the linear Levinson mollifier

The positive-natural linear mollifier is reindexed into the zero-based `Fin M` convention used by
`Sieve.dirConv`.  Substitution into the exact finite detector identity yields one direct convolution
polynomial and retains both reflected heads and pole terms exactly.
-/

noncomputable section

namespace RHTower

open Complex
open GaloisForLFunctions.HTGeometry

/-- Zero-based coefficient vector of the positive-natural linear mollifier. -/
def levinsonLinearMollifierFinCoeff (M : ℕ) : Fin M → ℂ :=
  fun n => Sieve.levinsonLinearMollifierCoeff M ((n : ℕ) + 1)

/-- The zero-based and positive-natural presentations of the linear mollifier
agree exactly. -/
theorem sieveDirPoly_levinsonLinearMollifierFinCoeff_neg
    (M : ℕ) (tau : ℝ) :
    Sieve.dirPoly M (levinsonLinearMollifierFinCoeff M) (-tau) =
      Sieve.levinsonLinearMollifier M tau := by
  rw [Sieve.levinsonLinearMollifier]
  change Sieve.dirPoly M
      (fun n => Sieve.levinsonLinearMollifierCoeff M ((n : ℕ) + 1)) (-tau) = _
  rw [← cdpoly_natPredCoeff_Icc_zero_eq_sieveDirPoly_neg M
    (fun n => Sieve.levinsonLinearMollifierCoeff M (n + 1)) tau]
  unfold cdpoly
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  simp only [cdterm, natPredCoeff]
  rw [Nat.sub_add_cancel hn1]

/-- Exact finite displaced detector normal form after multiplication by the
literal linear Levinson mollifier. -/
theorem smoothAFEZetaDisplacedFiniteClassicalDetector_mul_levinsonLinearMollifier
    (lam d x tau : ℝ) (L M : ℕ) :
    smoothAFEZetaDisplacedFiniteClassicalDetector lam d x tau L *
        Sieve.levinsonLinearMollifier M tau =
      Sieve.dirPoly (L * M)
          (Sieve.dirConv L M
            (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n)
            (levinsonLinearMollifierFinCoeff M)) (-tau) +
        (lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
          (Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau *
            Sieve.levinsonLinearMollifier M tau) +
        zetaChi (displacedLinePt d tau) *
          (Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau *
            Sieve.levinsonLinearMollifier M tau) -
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x *
          Sieve.levinsonLinearMollifier M tau +
        (lam : ℂ) * I *
          smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau *
            Sieve.levinsonLinearMollifier M tau := by
  simpa only [sieveDirPoly_levinsonLinearMollifierFinCoeff_neg] using
    smoothAFEZetaDisplacedFiniteClassicalDetector_mul_dirPoly
      lam d x tau L M (levinsonLinearMollifierFinCoeff M)

end RHTower
