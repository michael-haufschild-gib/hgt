import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFiniteDetectorDirichlet
import GaloisForLFunctions.HTGeometry.TwistedDirichletMeanValue

/-!
# Displaced finite detector bridge to classical Dirichlet polynomials

The smooth AFE detector is naturally zero-indexed through `Sieve.dirPoly`, while the twisted
mean-value infrastructure uses positive natural indices through `HTGeometry.cdpoly`.  This file
provides the exact reindexing at `sigma = 0`; all displaced-line amplitudes already live in the
detector coefficients.
-/

noncomputable section

namespace RHTower

open Complex
open GaloisForLFunctions.HTGeometry

/-- Turn zero-based `Fin` coefficients into positive-natural coefficients. -/
def natPredCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ := a (n - 1)

private theorem sum_Icc_one_eq_sum_range
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (L : ℕ) :
    ∑ n ∈ Finset.Icc 1 L, f n = ∑ j ∈ Finset.range L, f (j + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- A positive-height `cdpoly` is exactly the negative-frequency `Sieve.dirPoly`
after the zero-based/positive-natural reindexing. -/
theorem cdpoly_natPredCoeff_Icc_zero_eq_sieveDirPoly_neg
    (L : ℕ) (a : ℕ → ℂ) (tau : ℝ) :
    cdpoly (natPredCoeff a) (Finset.Icc 1 L) 0 tau =
      Sieve.dirPoly L (fun n => a n) (-tau) := by
  rw [cdpoly, sum_Icc_one_eq_sum_range,
    sieveDirPoly_nat_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [cdterm, natPredCoeff, Nat.add_sub_cancel, neg_zero, Real.rpow_zero,
    Complex.ofReal_one, mul_one]
  congr 2
  push_cast
  ring

/-- The positive-frequency `Sieve.dirPoly` is the same `cdpoly` evaluated at
the reflected height. -/
theorem cdpoly_natPredCoeff_Icc_zero_neg_eq_sieveDirPoly
    (L : ℕ) (a : ℕ → ℂ) (tau : ℝ) :
    cdpoly (natPredCoeff a) (Finset.Icc 1 L) 0 (-tau) =
      Sieve.dirPoly L (fun n => a n) tau := by
  simpa using cdpoly_natPredCoeff_Icc_zero_eq_sieveDirPoly_neg L a (-tau)

end RHTower
