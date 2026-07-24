import GaloisForLFunctions.RHTower.MobiusGammaEulerDifferenceTailParity

/-!
# Iterated Gamma-Euler tail-parity

Inserting `k` normalized Euler factors composes `k` commuting Gamma-Euler central differences.  On
the Gamma characteristic the leading tail mode is annihilated and the next tail mode is scaled by the
product of the `k` next-mode eigenvalues, each of which is negative.  Hence the next tail coefficient
has sign `(-1)^(k+1)` (`gammaEulerIteratedNextCoefficient_sign`): an odd number of Euler differences
leaves an eventually positive correlation tail, an even number an eventually negative one — the exact
tail-parity obstruction that breaks prime-by-prime Gamma energy contraction after two channels.  The
coefficient is displayed in cosh-bracket form (`gammaEulerIteratedNextCoefficient_eq`, equation (4))
and specialises to the two-channel coefficient (`gammaEulerIteratedNextCoefficient_two`).
-/

open scoped BigOperators

namespace RHTower

/-- Coefficient of the next tail mode after `k` commuting Euler differences: the leading Gamma-tail
coefficient `-r * 2^r` multiplied by the `k` next-mode eigenvalues. -/
noncomputable def gammaEulerIteratedNextCoefficient (r : ℝ) {k : ℕ} (h : Fin k → ℝ) : ℝ :=
  -r * gammaEulerTailScale r *
    ∏ j, gammaEulerCentralDifferenceEigenvalue r (h j) (r / 2 + 1)

/-- **Iterated tail-parity.**  For `k` positive-scale Euler differences the next Gamma-tail
coefficient has sign `(-1)^(k+1)`: an odd number of differences leaves an eventually positive
correlation tail, an even number an eventually negative one.  Each next-mode eigenvalue is negative,
so the product of `k` of them times the negative leading coefficient alternates. -/
theorem gammaEulerIteratedNextCoefficient_sign {r : ℝ} (hr : 0 < r) {k : ℕ} {h : Fin k → ℝ}
    (hh : ∀ j, 0 < h j) :
    0 < (-1) ^ (k + 1) * gammaEulerIteratedNextCoefficient r h := by
  have heig : ∀ j, gammaEulerCentralDifferenceEigenvalue r (h j) (r / 2 + 1) < 0 :=
    fun j => gammaEulerCentralDifferenceEigenvalue_next_neg hr (hh j)
  have hP : (0 : ℝ) < ∏ j, (- gammaEulerCentralDifferenceEigenvalue r (h j) (r / 2 + 1)) :=
    Finset.prod_pos (fun j _ => neg_pos.mpr (heig j))
  have hne : ∏ j, (- gammaEulerCentralDifferenceEigenvalue r (h j) (r / 2 + 1))
      = (-1) ^ k * ∏ j, gammaEulerCentralDifferenceEigenvalue r (h j) (r / 2 + 1) := by
    rw [Finset.prod_neg]; simp
  have key : (-1) ^ (k + 1) * gammaEulerIteratedNextCoefficient r h
      = r * gammaEulerTailScale r *
          ∏ j, (- gammaEulerCentralDifferenceEigenvalue r (h j) (r / 2 + 1)) := by
    rw [gammaEulerIteratedNextCoefficient, hne, pow_succ]; ring
  rw [key]
  exact mul_pos (mul_pos hr (gammaEulerTailScale_pos r)) hP

/-- The iterated next-coefficient specialises to the two-channel coefficient. -/
theorem gammaEulerIteratedNextCoefficient_two (r h k : ℝ) :
    gammaEulerIteratedNextCoefficient r ![h, k] = gammaEulerTwoDifferenceNextCoefficient r h k := by
  rw [gammaEulerIteratedNextCoefficient, gammaEulerTwoDifferenceNextCoefficient, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Exact iterated tail-coefficient in cosh-bracket form (equation (4)): every bracket
`cosh((r/2+1)h_j) - cosh(r h_j/2)` is positive, so the sign is carried by `(-1)^(k+1)`. -/
theorem gammaEulerIteratedNextCoefficient_eq {r : ℝ} {k : ℕ} (h : Fin k → ℝ) :
    gammaEulerIteratedNextCoefficient r h
      = -r * gammaEulerTailScale r *
          ∏ j, 2 * (Real.cosh (r * h j / 2) - Real.cosh ((r / 2 + 1) * h j)) := by
  rw [gammaEulerIteratedNextCoefficient]
  refine congrArg _ (Finset.prod_congr rfl (fun j _ => ?_))
  rw [gammaEulerCentralDifferenceEigenvalue]

end RHTower
