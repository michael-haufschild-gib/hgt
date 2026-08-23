import GaloisForLFunctions.RHTower.EulerSourceJetOpenness
import GaloisForLFunctions.RHTower.FriableMomentBellEvaluation

/-!
# The friable Euler flux jet lands in the period filtration

The corpus already computes every `s`-derivative of the degree-one Euler logarithmic flux in closed
form, `(log p)(-log p)^j A_j(w)/(1-w)^{j+1}` with `w = p^{-s}`.  At a positive integer argument `w`
is rational and the Eulerian-type polynomials `A_j` have rational coefficients, so the whole jet is
a rational multiple of `(log p)^{j+1}`.
-/

namespace RHTower

noncomputable section

/-- The Eulerian-type jet polynomials over `ℚ`. -/
def eulerJetPolyQ : ℕ → Polynomial ℚ
  | 0 => Polynomial.X
  | (j + 1) => Polynomial.X * ((1 - Polynomial.X) * Polynomial.derivative (eulerJetPolyQ j)
      + Polynomial.C ((j : ℚ) + 1) * eulerJetPolyQ j)

theorem eulerJetPolyQ_succ (j : ℕ) :
    eulerJetPolyQ (j + 1) = Polynomial.X * ((1 - Polynomial.X) *
      Polynomial.derivative (eulerJetPolyQ j) + Polynomial.C ((j : ℚ) + 1) * eulerJetPolyQ j) := rfl

/-- The Eulerian-type jet polynomials have rational coefficients. -/
theorem map_eulerJetPolyQ (j : ℕ) :
    (eulerJetPolyQ j).map (algebraMap ℚ ℂ) = eulerJetPoly j := by
  induction j with
  | zero =>
    rw [eulerJetPolyQ, eulerJetPoly, Polynomial.map_X]
  | succ j ih =>
    rw [eulerJetPolyQ_succ, eulerJetPoly_succ, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_X, ← Polynomial.derivative_map, ih, Polynomial.map_mul,
      Polynomial.map_C, ih]
    congr 2
    push_cast
    ring

theorem cpow_neg_natSucc {p : ℕ} (hp : 0 < p) (j : ℕ) :
    (p : ℂ) ^ (-((j : ℂ) + 1)) = ((1 / (p : ℚ) ^ (j + 1) : ℚ) : ℂ) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show (-((j : ℂ) + 1)) = -((j + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [one_div]

theorem eval_map_ratCast_poly (Q : Polynomial ℚ) (q : ℚ) :
    Polynomial.eval ((q : ℚ) : ℂ) (Q.map (algebraMap ℚ ℂ))
      = ((Polynomial.eval q Q : ℚ) : ℂ) := by
  have hq : ((q : ℚ) : ℂ) = algebraMap ℚ ℂ q := rfl
  rw [hq, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rfl

/-- **The local flux jet at a positive integer is a rational multiple of a power of `log p`.** -/
theorem localFluxJet_one_natSucc {p : ℕ} (hp : 2 ≤ p) (i j : ℕ) :
    localFluxJet p 1 i ((j : ℂ) + 1)
      = ((Real.log p : ℝ) : ℂ) ^ (i + 1)
        * (((-1) ^ i * Polynomial.eval (1 / (p : ℚ) ^ (j + 1)) (eulerJetPolyQ i)
            / (1 - 1 / (p : ℚ) ^ (j + 1)) ^ (i + 1) : ℚ) : ℂ) := by
  have hp0 : 0 < p := by omega
  have hw : (1 : ℂ) * (p : ℂ) ^ (-((j : ℂ) + 1)) = ((1 / (p : ℚ) ^ (j + 1) : ℚ) : ℂ) := by
    rw [one_mul, cpow_neg_natSucc hp0 j]
  rw [localFluxJet, hw, ← map_eulerJetPolyQ i, eval_map_ratCast_poly]
  push_cast
  ring

/-- The local flux jet at a positive integer lies in the period filtration. -/
theorem localFluxJet_one_natSucc_mem_periodFilt {S : Finset ℕ} {p : ℕ} (hp : p ∈ S)
    (hp2 : 2 ≤ p) (i j : ℕ) :
    localFluxJet p 1 i ((j : ℂ) + 1) ∈ periodFilt S (i + 1) := by
  rw [localFluxJet_one_natSucc hp2 i j]
  have hpow : ((Real.log p : ℝ) : ℂ) ^ (i + 1) ∈ periodFilt S (i + 1) := by
    have h := pow_mem_periodFilt (log_mem_periodFilt hp) (i + 1)
    rwa [one_mul] at h
  have hsmul := (periodFilt S (i + 1)).smul_mem
    ((-1 : ℚ) ^ i * Polynomial.eval (1 / (p : ℚ) ^ (j + 1)) (eulerJetPolyQ i)
      / (1 - 1 / (p : ℚ) ^ (j + 1)) ^ (i + 1)) hpow
  rwa [Rat.smul_def, mul_comm] at hsmul

end

end RHTower
