import GaloisForLFunctions.RHTower.ParabolicMassBlowup
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Divisor-level dominated convergence for the parabolic mass jet

The parabolic gap bound `a(M-a) ≥ (35/108)R` makes the massive half-wave factor uniformly smaller
than `e^{-(35t/54)R}` for every `a ≥ 1`, so a summable majorant over the divisor lets the termwise
parabolic limit pass to the sum.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **The uniform exponential majorant of the massive half-wave factor.** -/
theorem norm_parabolic_factor_le {a t R J M K : ℝ} (hR : 3 < R) (hJ : |J| ≤ 1 / 2) (ha : 1 ≤ a)
    (hM : 0 < M) (hsq : M ^ (2 : ℕ) - K ^ (2 : ℕ) = R ^ (2 : ℕ) - J ^ (2 : ℕ) + a ^ (2 : ℕ)) (hprod : M * K = R * J)
    (ht : 0 < t) {beta : ℂ} (hbre : beta.re = M) :
    ‖Complex.exp (2 * (a : ℂ) ^ (2 : ℕ) * (t : ℂ)) * Complex.exp (-(2 * (a : ℂ) * (t : ℂ) * beta))‖
      ≤ Real.exp (-(35 * t / 54) * R) := by
  have hgap := parabolic_gap_uniform_lower hR hJ ha hM hsq hprod
  have hre1 : (2 * (a : ℂ) ^ (2 : ℕ) * (t : ℂ)).re = 2 * a ^ (2 : ℕ) * t := by
    rw [show (2 : ℂ) * (a : ℂ) ^ (2 : ℕ) * (t : ℂ) = (((2 * a ^ (2 : ℕ) * t : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hre2 : (-(2 * (a : ℂ) * (t : ℂ) * beta)).re = -(2 * a * t * beta.re) := by
    rw [show -(2 * (a : ℂ) * (t : ℂ) * beta) = (((-(2 * a * t) : ℝ)) : ℂ) * beta by
      push_cast; ring]
    simp [Complex.mul_re]
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, hre1, hre2, hbre, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [hgap, ht]

/-- **(24.109) Divisor-level dominated convergence.**  With a summable majorant the termwise
parabolic heat limit passes to the whole divisor sum. -/
theorem tendsto_parabolic_divisor_sum {ι : Type*} (P w : ι → ℂ) (beta : ι → ℝ → ℂ)
    (hbeta : ∀ q a, beta q a ^ (2 : ℕ) = (a : ℂ) ^ (2 : ℕ) + w q)
    (hre : ∀ q a, 0 ≤ (beta q a).re) (t : ℝ)
    (bound : ι → ℝ) (hsum : Summable bound)
    (hb : ∀ᶠ a : ℝ in atTop, ∀ q,
      ‖P q * (Complex.exp (2 * (a : ℂ) ^ (2 : ℕ) * (t : ℂ))
        * Complex.exp (-(2 * (a : ℂ) * (t : ℂ) * beta q a)))‖ ≤ bound q) :
    Tendsto (fun a : ℝ => ∑' q, P q * (Complex.exp (2 * (a : ℂ) ^ (2 : ℕ) * (t : ℂ))
        * Complex.exp (-(2 * (a : ℂ) * (t : ℂ) * beta q a))))
      atTop (nhds (∑' q, P q * Complex.exp (-(t : ℂ) * w q))) := by
  refine tendsto_tsum_of_dominated_convergence hsum (fun q => ?_) hb
  exact (tendsto_parabolic_heat (fun a => hbeta q a) (fun a => hre q a) t).const_mul (P q)

end

end RHTower
