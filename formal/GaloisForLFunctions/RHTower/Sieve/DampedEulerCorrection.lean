import GaloisForLFunctions.RHTower.ZetaVerticalLineBound
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear

/-!
# The Euler correction of the damped Möbius series

The Dirichlet series of `μ(m)·t^{ω_P(m)}` is `1/ζ(s)` multiplied by the finite Euler product
`∏_{p ∈ P} (1 − t·p^{-s})/(1 − p^{-s})`.  On the half plane `Re s ≥ 1/2` that correction is bounded,
uniformly in `t ∈ [0,1]`, by `∏_{p ∈ P} (1 + p^{-Re s})/(1 − p^{-Re s})` — an `exp(O(∑_{p ∈ P} 1/p))`,
that is a polylog at the parameters of the Route E cards.

This is the factor by which a contour bound for the plain Möbius sum has to be widened to cover the
damped one, and it is bounded independently of `t`, which is what the transfer
`Sieve/DampedCofactorTransfer.norm_logPoly_ramareCofactorCoeff_le_of_uniform` requires.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- One Euler factor of the damped series, relative to the undamped one. -/
def dampedEulerFactor (t : ℝ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - (t : ℂ) * (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s))

/-- **One factor is bounded, uniformly in the damping.** -/
theorem norm_dampedEulerFactor_le {p : ℕ} (hp : 2 ≤ p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖dampedEulerFactor t p s‖
      ≤ (1 + (p : ℝ) ^ (-s.re)) / (1 - (p : ℝ) ^ (-s.re)) := by
  have hp1 : 1 ≤ p := by omega
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [RHTower.norm_natCast_cpow_zetaVerticalLineBound hp1, Complex.neg_re]
  have hpow0 : (0 : ℝ) < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hp0 _
  -- the damping factor never reaches one
  have hhalf : (p : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hmono : (p : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
    have hbase : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  have hlt1 : (p : ℝ) ^ (-s.re) < 1 := by
    have hsq : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by
      refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  have hden0 : (0 : ℝ) < 1 - (p : ℝ) ^ (-s.re) := by linarith
  -- numerator and denominator
  have hnum : ‖1 - (t : ℂ) * (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-s.re) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, hnorm]
    nlinarith [hpow0, ht1]
  have hden : (1 : ℝ) - (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hnorm] at h
    linarith
  rw [dampedEulerFactor, norm_div]
  rw [div_le_div_iff₀ (by linarith [hden, hden0]) hden0]
  nlinarith [hnum, hden, hden0, norm_nonneg ((1 : ℂ) - (p : ℂ) ^ (-s)),
    norm_nonneg ((1 : ℂ) - (t : ℂ) * (p : ℂ) ^ (-s)), hpow0]

/-- **The whole correction is bounded, uniformly in the damping.** -/
theorem norm_prod_dampedEulerFactor_le {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖∏ p ∈ P, dampedEulerFactor t p s‖
      ≤ ∏ p ∈ P, (1 + (p : ℝ) ^ (-s.re)) / (1 - (p : ℝ) ^ (-s.re)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) ?_
  intro p hp
  exact norm_dampedEulerFactor_le (hP p hp) ht0 ht1 hs

end

end RHTower.Sieve
