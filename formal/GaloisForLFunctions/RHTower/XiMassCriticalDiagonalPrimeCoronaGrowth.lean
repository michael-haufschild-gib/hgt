import GaloisForLFunctions.RHTower.XiMassCriticalDiagonalPrimeCorona
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Quadratic growth law on the critical mass phase wall

The critical diagonal-corona theorem reduces the literal prime source to a moving finite Xi packet.
The corpus's unconditional exterior-probe budget bounds the number of divisor copies of height at
most `T` by `3(T²+1)/50`.  Applying that capacity theorem to the critical corona yields a complete
quadratic envelope for the literal von-Mangoldt source on `4σv=1`.

This closes the first three-regime phase classification: exponential absorption above the wall,
unconditional polynomial growth on the wall, and numerically certified exponential escape below
the wall.  No RH, zero-free, or cancellation assumption enters the boundary theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- The critical Xi corona contains at most quadratically many divisor copies. -/
theorem xiMassCriticalDiagonalCorona_card_le_quadratic
    {a : ℝ} (ha : 2 ≤ a) :
    ((xiMassCriticalDiagonalCorona a).card : ℝ) ≤
      3 * ((2 * (a - 1 / 2)) ^ 2 + 1) / 50 := by
  apply card_le_of_height_le_certified (T := 2 * (a - 1 / 2))
  intro q hq
  have hmem := xiPoissonAbstract.mem_criticalDiagonalCorona.mp hq
  have hR : (xiPoissonPoint q).re ≤ 2 * (a - 1 / 2) := by
    simpa only [xiMassCriticalDiagonalCorona, xiPoissonAbstract_pt] using hmem.2
  have heq := xiPoissonPoint_re_eq_abs q
  rw [heq] at hR
  have hT : 0 ≤ 2 * (a - 1 / 2) := by linarith
  have hsquare := mul_self_le_mul_self (abs_nonneg (xiSpectralPoint q).re) hR
  nlinarith [sq_abs (xiSpectralPoint q).re]

/-- Unconditional quadratic envelope for the literal prime source on the exact critical wall. -/
theorem norm_xiMassBottomPrimeIntegral_critical_le_quadratic
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) (u : ℝ) :
    let a := xiObliqueComovingMass v u
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ *
          (3 * ((2 * (a - 1 / 2)) ^ 2 + 1) / 50) +
        ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (σ / 12) +
        xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let a : ℝ := xiObliqueComovingMass v u
  have ha : 2 ≤ a := by
    dsimp only [a]
    exact xiObliqueComovingMass_ge_two hv.le u
  have hsource :=
    norm_xiMassBottomPrimeIntegral_critical_le_coronaCard_add_tails hσ hv hcritical u
  have hcard := xiMassCriticalDiagonalCorona_card_le_quadratic ha
  have hσ12 : 0 < σ / 12 := by positivity
  have htraceNonneg : 0 ≤ xiPoissonTraceReal (σ / 12) := xiPoissonTraceReal_nonneg _
  have harchNonneg : 0 ≤ xiMassBottomArchUniformBound 2 (σ / 2) :=
    xiMassBottomArchUniformBound_nonneg (by norm_num) (by positivity)
  have hA : 0 ≤ a - 1 / 2 := by linarith
  have hexpTrace : Real.exp (-(σ / 12) * (a - 1 / 2)) ≤ 1 := by
    have hnonpos : -(σ / 12) * (a - 1 / 2) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hA
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonpos
  have hexpArch : Real.exp (-(σ / 2) * (a - 1 / 2)) ≤ 1 := by
    have hnonpos : -(σ / 2) * (a - 1 / 2) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hA
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonpos
  have htraceTail :
      Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12) ≤
        xiPoissonTraceReal (σ / 12) := by
    nlinarith [mul_le_mul_of_nonneg_right hexpTrace htraceNonneg]
  have harchTail :
      Real.exp (-(σ / 2) * (a - 1 / 2)) * xiMassBottomArchUniformBound 2 (σ / 2) ≤
        xiMassBottomArchUniformBound 2 (σ / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hexpArch harchNonneg]
  exact hsource.trans (by
    have hcardMul := mul_le_mul_of_nonneg_left hcard (norm_nonneg ((Real.pi : ℂ) * I))
    nlinarith [mul_le_mul_of_nonneg_left htraceTail (norm_nonneg ((Real.pi : ℂ) * I))])

end

end RHTower
