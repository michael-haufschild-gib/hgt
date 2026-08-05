import GaloisForLFunctions.HTGeometry.AbstractSpectralCriticalDiagonalCorona
import GaloisForLFunctions.RHTower.XiMassObliqueComovingPrimeExponential

/-!
# Critical Xi prime source as a finite cofinal diagonal corona

At the sharp oblique phase wall `4σv=1`, the mass trace is no longer exponentially extinguished.
The universal critical localization theorem shows exactly what survives: Xi zeros whose Poisson
height is comparable to `a-1/2`.  This module transports that theorem through the exact
Gamma/Euler-source identity.

The literal von-Mangoldt source equals a finite critical-corona trace model modulo two explicit
exponential tails: one spectral and one Archimedean.  Consequently the whole critical source is
bounded by the cardinality of one moving finite zero packet plus those tails.  This identifies the
first genuinely cofinal observable exposed by the mass route.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Xi index packet whose original Poisson height lies in the critical moving diagonal corona. -/
def xiMassCriticalDiagonalCorona (a : ℝ) : Finset XiZeroCopy :=
  xiPoissonAbstract.criticalDiagonalCorona a

/-- Finite massive Xi trace supported on the critical moving corona. -/
def xiMassCriticalDiagonalCoronaTraceC
    (a : ℝ) (ha : 1 / 2 ≤ a) (τ : ℂ) : ℂ :=
  xiPoissonAbstract.massCriticalDiagonalCoronaTraceC a ha τ

/-- Prime-side model carried by the finite critical Xi corona. -/
def xiMassCriticalPrimeCoronaModel
    (a : ℝ) (ha : 1 / 2 ≤ a) (τ : ℂ) : ℂ :=
  I * (Real.pi * I * xiMassCriticalDiagonalCoronaTraceC a ha τ)

/-- Critical Xi trace equals its finite moving corona modulo an exponential tail. -/
theorem norm_xiMassTraceC_sub_criticalDiagonalCoronaTraceC_le
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) (u : ℝ) :
    let a := xiObliqueComovingMass v u
    let ha : 1 / 2 ≤ a := by linarith [xiObliqueComovingMass_ge_two hv.le u]
    ‖(xiMassFamily ha).traceC ((σ : ℂ) + u * I) -
        xiMassCriticalDiagonalCoronaTraceC a ha ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12) := by
  dsimp only
  let a : ℝ := xiObliqueComovingMass v u
  let ha : 1 / 2 ≤ a := by
    dsimp only [a]
    linarith [xiObliqueComovingMass_ge_two hv.le u]
  have h := xiPoissonAbstract.norm_mass_traceC_sub_criticalDiagonalCoronaTraceC_le
    (xiObliqueComovingMass_ge_two hv.le u) hσ hv
    (velocity_mul_abs_le_xiObliqueComovingMass_sub_half v u) hcritical
  rw [← xiMassFamily_traceC_eq ha ((σ : ℂ) + u * I), xiPoissonAbstract_traceReal] at h
  simpa only [xiMassCriticalDiagonalCoronaTraceC, a, ha] using h

/-- The critical Xi corona trace is bounded by the cardinality of the cofinal zero packet. -/
theorem norm_xiMassCriticalDiagonalCoronaTraceC_le_card
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) (u : ℝ) :
    let a := xiObliqueComovingMass v u
    let ha : 1 / 2 ≤ a := by linarith [xiObliqueComovingMass_ge_two hv.le u]
    ‖xiMassCriticalDiagonalCoronaTraceC a ha ((σ : ℂ) + u * I)‖ ≤
      (xiMassCriticalDiagonalCorona a).card := by
  dsimp only
  exact xiPoissonAbstract.norm_massCriticalDiagonalCoronaTraceC_le_card
    (xiObliqueComovingMass_ge_two hv.le u) hσ hv
    (velocity_mul_abs_le_xiObliqueComovingMass_sub_half v u) hcritical

/-- **Critical literal-source localization.**  At `4σv=1`, the complete von-Mangoldt source is
its finite moving Xi-corona model modulo explicit spectral and Gamma exponential tails. -/
theorem norm_xiMassBottomPrimeIntegral_sub_criticalPrimeCoronaModel_le
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) (u : ℝ) :
    let a := xiObliqueComovingMass v u
    let ha : 1 / 2 ≤ a := by linarith [xiObliqueComovingMass_ge_two hv.le u]
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) -
        xiMassCriticalPrimeCoronaModel a ha ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let a : ℝ := xiObliqueComovingMass v u
  let ha : 1 / 2 ≤ a := by
    dsimp only [a]
    linarith [xiObliqueComovingMass_ge_two hv.le u]
  let τ : ℂ := (σ : ℂ) + u * I
  let C : ℂ := xiMassCriticalDiagonalCoronaTraceC a ha τ
  have ha2 : 2 ≤ a := by
    dsimp only [a]
    exact xiObliqueComovingMass_ge_two hv.le u
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hca : (1 : ℝ) < a := by linarith
  have hτ : 0 < τ.re := by dsimp only [τ]; simpa [Complex.mul_re] using hσ
  have hσ2 : 0 < σ / 2 := by positivity
  have hσ2lt : σ / 2 < σ := by linarith
  have htrace :
      ‖(xiMassFamily ha).traceC τ - C‖ ≤
        Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12) := by
    simpa only [a, ha, τ, C] using
      norm_xiMassTraceC_sub_criticalDiagonalCoronaTraceC_le hσ hv hcritical u
  have harch0 :
      ‖xiMassBottomArchIntegral a 1 τ‖ ≤ xiMassBottomArchUniformBound a σ :=
    norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hσ
  have harchGap := xiMassBottomArchUniformBound_le_exponential_gap
    (a := a) (b := (2 : ℝ)) (σ := σ) (δ := σ / 2)
    (by norm_num) ha2 hσ2 hσ2lt
  have harch :
      ‖xiMassBottomArchIntegral a 1 τ‖ ≤
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
    exact harch0.trans (by simpa only [sub_half] using harchGap)
  rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ,
    integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ]
  unfold xiMassCriticalPrimeCoronaModel
  change ‖I * (Real.pi * I * (xiMassFamily ha).traceC τ) +
      xiMassBottomArchIntegral a 1 τ - I * (Real.pi * I * C)‖ ≤ _
  have heq :
      I * (Real.pi * I * (xiMassFamily ha).traceC τ) +
          xiMassBottomArchIntegral a 1 τ - I * (Real.pi * I * C) =
        I * (Real.pi * I * ((xiMassFamily ha).traceC τ - C)) +
          xiMassBottomArchIntegral a 1 τ := by ring
  rw [heq]
  calc
    ‖I * (Real.pi * I * ((xiMassFamily ha).traceC τ - C)) +
        xiMassBottomArchIntegral a 1 τ‖ ≤
      ‖I * (Real.pi * I * ((xiMassFamily ha).traceC τ - C))‖ +
        ‖xiMassBottomArchIntegral a 1 τ‖ := norm_add_le _ _
    _ = ‖(Real.pi : ℂ) * I‖ * ‖(xiMassFamily ha).traceC τ - C‖ +
        ‖xiMassBottomArchIntegral a 1 τ‖ := by rw [norm_mul, norm_mul]; simp
    _ ≤ ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left htrace (norm_nonneg _)) harch

/-- Unconditional critical source bound by one finite cofinal corona count plus exponential tails. -/
theorem norm_xiMassBottomPrimeIntegral_critical_le_coronaCard_add_tails
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) (u : ℝ) :
    let a := xiObliqueComovingMass v u
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ * (xiMassCriticalDiagonalCorona a).card +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let a : ℝ := xiObliqueComovingMass v u
  let ha : 1 / 2 ≤ a := by
    dsimp only [a]
    linarith [xiObliqueComovingMass_ge_two hv.le u]
  let P : ℂ := xiMassCriticalPrimeCoronaModel a ha ((σ : ℂ) + u * I)
  have hP : ‖P‖ ≤ ‖(Real.pi : ℂ) * I‖ * (xiMassCriticalDiagonalCorona a).card := by
    unfold P xiMassCriticalPrimeCoronaModel
    rw [norm_mul, norm_mul]
    simp only [norm_I, one_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_xiMassCriticalDiagonalCoronaTraceC_le_card hσ hv hcritical u)
      (norm_nonneg _)
  have hrem :=
    norm_xiMassBottomPrimeIntegral_sub_criticalPrimeCoronaModel_le hσ hv hcritical u
  calc
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ =
        ‖(xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P) + P‖ := by ring_nf
    _ ≤ ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ (‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2)) +
        ‖(Real.pi : ℂ) * I‖ * (xiMassCriticalDiagonalCorona a).card := by
      exact add_le_add
        (by simpa only [a, ha, P] using hrem) hP
    _ = ‖(Real.pi : ℂ) * I‖ * (xiMassCriticalDiagonalCorona a).card +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by ring

end

end RHTower
