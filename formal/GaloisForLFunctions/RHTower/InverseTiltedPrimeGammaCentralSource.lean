import GaloisForLFunctions.RHTower.CCMInverseTiltedCriticalMellinFactorization
import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingHankel

/-!
# The inverse-tilted finite prime source recovers the central prime--Gamma germ

The inverse-tilted dyadic prime source is an actual finite-coefficient source whose Mellin
aperture is zero-free on the source half-plane.  Its existing factorization recovers the
regularized critical-Mellin defect after subtraction of an explicit holomorphic quadrature
correction.  Adding the fixed Gamma connection therefore reconstructs the complete centered
prime--Gamma relative trace.

This file composes those two previously separate value relations.  It introduces no Xi-divisor
coordinate and proves no positivity statement.  Its purpose is to make the finite prime source,
rather than an abstract continued defect, the exact Taylor-germ input to the prime--Gamma Hankel
criterion.
-/

open Complex Filter Function Set Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The completed centered trace reconstructed from the inverse-tilted dyadic prime source, its
explicit quadrature correction, and the fixed Gamma connection. -/
def inverseTiltedPrimeGammaSourceTrace (z : ℂ) : ℂ :=
  let s : ℂ := 1 + z * I
  I *
    ((inverseTiltedDyadicContinuedSource s -
          inverseTiltedCriticalMellinCorrection s) /
        (2 * inverseTiltedDyadicMellin s) +
      gammaRealLogConnection (1 / 2 + z * I))

/-- Away from the filled zeta pole and the zeta divisor, the regularized and ordinary continued
critical-Mellin defects agree.  The prior theorem imposed `0 < Re u`; this form isolates the exact
local hypotheses needed at the central coordinate `u = -1/2 + iz`. -/
theorem regularizedCriticalMellinDefect_eq_continued_of_ne_zero
    {u : ℂ} (hu : u ≠ 0) (hzeta : riemannZeta (u + 1) ≠ 0) :
    regularizedCriticalMellinDefect u = continuedCriticalMellinDefect u := by
  have hu1 : u + 1 ≠ 1 := by
    intro h
    apply hu
    linear_combination h
  rw [regularizedCriticalMellinDefect, continuedCriticalMellinDefect,
    logDeriv_regularizedRiemannZeta_eq hu1 hzeta, zetaLogDeriv,
    logDeriv_apply]
  have hcoord : u + 1 - 1 = u := by ring
  rw [hcoord]
  ring

/-- **Inverse-tilted prime--Gamma value relation.**  At every regular centered source point, the
completed trace reconstructed from the finite inverse-tilted prime source is exactly the canonical
continued prime--Gamma relative trace. -/
theorem inverseTiltedPrimeGammaSourceTrace_eq_continuedPrimeArchSourceRelativeTrace
    {z : ℂ} (hspos : 0 < (1 / 2 + z * I).re)
    (hs1 : 1 / 2 + z * I ≠ 1)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    inverseTiltedPrimeGammaSourceTrace z =
      continuedPrimeArchSourceRelativeTrace z := by
  let u : ℂ := xiCriticalMellinCoordinate z
  let s : ℂ := 1 + z * I
  have hsu : s - 3 / 2 = u := by
    dsimp only [s, u, xiCriticalMellinCoordinate]
    ring
  have huadd : u + 1 = 1 / 2 + z * I := by
    dsimp only [u, xiCriticalMellinCoordinate]
    ring
  have hu0 : u ≠ 0 := by
    intro h
    apply hs1
    rw [← huadd, h]
    ring
  have hzetaU : riemannZeta (u + 1) ≠ 0 := by
    simpa only [huadd] using hzeta
  have hsre : 0 < s.re := by
    dsimp only [s]
    have hcoord : (1 + z * I).re = (1 / 2 + z * I).re + 1 / 2 := by
      norm_num [Complex.add_re]
      ring
    rw [hcoord]
    linarith
  have hM : 2 * inverseTiltedDyadicMellin s ≠ 0 :=
    mul_ne_zero (by norm_num) (inverseTiltedDyadicMellin_ne_zero_of_re_pos hsre)
  have hfactor :=
    inverseTiltedDyadicContinuedSource_eq_criticalMellinDefect_add_correction s
  have hquot :
      (inverseTiltedDyadicContinuedSource s -
          inverseTiltedCriticalMellinCorrection s) /
          (2 * inverseTiltedDyadicMellin s) =
        regularizedCriticalMellinDefect u := by
    rw [hfactor, hsu]
    exact (div_eq_iff hM).2 (by ring)
  have hreg : regularizedCriticalMellinDefect u = continuedCriticalMellinDefect u :=
    regularizedCriticalMellinDefect_eq_continued_of_ne_zero hu0 hzetaU
  have hs0 : 1 / 2 + z * I ≠ 0 := by
    intro h
    have := hspos
    rw [h] at this
    norm_num at this
  rw [continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma hspos hs0 hs1]
  rw [inverseTiltedPrimeGammaSourceTrace, continuedMellinGammaSourceTrace]
  change I *
      ((inverseTiltedDyadicContinuedSource s -
          inverseTiltedCriticalMellinCorrection s) /
          (2 * inverseTiltedDyadicMellin s) +
        gammaRealLogConnection (1 / 2 + z * I)) =
    I *
      (continuedCriticalMellinDefect u +
        gammaRealLogConnection (1 / 2 + z * I))
  rw [hquot, hreg]

/-- The inverse-tilted reconstructed trace and the canonical prime--Gamma trace are the same germ
at the functional-equation center. -/
theorem inverseTiltedPrimeGammaSourceTrace_eventuallyEq_continuedPrimeArchSourceRelativeTrace :
    inverseTiltedPrimeGammaSourceTrace =ᶠ[𝓝 0]
      continuedPrimeArchSourceRelativeTrace := by
  let c : ℂ → ℂ := fun z => 1 / 2 + z * I
  have hccont : ContinuousAt c 0 := by
    dsimp only [c]
    fun_prop
  have hcrecont : ContinuousAt (fun z => (c z).re) 0 :=
    Complex.continuous_re.continuousAt.comp hccont
  have hcpos : ∀ᶠ z in 𝓝 0, 0 < (c z).re := by
    change ∀ᶠ z in 𝓝 0, (c z).re ∈ Set.Ioi 0
    exact hcrecont (Ioi_mem_nhds (by simp [c]))
  have hc1 : ∀ᶠ z in 𝓝 0, c z ≠ 1 :=
    hccont.eventually_ne (by simp [c])
  have hzetaReal :=
    riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
  have hzeta0 : riemannZeta (c 0) ≠ 0 := by
    simpa [c] using hzetaReal
  have hzetaCont : ContinuousAt (fun z => riemannZeta (c z)) 0 := by
    have hzetaAt : ContinuousAt riemannZeta (c 0) := by
      exact (differentiableAt_riemannZeta (by simp [c])).continuousAt
    exact hzetaAt.comp hccont
  have hzeta : ∀ᶠ z in 𝓝 0, riemannZeta (c z) ≠ 0 :=
    hzetaCont.eventually_ne hzeta0
  filter_upwards [hcpos, hc1, hzeta] with z hzpos hz1 hzzeta
  exact inverseTiltedPrimeGammaSourceTrace_eq_continuedPrimeArchSourceRelativeTrace
    (by simpa only [c] using hzpos) (by simpa only [c] using hz1)
    (by simpa only [c] using hzzeta)

/-- The reconstructed trace is analytic at the center because it is locally the already analytic
continued prime--Gamma trace. -/
theorem analyticAt_inverseTiltedPrimeGammaSourceTrace :
    AnalyticAt ℂ inverseTiltedPrimeGammaSourceTrace 0 :=
  analyticAt_continuedPrimeArchSourceRelativeTrace.congr
    inverseTiltedPrimeGammaSourceTrace_eventuallyEq_continuedPrimeArchSourceRelativeTrace.symm

/-- Normalized central division preserves the inverse-tilted source identity. -/
theorem normalizedTraceMomentGerm_inverseTiltedPrimeGammaSource_eventuallyEq :
    normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace =ᶠ[𝓝 0]
      normalizedPrimeArchMomentGerm := by
  rw [normalizedPrimeArchMomentGerm]
  exact normalizedTraceMomentGerm_eventuallyEq_of_eventuallyEq
    inverseTiltedPrimeGammaSourceTrace_eventuallyEq_continuedPrimeArchSourceRelativeTrace

/-- Every canonical normalized prime--Gamma moment is therefore the corresponding even Taylor
coefficient of one explicit inverse-tilted finite-prime/Gamma source germ. -/
theorem analyticTraceMoments_inverseTiltedPrimeGammaSource (n : ℕ) :
    analyticTraceMoments
        (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace) n =
      normalizedPrimeArchMoment n := by
  rw [normalizedPrimeArchMoment, analyticTraceMoments]
  rw [(normalizedTraceMomentGerm_inverseTiltedPrimeGammaSource_eventuallyEq.iteratedDeriv_eq
    (2 * n))]
  rfl

end

end RHTower
