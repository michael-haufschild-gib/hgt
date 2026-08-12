import GaloisForLFunctions.RHTower.CCMArchimedeanPhaseTemperate

/-!
# Exact logarithmic derivative of the CCM archimedean phase

The Connes--Consani trace formula ultimately reads the logarithmic derivative of
`u_infinity(t) = conj (zetaChi (1/2+it))`.  This file derives that first jet from the already
formalized normalized-Gamma phase ODE.  In particular,

`u_infinity^* u_infinity' = 2 i gammaHardyPhaseRate`.

This is the exact scalar density needed by the unresolved operator-trace cocycle.  It is proved
from Gamma identities, not introduced as a phase-derivative premise.
-/

noncomputable section

open Complex
open scoped Real SchwartzMap

namespace RHTower

/-- The source scattering phase is the square of the conjugate normalized-Gamma phase. -/
theorem ccmArchimedeanScatteringPhase_eq_conj_gamma_sq (t : ℝ) :
    ccmArchimedeanScatteringPhase t =
      (starRingEnd ℂ) (gammaHardyPhase t) *
        (starRingEnd ℂ) (gammaHardyPhase t) := by
  rw [ccmArchimedeanScatteringPhase, ← gammaHardyPhase_sq, map_mul]

/-- Exact first-jet equation for Connes--Consani's paper-convention phase. -/
theorem hasDerivAt_ccmArchimedeanScatteringPhase (t : ℝ) :
    HasDerivAt ccmArchimedeanScatteringPhase
      (2 * Complex.I * (gammaHardyPhaseRate t : ℂ) *
        ccmArchimedeanScatteringPhase t) t := by
  have hq : HasDerivAt (fun x : ℝ => star (gammaHardyPhase x))
      (Complex.I * (gammaHardyPhaseRate t : ℂ) *
        star (gammaHardyPhase t)) t := by
    have hraw := (hasDerivAt_gammaHardyPhase t).star
    have hcoeff : star (-I * (gammaHardyPhaseRate t : ℂ) *
        gammaHardyPhase t) =
        I * (gammaHardyPhaseRate t : ℂ) *
          (starRingEnd ℂ) (gammaHardyPhase t) := by
      change (starRingEnd ℂ)
        (-I * (gammaHardyPhaseRate t : ℂ) * gammaHardyPhase t) = _
      rw [map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hcoeff] at hraw
    exact hraw
  have hprod := hq.mul hq
  change HasDerivAt
    (fun x : ℝ => star (gammaHardyPhase x) * star (gammaHardyPhase x)) _ t at hprod
  rw [show (fun x : ℝ => star (gammaHardyPhase x) * star (gammaHardyPhase x)) =
      ccmArchimedeanScatteringPhase by
      funext x
      exact (ccmArchimedeanScatteringPhase_eq_conj_gamma_sq x).symm] at hprod
  convert hprod using 1
  rw [ccmArchimedeanScatteringPhase_eq_conj_gamma_sq]
  change 2 * I * (gammaHardyPhaseRate t : ℂ) *
      (star (gammaHardyPhase t) * star (gammaHardyPhase t)) = _
  ring

/-- Closed derivative formula for the source scattering phase. -/
theorem deriv_ccmArchimedeanScatteringPhase (t : ℝ) :
    deriv ccmArchimedeanScatteringPhase t =
      2 * Complex.I * (gammaHardyPhaseRate t : ℂ) *
        ccmArchimedeanScatteringPhase t :=
  (hasDerivAt_ccmArchimedeanScatteringPhase t).deriv

/-- **Exact logarithmic phase density.**  Unit modulus cancels the phase value and leaves twice
the imaginary Gamma Hardy rate. -/
theorem star_mul_deriv_ccmArchimedeanScatteringPhase (t : ℝ) :
    (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
        deriv ccmArchimedeanScatteringPhase t =
      2 * Complex.I * (gammaHardyPhaseRate t : ℂ) := by
  rw [deriv_ccmArchimedeanScatteringPhase]
  have hu : (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
      ccmArchimedeanScatteringPhase t = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq,
      norm_ccmArchimedeanScatteringPhase]
    norm_num
  calc
    (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
        (2 * I * (gammaHardyPhaseRate t : ℂ) *
          ccmArchimedeanScatteringPhase t) =
      (2 * I * (gammaHardyPhaseRate t : ℂ)) *
        ((starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
          ccmArchimedeanScatteringPhase t) := by ring
    _ = 2 * I * (gammaHardyPhaseRate t : ℂ) := by rw [hu, mul_one]

/-- Product rule for the literal scattering phase acting on a Schwartz spectral symbol. -/
theorem hasDerivAt_ccmArchimedeanScatteringPhaseMul
    (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (ccmArchimedeanScatteringPhaseMul g : ℝ → ℂ)
      (deriv ccmArchimedeanScatteringPhase t * g t +
        ccmArchimedeanScatteringPhase t * deriv (g : ℝ → ℂ) t) t := by
  have hprod := (hasDerivAt_ccmArchimedeanScatteringPhase t).mul
    (g.hasDerivAt t)
  change HasDerivAt
    (fun x : ℝ => ccmArchimedeanScatteringPhase x * g x) _ t at hprod
  have hfun : (ccmArchimedeanScatteringPhaseMul g : ℝ → ℂ) =
      fun x : ℝ => ccmArchimedeanScatteringPhase x * g x := by
    funext x
    exact ccmArchimedeanScatteringPhaseMul_apply g x
  rw [hfun]
  convert hprod using 1
  rw [deriv_ccmArchimedeanScatteringPhase]

/-- Closed product derivative for the phase-multiplied Schwartz symbol. -/
theorem deriv_ccmArchimedeanScatteringPhaseMul
    (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deriv (ccmArchimedeanScatteringPhaseMul g : ℝ → ℂ) t =
      deriv ccmArchimedeanScatteringPhase t * g t +
        ccmArchimedeanScatteringPhase t * deriv (g : ℝ → ℂ) t :=
  (hasDerivAt_ccmArchimedeanScatteringPhaseMul g t).deriv

/-- After conjugating by the unitary phase, the product derivative splits into the exact Gamma
phase density and the ordinary derivative of the test. -/
theorem star_mul_deriv_ccmArchimedeanScatteringPhaseMul
    (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
        deriv (ccmArchimedeanScatteringPhaseMul g : ℝ → ℂ) t =
      2 * Complex.I * (gammaHardyPhaseRate t : ℂ) * g t +
        deriv (g : ℝ → ℂ) t := by
  rw [deriv_ccmArchimedeanScatteringPhaseMul]
  have hu : (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
      ccmArchimedeanScatteringPhase t = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq,
      norm_ccmArchimedeanScatteringPhase]
    norm_num
  calc
    (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
        (deriv ccmArchimedeanScatteringPhase t * g t +
          ccmArchimedeanScatteringPhase t * deriv (g : ℝ → ℂ) t) =
      ((starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
          deriv ccmArchimedeanScatteringPhase t) * g t +
        ((starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
          ccmArchimedeanScatteringPhase t) * deriv (g : ℝ → ℂ) t := by ring
    _ = 2 * Complex.I * (gammaHardyPhaseRate t : ℂ) * g t +
        deriv (g : ℝ → ℂ) t := by
      rw [star_mul_deriv_ccmArchimedeanScatteringPhase, hu, one_mul]

end RHTower
