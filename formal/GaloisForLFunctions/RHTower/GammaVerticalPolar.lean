import GaloisForLFunctions.RHTower.GammaVerticalPhaseAsymptotic
import GaloisForLFunctions.RHTower.GammaJumpMultiplierBounds
import GaloisForLFunctions.HTGeometry.UnitaryReflectionPhaseHalving
open Complex Filter Topology intervalIntegral


open scoped ComplexConjugate

noncomputable section

namespace RHTower

def gammaVerticalValue (σ t : ℝ) : ℂ :=
  Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)

def gammaVerticalConjPhase (σ t : ℝ) : ℂ :=
  (starRingEnd ℂ) (gammaVerticalValue σ t) / ‖gammaVerticalValue σ t‖

theorem gammaVerticalValue_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gammaVerticalValue σ t ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n h
  have hre := congrArg Complex.re h
  simp at hre
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem hasDerivAt_gammaVerticalValue {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (gammaVerticalValue σ)
      (gammaVerticalValue σ t * Complex.digamma ((σ : ℂ) + (t : ℂ) * I) * I) t := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hz : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    dsimp [z] at hre
    simp at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hΓ := (Complex.differentiableAt_Gamma z hz).hasDerivAt
  have hpath : HasDerivAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) I t := by
    have hcast : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
    have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * I) I t := by
      simpa using hcast.mul_const I
    have hadd := (hasDerivAt_const t (σ : ℂ)).add hmul
    simpa only [Pi.add_apply, zero_add] using! hadd
  have hcomp := hΓ.comp t hpath
  have hderiv : deriv Complex.Gamma z = Complex.Gamma z * Complex.digamma z := by
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [Complex.Gamma_ne_zero hz]
  rw [hderiv] at hcomp
  change HasDerivAt (gammaVerticalValue σ)
    (gammaVerticalValue σ t * Complex.digamma ((σ : ℂ) + (t : ℂ) * I) * I) t at hcomp
  exact hcomp

theorem hasDerivAt_gammaVerticalConjPhase {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (gammaVerticalConjPhase σ)
      (-I * ((Complex.digamma ((σ : ℂ) + (t : ℂ) * I)).re : ℂ) *
        gammaVerticalConjPhase σ t) t := by
  have h := GaloisForLFunctions.HTGeometry.hasDerivAt_normalizedConjPhase
    (hasDerivAt_gammaVerticalValue hσ t) (gammaVerticalValue_ne_zero hσ t)
  convert h using 1
  · rfl
  · have hcancel :
        (gammaVerticalValue σ t * Complex.digamma ((σ : ℂ) + (t : ℂ) * I) * I) /
            gammaVerticalValue σ t =
          Complex.digamma ((σ : ℂ) + (t : ℂ) * I) * I := by
      field_simp [gammaVerticalValue_ne_zero hσ t]
    rw [hcancel]
    simp [gammaVerticalConjPhase]

theorem hasDerivAt_gammaVerticalPhase {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (gammaVerticalPhase σ)
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * I)).re t :=
  ((continuous_digammaVerticalRe hσ).integral_hasStrictDerivAt 0 t).hasDerivAt

private def gammaVerticalPhaseGauge (σ t : ℝ) : ℂ :=
  gammaVerticalConjPhase σ t * Complex.exp (I * (gammaVerticalPhase σ t : ℂ))

private theorem hasDerivAt_gammaVerticalPhaseGauge {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (gammaVerticalPhaseGauge σ) 0 t := by
  have hphaseC : HasDerivAt (fun u : ℝ => (gammaVerticalPhase σ u : ℂ))
      ((Complex.digamma ((σ : ℂ) + (t : ℂ) * I)).re : ℂ) t := by
    simpa using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_gammaVerticalPhase hσ t)
  have hinner := hphaseC.const_mul I
  have hexp := hinner.cexp
  have hprod := (hasDerivAt_gammaVerticalConjPhase hσ t).mul hexp
  have hprod' : HasDerivAt
      (fun u : ℝ => gammaVerticalConjPhase σ u *
        Complex.exp (I * (gammaVerticalPhase σ u : ℂ)))
      ((-I * ((Complex.digamma ((σ : ℂ) + (t : ℂ) * I)).re : ℂ) *
          gammaVerticalConjPhase σ t) *
          Complex.exp (I * (gammaVerticalPhase σ t : ℂ)) +
        gammaVerticalConjPhase σ t *
          (Complex.exp (I * (gammaVerticalPhase σ t : ℂ)) *
            (I * ((Complex.digamma ((σ : ℂ) + (t : ℂ) * I)).re : ℂ)))) t := by
    simpa only [Pi.mul_apply] using! hprod
  unfold gammaVerticalPhaseGauge
  convert hprod' using 1
  ring

theorem gammaVerticalConjPhase_eq_exp_neg_phase {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gammaVerticalConjPhase σ t =
      Complex.exp (-I * (gammaVerticalPhase σ t : ℂ)) := by
  have hdiff : Differentiable ℝ (gammaVerticalPhaseGauge σ) :=
    fun u => (hasDerivAt_gammaVerticalPhaseGauge hσ u).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff
    (fun u => (hasDerivAt_gammaVerticalPhaseGauge hσ u).deriv) t 0
  have hcenter : gammaVerticalPhaseGauge σ 0 = 1 := by
    have hgamma : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos hσ
    have hval : gammaVerticalValue σ 0 = (Real.Gamma σ : ℂ) := by
      simp [gammaVerticalValue, Complex.Gamma_ofReal]
    rw [gammaVerticalPhaseGauge, gammaVerticalPhase, intervalIntegral.integral_same, ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one, gammaVerticalConjPhase, hval]
    simp [Real.norm_eq_abs, abs_of_pos hgamma, hgamma.ne']
  rw [hcenter] at hconst
  have hexp : Complex.exp (I * (gammaVerticalPhase σ t : ℂ)) *
      Complex.exp (-I * (gammaVerticalPhase σ t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero
    ring
  calc
    gammaVerticalConjPhase σ t = gammaVerticalConjPhase σ t * 1 := by ring
    _ = gammaVerticalConjPhase σ t *
        (Complex.exp (I * (gammaVerticalPhase σ t : ℂ)) *
          Complex.exp (-I * (gammaVerticalPhase σ t : ℂ))) := by rw [hexp]
    _ = gammaVerticalPhaseGauge σ t *
          Complex.exp (-I * (gammaVerticalPhase σ t : ℂ)) := by
      rw [gammaVerticalPhaseGauge]
      ring
    _ = _ := by rw [hconst, one_mul]

theorem gammaVerticalValue_eq_norm_mul_exp_phase {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gammaVerticalValue σ t =
      (‖gammaVerticalValue σ t‖ : ℂ) *
        Complex.exp (I * (gammaVerticalPhase σ t : ℂ)) := by
  have h := congrArg (starRingEnd ℂ)
    (gammaVerticalConjPhase_eq_exp_neg_phase hσ t)
  have hnorm : (‖gammaVerticalValue σ t‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (gammaVerticalValue_ne_zero hσ t))
  unfold gammaVerticalConjPhase at h
  simp at h
  rw [div_eq_iff hnorm] at h
  rw [← Complex.exp_conj] at h
  simpa [mul_comm] using h

@[simp] theorem gammaVerticalPhase_neg {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gammaVerticalPhase σ (-t) = -gammaVerticalPhase σ t := by
  unfold gammaVerticalPhase
  calc
    (∫ u in 0..-t,
      (Complex.digamma ((σ : ℂ) + (u : ℂ) * I)).re) =
        ∫ u in t..0,
          (Complex.digamma ((σ : ℂ) + ((-u : ℝ) : ℂ) * I)).re := by
      simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
        (f := fun u : ℝ => (Complex.digamma ((σ : ℂ) + (u : ℂ) * I)).re)
        (a := t) (b := 0)).symm
    _ = ∫ u in t..0,
          (Complex.digamma ((σ : ℂ) + (u : ℂ) * I)).re := by
      apply intervalIntegral.integral_congr
      intro u _
      exact GaloisForLFunctions.RHTower.re_digamma_vertical_even hσ u
    _ = -(∫ u in 0..t,
          (Complex.digamma ((σ : ℂ) + (u : ℂ) * I)).re) := by
      rw [intervalIntegral.integral_symm]
