import GaloisForLFunctions.HTGeometry.AbstractSpectralComovingMass
import GaloisForLFunctions.RHTower.XiMassPrimeOpenCore

/-!
# A co-moving mass cone for the literal Xi prime source

The fixed-mass vertical bound remains the exact RH-strength open core.  There is nevertheless a
sharp unconditional neighboring region.  If mass aperture grows at least linearly with vertical
time, charge conservation absorbs the transverse exponential growth.  For the concrete aperture

`a(u) = |u| + 2`

the full mass trace, the completed archimedean channel, and therefore the literal von-Mangoldt
bottom integral are uniformly bounded for every real `u` when `sigma > 1/2`.

This theorem changes mass with `u`; it is not a fixed-family line bound and does not imply RH.  It
identifies the remaining problem as recovery of one fixed aperture from the co-moving cone.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-! ## The archimedean channel is antitone in mass -/

theorem norm_xiMassCenteredArchIntegrand_antitone
    {a b σ x : ℝ} (hb : 0 < b) (hba : b ≤ a) (hσ : 0 < σ) :
    ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖ ≤
      ‖xiMassCenteredArchIntegrand b (σ : ℂ) x‖ := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hsq : b ^ (2 : ℕ) ≤ a ^ (2 : ℕ) := by nlinarith
  have hsqrt : Real.sqrt (x ^ (2 : ℕ) + b ^ (2 : ℕ)) ≤ Real.sqrt (x ^ (2 : ℕ) + a ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have htest :
      ‖xiMassAnalyticTest a (σ : ℂ) (x : ℂ)‖ ≤
        ‖xiMassAnalyticTest b (σ : ℂ) (x : ℂ)‖ := by
    have hma := norm_xiMassAnalyticTest_ofReal_eq
      (a := a) (σ := σ) (u := 0) (x := x) ha
    have hmb := norm_xiMassAnalyticTest_ofReal_eq
      (a := b) (σ := σ) (u := 0) (x := x) hb
    have hma' : ‖xiMassAnalyticTest a (σ : ℂ) (x : ℂ)‖ =
        Real.exp (-σ * Real.sqrt (x ^ (2 : ℕ) + a ^ (2 : ℕ))) := by simpa using hma
    have hmb' : ‖xiMassAnalyticTest b (σ : ℂ) (x : ℂ)‖ =
        Real.exp (-σ * Real.sqrt (x ^ (2 : ℕ) + b ^ (2 : ℕ))) := by simpa using hmb
    rw [hma', hmb']
    exact Real.exp_le_exp.mpr (by nlinarith)
  unfold xiMassCenteredArchIntegrand
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right htest (norm_nonneg _)

theorem xiMassArchPoleFrequency_mono
    {a b : ℝ} (hb : 1 / 2 < b) (hba : b ≤ a) :
    xiMassArchPoleFrequency b ≤ xiMassArchPoleFrequency a := by
  unfold xiMassArchPoleFrequency
  apply Real.sqrt_le_sqrt
  nlinarith

/-- The complete height-independent Gamma bound decreases as mass increases. -/
theorem xiMassBottomArchUniformBound_antitone
    {a b σ : ℝ} (hb : 1 / 2 < b) (hba : b ≤ a) (hσ : 0 < σ) :
    xiMassBottomArchUniformBound a σ ≤ xiMassBottomArchUniformBound b σ := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
  have hia := (integrable_xiMassCenteredArchIntegrand
    (a := a) (σ := σ) (u := 0) ha0 hσ).norm
  have hib := (integrable_xiMassCenteredArchIntegrand
    (a := b) (σ := σ) (u := 0) hb0 hσ).norm
  have hia' : Integrable (fun x : ℝ =>
      ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖) := by simpa using hia
  have hib' : Integrable (fun x : ℝ =>
      ‖xiMassCenteredArchIntegrand b (σ : ℂ) x‖) := by simpa using hib
  have hint :
      (∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖) ≤
        ∫ x : ℝ, ‖xiMassCenteredArchIntegrand b (σ : ℂ) x‖ := by
    apply MeasureTheory.integral_mono hia' hib'
    intro x
    exact norm_xiMassCenteredArchIntegrand_antitone hb0 hba hσ
  have hpole := xiMassArchPoleFrequency_mono hb hba
  have hexp :
      Real.exp (-σ * xiMassArchPoleFrequency a) ≤
        Real.exp (-σ * xiMassArchPoleFrequency b) :=
    Real.exp_le_exp.mpr (by nlinarith)
  unfold xiMassBottomArchUniformBound
  exact add_le_add hint (mul_le_mul_of_nonneg_left hexp (by positivity))

/-! ## Xi trace and literal prime-source cone -/

/-- Aperture used by the co-moving mass cone. -/
def xiComovingMass (u : ℝ) : ℝ := |u| + 2

theorem xiComovingMass_ge_two (u : ℝ) : 2 ≤ xiComovingMass u := by
  unfold xiComovingMass
  linarith [abs_nonneg u]

theorem abs_le_xiComovingMass (u : ℝ) : |u| ≤ xiComovingMass u := by
  unfold xiComovingMass
  linarith

theorem xiPoissonAbstract_traceReal (σ : ℝ) :
    xiPoissonAbstract.traceReal σ = xiPoissonTraceReal σ := rfl

/-- Xi specialization of the universal co-moving trace cone. -/
theorem norm_xiMassTraceC_comoving_le
    {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    ‖(xiMassFamily (show 1 / 2 ≤ xiComovingMass u by
        linarith [xiComovingMass_ge_two u])).traceC ((σ : ℂ) + u * I)‖ ≤
      xiPoissonTraceReal (σ - 1 / 2) := by
  let ha : 1 / 2 ≤ xiComovingMass u := by
    linarith [xiComovingMass_ge_two u]
  have hbase : 1 / 2 ≤ xiPoissonAbstract.base := by
    rw [xiPoissonAbstract_base]
    linarith [three_lt_xiPoissonBottomHeight]
  have h := xiPoissonAbstract.norm_mass_traceC_le_comoving ha hbase
    (abs_le_xiComovingMass u) hσ
  rw [← xiMassFamily_traceC_eq ha ((σ : ℂ) + u * I),
    xiPoissonAbstract_traceReal] at h
  simpa only using h

/-- **Unconditional co-moving prime-source cone.**  The literal von-Mangoldt bottom integral at
fixed legal Euler depth `1` is uniformly bounded when its mass aperture is `|u|+2`. -/
theorem norm_xiMassBottomPrimeIntegral_comoving_le
    {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    ‖xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (σ - 1 / 2) +
        xiMassBottomArchUniformBound 2 σ := by
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hca : (1 : ℝ) < xiComovingMass u := by
    linarith [xiComovingMass_ge_two u]
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    linarith
  have htrace := norm_xiMassTraceC_comoving_le hσ u
  have harch :
      ‖xiMassBottomArchIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ ≤
        xiMassBottomArchUniformBound 2 σ := by
    refine (norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca
      (show 0 < σ by linarith)).trans ?_
    exact xiMassBottomArchUniformBound_antitone (by norm_num)
      (xiComovingMass_ge_two u) (by linarith)
  rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ,
    integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ]
  calc
    ‖I * (Real.pi * I *
          (xiMassFamily (show 1 / 2 ≤ xiComovingMass u by linarith)).traceC
            ((σ : ℂ) + u * I)) +
        xiMassBottomArchIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ ≤
      ‖I * (Real.pi * I *
          (xiMassFamily (show 1 / 2 ≤ xiComovingMass u by linarith)).traceC
            ((σ : ℂ) + u * I))‖ +
        ‖xiMassBottomArchIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ :=
      norm_add_le _ _
    _ = ‖(Real.pi : ℂ) * I‖ *
          ‖(xiMassFamily (show 1 / 2 ≤ xiComovingMass u by linarith)).traceC
            ((σ : ℂ) + u * I)‖ +
        ‖xiMassBottomArchIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ := by
      rw [norm_mul, norm_mul]
      simp
    _ ≤ ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (σ - 1 / 2) +
        xiMassBottomArchUniformBound 2 σ :=
      add_le_add (mul_le_mul_of_nonneg_left htrace (norm_nonneg _)) harch

end

end RHTower
