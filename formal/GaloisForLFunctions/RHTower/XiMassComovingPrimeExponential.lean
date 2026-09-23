import GaloisForLFunctions.HTGeometry.AbstractSpectralComovingExponential
import GaloisForLFunctions.RHTower.XiMassComovingPrimeExtinction

/-!
# Exponential flatness of the co-moving Xi prime source

The universal joint mass-height estimate upgrades qualitative co-moving extinction to a pointwise
exponential bound.  The Gamma channel obeys a matching mass-gap estimate: real time can be split
between the larger aperture and any fixed reference aperture, while the crossed-pole frequency is
at least `a - 1/2`.

For `A(u)=|u|+2` and `σ>1/2`, the complete literal von-Mangoldt source therefore decays at the
explicit rate

`κ(σ) = 2σ/3 - 3/16 > 0`.

Consequently the canonical mass-semigroup high-pass differs from the fixed source by an
exponentially decaying function on the entire real height axis.  The adaptive correction is much
smaller than merely `C₀`: no polynomially rescaled finite aperture response can recover the fixed
source from it.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

open MeasureTheory Set

/-- Exponential mass-gap comparison for the centered Gamma density. -/
theorem norm_xiMassCenteredArchIntegrand_le_exponential_gap
    {a b σ δ x : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hδ : 0 < δ) (hδσ : δ < σ) :
    ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖ ≤
      Real.exp (-δ * (a - 1 / 2)) *
        ‖xiMassCenteredArchIntegrand b ((σ - δ : ℝ) : ℂ) x‖ := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hσδ : 0 < σ - δ := by linarith
  have hsq : b ^ (2 : ℕ) ≤ a ^ (2 : ℕ) := by nlinarith
  have hsqrtBA : Real.sqrt (x ^ (2 : ℕ) + b ^ (2 : ℕ)) ≤ Real.sqrt (x ^ (2 : ℕ) + a ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hargA : 0 ≤ x ^ (2 : ℕ) + a ^ (2 : ℕ) := by positivity
  have hsquareA := Real.sq_sqrt hargA
  have hsqrtA0 := Real.sqrt_nonneg (x ^ (2 : ℕ) + a ^ (2 : ℕ))
  have haRoot : a ≤ Real.sqrt (x ^ (2 : ℕ) + a ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg x]
  have htest :
      ‖xiMassAnalyticTest a (σ : ℂ) (x : ℂ)‖ ≤
        Real.exp (-δ * (a - 1 / 2)) *
          ‖xiMassAnalyticTest b ((σ - δ : ℝ) : ℂ) (x : ℂ)‖ := by
    have hma := norm_xiMassAnalyticTest_ofReal_eq
      (a := a) (σ := σ) (u := 0) (x := x) ha
    have hmb := norm_xiMassAnalyticTest_ofReal_eq
      (a := b) (σ := σ - δ) (u := 0) (x := x) hb
    have hma' : ‖xiMassAnalyticTest a (σ : ℂ) (x : ℂ)‖ =
        Real.exp (-σ * Real.sqrt (x ^ (2 : ℕ) + a ^ (2 : ℕ))) := by simpa using hma
    have hmb' : ‖xiMassAnalyticTest b ((σ - δ : ℝ) : ℂ) (x : ℂ)‖ =
        Real.exp (-(σ - δ) * Real.sqrt (x ^ (2 : ℕ) + b ^ (2 : ℕ))) := by simpa using hmb
    rw [hma', hmb', ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  unfold xiMassCenteredArchIntegrand
  rw [norm_mul, norm_mul]
  calc
    ‖xiMassAnalyticTest a (σ : ℂ) (x : ℂ)‖ *
        ‖logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))‖ ≤
      (Real.exp (-δ * (a - 1 / 2)) *
        ‖xiMassAnalyticTest b ((σ - δ : ℝ) : ℂ) (x : ℂ)‖) *
          ‖logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))‖ :=
      mul_le_mul_of_nonneg_right htest (norm_nonneg _)
    _ = Real.exp (-δ * (a - 1 / 2)) *
        (‖xiMassAnalyticTest b ((σ - δ : ℝ) : ℂ) (x : ℂ)‖ *
          ‖logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))‖) := by ring

/-- The crossed Gamma-pole frequency loses at most the threshold `1/2` from the mass. -/
theorem xiMassArchPoleFrequency_ge_sub_half
    {a : ℝ} (hhalf : 1 / 2 < a) :
    a - 1 / 2 ≤ xiMassArchPoleFrequency a := by
  have harg : 0 ≤ a ^ (2 : ℕ) - 1 / 4 := by nlinarith
  have hsquare : xiMassArchPoleFrequency a ^ (2 : ℕ) = a ^ (2 : ℕ) - 1 / 4 := by
    rw [xiMassArchPoleFrequency, Real.sq_sqrt harg]
  have hfreq := Real.sqrt_nonneg (a ^ (2 : ℕ) - 1 / 4)
  rw [← xiMassArchPoleFrequency] at hfreq
  nlinarith

/-- **Exponential mass-gap law for the complete height-uniform Gamma bound.** -/
theorem xiMassBottomArchUniformBound_le_exponential_gap
    {a b σ δ : ℝ} (hb : 1 / 2 < b) (hba : b ≤ a)
    (hδ : 0 < δ) (hδσ : δ < σ) :
    xiMassBottomArchUniformBound a σ ≤
      Real.exp (-δ * (a - 1 / 2)) *
        xiMassBottomArchUniformBound b (σ - δ) := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
  have hσ0 : 0 < σ := by linarith
  have hσδ : 0 < σ - δ := by linarith
  let E : ℝ := Real.exp (-δ * (a - 1 / 2))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hia := (integrable_xiMassCenteredArchIntegrand
    (a := a) (σ := σ) (u := 0) ha0 hσ0).norm
  have hib := (integrable_xiMassCenteredArchIntegrand
    (a := b) (σ := σ - δ) (u := 0) hb0 hσδ).norm
  have hia' : Integrable (fun x : ℝ =>
      ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖) := by simpa using hia
  have hib' : Integrable (fun x : ℝ =>
      ‖xiMassCenteredArchIntegrand b ((σ - δ : ℝ) : ℂ) x‖) := by simpa using hib
  have hcenter :
      (∫ x : ℝ, ‖xiMassCenteredArchIntegrand a (σ : ℂ) x‖) ≤
        E * ∫ x : ℝ, ‖xiMassCenteredArchIntegrand b ((σ - δ : ℝ) : ℂ) x‖ := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono hia' (hib'.const_mul E)
    intro x
    simpa only [E] using
      norm_xiMassCenteredArchIntegrand_le_exponential_gap hb0 hba hδ hδσ
  have hfreqA := xiMassArchPoleFrequency_ge_sub_half
    (show 1 / 2 < a by linarith)
  have hfreqBA := xiMassArchPoleFrequency_mono hb hba
  have hpoleExp :
      Real.exp (-σ * xiMassArchPoleFrequency a) ≤
        E * Real.exp (-(σ - δ) * xiMassArchPoleFrequency b) := by
    dsimp only [E]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  unfold xiMassBottomArchUniformBound
  have hpole := mul_le_mul_of_nonneg_left hpoleExp (by positivity : 0 ≤ 2 * Real.pi)
  dsimp only [E] at hcenter ⊢
  nlinarith

/-- Xi alias for the universal co-moving exponential rate. -/
def xiMassComovingExponentialRate (σ : ℝ) : ℝ :=
  HTGeometry.AbstractSpectralFamily.comovingExponentialRate σ

theorem xiMassComovingExponentialRate_pos {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 < xiMassComovingExponentialRate σ :=
  HTGeometry.AbstractSpectralFamily.comovingExponentialRate_pos hσ

theorem xiMassComovingExponentialRate_lt {σ : ℝ} (hσ : 1 / 2 < σ) :
    xiMassComovingExponentialRate σ < σ := by
  unfold xiMassComovingExponentialRate
    HTGeometry.AbstractSpectralFamily.comovingExponentialRate
  linarith

/-- Xi specialization of universal exponential co-moving trace extinction. -/
theorem norm_xiMassTraceC_comoving_le_exponential
    {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    ‖(xiMassFamily (show 1 / 2 ≤ xiComovingMass u by
        linarith [xiComovingMass_ge_two u])).traceC ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-xiMassComovingExponentialRate σ * xiComovingMass u) *
        xiPoissonTraceReal (xiMassComovingExponentialRate σ) := by
  let ha : 1 / 2 ≤ xiComovingMass u := by
    linarith [xiComovingMass_ge_two u]
  have h := xiPoissonAbstract.norm_mass_traceC_le_comoving_exponential
    (xiComovingMass_ge_two u) (abs_le_xiComovingMass u) hσ
  rw [← xiMassFamily_traceC_eq ha ((σ : ℂ) + u * I),
    xiPoissonAbstract_traceReal] at h
  simpa only [xiMassComovingExponentialRate] using h

/-- Fixed coefficient in the exponentially decaying literal prime-source bound. -/
def xiMassComovingPrimeExponentialConstant (σ : ℝ) : ℝ :=
  ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (xiMassComovingExponentialRate σ) +
    xiMassBottomArchUniformBound 2 (σ - xiMassComovingExponentialRate σ)

theorem xiMassComovingPrimeExponentialConstant_nonneg
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 ≤ xiMassComovingPrimeExponentialConstant σ := by
  have hκ := xiMassComovingExponentialRate_pos hσ
  have hκσ := xiMassComovingExponentialRate_lt hσ
  unfold xiMassComovingPrimeExponentialConstant
  exact add_nonneg
    (mul_nonneg (norm_nonneg _) (xiPoissonAbstract.traceReal_nonneg _))
    (xiMassBottomArchUniformBound_nonneg (by norm_num) (by linarith))

/-- **Exponentially decaying co-moving prime cone.**  This unconditional all-height estimate is
strictly stronger than qualitative `C₀` extinction. -/
theorem norm_xiMassBottomPrimeIntegral_comoving_le_exponential
    {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    ‖xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-xiMassComovingExponentialRate σ *
          (xiComovingMass u - 1 / 2)) *
        xiMassComovingPrimeExponentialConstant σ := by
  let κ : ℝ := xiMassComovingExponentialRate σ
  let A : ℝ := xiComovingMass u
  let E : ℝ := Real.exp (-κ * (A - 1 / 2))
  have hκ : 0 < κ := xiMassComovingExponentialRate_pos hσ
  have hκσ : κ < σ := xiMassComovingExponentialRate_lt hσ
  have hA : 2 ≤ A := xiComovingMass_ge_two u
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hca : (1 : ℝ) < A := by linarith
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    linarith
  have htrace0 := norm_xiMassTraceC_comoving_le_exponential hσ u
  have hexpTrace : Real.exp (-κ * A) ≤ E := by
    dsimp only [E]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have htrace :
      ‖(xiMassFamily (show 1 / 2 ≤ A by linarith)).traceC ((σ : ℂ) + u * I)‖ ≤
        E * xiPoissonTraceReal κ := by
    have hweight := mul_le_mul_of_nonneg_right hexpTrace
      (xiPoissonTraceReal_nonneg κ)
    exact htrace0.trans (by simpa only [A, κ] using hweight)
  have harch0 :
      ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ ≤
        xiMassBottomArchUniformBound A σ :=
    norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca (by linarith)
  have harchGap := xiMassBottomArchUniformBound_le_exponential_gap
    (a := A) (b := (2 : ℝ)) (σ := σ) (δ := κ)
    (by norm_num) hA hκ hκσ
  have harch :
      ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ ≤
        E * xiMassBottomArchUniformBound 2 (σ - κ) :=
    harch0.trans (by simpa only [E] using harchGap)
  rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ,
    integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ]
  calc
    ‖I * (Real.pi * I *
          (xiMassFamily (show 1 / 2 ≤ A by linarith)).traceC ((σ : ℂ) + u * I)) +
        xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ ≤
      ‖I * (Real.pi * I *
          (xiMassFamily (show 1 / 2 ≤ A by linarith)).traceC ((σ : ℂ) + u * I))‖ +
        ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ := norm_add_le _ _
    _ = ‖(Real.pi : ℂ) * I‖ *
          ‖(xiMassFamily (show 1 / 2 ≤ A by linarith)).traceC ((σ : ℂ) + u * I)‖ +
        ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ := by
      rw [norm_mul, norm_mul]
      simp
    _ ≤ ‖(Real.pi : ℂ) * I‖ *
          (E * xiPoissonTraceReal κ) +
        E * xiMassBottomArchUniformBound 2 (σ - κ) :=
      add_le_add (mul_le_mul_of_nonneg_left htrace (norm_nonneg _)) harch
    _ = Real.exp (-xiMassComovingExponentialRate σ *
          (xiComovingMass u - 1 / 2)) *
        xiMassComovingPrimeExponentialConstant σ := by
      dsimp only [E, A, κ]
      unfold xiMassComovingPrimeExponentialConstant
      ring

/-- **Exponential quotient theorem.**  High-pass and fixed source differ by an explicitly
exponentially decaying function on all real heights. -/
theorem norm_xiMassPrimeSemigroupHighPass_sub_fixedSource_le_exponential
    {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    ‖xiMassPrimeSemigroupHighPass σ u -
        xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-xiMassComovingExponentialRate σ *
          (xiComovingMass u - 1 / 2)) *
        xiMassComovingPrimeExponentialConstant σ := by
  have heq :
      xiMassPrimeSemigroupHighPass σ u -
          xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I) =
        -xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I) := by
    rw [xiMassPrimeSemigroupHighPass_eq_apertureGap (by linarith) u]
    unfold xiMassBottomPrimeApertureGap
    ring
  rw [heq, norm_neg]
  exact norm_xiMassBottomPrimeIntegral_comoving_le_exponential hσ u

end


end RHTower
