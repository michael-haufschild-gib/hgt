import GaloisForLFunctions.HTGeometry.AbstractSpectralComovingExtinction
import GaloisForLFunctions.RHTower.XiMassPrimeSemigroupHighPass

/-!
# Extinction of the co-moving Xi prime source

The aperture `|u|+2` does more than bound the mass-shifted Xi source.  The abstract trace vanishes
by co-moving Tannery convergence.  The centered Gamma integral and crossed-pole residue vanish as
mass tends to infinity, so the complete literal von-Mangoldt bottom source also tends to zero.

Consequently the canonical mass-semigroup high-pass is asymptotic to the original fixed-mass
prime source.  Its co-moving subtraction is a `C₀` correction, not merely a bounded one.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

open MeasureTheory Set

/-- Pointwise extinction of the centered Gamma density along integer masses. -/
theorem tendsto_norm_xiMassCenteredArchIntegrand_natMass_zero
    {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    Tendsto
      (fun n : ℕ => ‖xiMassCenteredArchIntegrand (n + 2) (σ : ℂ) x‖)
      atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun n : ℕ => Real.exp (-σ * ((n : ℝ) + 2)) *
        ‖logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))‖)
      atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hlin : Tendsto (fun n : ℕ => -σ * ((n : ℝ) + 2)) atTop atBot :=
      hnat.const_mul_atTop_of_neg (neg_neg_of_pos hσ)
    simpa only [Function.comp_apply, zero_mul] using
      (Real.tendsto_exp_atBot.comp hlin).mul_const
        ‖logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))‖
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmajor
  exact Eventually.of_forall fun n => by
    have ha : 0 < ((n : ℝ) + 2) := by positivity
    have harg : 0 ≤ x ^ 2 + ((n : ℝ) + 2) ^ 2 := by positivity
    have hsquare := Real.sq_sqrt harg
    have hsqrt := Real.sqrt_nonneg (x ^ 2 + ((n : ℝ) + 2) ^ 2)
    have hroot : (n : ℝ) + 2 ≤ Real.sqrt (x ^ 2 + ((n : ℝ) + 2) ^ 2) := by
      nlinarith [sq_nonneg x]
    rw [xiMassCenteredArchIntegrand, norm_mul]
    have hnorm := norm_xiMassAnalyticTest_ofReal_eq
      (a := (n : ℝ) + 2) (σ := σ) (u := 0) (x := x) ha
    rw [show ‖xiMassAnalyticTest ((n : ℝ) + 2) (σ : ℂ) (x : ℂ)‖ =
      Real.exp (-σ * Real.sqrt (x ^ 2 + ((n : ℝ) + 2) ^ 2)) by simpa using hnorm]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith)) (norm_nonneg _)

/-- The centered Gamma `L¹` mass vanishes as aperture tends to infinity through integers. -/
theorem tendsto_integral_norm_xiMassCenteredArchIntegrand_natMass_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ, ‖xiMassCenteredArchIntegrand (n + 2) (σ : ℂ) x‖)
      atTop (𝓝 0) := by
  have hdom : Integrable (fun x : ℝ => ‖xiMassCenteredArchIntegrand 2 (σ : ℂ) x‖) := by
    simpa using (integrable_xiMassCenteredArchIntegrand
      (a := (2 : ℝ)) (σ := σ) (u := 0) (by norm_num) hσ).norm
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : ℝ => ‖xiMassCenteredArchIntegrand 2 (σ : ℂ) x‖)
    (fun n => (continuous_xiMassCenteredArchIntegrand
      (show 0 < ((n : ℝ) + 2) by positivity) (σ : ℂ)).norm.aestronglyMeasurable)
    hdom
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_xiMassCenteredArchIntegrand_antitone
        (a := (n : ℝ) + 2) (b := 2) (σ := σ) (x := x)
        (show 0 < (2 : ℝ) by norm_num)
        (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) hσ)
    (Eventually.of_forall fun x =>
      tendsto_norm_xiMassCenteredArchIntegrand_natMass_zero hσ x)
  simpa using hdct

/-- The crossed Gamma-pole residue vanishes along integer masses. -/
theorem tendsto_exp_neg_xiMassArchPoleFrequency_natMass_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto
      (fun n : ℕ => Real.exp (-σ * xiMassArchPoleFrequency (n + 2)))
      atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun n : ℕ => Real.exp (-σ * (((n : ℝ) + 2) / 2)))
      atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / 2) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_div_const
        (by norm_num)
    have hlin : Tendsto (fun n : ℕ => -σ * (((n : ℝ) + 2) / 2)) atTop atBot :=
      hnat.const_mul_atTop_of_neg (neg_neg_of_pos hσ)
    exact Real.tendsto_exp_atBot.comp hlin
  refine squeeze_zero' (Eventually.of_forall fun n => (Real.exp_pos _).le) ?_ hmajor
  exact Eventually.of_forall fun n => by
    have hA : 0 ≤ (n : ℝ) + 2 := by positivity
    have harg : 0 ≤ ((n : ℝ) + 2) ^ 2 - 1 / 4 := by nlinarith
    have hsquare : xiMassArchPoleFrequency ((n : ℝ) + 2) ^ 2 =
        ((n : ℝ) + 2) ^ 2 - 1 / 4 := by
      rw [xiMassArchPoleFrequency, Real.sq_sqrt harg]
    have hfreq := Real.sqrt_nonneg (((n : ℝ) + 2) ^ 2 - 1 / 4)
    rw [← xiMassArchPoleFrequency] at hfreq
    have hlower : ((n : ℝ) + 2) / 2 ≤
        xiMassArchPoleFrequency ((n : ℝ) + 2) := by
      nlinarith [sq_nonneg ((n : ℝ) + 2)]
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem tendsto_xiMassBottomArchUniformBound_natMass_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun n : ℕ => xiMassBottomArchUniformBound (n : ℝ) σ)
      atTop (𝓝 0) := by
  have hshift : Tendsto
      (fun n : ℕ => xiMassBottomArchUniformBound ((n : ℝ) + 2) σ)
      atTop (𝓝 0) := by
    have hcenter := tendsto_integral_norm_xiMassCenteredArchIntegrand_natMass_zero hσ
    have hpole := tendsto_exp_neg_xiMassArchPoleFrequency_natMass_zero hσ
    simpa [xiMassBottomArchUniformBound] using hcenter.add (hpole.const_mul (2 * Real.pi))
  exact (tendsto_add_atTop_iff_nat 2).mp (by simpa [Nat.cast_add] using hshift)

/-- The complete height-uniform Gamma bound vanishes as real mass tends to infinity. -/
theorem tendsto_xiMassBottomArchUniformBound_atTop_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun a : ℝ => xiMassBottomArchUniformBound a σ)
      atTop (𝓝 0) := by
  have hfloor : Tendsto
      (fun a : ℝ => xiMassBottomArchUniformBound (Nat.floor a : ℝ) σ)
      atTop (𝓝 0) :=
    (tendsto_xiMassBottomArchUniformBound_natMass_zero hσ).comp
      tendsto_nat_floor_atTop
  refine squeeze_zero' ?_ ?_ hfloor
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
    exact xiMassBottomArchUniformBound_nonneg (by linarith) hσ
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
    have hfloorTwo : 2 ≤ Nat.floor a := Nat.le_floor ha
    have hfloorTwoCast : (2 : ℝ) ≤ (Nat.floor a : ℝ) := by exact_mod_cast hfloorTwo
    have hfloorHalf : (1 : ℝ) / 2 < (Nat.floor a : ℝ) := by linarith
    have hfloorLe : (Nat.floor a : ℝ) ≤ a := Nat.floor_le (by linarith)
    exact xiMassBottomArchUniformBound_antitone hfloorHalf hfloorLe hσ

theorem tendsto_xiComovingMass_atTop : Tendsto xiComovingMass atTop atTop := by
  unfold xiComovingMass
  exact tendsto_atTop_add_const_right atTop 2 tendsto_abs_atTop_atTop

/-- The co-moving Xi trace vanishes; boundedness from the cone theorem is not sharp. -/
theorem tendsto_xiMassTraceC_comoving_zero
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto
      (fun u : ℝ =>
        (xiMassFamily (show 1 / 2 ≤ xiComovingMass u by
          linarith [xiComovingMass_ge_two u])).traceC ((σ : ℂ) + u * I))
      atTop (𝓝 0) := by
  have hbase : 1 / 2 ≤ xiPoissonAbstract.base := by
    rw [xiPoissonAbstract_base]
    linarith [three_lt_xiPoissonBottomHeight]
  have h := xiPoissonAbstract.tendsto_mass_traceC_comoving_zero
    (mass := xiComovingMass)
    (fun u => by linarith [xiComovingMass_ge_two u]) hbase
    abs_le_xiComovingMass tendsto_xiComovingMass_atTop hσ
  exact h.congr' (Eventually.of_forall fun u =>
    (xiMassFamily_traceC_eq
      (show 1 / 2 ≤ xiComovingMass u by
        linarith [xiComovingMass_ge_two u]) ((σ : ℂ) + u * I)).symm)

/-- The entire co-moving Gamma bottom channel tends to zero. -/
theorem tendsto_xiMassBottomArchIntegral_comoving_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto
      (fun u : ℝ => xiMassBottomArchIntegral (xiComovingMass u) 1
        ((σ : ℂ) + u * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor : Tendsto
      (fun u : ℝ => xiMassBottomArchUniformBound (xiComovingMass u) σ)
      atTop (𝓝 0) :=
    (tendsto_xiMassBottomArchUniformBound_atTop_zero hσ).comp
      tendsto_xiComovingMass_atTop
  refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hmajor
  exact Eventually.of_forall fun u => by
    simpa [xiMassBottomArchIntegral] using
      norm_integral_xiMassBottomArchIntegrand_le_uniform
        (show 1 / 2 < (1 : ℝ) by norm_num)
        (show (1 : ℝ) < xiComovingMass u by
          linarith [xiComovingMass_ge_two u]) hσ

/-- **Co-moving source extinction.** The literal von-Mangoldt bottom source tends to zero along
the widening mass cone. -/
theorem tendsto_xiMassBottomPrimeIntegral_comoving_zero
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto
      (fun u : ℝ => xiMassBottomPrimeIntegral (xiComovingMass u) 1
        ((σ : ℂ) + u * I))
      atTop (𝓝 0) := by
  have htrace := tendsto_xiMassTraceC_comoving_zero hσ
  have harch := tendsto_xiMassBottomArchIntegral_comoving_zero
    (show 0 < σ by linarith)
  have hsum := (htrace.const_mul (I * ((Real.pi : ℂ) * I))).add harch
  have hsum0 : Tendsto
      (fun u : ℝ => I * ((Real.pi : ℂ) * I) *
        (xiMassFamily (show 1 / 2 ≤ xiComovingMass u by
          linarith [xiComovingMass_ge_two u])).traceC ((σ : ℂ) + u * I) +
        xiMassBottomArchIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I))
      atTop (𝓝 0) := by
    simpa using hsum
  have heq : ∀ u : ℝ,
      xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I) =
        I * ((Real.pi : ℂ) * I) *
          (xiMassFamily (show 1 / 2 ≤ xiComovingMass u by
            linarith [xiComovingMass_ge_two u])).traceC ((σ : ℂ) + u * I) +
          xiMassBottomArchIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I) := by
    intro u
    have hhalf : 1 / 2 < (1 : ℝ) := by norm_num
    have hca : (1 : ℝ) < xiComovingMass u := by
      linarith [xiComovingMass_ge_two u]
    have hτ : 0 < (((σ : ℂ) + u * I)).re := by
      simpa [Complex.mul_re] using (show 0 < σ by linarith)
    rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ,
      integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ]
    ring
  exact hsum0.congr' (Eventually.of_forall fun u => (heq u).symm)

/-- The canonical semigroup high-pass is asymptotic to the original fixed-mass prime source: its
subtracted co-moving arm is a `C₀` correction. -/
theorem tendsto_xiMassPrimeSemigroupHighPass_sub_fixedSource_zero
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto
      (fun u : ℝ => xiMassPrimeSemigroupHighPass σ u -
        xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I))
      atTop (𝓝 0) := by
  have hmove : Tendsto
      (fun u : ℝ => -xiMassBottomPrimeIntegral (xiComovingMass u) 1
        ((σ : ℂ) + u * I)) atTop (𝓝 0) := by
    simpa using (tendsto_xiMassBottomPrimeIntegral_comoving_zero hσ).neg
  exact hmove.congr' (Eventually.of_forall fun u => by
    change -xiMassBottomPrimeIntegral (xiComovingMass u) 1 ((σ : ℂ) + u * I) =
      xiMassPrimeSemigroupHighPass σ u -
        xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I)
    rw [xiMassPrimeSemigroupHighPass_eq_apertureGap (by linarith) u]
    unfold xiMassBottomPrimeApertureGap
    ring)

end


end RHTower
