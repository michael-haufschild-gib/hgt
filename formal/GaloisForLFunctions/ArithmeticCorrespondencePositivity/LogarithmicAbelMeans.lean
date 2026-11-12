import GaloisForLFunctions.ArithmeticCorrespondencePositivity.StrictPowerGrowthHasAnOpenMellinHalfPlane

/-!
# Logarithmic Abel means of arithmetic sequences

The logarithmic staircase turns ordinary sequence convergence into an
Abel limit. Subpolynomial growth guarantees integrability for every
positive Abel parameter, so these means preserve finite linear identities.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open SelbergClass.DegreeOne

/-- The logarithmic Abel mean of the actual integer samples. -/
def logarithmicAbelMean (f : ℕ → ℝ) (ε : ℝ) : ℂ :=
  (ε : ℂ) * abelIntegral (stepLaplaceIntegrand f 0) 0 (ε : ℂ)

/-- The value at the unused zero index does not affect the logarithmic mean. -/
theorem logarithmicAbelMean_congr_pos {f g : ℕ → ℝ}
    (he : ∀ N : ℕ, 1 ≤ N → f N = g N) (ε : ℝ) :
    logarithmicAbelMean f ε = logarithmicAbelMean g ε := by
  rw [logarithmicAbelMean, logarithmicAbelMean]
  congr 1
  rw [abelIntegral, abelIntegral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hN : 1 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor (Real.one_le_exp (le_of_lt hu))
  rw [stepLaplaceIntegrand, stepLaplaceIntegrand, he _ hN]

/-- The resonant Abel theorem at exponent zero reads the ordinary limit
of a bounded logarithmic profile. -/
theorem tendsto_abelMean_of_bounded_tendsto
    {r : ℝ → ℂ} {C : ℝ} {L : ℂ}
    (hr : AEStronglyMeasurable r (volume.restrict (Ioi 0)))
    (hb : ∀ u : ℝ, 0 < u → ‖r u‖ ≤ C) (hL : Tendsto r atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * abelIntegral r 0 (ε : ℂ))
      (𝓝[>] 0) (𝓝 L) := by
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hh := tendsto_abelIntegral_resonant hr hb hL 0
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin)
    heps (τ := fun _ : ℝ => 0) (by simpa only [zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)))
  simpa only [abelExponent, ofReal_zero, mul_zero, sub_zero, Complex.cpow_one,
    zero_mul, add_zero, Complex.Gamma_one, mul_one] using hh

/-- Ordinary convergence is preserved by logarithmic Abel averaging. -/
theorem tendsto_logarithmicAbelMean_of_tendsto
    {f : ℕ → ℝ} {L : ℝ} (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto (logarithmicAbelMean f) (𝓝[>] 0) (𝓝 (L : ℂ)) := by
  obtain ⟨B, hB⟩ := hf.abs.bddAbove_range
  have hb : ∀ u : ℝ, 0 < u → ‖stepLaplaceIntegrand f 0 u‖ ≤ B := by
    intro u _
    rw [norm_stepLaplaceIntegrand, zero_re, zero_mul, neg_zero, Real.exp_zero, one_mul]
    exact hB ⟨⌊Real.exp u⌋₊, rfl⟩
  have hnorm : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(0 : ℝ)) * f N) atTop (𝓝 L) := by
    simpa only [neg_zero, Real.rpow_zero, one_mul] using hf
  have hlim := tendsto_stepLaplaceIntegrand_of_power_asymptotic hnorm
  simp only [ofReal_zero] at hlim
  exact tendsto_abelMean_of_bounded_tendsto
    (measurable_stepLaplaceIntegrand f 0).aestronglyMeasurable hb hlim

/-- A convergent sequence has subpolynomial growth. -/
theorem strictPowerGrowth_zero_of_tendsto
    {f : ℕ → ℝ} {L : ℝ} (hf : Tendsto f atTop (𝓝 L)) :
    _root_.HTGeometry.StrictNaturalPowerGrowth f 0 := by
  obtain ⟨B, hB⟩ := hf.abs.bddAbove_range
  intro δ hδ
  refine ⟨|B|, abs_nonneg _, fun N hN => ?_⟩
  have hb := (hB ⟨N, rfl⟩).trans (le_abs_self B)
  have hp := Real.one_le_rpow (by exact_mod_cast hN : (1 : ℝ) ≤ N) hδ.le
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg B)
  rw [mul_one] at hm
  simpa only [zero_add] using hb.trans hm

/-- Subpolynomial growth makes every positive logarithmic Abel integral finite. -/
theorem integrableOn_logarithmicAbelIntegrand
    {f : ℕ → ℝ} (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f 0)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u => stepLaplaceIntegrand f 0 u * abelKernel 0 (ε : ℂ) u) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := hf (ε / 2) (by linarith only [hε])
  refine ((exp_neg_integrableOn_Ioi 0 (by linarith only [hε] : 0 < ε / 2)).const_mul C).mono'
    ((measurable_stepLaplaceIntegrand f 0).mul (measurable_abelKernel 0 (ε : ℂ)))
      .aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  have hN : 1 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor (Real.one_le_exp hu0.le)
  have hnp := Nat.floor_le (Real.exp_pos u).le
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg ⌊Real.exp u⌋₊) hnp
    (by linarith only [hε] : 0 ≤ ε / 2)
  rw [norm_mul, norm_stepLaplaceIntegrand, zero_re, zero_mul, neg_zero,
    Real.exp_zero, one_mul, norm_abelKernel 0 (ε : ℂ) hu0, ofReal_re]
  calc
    _ ≤ (C * (⌊Real.exp u⌋₊ : ℝ) ^ (ε / 2)) * Real.exp (-ε * u) :=
      mul_le_mul_of_nonneg_right (by simpa only [zero_add] using hb _ hN) (Real.exp_pos _).le
    _ ≤ (C * (Real.exp u) ^ (ε / 2)) * Real.exp (-ε * u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (Real.exp_pos _).le
    _ = C * Real.exp (-(ε / 2) * u) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Logarithmic Abel means preserve subtraction of subpolynomial sequences. -/
theorem logarithmicAbelMean_sub
    {f g : ℕ → ℝ} (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f 0)
    (hg : _root_.HTGeometry.StrictNaturalPowerGrowth g 0) {ε : ℝ} (hε : 0 < ε) :
    logarithmicAbelMean (fun N => f N - g N) ε =
      logarithmicAbelMean f ε - logarithmicAbelMean g ε := by
  rw [logarithmicAbelMean, logarithmicAbelMean, logarithmicAbelMean, ← mul_sub]
  congr 1
  rw [abelIntegral, abelIntegral, abelIntegral,
    ← integral_sub (integrableOn_logarithmicAbelIntegrand hf hε)
      (integrableOn_logarithmicAbelIntegrand hg hε)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp only [stepLaplaceIntegrand, ofReal_sub]
    ring

/-- Multiplying the original sequence multiplies its logarithmic Abel mean. -/
theorem logarithmicAbelMean_const_mul (f : ℕ → ℝ) (c ε : ℝ) :
    logarithmicAbelMean (fun N => c * f N) ε = (c : ℂ) * logarithmicAbelMean f ε := by
  have he : (fun u => stepLaplaceIntegrand (fun N => c * f N) 0 u * abelKernel 0 (ε : ℂ) u) =
      fun u => (c : ℂ) * (stepLaplaceIntegrand f 0 u * abelKernel 0 (ε : ℂ) u) := by
    funext u
    simp only [stepLaplaceIntegrand, ofReal_mul]
    ring
  rw [logarithmicAbelMean, logarithmicAbelMean, abelIntegral, he, integral_const_mul, abelIntegral]
  ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
