import GaloisForLFunctions.RHTower.MobiusWeightedMertensVector

/-!
# The critical `L²` limit of the weighted-Mertens boundary vector

`mobius-schur-centered-boundary-limit-law.md`, equations `(14)`, `(15)` and `(17)`.

Plancherel transports the strong Hardy limit `G_omega → G_0` to the time domain:

```text
∫ ‖G_omega(iτ)‖² dτ = 2π ∫ ‖m_omega‖² ,
m_0 ∈ L²(0,∞) ,
∫ ‖m_omega - m_0‖² → 0 ,
∫ ‖m_0‖² = (2π)⁻¹ ∫ ‖1/(iτ ζ(1+iτ))‖² dτ .
```
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace RHTower

/-! ### The prelimit energy identities -/

theorem integrable_norm_sq_centeredSchurQuotient {ω : ℝ} (hω : 0 < ω) :
    Integrable (fun τ : ℝ => ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I)‖ ^ 2) := by
  have h := integrable_norm_sq_laplaceBoundary (integrable_centeredMertensVector hω)
    (memLp_centeredMertensVector hω)
  refine h.congr ?_
  filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with y hy
  rw [laplaceBoundary_centeredMertensVector hω hy]

/-- **Card `(15)` prelimit.** -/
theorem integral_norm_sq_centeredSchur_eq {ω : ℝ} (hω : 0 < ω) :
    (∫ τ : ℝ, ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I)‖ ^ 2)
      = 2 * Real.pi * ∫ t : ℝ, ‖centeredMertensVector ω t‖ ^ 2 := by
  rw [← integral_norm_sq_laplaceBoundary (integrable_centeredMertensVector hω)
    (memLp_centeredMertensVector hω)]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with y hy
  rw [laplaceBoundary_centeredMertensVector hω hy]

theorem integral_norm_sq_centeredSchur_sub_eq {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    (∫ τ : ℝ, ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
        centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2)
      = 2 * Real.pi * ∫ t : ℝ,
          ‖centeredMertensVector ω t - centeredMertensVector ν t‖ ^ 2 := by
  have hint : Integrable (fun u : ℝ => centeredMertensVector ω u - centeredMertensVector ν u) :=
    (integrable_centeredMertensVector hω).sub (integrable_centeredMertensVector hν)
  have hmem : MemLp (fun u : ℝ => centeredMertensVector ω u - centeredMertensVector ν u)
      2 volume := (memLp_centeredMertensVector hω).sub (memLp_centeredMertensVector hν)
  rw [← integral_norm_sq_laplaceBoundary hint hmem]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with y hy
  rw [laplaceBoundary_sub (integrable_centeredMertensVector hω)
    (integrable_centeredMertensVector hν),
    laplaceBoundary_centeredMertensVector hω hy,
    laplaceBoundary_centeredMertensVector hν hy]

/-! ### The critical limit -/

/-- A sequence of shifts approaching the critical parameter from the right. -/
def criticalShiftSeq (k : ℕ) : ℝ := 1 / (k + 1)

theorem criticalShiftSeq_pos (k : ℕ) : 0 < criticalShiftSeq k := by
  rw [criticalShiftSeq]
  positivity

theorem tendsto_criticalShiftSeq :
    Tendsto criticalShiftSeq atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Filter.Eventually.of_forall fun k => criticalShiftSeq_pos k⟩
  have h : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact h

theorem tendsto_centeredMertensVector_seq (t : ℝ) :
    Tendsto (fun k : ℕ => centeredMertensVector (criticalShiftSeq k) t) atTop
      (nhds (criticalMertensVector t)) :=
  (tendsto_centeredMertensVector_pointwise t).comp tendsto_criticalShiftSeq

/-- Fatou against the prelimit energies. -/
theorem lintegral_enorm_sq_criticalMertensVector_sub_le (ν : ℝ) :
    (∫⁻ t : ℝ, ‖criticalMertensVector t - centeredMertensVector ν t‖ₑ ^ 2)
      ≤ liminf (fun k : ℕ => ∫⁻ t : ℝ,
          ‖centeredMertensVector (criticalShiftSeq k) t - centeredMertensVector ν t‖ₑ ^ 2)
        atTop := by
  have hmeas : ∀ k : ℕ, Measurable (fun t : ℝ =>
      ‖centeredMertensVector (criticalShiftSeq k) t - centeredMertensVector ν t‖ₑ ^ 2) := by
    intro k
    exact (((measurable_centeredMertensVector (criticalShiftSeq k)).sub
      (measurable_centeredMertensVector ν)).enorm).pow_const 2
  have hlim : ∀ t : ℝ,
      liminf (fun k : ℕ =>
        ‖centeredMertensVector (criticalShiftSeq k) t - centeredMertensVector ν t‖ₑ ^ 2) atTop
        = ‖criticalMertensVector t - centeredMertensVector ν t‖ₑ ^ 2 := by
    intro t
    refine Filter.Tendsto.liminf_eq ?_
    have h := (tendsto_centeredMertensVector_seq t).sub
      (tendsto_const_nhds (x := centeredMertensVector ν t))
    have hcont : Continuous fun a : ℝ≥0∞ => a ^ 2 := ENNReal.continuous_pow 2
    exact (hcont.tendsto _).comp h.enorm
  calc (∫⁻ t : ℝ, ‖criticalMertensVector t - centeredMertensVector ν t‖ₑ ^ 2)
      = ∫⁻ t : ℝ, liminf (fun k : ℕ =>
          ‖centeredMertensVector (criticalShiftSeq k) t - centeredMertensVector ν t‖ₑ ^ 2)
          atTop := by
        refine lintegral_congr fun t => (hlim t).symm
    _ ≤ liminf (fun k : ℕ => ∫⁻ t : ℝ,
          ‖centeredMertensVector (criticalShiftSeq k) t - centeredMertensVector ν t‖ₑ ^ 2)
          atTop := lintegral_liminf_le hmeas


/-! ### From the lintegral bound to the `L²` statements -/

theorem lintegral_enorm_sq_eq_ofReal {f : ℝ → ℂ}
    (hf : Integrable (fun t : ℝ => ‖f t‖ ^ 2)) :
    (∫⁻ t : ℝ, ‖f t‖ₑ ^ 2) = ENNReal.ofReal (∫ t : ℝ, ‖f t‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun t => by positivity)]
  refine lintegral_congr fun t => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem integrable_norm_sq_sub {f g : ℝ → ℂ}
    (hf : Integrable (fun τ : ℝ => ‖f τ‖ ^ 2)) (hg : Integrable (fun τ : ℝ => ‖g τ‖ ^ 2))
    (hmeas : AEStronglyMeasurable (fun τ : ℝ => f τ - g τ) volume) :
    Integrable (fun τ : ℝ => ‖f τ - g τ‖ ^ 2) := by
  refine Integrable.mono ((hf.const_mul 2).add (hg.const_mul 2)) (hmeas.norm.pow 2) ?_
  filter_upwards [] with τ
  simp only [Pi.add_apply]
  have h1 : ‖f τ - g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_sub_le _ _
  have h2 : (0 : ℝ) ≤ ‖f τ - g τ‖ := norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖f τ‖ - ‖g τ‖), norm_nonneg (f τ), norm_nonneg (g τ)]

theorem integrable_norm_sq_centeredSchur_sub {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    Integrable (fun τ : ℝ => ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
      centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2) := by
  have hint : Integrable (fun u : ℝ => centeredMertensVector ω u - centeredMertensVector ν u) :=
    (integrable_centeredMertensVector hω).sub (integrable_centeredMertensVector hν)
  have hmem : MemLp (fun u : ℝ => centeredMertensVector ω u - centeredMertensVector ν u)
      2 volume := (memLp_centeredMertensVector hω).sub (memLp_centeredMertensVector hν)
  have h := integrable_norm_sq_laplaceBoundary hint hmem
  refine h.congr ?_
  filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with y hy
  rw [laplaceBoundary_sub (integrable_centeredMertensVector hω)
    (integrable_centeredMertensVector hν),
    laplaceBoundary_centeredMertensVector hω hy,
    laplaceBoundary_centeredMertensVector hν hy]

theorem aestronglyMeasurable_centeredSchur_line {ω : ℝ} (hω : 0 < ω) :
    AEStronglyMeasurable (fun τ : ℝ => centeredSchurQuotient ω ((τ : ℂ) * Complex.I)) volume :=
  aestronglyMeasurable_of_continuousOn_ne_zero (continuousOn_centeredSchurQuotient_line hω)

theorem aestronglyMeasurable_centeredSchurLimit_line :
    AEStronglyMeasurable (fun τ : ℝ => centeredSchurLimit ((τ : ℂ) * Complex.I)) volume := by
  refine aestronglyMeasurable_of_continuousOn_ne_zero ?_
  intro τ hτ0
  have hτ : τ ≠ 0 := hτ0
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := line_ne_one (by simp) hτ
  have hζ0 : riemannZeta ((1 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp
  have hz : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I)) τ := by
    have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I)) := by continuity
    exact this.continuousAt
  have hA : ContinuousAt (fun t : ℝ => riemannZeta (1 + (t : ℂ) * Complex.I)) τ :=
    continuousAt_zeta_line hne1
  exact (continuousAt_const.div (hz.mul hA) (mul_ne_zero hz0 hζ0)).continuousWithinAt

/-- The critical Hardy energy of the limit. -/
def criticalHardyEnergy (ν : ℝ) : ℝ :=
  ∫ τ : ℝ, ‖centeredSchurLimit ((τ : ℂ) * Complex.I) -
    centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2

theorem criticalHardyEnergy_nonneg (ν : ℝ) : 0 ≤ criticalHardyEnergy ν :=
  integral_nonneg fun τ => by positivity

theorem tendsto_criticalHardyEnergy :
    Tendsto criticalHardyEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h := tendsto_boundary_centeredSchur_energy
  refine h.congr fun ν => ?_
  rw [criticalHardyEnergy]
  refine integral_congr_ae ?_
  filter_upwards [] with τ
  rw [← norm_neg]
  congr 1
  ring


/-! ### The critical `L²` statements -/

theorem memLp_two_of_lintegral_lt_top {f : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable f volume) (h : (∫⁻ t : ℝ, ‖f t‖ₑ ^ 2) < ⊤) :
    MemLp f 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ⟨hmeas.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The prelimit difference energies are controlled by the Hardy energies. -/
theorem lintegral_criticalMertens_sub_le {ν : ℝ} (hν : 0 < ν) :
    (∫⁻ t : ℝ, ‖criticalMertensVector t - centeredMertensVector ν t‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * criticalHardyEnergy ν)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set A : ℕ → ℝ := fun k => ∫ τ : ℝ,
    ‖centeredSchurQuotient (criticalShiftSeq k) ((τ : ℂ) * Complex.I) -
      centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2 with hA
  have hA0 : Tendsto A atTop (nhds 0) :=
    tendsto_boundary_centeredSchur_energy.comp tendsto_criticalShiftSeq
  have hstep : ∀ k : ℕ,
      (∫⁻ t : ℝ, ‖centeredMertensVector (criticalShiftSeq k) t -
        centeredMertensVector ν t‖ₑ ^ 2)
        ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * A k + 2 * criticalHardyEnergy ν)) := by
    intro k
    have hk := criticalShiftSeq_pos k
    have hintm : Integrable (fun t : ℝ =>
        ‖centeredMertensVector (criticalShiftSeq k) t - centeredMertensVector ν t‖ ^ 2) := by
      have hm := (memLp_centeredMertensVector hk).sub (memLp_centeredMertensVector hν)
      exact (memLp_two_iff_integrable_sq_norm
        (((measurable_centeredMertensVector (criticalShiftSeq k)).sub
          (measurable_centeredMertensVector ν)).aestronglyMeasurable)).mp hm
    rw [lintegral_enorm_sq_eq_ofReal hintm]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq := integral_norm_sq_centeredSchur_sub_eq hk hν
    have hbound : (∫ τ : ℝ, ‖centeredSchurQuotient (criticalShiftSeq k) ((τ : ℂ) * Complex.I) -
        centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2)
        ≤ 2 * A k + 2 * criticalHardyEnergy ν := by
      have h1 : Integrable (fun τ : ℝ =>
          ‖centeredSchurQuotient (criticalShiftSeq k) ((τ : ℂ) * Complex.I) -
            centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2) :=
        integrable_norm_sq_sub (integrable_norm_sq_centeredSchurQuotient hk)
          integrable_norm_sq_centeredSchurLimit
          ((aestronglyMeasurable_centeredSchur_line hk).sub
            aestronglyMeasurable_centeredSchurLimit_line)
      have h2 : Integrable (fun τ : ℝ =>
          ‖centeredSchurLimit ((τ : ℂ) * Complex.I) -
            centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2) :=
        integrable_norm_sq_sub integrable_norm_sq_centeredSchurLimit
          (integrable_norm_sq_centeredSchurQuotient hν)
          (aestronglyMeasurable_centeredSchurLimit_line.sub
            (aestronglyMeasurable_centeredSchur_line hν))
      have hmono : ∀ τ : ℝ,
          ‖centeredSchurQuotient (criticalShiftSeq k) ((τ : ℂ) * Complex.I) -
            centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2
            ≤ 2 * ‖centeredSchurQuotient (criticalShiftSeq k) ((τ : ℂ) * Complex.I) -
                centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2 +
              2 * ‖centeredSchurLimit ((τ : ℂ) * Complex.I) -
                centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2 := by
        intro τ
        set a := centeredSchurQuotient (criticalShiftSeq k) ((τ : ℂ) * Complex.I)
        set b := centeredSchurLimit ((τ : ℂ) * Complex.I)
        set c := centeredSchurQuotient ν ((τ : ℂ) * Complex.I)
        have htri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
          have : a - c = (a - b) + (b - c) := by ring
          rw [this]
          exact norm_add_le _ _
        nlinarith [norm_nonneg (a - b), norm_nonneg (b - c), norm_nonneg (a - c),
          sq_nonneg (‖a - b‖ - ‖b - c‖)]
      have hint := integrable_norm_sq_centeredSchur_sub hk hν
      have hmain := integral_mono hint ((h1.const_mul 2).add (h2.const_mul 2)) hmono
      simp only [Pi.add_apply] at hmain
      rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul,
        integral_const_mul] at hmain
      exact hmain
    have hfinal : (∫ t : ℝ, ‖centeredMertensVector (criticalShiftSeq k) t -
        centeredMertensVector ν t‖ ^ 2)
        = (2 * Real.pi)⁻¹ * (∫ τ : ℝ,
          ‖centeredSchurQuotient (criticalShiftSeq k) ((τ : ℂ) * Complex.I) -
            centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2) := by
      rw [heq]
      field_simp
    rw [hfinal]
    have hinv : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hbound hinv
  have hlim : Tendsto
      (fun k : ℕ => ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * A k + 2 * criticalHardyEnergy ν)))
      atTop (nhds (ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * criticalHardyEnergy ν)))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have h := ((hA0.const_mul 2).add_const (2 * criticalHardyEnergy ν)).const_mul
      ((2 * Real.pi)⁻¹)
    simpa using h
  refine le_trans (lintegral_enorm_sq_criticalMertensVector_sub_le ν) ?_
  refine le_trans (liminf_le_liminf (Filter.Eventually.of_forall hstep)) ?_
  exact le_of_eq hlim.liminf_eq


/-- **Card `(14)`.**  The critical weighted-Mertens boundary vector belongs to `L²(0,∞)`,
unconditionally. -/
theorem memLp_criticalMertensVector : MemLp criticalMertensVector 2 volume := by
  have hone : (0 : ℝ) < 1 := one_pos
  have hlt : (∫⁻ t : ℝ, ‖criticalMertensVector t - centeredMertensVector 1 t‖ₑ ^ 2) < ⊤ :=
    lt_of_le_of_lt (lintegral_criticalMertens_sub_le hone) ENNReal.ofReal_lt_top
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => criticalMertensVector t - centeredMertensVector 1 t) volume :=
    (measurable_criticalMertensVector.sub
      (measurable_centeredMertensVector 1)).aestronglyMeasurable
  have hsub : MemLp (fun t : ℝ => criticalMertensVector t - centeredMertensVector 1 t) 2 volume :=
    memLp_two_of_lintegral_lt_top hmeas hlt
  have hsum := hsub.add (memLp_centeredMertensVector hone)
  have hae : (fun t : ℝ => (criticalMertensVector t - centeredMertensVector 1 t)
      + centeredMertensVector 1 t) = criticalMertensVector := by
    funext t
    ring
  exact hae ▸ hsum

theorem integrable_norm_sq_criticalMertens_sub {ν : ℝ} (hν : 0 < ν) :
    Integrable (fun t : ℝ => ‖criticalMertensVector t - centeredMertensVector ν t‖ ^ 2) := by
  have hm := memLp_criticalMertensVector.sub (memLp_centeredMertensVector hν)
  exact (memLp_two_iff_integrable_sq_norm
    ((measurable_criticalMertensVector.sub
      (measurable_centeredMertensVector ν)).aestronglyMeasurable)).mp hm

theorem integral_norm_sq_criticalMertens_sub_le {ν : ℝ} (hν : 0 < ν) :
    (∫ t : ℝ, ‖criticalMertensVector t - centeredMertensVector ν t‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹ * (2 * criticalHardyEnergy ν) := by
  have hint := integrable_norm_sq_criticalMertens_sub hν
  have hbound := lintegral_criticalMertens_sub_le hν
  rw [lintegral_enorm_sq_eq_ofReal hint] at hbound
  have hnn : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ * (2 * criticalHardyEnergy ν) := by
    have := criticalHardyEnergy_nonneg ν
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hbound

/-- **Card `(17)`.**  The prelimit centered vectors converge to the critical vector in `L²`. -/
theorem tendsto_integral_norm_sq_criticalMertens_sub :
    Tendsto (fun ν : ℝ => ∫ t : ℝ, ‖criticalMertensVector t - centeredMertensVector ν t‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (?_ : Tendsto (fun ν : ℝ => (2 * Real.pi)⁻¹ * (2 * criticalHardyEnergy ν))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ?_ ?_
  · have h := (tendsto_criticalHardyEnergy.const_mul (2 : ℝ)).const_mul ((2 * Real.pi)⁻¹)
    simpa using h
  · filter_upwards [] with ν
    exact integral_nonneg fun t => by positivity
  · filter_upwards [self_mem_nhdsWithin] with ν hν
    exact integral_norm_sq_criticalMertens_sub_le hν

/-! ### `L²` continuity of the energy -/

theorem norm_l2_sq_eq_integral (K : Lp (α := ℝ) ℂ 2) : ‖K‖ ^ 2 = ∫ x : ℝ, ‖K x‖ ^ 2 := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable K),
    lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable K)]
  norm_num [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  exact integral_nonneg fun x => sq_nonneg _

theorem tendsto_integral_norm_sq_of_L2 {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ i, MemLp (f i) 2 volume) (hg : MemLp g 2 volume)
    (h : Tendsto (fun i => ∫ t : ℝ, ‖f i t - g t‖ ^ 2) l (nhds 0)) :
    Tendsto (fun i => ∫ t : ℝ, ‖f i t‖ ^ 2) l (nhds (∫ t : ℝ, ‖g t‖ ^ 2)) := by
  set A : ι → Lp (α := ℝ) ℂ 2 := fun i => (hf i).toLp (f i) with hAdef
  set B : Lp (α := ℝ) ℂ 2 := hg.toLp g with hBdef
  have hAeq : ∀ i, (∫ t : ℝ, ‖A i t‖ ^ 2) = ∫ t : ℝ, ‖f i t‖ ^ 2 := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [(hf i).coeFn_toLp] with t ht
    rw [ht]
  have hBeq : (∫ t : ℝ, ‖B t‖ ^ 2) = ∫ t : ℝ, ‖g t‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with t ht
    rw [ht]
  have hsub : ∀ i, ‖A i - B‖ ^ 2 = ∫ t : ℝ, ‖f i t - g t‖ ^ 2 := by
    intro i
    rw [norm_l2_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (A i) B, (hf i).coeFn_toLp, hg.coeFn_toLp] with t h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h3]
  have hsq : Tendsto (fun i => ‖A i - B‖ ^ 2) l (nhds 0) := h.congr fun i => (hsub i).symm
  have hnorm : Tendsto (fun i => ‖A i - B‖) l (nhds 0) := by
    have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hcomp
  have hAB : Tendsto (fun i => ‖A i‖) l (nhds ‖B‖) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun i => dist_nonneg) (fun i => ?_) hnorm
    rw [Real.dist_eq]
    exact abs_norm_sub_norm_le _ _
  have hAB2 : Tendsto (fun i => ‖A i‖ ^ 2) l (nhds (‖B‖ ^ 2)) := hAB.pow 2
  have hfinal : Tendsto (fun i => ∫ t : ℝ, ‖A i t‖ ^ 2) l (nhds (∫ t : ℝ, ‖B t‖ ^ 2)) := by
    rw [← norm_l2_sq_eq_integral B]
    exact hAB2.congr fun i => norm_l2_sq_eq_integral (A i)
  rw [hBeq] at hfinal
  exact hfinal.congr hAeq

/-- The centered vector, truncated to the causal parameter range so that `L²` membership is
unconditional in the parameter. -/
def truncCenteredMertens (ν : ℝ) : ℝ → ℂ :=
  if 0 < ν then centeredMertensVector ν else 0

/-- The centered Schur quotient, truncated in the same way. -/
def truncCenteredSchur (ν : ℝ) : ℝ → ℂ :=
  if 0 < ν then (fun τ : ℝ => centeredSchurQuotient ν ((τ : ℂ) * Complex.I)) else 0

theorem truncCenteredMertens_of_pos {ν : ℝ} (hν : 0 < ν) :
    truncCenteredMertens ν = centeredMertensVector ν := by
  rw [truncCenteredMertens, if_pos hν]

theorem truncCenteredSchur_of_pos {ν : ℝ} (hν : 0 < ν) :
    truncCenteredSchur ν = fun τ : ℝ => centeredSchurQuotient ν ((τ : ℂ) * Complex.I) := by
  rw [truncCenteredSchur, if_pos hν]

theorem memLp_truncCenteredMertens (ν : ℝ) : MemLp (truncCenteredMertens ν) 2 volume := by
  rw [truncCenteredMertens]
  split_ifs with h
  · exact memLp_centeredMertensVector h
  · exact MemLp.zero'

theorem memLp_truncCenteredSchur (ν : ℝ) : MemLp (truncCenteredSchur ν) 2 volume := by
  rw [truncCenteredSchur]
  split_ifs with h
  · exact (memLp_two_iff_integrable_sq_norm
      (aestronglyMeasurable_centeredSchur_line h)).mpr
      (integrable_norm_sq_centeredSchurQuotient h)
  · exact MemLp.zero'

theorem memLp_centeredSchurLimit_line :
    MemLp (fun τ : ℝ => centeredSchurLimit ((τ : ℂ) * Complex.I)) 2 volume :=
  (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_centeredSchurLimit_line).mpr
    integrable_norm_sq_centeredSchurLimit

/-- **Card `(15)`.**  The critical boundary energy identity. -/
theorem integral_norm_sq_criticalMertensVector :
    (∫ τ : ℝ, ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2)
      = 2 * Real.pi * ∫ t : ℝ, ‖criticalMertensVector t‖ ^ 2 := by
  have hHardy : Tendsto (fun ν : ℝ => ∫ τ : ℝ,
      ‖centeredSchurQuotient ν ((τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ τ : ℝ, ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2)) := by
    have hbase := tendsto_integral_norm_sq_of_L2 (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      memLp_truncCenteredSchur memLp_centeredSchurLimit_line ?_
    · refine hbase.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ν hν
      rw [truncCenteredSchur_of_pos hν]
    · refine tendsto_boundary_centeredSchur_energy.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ν hν
      rw [truncCenteredSchur_of_pos hν]
  have hTime : Tendsto (fun ν : ℝ => ∫ t : ℝ, ‖centeredMertensVector ν t‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ t : ℝ, ‖criticalMertensVector t‖ ^ 2)) := by
    have hbase := tendsto_integral_norm_sq_of_L2 (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      memLp_truncCenteredMertens memLp_criticalMertensVector ?_
    · refine hbase.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ν hν
      rw [truncCenteredMertens_of_pos hν]
    · refine tendsto_integral_norm_sq_criticalMertens_sub.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ν hν
      rw [truncCenteredMertens_of_pos hν]
      refine integral_congr_ae ?_
      filter_upwards [] with t
      rw [← norm_neg]
      congr 1
      ring
  have hEq : Tendsto (fun ν : ℝ => 2 * Real.pi * ∫ t : ℝ, ‖centeredMertensVector ν t‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ τ : ℝ, ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2)) := by
    refine hHardy.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ν hν
    exact integral_norm_sq_centeredSchur_eq hν
  exact tendsto_nhds_unique hEq (hTime.const_mul _)

end RHTower
