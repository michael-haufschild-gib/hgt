import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelVariance

/-!
# Unconditional PNT decay of complete physical FCRJ carriers

The normalized Chebyshev-theta error tends to zero by the corpus power-log prime number theorem.
The exact theta--Abel provider then gives a uniform response bound on every fixed enlarged physical
band and proves qualitative extinction of complete fixed-width FCRJ carrier energy. This does not
supply the RH-equivalent `exp (-m)` rate; it identifies precisely what ordinary PNT does provide.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Signed normalized Chebyshev-theta discrepancy in logarithmic coordinates. -/
def xiPhysicalPrimeLogNormalizedThetaError (h : ℝ) : ℝ :=
  xiMassThetaLogDiscrepancy h * Real.exp (-h)

/-- Absolute normalized Chebyshev-theta discrepancy. -/
def xiPhysicalPrimeLogAbsNormalizedThetaError (h : ℝ) : ℝ :=
  |xiMassThetaLogDiscrepancy h| / Real.exp h

theorem abs_xiPhysicalPrimeLogNormalizedThetaError
    (h : ℝ) :
    |xiPhysicalPrimeLogNormalizedThetaError h| =
      xiPhysicalPrimeLogAbsNormalizedThetaError h := by
  rw [xiPhysicalPrimeLogNormalizedThetaError,
    xiPhysicalPrimeLogAbsNormalizedThetaError, abs_mul, abs_of_pos (Real.exp_pos _),
    Real.exp_neg]
  rfl

theorem tendsto_xiPhysicalPrimeLogAbsNormalizedThetaError_zero :
    Tendsto xiPhysicalPrimeLogAbsNormalizedThetaError atTop (nhds 0) := by
  obtain ⟨c, C, h₀, hc, hC, hh₀, hE⟩ :=
    exists_norm_xiMassThetaLogDiscrepancy_le
  have hpow : Tendsto (fun h : ℝ => h ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hctop : Tendsto (fun h : ℝ => c * h ^ ((1 : ℝ) / 10)) atTop atTop :=
    hpow.const_mul_atTop hc
  have hdec : Tendsto
      (fun h : ℝ => C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))))
      atTop (nhds 0) := by
    have hneg : Tendsto (fun h : ℝ => -(c * h ^ ((1 : ℝ) / 10))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hctop
    have hexp := Real.tendsto_exp_atBot.comp hneg
    simpa using (tendsto_const_nhds.mul hexp :
      Tendsto (fun h : ℝ => C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))))
        atTop (nhds (C * 0)))
  rw [Metric.tendsto_atTop] at hdec ⊢
  intro ε hε
  obtain ⟨H, hH⟩ := hdec ε hε
  refine ⟨max h₀ H, fun h hh => ?_⟩
  have hh0 : h₀ ≤ h := le_trans (le_max_left _ _) hh
  have hhH : H ≤ h := le_trans (le_max_right _ _) hh
  have hbound : xiPhysicalPrimeLogAbsNormalizedThetaError h ≤
      C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))) := by
    unfold xiPhysicalPrimeLogAbsNormalizedThetaError
    calc
      |xiMassThetaLogDiscrepancy h| / Real.exp h ≤
          (C * Real.exp h * Real.exp (-(c * h ^ ((1 : ℝ) / 10)))) /
            Real.exp h :=
        div_le_div_of_nonneg_right (hE h hh0) (Real.exp_pos _).le
      _ = C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))) := by
        field_simp
  have hdecε : C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))) < ε := by
    have := hH h hhH
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hC,
      abs_of_pos (Real.exp_pos _)] at this
    exact this
  have hnonneg : 0 ≤ xiPhysicalPrimeLogAbsNormalizedThetaError h := by
    unfold xiPhysicalPrimeLogAbsNormalizedThetaError
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hbound hdecε

theorem tendsto_xiPhysicalPrimeLogNormalizedThetaError_zero :
    Tendsto xiPhysicalPrimeLogNormalizedThetaError atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hnorm := tendsto_xiPhysicalPrimeLogAbsNormalizedThetaError_zero
  rw [Metric.tendsto_atTop] at hnorm
  obtain ⟨H, hH⟩ := hnorm ε hε
  refine ⟨H, fun h hh => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_xiPhysicalPrimeLogNormalizedThetaError]
  have hn : 0 ≤ xiPhysicalPrimeLogAbsNormalizedThetaError h := by
    unfold xiPhysicalPrimeLogAbsNormalizedThetaError
    positivity
  simpa [Real.dist_eq, abs_of_nonneg hn] using hH h hh

theorem measurable_xiPhysicalPrimeLogNormalizedThetaError :
    Measurable xiPhysicalPrimeLogNormalizedThetaError := by
  have htheta : Measurable (fun h : ℝ => Chebyshev.theta (Real.exp h)) :=
    Chebyshev.theta_mono.measurable.comp Real.continuous_exp.measurable
  unfold xiPhysicalPrimeLogNormalizedThetaError xiMassThetaLogDiscrepancy
  exact (htheta.sub Real.continuous_exp.measurable).mul
    (Real.continuous_exp.measurable.comp measurable_neg)

theorem xiPhysicalPrimeLogThetaAbelResponse_eq_normalizedThetaError
    (m k u : ℝ) :
    xiPhysicalPrimeLogThetaAbelResponse m k u =
      xiPhysicalPrimeLogNormalizedThetaError (k - u) -
        xiPhysicalPrimeLogNormalizedThetaError (m - u) +
          ∫ h in (m - u)..(k - u), xiPhysicalPrimeLogNormalizedThetaError h := by
  rfl

/-- Uniform normalized PNT error on enlarged physical band bounds complete Abel response,
including both endpoints and interior transport. -/
theorem abs_xiPhysicalPrimeLogThetaAbelResponse_le_of_normalizedThetaError
    {A m c B : ℝ} (hc : 0 ≤ c)
    (hq : ∀ h ∈ Icc (m - A) (m + c),
      |xiPhysicalPrimeLogNormalizedThetaError h| ≤ B)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) A) :
    |xiPhysicalPrimeLogThetaAbelResponse m (m + c) u| ≤ (2 + c) * B := by
  have hlow : m - u ≤ m + c - u := by linarith
  have hku : m + c - u ∈ Icc (m - A) (m + c) := by
    constructor <;> linarith [hu.1, hu.2]
  have hmu : m - u ∈ Icc (m - A) (m + c) := by
    constructor <;> linarith [hu.1, hu.2]
  have hband : ∀ h ∈ Icc (m - u) (m + c - u),
      |xiPhysicalPrimeLogNormalizedThetaError h| ≤ B := by
    intro h hh
    exact hq h ⟨by linarith [hh.1, hu.2], by linarith [hh.2, hu.1]⟩
  have hqInt : IntervalIntegrable xiPhysicalPrimeLogNormalizedThetaError
      volume (m - u) (m + c - u) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlow]
    refine Integrable.mono'
      (integrableOn_const (C := B) measure_Icc_lt_top.ne)
      measurable_xiPhysicalPrimeLogNormalizedThetaError.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with h hh
    exact hband h hh
  have hintAbs :
      |∫ h in (m - u)..(m + c - u), xiPhysicalPrimeLogNormalizedThetaError h| ≤
        c * B := by
    refine (intervalIntegral.abs_integral_le_integral_abs hlow).trans ?_
    calc
      (∫ h in (m - u)..(m + c - u),
          |xiPhysicalPrimeLogNormalizedThetaError h|) ≤
          ∫ _h in (m - u)..(m + c - u), B := by
        apply intervalIntegral.integral_mono_on hlow hqInt.abs intervalIntegrable_const
        intro h hh
        exact hband h hh
      _ = c * B := by
        rw [intervalIntegral.integral_const]
        simp
  rw [xiPhysicalPrimeLogThetaAbelResponse_eq_normalizedThetaError]
  calc
    |xiPhysicalPrimeLogNormalizedThetaError (m + c - u) -
        xiPhysicalPrimeLogNormalizedThetaError (m - u) +
          ∫ h in (m - u)..(m + c - u), xiPhysicalPrimeLogNormalizedThetaError h| ≤
        |xiPhysicalPrimeLogNormalizedThetaError (m + c - u)| +
          |xiPhysicalPrimeLogNormalizedThetaError (m - u)| +
            |∫ h in (m - u)..(m + c - u),
              xiPhysicalPrimeLogNormalizedThetaError h| := by
      calc
        |_ + _| ≤
            |xiPhysicalPrimeLogNormalizedThetaError (m + c - u) -
              xiPhysicalPrimeLogNormalizedThetaError (m - u)| +
              |∫ h in (m - u)..(m + c - u),
                xiPhysicalPrimeLogNormalizedThetaError h| := abs_add_le _ _
        _ ≤ _ := by
          gcongr
          exact abs_sub _ _
    _ ≤ (2 + c) * B := by
      have hk := hq _ hku
      have hm := hq _ hmu
      linarith

/-- Complete physical FCRJ energy bound from one uniform normalized PNT estimate on enlarged
logarithmic band. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_of_normalizedThetaError
    {A : ℝ} (hA : 0 < A) {m c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hq : ∀ h ∈ Icc (m - A) (m + c),
      |xiPhysicalPrimeLogNormalizedThetaError h| ≤ B) :
    xiPhysicalPrimeLogApertureFusionEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c) ≤
      A * ((2 + c) * B) ^ 2 := by
  apply xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_mul_sq_of_response_bound
    hA (by linarith) (mul_nonneg (by linarith) hB)
  intro u hu
  exact abs_xiPhysicalPrimeLogThetaAbelResponse_le_of_normalizedThetaError hc hq hu

/-- Fixed-width complete FCRJ carrier at logarithmic height `m`. -/
def xiPhysicalPrimeLogPNTCarrierEnergy (A c m : ℝ) : ℝ :=
  xiPhysicalPrimeLogApertureFusionEnergy
    (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)

/-- Corpus PNT forces every fixed-width complete physical carrier to vanish qualitatively. -/
theorem tendsto_xiPhysicalPrimeLogPNTCarrierEnergy_zero
    {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c) :
    Tendsto (xiPhysicalPrimeLogPNTCarrierEnergy A c) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let D := A * (2 + c) ^ 2
  have htwo : 0 < 2 + c := by linarith
  have hD : 0 < D := mul_pos hA (sq_pos_of_pos htwo)
  let η := Real.sqrt (ε / D) / 2
  have hη : 0 < η := div_pos (Real.sqrt_pos.2 (div_pos hε hD)) (by norm_num)
  have hbudget : A * ((2 + c) * η) ^ 2 < ε := by
    have hsqrt : (Real.sqrt (ε / D)) ^ 2 = ε / D :=
      Real.sq_sqrt (div_nonneg hε.le hD.le)
    have heq : A * ((2 + c) * η) ^ 2 = ε / 4 := by
      dsimp only [η]
      rw [show ((2 + c) * (Real.sqrt (ε / D) / 2)) ^ 2 =
          (2 + c) ^ 2 * (Real.sqrt (ε / D)) ^ 2 / 4 by ring,
        hsqrt]
      dsimp only [D]
      field_simp [hA.ne', htwo.ne']
    rw [heq]
    linarith
  have hqLimit := tendsto_xiPhysicalPrimeLogNormalizedThetaError_zero
  rw [Metric.tendsto_atTop] at hqLimit
  obtain ⟨H, hH⟩ := hqLimit η hη
  refine ⟨H + A, fun m hm => ?_⟩
  have hq : ∀ h ∈ Icc (m - A) (m + c),
      |xiPhysicalPrimeLogNormalizedThetaError h| ≤ η := by
    intro h hh
    have hlarge : H ≤ h := by linarith [hh.1]
    have hsmall := hH h hlarge
    rw [Real.dist_eq, sub_zero] at hsmall
    exact hsmall.le
  have hupper :=
    xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_of_normalizedThetaError
      hA hc hη.le hq
  have hnonneg := xiPhysicalPrimeLogApertureFusionEnergy_nonneg
    (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) hA m (m + c)
  rw [Real.dist_eq, sub_zero]
  change |xiPhysicalPrimeLogApertureFusionEnergy
      (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)| < ε
  rw [abs_of_nonneg hnonneg]
  exact hupper.trans_lt hbudget

end

end RHTower
