import GaloisForLFunctions.RHTower.HighExponentShellClockMeasure

/-!
# The four-unit incidence energy of a high-exponent shell

The shell clock converges weakly to `Exp(1)` and its second moment is uniformly bounded near the
pole, so the Gini mean difference of two independent shell clocks converges to the Gini mean
difference of the universal Laplace gap law, which is one:

* `RHTower.integral_shellClock_sq` — the clock second moment is the rescaled log-moment;
* `RHTower.tendsto_integral_abs_shellGapProbabilityMeasure` — `ε·E|H - H'| → 1`;
* `RHTower.tendsto_shellRelativeClockEnergy` — the rank-one incidence energy of every
  high-exponent shell carries exactly four asymptotic units.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter
open scoped Topology

/-! ## Summability of the logarithmic moment series -/

theorem summable_shellMass_logPow (m k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => shellMass m σ n * (Real.log n) ^ k) := by
  have hmaj : Summable (fun n : ℕ => |Real.log n| ^ k * (n : ℝ) ^ (-σ)) :=
    summable_abs_log_natCast_pow_mul_rpow_neg k σ hσ
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact mul_nonneg (shellMass_nonneg m σ n) (pow_nonneg (Real.log_natCast_nonneg n) k)
  · have hlog : (Real.log n) ^ k = |Real.log n| ^ k := by
      rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
    have hInd : (shellIndicator m n : ℝ) ≤ 1 := by
      rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h] <;> norm_num
    have hpow : (0 : ℝ) ≤ (((n : ℝ)) ^ σ)⁻¹ := by positivity
    have habs : (0 : ℝ) ≤ |Real.log n| ^ k := by positivity
    rw [shellMass, hlog, Real.rpow_neg (Nat.cast_nonneg n)]
    calc (shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹ * |Real.log n| ^ k
        ≤ 1 * (((n : ℝ)) ^ σ)⁻¹ * |Real.log n| ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hInd hpow) habs
      _ = |Real.log n| ^ k * (((n : ℝ)) ^ σ)⁻¹ := by ring

theorem summable_shellProbability_logPow (m k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => shellProbability m σ n * (Real.log n) ^ k) := by
  have h := (summable_shellMass_logPow m k hσ).div_const (shellMellin m σ)
  refine h.congr fun n => ?_
  rw [shellProbability]
  ring

theorem tsum_shellProbability_logPow (m k : ℕ) (σ : ℝ) :
    ∑' n : ℕ, shellProbability m σ n * (Real.log n) ^ k = shellLogMoment m k σ := by
  rw [shellLogMoment, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [shellProbability, shellMass]
  ring

/-! ## Second moments of the shell clock -/

private theorem pmf_toMeasure_eq_sum_smul_dirac' {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable X] (p : PMF X) :
    p.toMeasure = Measure.sum (fun x => (p x) • Measure.dirac x) := by
  ext s hs
  rw [p.toMeasure_apply hs, Measure.sum_apply _ hs]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ s <;> simp [Measure.smul_apply, hs, hx]

theorem integrable_shellClock_sq {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun y : ℝ => y ^ 2) (shellClockProbabilityMeasure m σ : Measure ℝ) := by
  have hsum : Summable (fun n : ℕ =>
      (shellCriticalPMF m σ n).toReal * ‖shellClock σ n ^ 2‖) := by
    have h := (summable_shellProbability_logPow m 2 hσ).mul_left ((σ - 1) ^ 2)
    refine h.congr fun n => ?_
    rw [shellCriticalPMF_toReal hm hσ, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), shellClock]
    ring
  have hsource : Integrable (fun n : ℕ => shellClock σ n ^ 2)
      (shellCriticalPMF m σ).toMeasure := by
    rw [pmf_toMeasure_eq_sum_smul_dirac']
    exact integrable_sum_dirac (fun n => (shellCriticalPMF m σ).apply_ne_top n) hsum
  unfold shellClockProbabilityMeasure shellIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (shellClock σ) (shellCriticalPMF m σ).toMeasure)).2 hsource

theorem integral_shellClock_sq {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    (∫ y : ℝ, y ^ 2 ∂(shellClockProbabilityMeasure m σ : Measure ℝ))
      = (σ - 1) ^ 2 * shellLogMoment m 2 σ := by
  have hsum : Summable (fun n : ℕ =>
      (shellCriticalPMF m σ n).toReal * ‖shellClock σ n ^ 2‖) := by
    have h := (summable_shellProbability_logPow m 2 hσ).mul_left ((σ - 1) ^ 2)
    refine h.congr fun n => ?_
    rw [shellCriticalPMF_toReal hm hσ, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), shellClock]
    ring
  have hsource : Integrable (fun n : ℕ => shellClock σ n ^ 2)
      (shellCriticalPMF m σ).toMeasure := by
    rw [pmf_toMeasure_eq_sum_smul_dirac']
    exact integrable_sum_dirac (fun n => (shellCriticalPMF m σ).apply_ne_top n) hsum
  unfold shellClockProbabilityMeasure shellIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (shellClock σ) (shellCriticalPMF m σ).toMeasure)
    (continuous_pow 2).aestronglyMeasurable]
  rw [PMF.integral_eq_tsum _ _ hsource]
  simp only [smul_eq_mul]
  simp_rw [shellCriticalPMF_toReal hm hσ]
  rw [← tsum_shellProbability_logPow m 2 σ, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [shellClock]
  ring

/-! ## Second moments of the shell gap -/

private theorem integrable_shellGapPair_sq {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2)
      (((shellClockProbabilityMeasure m σ : Measure ℝ)).prod
        ((shellClockProbabilityMeasure m σ : Measure ℝ))) := by
  set μ := (shellClockProbabilityMeasure m σ : Measure ℝ) with hμ
  have hsquare : Integrable (fun x : ℝ => x ^ 2) μ := integrable_shellClock_sq hm hσ
  have hfst : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2) (μ.prod μ) :=
    (hsquare.comp_fst μ).const_mul 2
  have hsnd : Integrable (fun p : ℝ × ℝ => 2 * p.2 ^ 2) (μ.prod μ) :=
    (hsquare.comp_snd μ).const_mul 2
  have hdom : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 2 * p.2 ^ 2) (μ.prod μ) :=
    hfst.add hsnd
  refine hdom.mono' (by fun_prop) ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (p.1 + p.2)]

theorem integrable_shellGap_sq {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun y : ℝ => y ^ 2) (shellGapProbabilityMeasure m σ : Measure ℝ) := by
  unfold shellGapProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.toMeasure_prod]
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    (continuous_fst.sub continuous_snd).aemeasurable).2 (integrable_shellGapPair_sq hm hσ)

theorem integral_shellGap_sq_le {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    (∫ y : ℝ, y ^ 2 ∂(shellGapProbabilityMeasure m σ : Measure ℝ))
      ≤ 4 * ((σ - 1) ^ 2 * shellLogMoment m 2 σ) := by
  set μ := (shellClockProbabilityMeasure m σ : Measure ℝ) with hμ
  have hsquare : Integrable (fun x : ℝ => x ^ 2) μ := integrable_shellClock_sq hm hσ
  have hfst : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2) (μ.prod μ) :=
    (hsquare.comp_fst μ).const_mul 2
  have hsnd : Integrable (fun p : ℝ × ℝ => 2 * p.2 ^ 2) (μ.prod μ) :=
    (hsquare.comp_snd μ).const_mul 2
  have hdom : Integrable (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 2 * p.2 ^ 2) (μ.prod μ) :=
    hfst.add hsnd
  have hsource := integrable_shellGapPair_sq hm hσ
  have hmono : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ))
      ≤ ∫ p : ℝ × ℝ, (2 * p.1 ^ 2 + 2 * p.2 ^ 2) ∂(μ.prod μ) := by
    refine integral_mono hsource hdom fun p => ?_
    nlinarith [sq_nonneg (p.1 + p.2)]
  have hsplit : (∫ p : ℝ × ℝ, (2 * p.1 ^ 2 + 2 * p.2 ^ 2) ∂(μ.prod μ))
      = 4 * ∫ x : ℝ, x ^ 2 ∂μ := by
    have hifst : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂(μ.prod μ)) = ∫ x : ℝ, x ^ 2 ∂μ := by
      simpa [μ] using (integral_fun_fst (μ := μ) (ν := μ) (fun x : ℝ => x ^ 2))
    have hisnd : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂(μ.prod μ)) = ∫ x : ℝ, x ^ 2 ∂μ := by
      simpa [μ] using (integral_fun_snd (μ := μ) (ν := μ) (fun x : ℝ => x ^ 2))
    rw [integral_add hfst hsnd, integral_const_mul, integral_const_mul, hifst, hisnd]
    ring
  have hgap : (∫ y : ℝ, y ^ 2 ∂(shellGapProbabilityMeasure m σ : Measure ℝ))
      = ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ) := by
    unfold shellGapProbabilityMeasure ProbabilityMeasure.map
    simp only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.toMeasure_prod]
    rw [integral_map (continuous_fst.sub continuous_snd).aemeasurable
      (continuous_pow 2).aestronglyMeasurable]
  rw [hgap, ← integral_shellClock_sq hm hσ]
  calc (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ))
      ≤ ∫ p : ℝ × ℝ, (2 * p.1 ^ 2 + 2 * p.2 ^ 2) ∂(μ.prod μ) := hmono
    _ = 4 * ∫ x : ℝ, x ^ 2 ∂μ := hsplit

/-! ## The four-unit incidence energy -/

/-- **Gini mean difference of the shell clock.**  `ε·E|H - H'| → 1`. -/
theorem tendsto_integral_abs_shellGapProbabilityMeasure {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (fun σ : ℝ => ∫ x : ℝ, |x| ∂(shellGapProbabilityMeasure m σ : Measure ℝ))
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have hmomentEventually : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      (σ - 1) ^ 2 * shellLogMoment m 2 σ ≤ 3 := by
    have hlt := (tendsto_order.1 (tendsto_shellLogMoment_two hm)).2 3 (by norm_num)
    exact hlt.mono fun σ h => h.le
  have hsqEventually : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      Integrable (fun x : ℝ => x ^ 2) (shellGapProbabilityMeasure m σ : Measure ℝ) ∧
        (∫ x : ℝ, x ^ 2 ∂(shellGapProbabilityMeasure m σ : Measure ℝ)) ≤ 12 := by
    filter_upwards [self_mem_nhdsWithin, hmomentEventually] with σ hσmem hmoment
    have hσ : 1 < σ := Set.mem_Ioi.mp hσmem
    refine ⟨integrable_shellGap_sq (by omega) hσ, ?_⟩
    exact (integral_shellGap_sq_le (by omega) hσ).trans (by nlinarith)
  have htendsto := tendsto_integral_abs_of_weak_of_uniform_sq (C := (12 : ℝ))
    (by norm_num) (tendsto_shellGapProbabilityMeasure hm) hsqEventually
    integrable_sq_mobiusCriticalExponentialGapProbabilityMeasure
    (by rw [integral_sq_mobiusCriticalExponentialGapProbabilityMeasure]; norm_num)
  rwa [integral_abs_mobiusCriticalExponentialGapProbabilityMeasure] at htendsto

/-- Rank-one incidence energy of the shell packet after the intrinsic clock rescaling. -/
def shellRelativeClockEnergy (m : ℕ) (σ : ℝ) : ℝ :=
  4 * ∫ x : ℝ, |x| ∂(shellGapProbabilityMeasure m σ : Measure ℝ)

/-- **Four units.**  The divisor-incidence clock of every high-exponent shell carries exactly
four asymptotic energy units, on pairwise disjoint arithmetic supports. -/
theorem tendsto_shellRelativeClockEnergy {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (shellRelativeClockEnergy m) (𝓝[>] (1 : ℝ)) (𝓝 4) := by
  have h := (tendsto_integral_abs_shellGapProbabilityMeasure hm).const_mul (4 : ℝ)
  rw [mul_one] at h
  exact h

end RHTower
