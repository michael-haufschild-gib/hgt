import GaloisForLFunctions.RHTower.WeilWorkQuantizationFrequencySum
import GaloisForLFunctions.RHTower.WeilWorkQuantizationPowerRigidity

/-!
# Complete resonant equations for the canonical spectral phase

The actual reflected far tail fixes the normalization at m = 1. Any
exponentially summable frequency representation of the actual phase must
therefore have a nonzero resonant coefficient sum that is constant at every
positive integer. This is a necessary representation constraint, not a
claim that Weil positivity supplies such a representation or quantization.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist RightEdgeKernel IntegerMassRigidity HamburgerStability
  PhaseLockRigidity GaloisForLFunctions.HTGeometry

/-- The actual reflected far tail retains the source normalization. -/
theorem tendsto_quantization_far_reflected {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      quantizationReflectedTraceF hW (2 * t) *
        pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (2 * betaG (quantizationCompletion hW))) := by
  obtain ⟨CB, hCB, hpoly⟩ := exists_quantization_trace_pair_bound hW
  let Ψ : ℝ → ℂ := fun t => quantizationReflectedTraceF hW (2 * t)
  have hmid := tendsto_eps_mul_setIntegral_Ioo (h := Ψ) (B := 2 * CB) (m := m) (by
    intro t ht
    have hb := (hpoly t).2
    dsimp [Ψ]
    exact hb.trans (by rw [pow_one, abs_of_neg ht.2]; nlinarith [ht.1])) hm
  have hlim := ((tendsto_quantization_lower_reflected_radial hW hm).const_mul
    (((2 * Real.pi : ℝ) : ℂ))).sub hmid
  have hv : (((2 * Real.pi : ℝ) : ℂ)) *
      (betaG (quantizationCompletion hW) / (Real.pi : ℂ)) - 0 =
      2 * betaG (quantizationCompletion hW) := by
    push_cast
    field_simp; ring
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
  have hτ : 0 < τ.re := by simpa [τ] using hε
  have hint : Integrable fun t => Ψ t * pairKernel (2 * t) τ :=
    integrable_defectLaplace_integrand
      ((measurable_quantizationReflectedTraceF hW).comp
        (measurable_const.mul measurable_id)).aestronglyMeasurable
      (fun t => (hpoly t).2) hτ
  have hind : (fun t => (Iio (0 : ℝ)).indicator Ψ t * pairKernel (2 * t) τ) =
      (Iio (0 : ℝ)).indicator (fun t => Ψ t * pairKernel (2 * t) τ) := by
    funext t
    by_cases ht : t ∈ Iio (0 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
    ext t
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro ht
      by_cases h1 : t ≤ -1
      · exact Or.inl h1
      · exact Or.inr ⟨by linarith, ht⟩
    · rintro (ht | ht)
      · linarith
      · exact ht.2
  have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
    Set.disjoint_left.mpr fun t h1 h2 => by
      simp only [mem_Iic] at h1
      simp only [mem_Ioo] at h2
      linarith [h2.1]
  change (((2 * Real.pi : ℝ) : ℂ)) * ((ε : ℂ) * defectLaplace
    ((Iio (0 : ℝ)).indicator Ψ) τ) - (ε : ℂ) *
      (∫ t in Ioo (-1 : ℝ) 0, Ψ t * pairKernel (2 * t) τ) = _
  unfold defectLaplace
  rw [hind, integral_indicator measurableSet_Iio, hsplit,
    setIntegral_union hdisj measurableSet_Ioo hint.integrableOn hint.integrableOn]
  push_cast
  field_simp; ring

/-- A representation of the actual phase satisfies the complete resonant radial system. -/
theorem tendsto_quantization_phase_resonance {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I))
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => quantizationOriginPhase hW *
      (∑' j, p j * quantizationFrequencyResidue lam (ω j) m) *
        quantizationMainRadial m ε) (𝓝[>] 0)
      (𝓝 (4 * betaG (quantizationCompletion hW))) := by
  let P : ℝ → ℂ := fun y => ∑' j, p j *
    linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)
  have hfar : Tendsto (fun ε : ℝ => quantizationOriginPhase hW * ((ε : ℂ) *
      ∫ y in Iic (-2 : ℝ), P y *
        (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I))))
      (𝓝[>] 0) (𝓝 (4 * betaG (quantizationCompletion hW))) := by
    have h := (tendsto_quantization_far_reflected hW hm).const_mul (2 : ℂ)
    rw [show (2 : ℂ) * (2 * betaG (quantizationCompletion hW)) =
      4 * betaG (quantizationCompletion hW) by ring] at h
    apply h.congr
    intro ε
    let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
    have heq : (∫ t in Iic (-1 : ℝ), quantizationReflectedTraceF hW (2 * t) *
        pairKernel (2 * t) τ) = quantizationOriginPhase hW *
        ∫ t in Iic (-1 : ℝ), P (2 * t) *
          (quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_quantizationReflectedTraceF_cumulative_phase hW),
        ae_restrict_mem measurableSet_Iic] with t ht ht1
      have ht0 : t < 0 := lt_of_le_of_lt ht1 (by norm_num)
      rw [ht ht0, hphase (-t) (by linarith)]
      have hP : P (2 * t) = ∑' j, p j * cexp (((ω j * (-t) : ℝ) : ℂ) * I) := by
        apply tsum_congr
        intro j
        congr 1
        unfold linTwist
        congr 1
        push_cast
        ring
      rw [hP]
      ring
    have hchange := setIntegral_Iic_comp_two_mul
      (fun y => P y * (quantizationTraceF hW y * pairKernel y τ)) (-1)
    norm_num only [mul_neg, mul_one] at hchange
    rw [heq, hchange]
    ring
  have hd := (tendsto_quantization_frequency_sum_resonance hW hp hm).const_mul
    (quantizationOriginPhase hW)
  have h := hfar.sub hd
  simpa only [P, mul_zero, sub_zero, mul_sub, sub_sub_cancel, mul_assoc] using h

/-- The actual phase forces every resonant coefficient sum to equal its nonzero value at one. -/
theorem quantization_phase_resonance_constant {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I)) :
    (∑' j, p j * quantizationFrequencyResidue lam (ω j) 1) ≠ 0 ∧
      ∀ m : ℕ, 1 ≤ m →
        (∑' j, p j * quantizationFrequencyResidue lam (ω j) m) =
          ∑' j, p j * quantizationFrequencyResidue lam (ω j) 1 := by
  let B : ℕ → ℂ := fun m => ∑' j, p j * quantizationFrequencyResidue lam (ω j) m
  let κ := quantizationOriginPhase hW
  let D : ℂ := 4 * betaG (quantizationCompletion hW)
  have hβ : betaG (quantizationCompletion hW) ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero (differentiableOn_weilContinuation hW)
      (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW)
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)) two_ne_zero
  have hD : D ≠ 0 := mul_ne_zero (by norm_num) hβ
  have hκ : κ ≠ 0 := by
    intro he
    have hn := norm_quantizationOriginPhase hW
    change ‖κ‖ = 1 at hn
    rw [he, norm_zero] at hn
    norm_num at hn
  have hr (m : ℕ) (hm : 1 ≤ m) : Tendsto
      (fun ε : ℝ => κ * B m * quantizationMainRadial m ε) (𝓝[>] 0) (𝓝 D) :=
    tendsto_quantization_phase_resonance hW hp hphase hm
  have hB1 : B 1 ≠ 0 := by
    intro he
    have hz : Tendsto (fun ε : ℝ => κ * B 1 * quantizationMainRadial 1 ε)
        (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
      simp only [he, mul_zero, zero_mul]
      exact tendsto_const_nhds
    exact hD (tendsto_nhds_unique (hr 1 le_rfl) hz)
  have hden : κ * B 1 ≠ 0 := mul_ne_zero hκ hB1
  let L : ℂ := D / (κ * B 1)
  have hL : L ≠ 0 := div_ne_zero hD hden
  have hmain : Tendsto (quantizationMainRadial 1) (𝓝[>] 0) (𝓝 L) := by
    have h := (hr 1 le_rfl).div_const (κ * B 1)
    have he : ∀ ε : ℝ,
        (κ * B 1 * quantizationMainRadial 1 ε) / (κ * B 1) =
          quantizationMainRadial 1 ε := by
      intro ε
      field_simp
    simpa only [he] using h
  refine ⟨hB1, fun m hm => ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hscale : Tendsto (fun ε : ℝ => ε / m) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun ε : ℝ => ε / m) (𝓝 0) (𝓝 (0 / m)) :=
        (continuous_id.div_const _).tendsto 0
      rw [zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun ε hε => div_pos hε hmpos
  have hscaled : Tendsto (quantizationMainRadial m) (𝓝[>] 0) (𝓝 L) := by
    exact (hmain.comp hscale).congr fun ε => (quantizationMainRadial_scale hm ε).symm
  have he := tendsto_nhds_unique (hscaled.const_mul (κ * B m)) (hr m hm)
  have he1 : κ * B 1 * L = D := by dsimp [L]; field_simp
  exact mul_left_cancel₀ hκ (mul_right_cancel₀ hL (he.trans he1.symm))

end RHTower.WeilSpectral
