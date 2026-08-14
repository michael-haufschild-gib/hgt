import GaloisForLFunctions.RHTower.SoninPacketSupportCutoffs

/-!
# Wavepackets on an arbitrary annulus amplitude

The wavepacket construction of the Sonin coupling uses nothing about the amplitude beyond five
facts: it is even, measurable, bounded, supported strictly inside one annulus, and of positive
total mass.  In particular it need not be smooth or even continuous.

This module packages those five facts as `AnnulusAmplitude` and rebuilds the packet, its `L²`
class, its uniform bound, and its physical cutoffs at that level of generality.  A discontinuous
indicator amplitude is then a legitimate carrier for the whole coupling architecture.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology InnerProductSpace

/-- An amplitude carried by the strict annulus `b < |x| < c`: even, measurable, bounded,
nonnegative, supported in the annulus, and of positive mass. -/
structure AnnulusAmplitude (b c : ℝ) where
  /-- The amplitude itself. -/
  toFun : ℝ → ℝ
  /-- It is measurable. -/
  measurable' : Measurable toFun
  /-- It is even. -/
  even' : ∀ x, toFun (-x) = toFun x
  /-- It is nonnegative. -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- A uniform bound. -/
  bound : ℝ
  /-- The bound bounds. -/
  le_bound' : ∀ x, toFun x ≤ bound
  /-- The support lies strictly inside the annulus. -/
  support' : ∀ x, toFun x ≠ 0 → b < |x| ∧ |x| < c
  /-- The amplitude has positive mass. -/
  mass_pos' : 0 < ∫ x, toFun x

namespace AnnulusAmplitude

variable {b c : ℝ} (A : AnnulusAmplitude b c)

theorem eq_zero_of_abs_le {x : ℝ} (hx : |x| ≤ b) : A.toFun x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (A.support' x hne).1)

theorem eq_zero_of_le_abs {x : ℝ} (hx : c ≤ |x|) : A.toFun x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (A.support' x hne).2)

theorem support_subset_closedBall : Function.support A.toFun ⊆ Metric.closedBall (0 : ℝ) c := by
  intro x hx
  have h := (A.support' x hx).2
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact le_of_lt h

theorem hasCompactSupport : HasCompactSupport A.toFun :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 c)
    A.support_subset_closedBall

theorem bound_nonneg : 0 ≤ A.bound := le_trans (A.nonneg' 0) (A.le_bound' 0)

theorem abs_eq (x : ℝ) : |A.toFun x| = A.toFun x := abs_of_nonneg (A.nonneg' x)

/-- The bounded, compactly supported amplitude is integrable against any bounded weight. -/
theorem integrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ x, |f x| ≤ K) (hvan : ∀ x, A.toFun x = 0 → f x = 0) : Integrable f := by
  have hKnn : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hfin : (volume (Metric.closedBall (0 : ℝ) c)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hind : Integrable ((Metric.closedBall (0 : ℝ) c).indicator (fun _ : ℝ => K)) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr (integrableOn_const hfin)
  refine Integrable.mono'
    (g := fun x => (Metric.closedBall (0 : ℝ) c).indicator (fun _ => K) x) hind
    hf.aestronglyMeasurable ?_
  · filter_upwards with x
    by_cases hx : x ∈ Metric.closedBall (0 : ℝ) c
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
      exact hK x
    · have hzero : A.toFun x = 0 := by
        by_contra hne
        exact hx (A.support_subset_closedBall hne)
      rw [Set.indicator_of_notMem hx, hvan x hzero]
      simp

/-- The complex-valued version of the domination bound. -/
theorem integrable_complex_of_bound {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) {K : ℝ}
    (hK : ∀ x, ‖f x‖ ≤ K) (hvan : ∀ x, A.toFun x = 0 → f x = 0) : Integrable f := by
  have hKnn : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hfin : (volume (Metric.closedBall (0 : ℝ) c)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hind : Integrable ((Metric.closedBall (0 : ℝ) c).indicator (fun _ : ℝ => K)) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr (integrableOn_const hfin)
  refine Integrable.mono'
    (g := fun x => (Metric.closedBall (0 : ℝ) c).indicator (fun _ => K) x) hind hf ?_
  filter_upwards with x
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ) c
  · rw [Set.indicator_of_mem hx]
    exact hK x
  · have hzero : A.toFun x = 0 := by
      by_contra hne
      exact hx (A.support_subset_closedBall hne)
    rw [Set.indicator_of_notMem hx, hvan x hzero]
    simp

theorem integrable : Integrable A.toFun :=
  A.integrable_of_bound A.measurable' (fun x => by rw [A.abs_eq]; exact A.le_bound' x)
    (fun _ h => h)

theorem integrable_sq : Integrable (fun x => A.toFun x ^ 2) := by
  refine A.integrable_of_bound (A.measurable'.pow_const 2) (K := A.bound ^ 2) (fun x => ?_)
    (fun x hx => by rw [hx]; ring)
  have h1 : 0 ≤ A.toFun x := A.nonneg' x
  have h2 : A.toFun x ≤ A.bound := A.le_bound' x
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ A.toFun x ^ 2)]
  nlinarith [A.bound_nonneg]

theorem integrable_mul {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Integrable (fun x => A.toFun x * f x) := by
  refine A.integrable_of_bound (A.measurable'.mul hf) (K := A.bound * K) (fun x => ?_)
    (fun x hx => by rw [hx]; ring)
  have hKnn : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  rw [abs_mul, A.abs_eq]
  exact mul_le_mul (A.le_bound' x) (hK x) (abs_nonneg _) A.bound_nonneg

/-- The complexified amplitude is square integrable. -/
theorem memLp_ofReal : MemLp (fun x : ℝ => (A.toFun x : ℂ)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (A.toFun x : ℂ)) (volume : Measure ℝ) :=
    (Complex.continuous_ofReal.measurable.comp A.measurable').aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  refine A.integrable_sq.congr (Filter.Eventually.of_forall fun x => ?_)
  show A.toFun x ^ 2 = ‖((A.toFun x : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The amplitude as an element of `L²(ℝ)`. -/
def ampL2 : SoninL2 := A.memLp_ofReal.toLp _

theorem ampL2_coeFn : (A.ampL2 : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (A.toFun x : ℂ) :=
  MemLp.coeFn_toLp A.memLp_ofReal

/-! ### The frequency-locked packet -/

/-- The shell average of the modulating cosine against the amplitude. -/
def ampPacketMean (κ : ℝ) : ℝ :=
  (∫ x : ℝ, A.toFun x * Real.cos (κ * x)) / ∫ x : ℝ, A.toFun x

/-- The frequency-locked packet of an annulus amplitude. -/
def ampPacket (κ : ℝ) : ℝ → ℝ := fun x =>
  A.toFun x * (Real.cos (κ * x) - A.ampPacketMean κ)

theorem ampPacket_even (κ x : ℝ) : A.ampPacket κ (-x) = A.ampPacket κ x := by
  simp only [ampPacket, A.even' x, mul_neg, Real.cos_neg]

theorem measurable_ampPacket (κ : ℝ) : Measurable (A.ampPacket κ) :=
  A.measurable'.mul ((Real.measurable_cos.comp (measurable_const_mul κ)).sub measurable_const)

theorem ampPacket_eq_zero_of_amp_eq_zero {κ x : ℝ} (hx : A.toFun x = 0) :
    A.ampPacket κ x = 0 := by
  simp [ampPacket, hx]

theorem ampPacket_eq_zero_of_abs_le {κ x : ℝ} (hx : |x| ≤ b) : A.ampPacket κ x = 0 :=
  A.ampPacket_eq_zero_of_amp_eq_zero (A.eq_zero_of_abs_le hx)

theorem ampPacket_eq_zero_of_le_abs {κ x : ℝ} (hx : c ≤ |x|) : A.ampPacket κ x = 0 :=
  A.ampPacket_eq_zero_of_amp_eq_zero (A.eq_zero_of_le_abs hx)

theorem abs_ampPacketMean_le_one (κ : ℝ) : |A.ampPacketMean κ| ≤ 1 := by
  have hmass := A.mass_pos'
  have hnum : |∫ x : ℝ, A.toFun x * Real.cos (κ * x)| ≤ ∫ x : ℝ, A.toFun x := by
    have hle : ∀ x : ℝ, ‖A.toFun x * Real.cos (κ * x)‖ ≤ A.toFun x := by
      intro x
      rw [Real.norm_eq_abs, abs_mul, A.abs_eq]
      calc A.toFun x * |Real.cos (κ * x)| ≤ A.toFun x * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (A.nonneg' x)
        _ = A.toFun x := mul_one _
    have := norm_integral_le_of_norm_le A.integrable (Filter.Eventually.of_forall hle)
    rwa [Real.norm_eq_abs] at this
  rw [ampPacketMean, abs_div, abs_of_pos hmass, div_le_one hmass]
  exact hnum

theorem abs_ampPacket_le (κ x : ℝ) : |A.ampPacket κ x| ≤ 2 * A.toFun x := by
  have hμ := A.abs_ampPacketMean_le_one κ
  rw [ampPacket, abs_mul, A.abs_eq]
  have hfac : |Real.cos (κ * x) - A.ampPacketMean κ| ≤ 2 := by
    calc |Real.cos (κ * x) - A.ampPacketMean κ|
        ≤ |Real.cos (κ * x)| + |A.ampPacketMean κ| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) hμ
      _ = 2 := by norm_num
  calc A.toFun x * |Real.cos (κ * x) - A.ampPacketMean κ| ≤ A.toFun x * 2 :=
        mul_le_mul_of_nonneg_left hfac (A.nonneg' x)
    _ = 2 * A.toFun x := mul_comm _ _

theorem integrable_ampPacket (κ : ℝ) : Integrable (A.ampPacket κ) := by
  refine A.integrable_of_bound (A.measurable_ampPacket κ) (K := 2 * A.bound) (fun x => ?_)
    (fun x hx => A.ampPacket_eq_zero_of_amp_eq_zero hx)
  calc |A.ampPacket κ x| ≤ 2 * A.toFun x := A.abs_ampPacket_le κ x
    _ ≤ 2 * A.bound := by
        have := A.le_bound' x
        linarith

theorem abs_ampPacket_le_bound (κ x : ℝ) : |A.ampPacket κ x| ≤ 2 * A.bound := by
  have h1 := A.abs_ampPacket_le κ x
  have h2 := A.le_bound' x
  linarith

theorem integrable_ampPacket_sq (κ : ℝ) : Integrable (fun x => A.ampPacket κ x ^ 2) := by
  refine A.integrable_of_bound ((A.measurable_ampPacket κ).pow_const 2)
    (K := (2 * A.bound) ^ 2) (fun x => ?_)
    (fun x hx => by rw [A.ampPacket_eq_zero_of_amp_eq_zero hx]; ring)
  have h1 := A.abs_ampPacket_le_bound κ x
  have h2 : (0 : ℝ) ≤ |A.ampPacket κ x| := abs_nonneg _
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  nlinarith

/-- The packet is square integrable. -/
theorem memLp_ampPacket (κ : ℝ) :
    MemLp (fun x : ℝ => (A.ampPacket κ x : ℂ)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (A.ampPacket κ x : ℂ)) (volume : Measure ℝ) :=
    (Complex.continuous_ofReal.measurable.comp (A.measurable_ampPacket κ)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  refine (A.integrable_ampPacket_sq κ).congr (Filter.Eventually.of_forall fun x => ?_)
  show A.ampPacket κ x ^ 2 = ‖((A.ampPacket κ x : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The packet as a vector of the even Sonin carrier -/

/-- The packet as an element of `L²(ℝ)`. -/
def ampPacketL2 (κ : ℝ) : SoninL2 := (A.memLp_ampPacket κ).toLp _

theorem ampPacketL2_coeFn (κ : ℝ) :
    (A.ampPacketL2 κ : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (A.ampPacket κ x : ℂ) :=
  MemLp.coeFn_toLp (A.memLp_ampPacket κ)

theorem ampPacketL2_mem_evenSubspace (κ : ℝ) : A.ampPacketL2 κ ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hrefl := l2Reflection_ae (A.ampPacketL2 κ)
  have hcoe := A.ampPacketL2_coeFn κ
  have hcoeNeg := hcoe.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hrefl, hcoe, hcoeNeg] with x hx hval hvalNeg
  rw [hx]
  have hvalNeg' : (A.ampPacketL2 κ : ℝ → ℂ) (-x) = (A.ampPacket κ (-x) : ℂ) := by
    simpa [Function.comp_apply] using hvalNeg
  rw [hvalNeg', hval, A.ampPacket_even κ x]

/-- The packet as a vector of the even Sonin carrier. -/
def ampPacketEven (κ : ℝ) : evenSubspace :=
  ⟨A.ampPacketL2 κ, A.ampPacketL2_mem_evenSubspace κ⟩

@[simp] theorem coe_ampPacketEven (κ : ℝ) :
    ((A.ampPacketEven κ : evenSubspace) : SoninL2) = A.ampPacketL2 κ := rfl

/-- **Uniform bound.**  The packet family is bounded in `L²` independently of the frequency. -/
theorem norm_ampPacketL2_le (κ : ℝ) : ‖A.ampPacketL2 κ‖ ≤ 2 * ‖A.ampL2‖ := by
  have hbound : ∀ᵐ x : ℝ, ‖(A.ampPacket κ x : ℂ)‖ ≤
      ‖((2 : ℝ) • fun y : ℝ => (A.toFun y : ℂ)) x‖ := by
    filter_upwards with x
    have h := A.abs_ampPacket_le κ x
    have hφ := A.nonneg' x
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * A.toFun x)] using h
  have hmono := eLpNorm_mono_ae (p := 2) (μ := (volume : Measure ℝ)) hbound
  have hfin : eLpNorm (fun y : ℝ => (A.toFun y : ℂ)) 2 (volume : Measure ℝ) ≠ ⊤ :=
    A.memLp_ofReal.2.ne
  have hsmul : eLpNorm ((2 : ℝ) • fun y : ℝ => (A.toFun y : ℂ)) 2 (volume : Measure ℝ) =
      ‖(2 : ℝ)‖ₑ * eLpNorm (fun y : ℝ => (A.toFun y : ℂ)) 2 volume :=
    eLpNorm_const_smul (2 : ℝ) _ 2 volume
  rw [hsmul] at hmono
  have hle := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hmono
  rw [ENNReal.toReal_mul] at hle
  rw [ampPacketL2, ampL2, Lp.norm_toLp, Lp.norm_toLp]
  simpa using hle

theorem norm_ampPacketEven_le (κ : ℝ) : ‖A.ampPacketEven κ‖ ≤ 2 * ‖A.ampL2‖ :=
  A.norm_ampPacketL2_le κ

/-! ### The mean vanishes at high frequency -/

/-- **Riemann--Lebesgue for the amplitude.**  The modulated mass of the amplitude vanishes. -/
theorem tendsto_integral_amp_mul_cos_atTop :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, A.toFun x * Real.cos (κ * x)) atTop (𝓝 0) :=
  tendsto_integral_mul_cos_freq_atTop A.integrable

/-- **The packet mean vanishes at high frequency.** -/
theorem tendsto_ampPacketMean_atTop :
    Tendsto (fun κ : ℝ => A.ampPacketMean κ) atTop (𝓝 0) := by
  have h := A.tendsto_integral_amp_mul_cos_atTop
  have hmass : (∫ x : ℝ, A.toFun x) ≠ 0 := ne_of_gt A.mass_pos'
  simpa [ampPacketMean, hmass] using h.div_const (∫ x : ℝ, A.toFun x)

/-! ### Physical cutoffs -/

/-- The inner physical cutoff annihilates the packet. -/
theorem evenIndicatorCutoff_ampPacketEven_eq_zero (κ : ℝ) :
    evenIndicatorCutoff b (A.ampPacketEven κ) = 0 := by
  have hgoal : indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
      (A.ampPacketL2 κ) = 0 := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b)
      (A.ampPacketL2 κ), A.ampPacketL2_coeFn κ,
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hval hzero
    rw [hx, hzero]
    by_cases hmem : x ∈ centralInterval b
    · rw [Set.indicator_of_mem hmem, hval]
      have habs : |x| ≤ b := abs_le.mpr ⟨hmem.1, hmem.2⟩
      rw [A.ampPacket_eq_zero_of_abs_le habs]
      simp
    · rw [Set.indicator_of_notMem hmem]
      rfl
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_ampPacketEven, hgoal]
  simp

/-- The outer physical cutoff fixes the packet. -/
theorem evenIndicatorCutoff_ampPacketEven_eq_self (κ : ℝ) :
    evenIndicatorCutoff c (A.ampPacketEven κ) = A.ampPacketEven κ := by
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_ampPacketEven]
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval c) (measurableSet_centralInterval c)
    (A.ampPacketL2 κ), A.ampPacketL2_coeFn κ] with x hx hval
  rw [hx]
  by_cases hmem : x ∈ centralInterval c
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, hval]
    have habs : c ≤ |x| := by
      by_contra hlt
      push Not at hlt
      exact hmem (abs_le.mp hlt.le)
    rw [A.ampPacket_eq_zero_of_le_abs habs]
    simp

/-- A physical cutoff below the inner radius still annihilates the packet. -/
theorem evenIndicatorCutoff_ampPacketEven_eq_zero_of_le (κ s : ℝ) (hs : s ≤ b) :
    evenIndicatorCutoff s (A.ampPacketEven κ) = 0 := by
  have hnest := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le s b hs) (A.ampPacketEven κ)
  rw [mul_apply_eq_comp, A.evenIndicatorCutoff_ampPacketEven_eq_zero κ, map_zero] at hnest
  exact hnest.symm

/-- A physical cutoff above the outer radius still fixes the packet. -/
theorem evenIndicatorCutoff_ampPacketEven_eq_self_of_le (κ s : ℝ) (hs : c ≤ s) :
    evenIndicatorCutoff s (A.ampPacketEven κ) = A.ampPacketEven κ := by
  have hnest := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le_rev c s hs) (A.ampPacketEven κ)
  rw [mul_apply_eq_comp, A.evenIndicatorCutoff_ampPacketEven_eq_self κ] at hnest
  exact hnest

/-- Every aperture below `r b` misses the inverse-dilated packet. -/
theorem evenIndicatorCutoff_evenDilationCLM_inv_ampPacketEven_eq_zero
    (κ r : ℝ) (hr : 0 < r) (s : ℝ) (hs : s ≤ r * b) :
    evenIndicatorCutoff s (evenDilationCLM r⁻¹ (inv_pos.mpr hr) (A.ampPacketEven κ)) = 0 := by
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM s r⁻¹ (inv_pos.mpr hr)) (A.ampPacketEven κ)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  rw [hcov, A.evenIndicatorCutoff_ampPacketEven_eq_zero_of_le κ (r⁻¹ * s) ?_, map_zero]
  rw [inv_mul_le_iff₀ hr] at *
  linarith [hs]

/-- Every aperture above `r c` fixes the inverse-dilated packet. -/
theorem evenIndicatorCutoff_evenDilationCLM_inv_ampPacketEven_eq_self
    (κ r : ℝ) (hr : 0 < r) (s : ℝ) (hs : r * c ≤ s) :
    evenIndicatorCutoff s (evenDilationCLM r⁻¹ (inv_pos.mpr hr) (A.ampPacketEven κ)) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) (A.ampPacketEven κ) := by
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM s r⁻¹ (inv_pos.mpr hr)) (A.ampPacketEven κ)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  rw [hcov, A.evenIndicatorCutoff_ampPacketEven_eq_self_of_le κ (r⁻¹ * s) ?_]
  rw [le_inv_mul_iff₀ hr]
  linarith [hs]

end AnnulusAmplitude

end RHTower
