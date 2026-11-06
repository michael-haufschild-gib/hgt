import GaloisForLFunctions.RHTower.XiSegmentEstimate
import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.ZetaSelbergRightEdge
import GaloisForLFunctions.RHTower.LagExplicitFormula
import GaloisForLFunctions.RHTower.WeightedLittlewoodRectangle

/-!
# The critical line is a shift of the off-line field, at the cost of the zero count

For `0 < R ≤ 1`, the heights `t ∈ [T, 2T]` with
`λ ≤ |log|ζ(½ + R + it)| − log|ζ(½ + it)||` have measure `≤ C R T log T/λ`
(`exists_volume_log_norm_zeta_shift_ge_le`). At `R = κ/log T` the shift costs `O(κ)` in `L¹`-mean.

**Mechanism.** Off the zero ordinates, `Re ξ'/ξ` is a sum over the zeros of the signed Poisson
kernels `(u − β)/((u − β)² + (t − γ)²)`, and each kernel has mass at most `π` in `t` for every `u`.
Tonelli gives each zero the cost `π R` across the segment `½ ≤ u ≤ ½ + R`, with no logarithmic loss
at a zero on the segment. The zeros at ordinate distance `≥ 1` contribute `O(R log t)` by the
weighted density, and so does the archimedean factor.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open RHTower

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The absolute Poisson kernel of a zero copy at `u + it`. -/
def zeroKernel (q : XiZeroCopy) (u t : ℝ) : ℝ :=
  |u - (q.1 : ℂ).re| / ((u - (q.1 : ℂ).re) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ))

theorem zeroKernel_nonneg (q : XiZeroCopy) (u t : ℝ) : 0 ≤ zeroKernel q u t := by
  unfold zeroKernel
  positivity

theorem abs_re_inv_eq_zeroKernel (q : XiZeroCopy) (u t : ℝ) :
    |(((u : ℂ) + (t : ℂ) * I - (q.1 : ℂ))⁻¹).re| = zeroKernel q u t := by
  have hd : 0 ≤ (u - (q.1 : ℂ).re) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by positivity
  rw [re_inv_first, abs_div, abs_of_nonneg hd]
  rfl

theorem abs_re_inv_reflect_eq_zeroKernel (q : XiZeroCopy) (u t : ℝ) :
    |(((u : ℂ) + (t : ℂ) * I - 1 + (q.1 : ℂ))⁻¹).re| =
      zeroKernel (xiZeroCopyReflectEquiv q) u t := by
  rw [← abs_re_inv_eq_zeroKernel, xiZeroCopyReflect_coe]
  congr 3
  ring

/-- A far zero has kernel at most three times its Cauchy weight. -/
theorem zeroKernel_le_of_far {q : XiZeroCopy} {u t : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 3 / 2)
    (hfar : 1 ≤ |t - (q.1 : ℂ).im|) :
    zeroKernel q u t ≤ 3 * (1 / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) := by
  have hb0 := xiZeroCopy_re_pos q
  have hb1 := xiZeroCopy_re_lt_one q
  have hv : |u - (q.1 : ℂ).re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hy2 : 1 ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
    rw [← sq_abs]
    nlinarith
  have hden : 0 < (u - (q.1 : ℂ).re) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
    have := sq_nonneg (u - (q.1 : ℂ).re)
    linarith
  have h1y : 0 < 1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by linarith
  unfold zeroKernel
  rw [mul_one_div, div_le_div_iff₀ hden h1y]
  have hmul : |u - (q.1 : ℂ).re| * (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
      3 / 2 * (2 * (t - (q.1 : ℂ).im) ^ (2 : ℕ)) :=
    mul_le_mul hv (by linarith) h1y.le (by norm_num)
  nlinarith [sq_nonneg (u - (q.1 : ℂ).re)]

/-- For fixed `u` in the strip the kernels are summable over the zero copies. -/
theorem summable_zeroKernel {u : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 3 / 2) (t : ℝ) :
    Summable fun q : XiZeroCopy => zeroKernel q u t := by
  classical
  have hfin := finite_xiZeroCopy_band t (by norm_num : (0 : ℝ) ≤ 1)
  have hbs : Summable fun q : XiZeroCopy => if q ∈ hfin.toFinset then zeroKernel q u t else 0 :=
    summable_of_ne_finset_zero (s := hfin.toFinset) fun q hq => by simp [hq]
  refine Summable.of_nonneg_of_le (fun q => zeroKernel_nonneg q u t) (fun q => ?_)
    (hbs.add ((summable_xiZeroWeight t).mul_left 3))
  by_cases hq : q ∈ hfin.toFinset
  · simp only [hq, if_true]
    have : 0 ≤ 3 * ((1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) := by positivity
    linarith
  · simp only [hq, if_false, zero_add]
    refine zeroKernel_le_of_far hu hu' ?_
    rw [Set.Finite.mem_toFinset, mem_setOf_eq, not_le] at hq
    rw [abs_sub_comm]
    exact hq.le

/-- `|Re ξ'/ξ|` is at most the sum of the absolute Poisson kernels. -/
theorem abs_re_logDeriv_xi_le_tsum {u t : ℝ} (hne : xi ((u : ℂ) + (t : ℂ) * I) ≠ 0)
    (hu : 1 / 2 ≤ u) (hu' : u ≤ 3 / 2) :
    |(logDeriv xi ((u : ℂ) + (t : ℂ) * I)).re| ≤ ∑' q : XiZeroCopy, zeroKernel q u t := by
  have hk := summable_zeroKernel hu hu' t
  have h2 := two_logDeriv_xi_eq_pair_tsum hne
  have hs := summable_xiPairTerm hne
  have hre : 2 * (logDeriv xi ((u : ℂ) + (t : ℂ) * I)).re =
      ∑' q : XiZeroCopy, (((u : ℂ) + (t : ℂ) * I - (q.1 : ℂ))⁻¹ +
        ((u : ℂ) + (t : ℂ) * I - 1 + (q.1 : ℂ))⁻¹).re := by
    rw [← Complex.re_tsum hs, ← h2]
    simp
  have hsum : HasSum (fun q : XiZeroCopy => zeroKernel q u t +
      zeroKernel (xiZeroCopyReflectEquiv q) u t)
      ((∑' q : XiZeroCopy, zeroKernel q u t) + ∑' q : XiZeroCopy, zeroKernel q u t) :=
    hk.hasSum.add ((Equiv.hasSum_iff xiZeroCopyReflectEquiv).mpr hk.hasSum)
  have hb := tsum_of_norm_bounded hsum (f := fun q : XiZeroCopy =>
      (((u : ℂ) + (t : ℂ) * I - (q.1 : ℂ))⁻¹ +
        ((u : ℂ) + (t : ℂ) * I - 1 + (q.1 : ℂ))⁻¹).re) (fun q => by
      rw [Real.norm_eq_abs, Complex.add_re, ← abs_re_inv_eq_zeroKernel,
        ← abs_re_inv_reflect_eq_zeroKernel]
      exact abs_add_le _ _)
  rw [← hre, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
  linarith

/-- Off a finite set of near zeros the sum of kernels is `3` times the Cauchy weight. -/
theorem tsum_zeroKernel_le {u t B : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 3 / 2) {N : Finset XiZeroCopy}
    (hN : ∀ q, q ∉ N → 1 ≤ |t - (q.1 : ℂ).im|)
    (hB : ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤ B) :
    ∑' q : XiZeroCopy, zeroKernel q u t ≤ ∑ q ∈ N, zeroKernel q u t + 3 * B := by
  classical
  refine (summable_zeroKernel hu hu' t).tsum_le_of_sum_le fun F => ?_
  have hsplit : ∑ q ∈ F, zeroKernel q u t =
      ∑ q ∈ F ∩ N, zeroKernel q u t + ∑ q ∈ F \ N, zeroKernel q u t :=
    (Finset.sum_inter_add_sum_sdiff F N _).symm
  have h1 : ∑ q ∈ F ∩ N, zeroKernel q u t ≤ ∑ q ∈ N, zeroKernel q u t :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun q _ _ => zeroKernel_nonneg q u t
  have h2 : ∑ q ∈ F \ N, zeroKernel q u t ≤ 3 * B := by
    have hw := summable_xiZeroWeight t
    calc ∑ q ∈ F \ N, zeroKernel q u t
        ≤ ∑ q ∈ F \ N, 3 * ((1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) :=
          Finset.sum_le_sum fun q hq =>
            zeroKernel_le_of_far hu hu' (hN q (Finset.mem_sdiff.mp hq).2)
      _ = 3 * ∑ q ∈ F \ N, ((1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ 3 * B := by
          refine mul_le_mul_of_nonneg_left ((hw.sum_le_tsum _ fun q _ => by positivity).trans hB)
            (by norm_num)
  rw [hsplit]
  exact add_le_add h1 h2

/-! ### The logarithm along a horizontal segment -/

theorem analyticOnNhd_riemannZeta : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt)
    isOpen_compl_singleton

theorem horizontal_ne_one {t : ℝ} (ht : t ≠ 0) (u : ℝ) : (u : ℂ) + (t : ℂ) * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact ht this

theorem hasDerivAt_horizontal (t u : ℝ) :
    HasDerivAt (fun v : ℝ => (v : ℂ) + (t : ℂ) * I) 1 u := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).add_const ((t : ℂ) * I)

theorem continuous_horizontal (t : ℝ) : Continuous fun v : ℝ => (v : ℂ) + (t : ℂ) * I := by
  fun_prop

/-- `log|ζ|` along a horizontal line has derivative `Re ζ'/ζ` at a point off the zeros. -/
theorem hasDerivAt_log_norm_zeta_horizontal {t u : ℝ} (ht : t ≠ 0)
    (hne : riemannZeta ((u : ℂ) + (t : ℂ) * I) ≠ 0) :
    HasDerivAt (fun v : ℝ => Real.log ‖riemannZeta ((v : ℂ) + (t : ℂ) * I)‖)
      ((logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re) u := by
  have hd : HasDerivAt riemannZeta (deriv riemannZeta ((u : ℂ) + (t : ℂ) * I))
      ((u : ℂ) + (t : ℂ) * I) :=
    (differentiableAt_riemannZeta (horizontal_ne_one ht u)).hasDerivAt
  have hc := hd.comp_of_eq u (hasDerivAt_horizontal t u) rfl
  rw [mul_one] at hc
  have h := hasDerivAt_log_norm_comp hc hne
  simpa [logDeriv_apply] using h

/-- `Re ζ'/ζ` is continuous along a zero-free part of a horizontal line. -/
theorem continuousOn_re_logDeriv_zeta_horizontal {t : ℝ} (ht : t ≠ 0) {S : Set ℝ}
    (hne : ∀ u ∈ S, riemannZeta ((u : ℂ) + (t : ℂ) * I) ≠ 0) :
    ContinuousOn (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re) S := by
  refine Complex.continuous_re.comp_continuousOn ?_
  simp only [logDeriv_apply]
  have hmem : ∀ u : ℝ, (u : ℂ) + (t : ℂ) * I ∈ ({1}ᶜ : Set ℂ) := horizontal_ne_one ht
  exact ((analyticOnNhd_riemannZeta.deriv.continuousOn.comp_continuous
    (continuous_horizontal t) hmem).continuousOn).div
    ((analyticOnNhd_riemannZeta.continuousOn.comp_continuous
      (continuous_horizontal t) hmem).continuousOn) hne

/-! ### Tonelli for one zero -/

/-- The joint kernel `|u − β|/((u − β)² + (t − γ)²)` is integrable on a rectangle, its `t`-marginal
is integrable, and its mass is at most `π` times the length of the `u`-segment. -/
theorem integrable_and_integral_kernel_le (β γ : ℝ) {a R T₁ T₂ : ℝ} (hR : 0 ≤ R) (hT : T₁ ≤ T₂) :
    Integrable (fun t : ℝ => ∫ u in Ioc a (a + R), |u - β| / ((u - β) ^ (2 : ℕ) + (t - γ) ^ (2 : ℕ)))
        (volume.restrict (Ioc T₁ T₂)) ∧
      ∫ t in Ioc T₁ T₂, ∫ u in Ioc a (a + R), |u - β| / ((u - β) ^ (2 : ℕ) + (t - γ) ^ (2 : ℕ)) ≤
        Real.pi * R := by
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ → ℝ, f = fun u t => |u - β| / ((u - β) ^ (2 : ℕ) + (t - γ) ^ (2 : ℕ)) :=
    ⟨_, rfl⟩
  have hmeas : Measurable (Function.uncurry f) := by
    rw [hf]
    have h1 : Measurable fun p : ℝ × ℝ => p.1 - β := measurable_fst.sub_const β
    have h2 : Measurable fun p : ℝ × ℝ => p.2 - γ := measurable_snd.sub_const γ
    exact (continuous_abs.measurable.comp h1).div ((h1.pow_const 2).add (h2.pow_const 2))
  have hae : ∀ᵐ u ∂(volume.restrict (Ioc a (a + R))), u ≠ β :=
    ae_restrict_of_ae (by simp [ae_iff, Set.setOf_eq_eq_singleton])
  have hfib : ∀ u, u ≠ β → Integrable (f u) (volume.restrict (Ioc T₁ T₂)) ∧
      ∫ t in Ioc T₁ T₂, f u t ≤ Real.pi := by
    intro u hu
    have hv : 0 < |u - β| := abs_pos.mpr (sub_ne_zero.mpr hu)
    have hc : Continuous (f u) := by
      rw [hf]
      refine Continuous.div continuous_const (by fun_prop) fun t => ?_
      have : 0 < (u - β) ^ (2 : ℕ) := by rw [← sq_abs]; positivity
      have h2 : 0 ≤ (t - γ) ^ (2 : ℕ) := by positivity
      linarith
    refine ⟨hc.integrableOn_Ioc, ?_⟩
    rw [← intervalIntegral.integral_of_le hT]
    have hw := integral_lorentz_window_le hv γ hT
    have heq : ∀ t, f u t = |u - β| * (|u - β| ^ 2 + (t - γ) ^ 2)⁻¹ := by
      intro t
      simp only [hf, sq_abs, div_eq_mul_inv]
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul]
    calc |u - β| * ∫ t in T₁..T₂, (|u - β| ^ 2 + (t - γ) ^ 2)⁻¹
        ≤ |u - β| * (Real.pi / |u - β|) := mul_le_mul_of_nonneg_left hw hv.le
      _ = Real.pi := by field_simp
  have hnn : ∀ u t, 0 ≤ f u t := by
    intro u t
    rw [hf]
    positivity
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a (a + R))).prod (volume.restrict (Ioc T₁ T₂))) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact hae.mono fun u hu => (hfib u hu).1
    · refine Integrable.of_bound (C := Real.pi) ?_ ?_
      · exact (hmeas.stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
      · refine hae.mono fun u hu => ?_
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (hnn u _)]
        rw [abs_of_nonneg (integral_nonneg fun t => hnn u t)]
        exact (hfib u hu).2
  refine ⟨?_, ?_⟩
  · have h := hint.integral_prod_right
    have heq : (fun t : ℝ => ∫ u in Ioc a (a + R), |u - β| / ((u - β) ^ (2 : ℕ) + (t - γ) ^ (2 : ℕ))) =
        fun t => ∫ u in Ioc a (a + R), Function.uncurry f (u, t) := by
      funext t
      rw [hf]
      rfl
    rw [heq]
    exact h
  · have hswap := integral_integral_swap (f := f) hint
    have heq : ∀ t : ℝ, ∫ u in Ioc a (a + R), |u - β| / ((u - β) ^ (2 : ℕ) + (t - γ) ^ (2 : ℕ)) =
        ∫ u in Ioc a (a + R), f u t := by
      intro t
      rw [hf]
    simp_rw [heq]
    rw [← hswap]
    have hb : ∫ u in Ioc a (a + R), ∫ t in Ioc T₁ T₂, f u t ≤
        ∫ _ in Ioc a (a + R), Real.pi := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun u => integral_nonneg fun t => hnn u t)
        (integrable_const _) (hae.mono fun u hu => (hfib u hu).2)
    refine hb.trans (le_of_eq ?_)
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hR, mul_comm]

/-! ### The pointwise shift bound -/

theorem riemannZeta_ne_zero_of_xi_ne_zero {s : ℂ} (hre : 0 < s.re) (h1 : s ≠ 1) (hxi : xi s ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro h
  apply hxi
  have h0 : s ≠ 0 := by
    rintro rfl
    simp at hre
  rw [xi_eq_xiUnit_mul_zeta h0 h1 hre, h, mul_zero]

/-- `|Re ζ'/ζ| ≤ |Re ξ'/ξ| + ½ + log t + C` on a horizontal line in the strip. -/
theorem abs_re_logDeriv_zeta_le {u t : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 3) (ht : 4 ≤ t)
    (hne : xi ((u : ℂ) + (t : ℂ) * I) ≠ 0) :
    |(logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re| ≤
      |(logDeriv xi ((u : ℂ) + (t : ℂ) * I)).re| + 1 / 2 + Real.log t + digammaVerticalLogConstant := by
  have ht0 : t ≠ 0 := by linarith
  have hs1' := horizontal_ne_one ht0 u
  have hG' := norm_logDeriv_Gammaℝ_le hu hu' ht
  set s : ℂ := (u : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = u := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := hs1'
  have hre : 0 < s.re := by linarith
  have hz := riemannZeta_ne_zero_of_xi_ne_zero hre hs1 hne
  rw [logDeriv_zeta_eq_logDeriv_xi hre hs1 hz]
  have hi := norm_inv_le_quarter hsim ht
  have hi' : ‖(s - 1)⁻¹‖ ≤ 1 / 4 := norm_inv_le_quarter (s := s - 1) (by simp [hsim]) ht
  have hG : ‖logDeriv Gammaℝ s‖ ≤ Real.log t + digammaVerticalLogConstant := hG'
  simp only [Complex.sub_re]
  have h1 := Complex.abs_re_le_norm s⁻¹
  have h2 := Complex.abs_re_le_norm (s - 1)⁻¹
  have h3 := Complex.abs_re_le_norm (logDeriv Gammaℝ s)
  have h4 := abs_sub (logDeriv xi s).re (s⁻¹).re
  have h5 := abs_sub ((logDeriv xi s).re - (s⁻¹).re) ((s - 1)⁻¹).re
  have h6 := abs_sub ((logDeriv xi s).re - (s⁻¹).re - ((s - 1)⁻¹).re) (logDeriv Gammaℝ s).re
  linarith

/-- **The shift at one height.** For a height off the zero ordinates,
`|log|ζ(½ + R + it)| − log|ζ(½ + it)||` is at most the near-zero kernels over the segment, plus
`R (3B + ½ + log t + C)`, `B` the weighted density at `t`. -/
theorem abs_log_norm_zeta_shift_le {t R B : ℝ} (ht : 4 ≤ t) (hR : 0 < R) (hR1 : R ≤ 1)
    (hne : ∀ u : ℝ, xi ((u : ℂ) + (t : ℂ) * I) ≠ 0) {N : Finset XiZeroCopy}
    (hN : ∀ q, q ∉ N → 1 ≤ |t - (q.1 : ℂ).im|)
    (hB : ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤ B) :
    |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
        Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤
      ∑ q ∈ N, (∫ u in Ioc (1 / 2) (1 / 2 + R), zeroKernel q u t) +
        R * (3 * B + 1 / 2 + Real.log t + digammaVerticalLogConstant) := by
  have ht0 : t ≠ 0 := by linarith
  have hzne : ∀ u : ℝ, 0 < u → riemannZeta ((u : ℂ) + (t : ℂ) * I) ≠ 0 := fun u hu =>
    riemannZeta_ne_zero_of_xi_ne_zero (by simpa using hu) (horizontal_ne_one ht0 u) (hne u)
  have hle : (1 / 2 : ℝ) ≤ 1 / 2 + R := by linarith
  have hderiv : ∀ u ∈ uIcc (1 / 2 : ℝ) (1 / 2 + R), HasDerivAt
      (fun v : ℝ => Real.log ‖riemannZeta ((v : ℂ) + (t : ℂ) * I)‖)
      ((logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re) u := by
    intro u hu
    rw [uIcc_of_le hle] at hu
    exact hasDerivAt_log_norm_zeta_horizontal ht0 (hzne u (by linarith [hu.1]))
  have hcontOn : ContinuousOn (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re)
      (uIcc (1 / 2 : ℝ) (1 / 2 + R)) := by
    refine continuousOn_re_logDeriv_zeta_horizontal ht0 fun u hu => ?_
    rw [uIcc_of_le hle] at hu
    exact hzne u (by linarith [hu.1])
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcontOn.intervalIntegrable
  rw [← hftc]
  -- the integrand bound
  have hkc : ∀ q : XiZeroCopy, Continuous fun u : ℝ => zeroKernel q u t := by
    intro q
    unfold zeroKernel
    have hq : t - (q.1 : ℂ).im ≠ 0 := by
      intro h
      have hγ : t = (q.1 : ℂ).im := sub_eq_zero.mp h
      apply hne (q.1 : ℂ).re
      have hc : (((q.1 : ℂ).re : ℝ) : ℂ) + (t : ℂ) * I = (q.1 : ℂ) := by
        rw [hγ]
        exact Complex.re_add_im _
      rw [hc]
      exact xi_xiZeroCopy_eq_zero q
    refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
    have h1 : 0 < (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by positivity
    have h2 : 0 ≤ (u - (q.1 : ℂ).re) ^ (2 : ℕ) := by positivity
    linarith
  have hsumc : Continuous fun u : ℝ => ∑ q ∈ N, zeroKernel q u t :=
    continuous_finsetSum _ fun q _ => hkc q
  have hpt : ∀ u ∈ Ioc (1 / 2 : ℝ) (1 / 2 + R),
      ‖(logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I)).re‖ ≤
        ∑ q ∈ N, zeroKernel q u t +
          (3 * B + 1 / 2 + Real.log t + digammaVerticalLogConstant) := by
    intro u hu
    have hu1 : 1 / 2 ≤ u := hu.1.le
    have hu2 : u ≤ 3 / 2 := by linarith [hu.2]
    rw [Real.norm_eq_abs]
    have h1 := abs_re_logDeriv_zeta_le hu1 (by linarith) ht (hne u)
    have h2 := abs_re_logDeriv_xi_le_tsum (hne u) hu1 hu2
    have h3 := tsum_zeroKernel_le hu1 hu2 hN hB
    linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hle
    (g := fun u => ∑ q ∈ N, zeroKernel q u t +
      (3 * B + 1 / 2 + Real.log t + digammaVerticalLogConstant))
    (Eventually.of_forall fun u hu => hpt u hu)
    ((hsumc.add continuous_const).intervalIntegrable _ _)
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (hsumc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_finsetSum fun q _ => (hkc q).intervalIntegrable _ _,
    intervalIntegral.integral_const, smul_eq_mul]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [intervalIntegral.integral_of_le hle]
  · congr 1
    ring

/-! ### The measure of the large shifts -/

/-- **Shifting off the line costs the zero count.** For `0 < R ≤ 1` the heights `t ∈ [T, 2T]` with
`λ ≤ |log|ζ(½ + R + it)| − log|ζ(½ + it)||` have measure `≤ C R T log T/λ`. -/
theorem exists_volume_log_norm_zeta_shift_ge_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ lam : ℝ, 0 < lam →
      volume {t | t ∈ Icc T (2 * T) ∧ lam ≤ |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖|} ≤
        ENNReal.ofReal (C * R * T * Real.log T / lam) := by
  obtain ⟨C₁, hC₁, hdens⟩ := exists_tsum_weighted_density_le
  obtain ⟨C₂, hC₂, T₀, hT₀, hcard⟩ := exists_card_window_le
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp hdens
  have hCd : 0 ≤ digammaVerticalLogConstant := by
    unfold digammaVerticalLogConstant
    have := Real.pi_pos
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  refine ⟨(2 + 4 * Real.pi * C₂) + (6 * C₁ + 1 / 2 + 2 + digammaVerticalLogConstant),
    by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop t₁, eventually_ge_atTop (T₀ + 3), eventually_ge_atTop 16]
    with T hTt₁ hTT₀ hT16 R hR hR1 lam hlam
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log T := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog2T : Real.log (2 * T) ≤ 2 * L := by
    rw [hL, Real.log_mul (by norm_num) hT0.ne']
    have : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlog23 : Real.log (2 * T + 3) ≤ 2 * L := by
    have h : Real.log (2 * T + 3) ≤ Real.log (T ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h
    rw [hL]
    push_cast at h
    linarith
  -- the near zeros
  have hfin := finite_xiZeroCopy_band (3 * T / 2) (show (0 : ℝ) ≤ T / 2 + 2 by positivity)
  obtain ⟨N, hNdef⟩ : ∃ N : Finset XiZeroCopy, N = hfin.toFinset := ⟨_, rfl⟩
  have hmemN : ∀ q, q ∈ N ↔ |(q.1 : ℂ).im - 3 * T / 2| ≤ T / 2 + 2 := by
    intro q
    rw [hNdef, Set.Finite.mem_toFinset, mem_setOf_eq]
  have hcardN : (N.card : ℝ) ≤ (T + 6) / (2 * Real.pi) * Real.log (T - 3 + (T + 6)) +
      2 * C₂ * Real.log (T - 3 + (T + 6)) := by
    refine hcard (T - 3) (by linarith) (T + 6) (by linarith) N fun q hq => ?_
    have := abs_le.mp ((hmemN q).mp hq)
    constructor <;> linarith [this.1, this.2]
  have hlogeq : T - 3 + (T + 6) = 2 * T + 3 := by ring
  rw [hlogeq] at hcardN
  have hlog230 : 0 ≤ Real.log (2 * T + 3) := Real.log_nonneg (by linarith)
  have hcardN2 : (N.card : ℝ) ≤ (2 * T) / (2 * Real.pi) * (2 * L) + 2 * C₂ * (2 * L) := by
    refine hcardN.trans (add_le_add ?_ ?_)
    · have h1 : (T + 6) / (2 * Real.pi) ≤ 2 * T / (2 * Real.pi) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      exact mul_le_mul h1 hlog23 hlog230 (by positivity)
    · exact mul_le_mul_of_nonneg_left hlog23 (by positivity)
  -- the majorant
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = R * (3 * (C₁ * (2 * L)) + 1 / 2 + 2 * L + digammaVerticalLogConstant) :=
    ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE]
    positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ → ℝ, M = fun t => ∑ q ∈ N, (∫ u in Ioc (1 / 2) (1 / 2 + R), zeroKernel q u t) + E :=
    ⟨_, rfl⟩
  have hTle : T ≤ T + T := by linarith
  have hone : ∀ q : XiZeroCopy, Integrable (fun t : ℝ => ∫ u in Ioc (1 / 2) (1 / 2 + R),
      zeroKernel q u t) (volume.restrict (Ioc T (T + T))) ∧
      ∫ t in Ioc T (T + T), ∫ u in Ioc (1 / 2) (1 / 2 + R), zeroKernel q u t ≤ Real.pi * R :=
    fun q => integrable_and_integral_kernel_le (q.1 : ℂ).re (q.1 : ℂ).im hR.le hTle
  have hsumI : Integrable (fun t : ℝ => ∑ q ∈ N, ∫ u in Ioc (1 / 2) (1 / 2 + R),
      zeroKernel q u t) (volume.restrict (Ioc T (T + T))) :=
    integrable_finsetSum _ fun q _ => (hone q).1
  have hMI : Integrable M (volume.restrict (Ioc T (T + T))) := by
    rw [hM]
    exact hsumI.add (integrable_const _)
  have hM0 : ∀ t, 0 ≤ M t := by
    intro t
    rw [hM]
    refine add_nonneg (Finset.sum_nonneg fun q _ => ?_) hE0
    exact integral_nonneg fun u => zeroKernel_nonneg q u t
  have hMint : ∫ t in Ioc T (T + T), M t ≤
      (N.card : ℝ) * (Real.pi * R) + E * T := by
    rw [hM, integral_add hsumI (integrable_const _), integral_finsetSum _ fun q _ => (hone q).1]
    refine add_le_add ?_ ?_
    · refine (Finset.sum_le_sum fun q _ => (hone q).2).trans (le_of_eq ?_)
      simp
    · rw [setIntegral_const]
      simp only [Measure.real, Real.volume_Ioc, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith), add_sub_cancel_right, mul_comm]
  -- the pointwise bound off the ordinates
  have hpt : ∀ t ∈ Icc T (2 * T), (∀ q : XiZeroCopy, t ≠ (q.1 : ℂ).im) →
      |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
        Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ M t := by
    intro t ht hord
    have htT1 : t₁ ≤ t := hTt₁.trans ht.1
    have ht4 : 4 ≤ t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    obtain ⟨-, hB⟩ := ht₁ t htT1
    have hxi : ∀ u : ℝ, xi ((u : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro u h
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
      apply hord q
      rw [hq]
      simp
    have hfar : ∀ q, q ∉ N → 1 ≤ |t - (q.1 : ℂ).im| := by
      intro q hq
      rw [hmemN, not_le] at hq
      have hd : |t - 3 * T / 2| ≤ T / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h3 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im - 3 * T / 2) (t - 3 * T / 2)
      have h4 : (q.1 : ℂ).im - 3 * T / 2 - (t - 3 * T / 2) = (q.1 : ℂ).im - t := by ring
      rw [h4] at h3
      have h5 : |t - (q.1 : ℂ).im| = |(q.1 : ℂ).im - t| := abs_sub_comm _ _
      rw [h5]
      linarith
    have hshift := abs_log_norm_zeta_shift_le ht4 hR hR1 hxi hfar hB
    refine hshift.trans ?_
    rw [hM]
    simp only
    refine add_le_add le_rfl ?_
    rw [hE]
    have hlogt : Real.log t ≤ 2 * L := (Real.log_le_log ht0 ht.2).trans hlog2T
    have hC : C₁ * Real.log t ≤ C₁ * (2 * L) := mul_le_mul_of_nonneg_left hlogt hC₁.le
    exact mul_le_mul_of_nonneg_left (by linarith) hR.le
  -- Markov
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc T (T + T)))
    (Eventually.of_forall hM0) hMI lam
  have hfinite : volume.restrict (Ioc T (T + T)) {t | lam ≤ M t} ≠ ⊤ :=
    measure_ne_top_of_subset (Set.subset_univ _) (by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hbound : (N.card : ℝ) * (Real.pi * R) + E * T ≤
      ((2 + 4 * Real.pi * C₂) + (6 * C₁ + 1 / 2 + 2 + digammaVerticalLogConstant)) * R * T * L := by
    have hpiR : 0 ≤ Real.pi * R := by positivity
    have hT1 : (1 : ℝ) ≤ T := by linarith
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have h1 : (N.card : ℝ) * (Real.pi * R) ≤ (2 + 4 * Real.pi * C₂) * R * T * L := by
      calc (N.card : ℝ) * (Real.pi * R)
          ≤ ((2 * T) / (2 * Real.pi) * (2 * L) + 2 * C₂ * (2 * L)) * (Real.pi * R) :=
            mul_le_mul_of_nonneg_right hcardN2 hpiR
        _ = 2 * T * L * R + 4 * Real.pi * C₂ * L * R := by
            field_simp
            ring
        _ ≤ (2 + 4 * Real.pi * C₂) * R * T * L := by
            have h0 : 0 ≤ 4 * Real.pi * C₂ * L * R := by positivity
            have h2 : 4 * Real.pi * C₂ * L * R * 1 ≤ 4 * Real.pi * C₂ * L * R * T :=
              mul_le_mul_of_nonneg_left hT1 h0
            nlinarith
    have h2 : E * T ≤ (6 * C₁ + 1 / 2 + 2 + digammaVerticalLogConstant) * R * T * L := by
      have h3 : 3 * (C₁ * (2 * L)) + 1 / 2 + 2 * L + digammaVerticalLogConstant ≤
          (6 * C₁ + 1 / 2 + 2 + digammaVerticalLogConstant) * L := by
        nlinarith [mul_nonneg hCd (by linarith : 0 ≤ L - 1)]
      rw [hE]
      calc R * (3 * (C₁ * (2 * L)) + 1 / 2 + 2 * L + digammaVerticalLogConstant) * T
          ≤ R * ((6 * C₁ + 1 / 2 + 2 + digammaVerticalLogConstant) * L) * T :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hR.le) hT0.le
        _ = _ := by ring
    linarith
  have hreal : (volume.restrict (Ioc T (T + T))).real {t | lam ≤ M t} ≤
      ((2 + 4 * Real.pi * C₂) + (6 * C₁ + 1 / 2 + 2 + digammaVerticalLogConstant)) * R * T * L /
        lam := by
    rw [le_div_iff₀ hlam, mul_comm]
    exact hmark.trans (hMint.trans hbound)
  have hnull : volume (({T} : Set ℝ) ∪ Set.range fun q : XiZeroCopy => (q.1 : ℂ).im) = 0 :=
    ((Set.countable_singleton T).union (Set.countable_range _)).measure_zero volume
  have hsub : {t | t ∈ Icc T (2 * T) ∧ lam ≤ |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖|} ⊆
      ({t | lam ≤ M t} ∩ Ioc T (T + T)) ∪
        (({T} : Set ℝ) ∪ Set.range fun q : XiZeroCopy => (q.1 : ℂ).im) := by
    rintro t ⟨ht, hlt⟩
    by_cases hord : ∃ q : XiZeroCopy, t = (q.1 : ℂ).im
    · obtain ⟨q, hq⟩ := hord
      exact Or.inr (Or.inr ⟨q, hq.symm⟩)
    · by_cases htT : t = T
      · exact Or.inr (Or.inl htT)
      · refine Or.inl ⟨hlt.trans (hpt t ht fun q hq => hord ⟨q, hq⟩), ?_, ?_⟩
        · exact lt_of_le_of_ne ht.1 (Ne.symm htT)
        · linarith [ht.2]
  calc volume {t | t ∈ Icc T (2 * T) ∧ lam ≤ |Real.log ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ -
        Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖|}
      ≤ volume ({t | lam ≤ M t} ∩ Ioc T (T + T)) +
          volume (({T} : Set ℝ) ∪ Set.range fun q : XiZeroCopy => (q.1 : ℂ).im) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal ((volume.restrict (Ioc T (T + T))).real {t | lam ≤ M t}) := by
        rw [hnull, add_zero, Measure.real, ENNReal.ofReal_toReal hfinite,
          Measure.restrict_apply' measurableSet_Ioc]
    _ ≤ _ := by
        rw [← hL]
        exact ENNReal.ofReal_le_ofReal hreal

end GaloisForLFunctions.MultiscaleMollifiedZetaField
