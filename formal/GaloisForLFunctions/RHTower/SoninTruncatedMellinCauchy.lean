import GaloisForLFunctions.HTGeometry.InvAbsTailL2
import GaloisForLFunctions.HTGeometry.TruncatedPowerFourierBound
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.RHTower.SoninDeBrangesCarrier

/-!
# The uniform Cauchy estimate for truncated Mellin transforms of a Sonine function

Let `f` lie in the Sonine carrier `K_a` (`centralSoninCarrier a`), so that both `f` and its Fourier
transform vanish on the band `|t| ≤ a`.  For `a ≤ T ≤ T'` and `Re s > 0` the truncated Mellin
integral obeys

`‖∫_T^{T'} t^{-s} f(t) dt‖ ≤ ((2T^{-Re s} + ‖s‖T^{-Re s}/Re s)/(2π)) · N(a) · ‖f‖`,

with `N(a)` the `L²` norm of the tail kernel `1_{|u|>a}/|u|` — a bound **uniform in `T'`** which
tends to `0` as `T → ∞`, locally uniformly in `s` on `{Re s > 0}`.

The proof is Burnol's: pair with the truncated power through Plancherel, use that the Fourier
transform of `f` is supported outside the band, and apply the one-integration-by-parts bound
`‖𝓕(1_{(T,T')}t^{-s})(u)‖ = O(1/|u|)`.  This is the estimate that continues the Mellin transform of
a Sonine function across the critical line (arXiv:math/0203120, Thm. 2.1).

## Main results

* `inner_truncPowerVector_eq_truncMellin`
* `norm_truncMellin_le`
-/

noncomputable section

open MeasureTheory Set Complex Real FourierTransform
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Conjugation of a positive-real power flips the exponent. -/
theorem conj_ofReal_cpow_neg {t : ℝ} (ht : 0 < t) (s : ℂ) :
    (starRingEnd ℂ) (((t : ℝ) : ℂ) ^ (-(starRingEnd ℂ) s)) = ((t : ℝ) : ℂ) ^ (-s) := by
  have harg : ((t : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Ne.symm (ne_of_gt Real.pi_pos)
  have h := Complex.conj_cpow ((t : ℝ) : ℂ) (-s) harg
  rw [Complex.conj_ofReal, map_neg] at h
  exact h.symm

/-- The truncated power, as a vector of `L²(ℝ)`. -/
def truncPowerVector (T T' : ℝ) (hT : 0 < T) {s : ℂ} (hs : 0 < s.re) : SoninL2 :=
  (memLp_two_truncPower (T' := T') hT
    (s := (starRingEnd ℂ) s) (by rwa [Complex.conj_re])).toLp _

/-- Pairing the truncated power against a vector recovers the truncated Mellin integral. -/
theorem inner_truncPowerVector_eq_truncMellin {T T' : ℝ} (hT : 0 < T) {s : ℂ} (hs : 0 < s.re)
    (f : SoninL2) :
    ⟪truncPowerVector T T' hT hs, f⟫_ℂ
      = ∫ t in Set.Ioo T T', ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  rw [MeasureTheory.L2.inner_def]
  have hcoe := (memLp_two_truncPower (T' := T') hT
    (s := (starRingEnd ℂ) s) (by rwa [Complex.conj_re])).coeFn_toLp
  rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with u hu
  have hWu : ((truncPowerVector T T' hT hs : SoninL2) : ℝ → ℂ) u
      = truncPower T T' ((starRingEnd ℂ) s) u := by
    simp only [truncPowerVector]
    exact hu
  have hlhs : (starRingEnd ℂ) (((truncPowerVector T T' hT hs : SoninL2) : ℝ → ℂ) u)
      = (Set.Ioo T T').indicator (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s)) u := by
    rw [hWu, truncPower]
    by_cases hmem : u ∈ Set.Ioo T T'
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        conj_ofReal_cpow_neg (lt_trans hT hmem.1) s]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, map_zero]
  rw [RCLike.inner_apply, hlhs]
  by_cases hmem : u ∈ Set.Ioo T T'
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    ring

/-- **The uniform Cauchy estimate.** -/
theorem norm_truncMellin_le {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ (centralFourierForbidden a)ᗮ)
    {T T' : ℝ} (haT : a ≤ T) (hTT' : T ≤ T') {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioo T T', ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t‖
      ≤ ((2 * T ^ (-s.re) + ‖s‖ * T ^ (-s.re) / s.re) / (2 * Real.pi)) *
          invAbsTailNorm a * ‖f‖ := by
  have hT : 0 < T := lt_of_lt_of_le ha haT
  have hcs : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  set C : ℝ := (2 * T ^ (-s.re) + ‖s‖ * T ^ (-s.re) / s.re) / (2 * Real.pi) with hC
  have hC0 : 0 ≤ C := by
    have h1 : (0:ℝ) ≤ T ^ (-s.re) := Real.rpow_nonneg hT.le _
    have h2 : (0:ℝ) < 2 * Real.pi := by positivity
    have h3 : 0 ≤ ‖s‖ * T ^ (-s.re) / s.re := by positivity
    rw [hC]
    positivity
  set W : SoninL2 := truncPowerVector T T' hT hs with hW
  -- Plancherel
  have hplanch : ⟪W, f⟫_ℂ = ⟪fourierUnitary W, fourierUnitary f⟫_ℂ :=
    (fourierUnitary.inner_map_map W f).symm
  -- the cut-off Fourier transform of the truncated power
  set A : ℝ → ℂ :=
    Set.indicator {u : ℝ | a < |u|} (fun u => ((fourierUnitary W : SoninL2) : ℝ → ℂ) u) with hA
  have hAmem : MemLp A 2 volume := by
    refine MemLp.indicator ?_ (Lp.memLp (fourierUnitary W))
    exact measurableSet_lt measurable_const continuous_abs.measurable
  have hband := fourier_indicator_ae_zero_of_mem_fourierOrthogonal hf
  have hbandpt : ∀ᵐ u ∂(volume : Measure ℝ),
      u ∈ centralInterval a → ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0 := by
    filter_upwards [hband] with u hu hmem
    simpa [Set.indicator_of_mem hmem] using hu
  have hAval : ∀ v : ℝ, a < |v| → A v = ((fourierUnitary W : SoninL2) : ℝ → ℂ) v := by
    intro v hv
    have hv' : v ∈ {u : ℝ | a < |u|} := hv
    rw [hA]
    exact Set.indicator_of_mem hv' (fun u => ((fourierUnitary W : SoninL2) : ℝ → ℂ) u)
  have hAval0 : ∀ v : ℝ, ¬ (a < |v|) → A v = 0 := by
    intro v hv
    have hv' : v ∉ {u : ℝ | a < |u|} := hv
    rw [hA]
    exact Set.indicator_of_notMem hv' (fun u => ((fourierUnitary W : SoninL2) : ℝ → ℂ) u)
  have hinnerA : ⟪fourierUnitary W, fourierUnitary f⟫_ℂ = ⟪hAmem.toLp A, fourierUnitary f⟫_ℂ := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hbandpt, hAmem.coeFn_toLp] with u hu hAu
    rw [RCLike.inner_apply, RCLike.inner_apply, hAu]
    by_cases hlt : a < |u|
    · rw [hAval u hlt]
    · rw [hAval0 u hlt]
      have hmem : u ∈ centralInterval a := by
        rw [centralInterval, Set.mem_Icc, ← abs_le]
        exact not_lt.mp hlt
      rw [hu hmem, zero_mul, zero_mul]
  -- Cauchy--Schwarz
  have hcs2 : ‖⟪hAmem.toLp A, fourierUnitary f⟫_ℂ‖ ≤ ‖hAmem.toLp A‖ * ‖fourierUnitary f‖ :=
    norm_inner_le_norm _ _
  -- the majorant bound
  have hbridge := l2_fourier_coeFn_eq_l1_fourier_of_integrable W
    (by
      rw [hW, truncPowerVector]
      refine Integrable.congr (integrable_truncPower (T' := T') hT hcs) ?_
      exact ((memLp_two_truncPower (T' := T') hT hcs).coeFn_toLp).symm)
  have hAbound : ∀ᵐ u ∂(volume : Measure ℝ), ‖A u‖ ≤ ‖(C • invAbsTail a) u‖ := by
    have hcoeW := (memLp_two_truncPower (T' := T') hT hcs).coeFn_toLp
    filter_upwards [hbridge] with u hu
    by_cases hlt : a < |u|
    · rw [hAval u hlt]
      have hune : u ≠ 0 := by
        intro h
        rw [h] at hlt
        simp at hlt
        linarith
      have hae : ((W : SoninL2) : ℝ → ℂ) =ᵐ[volume] truncPower T T' ((starRingEnd ℂ) s) := by
        simpa [hW, truncPowerVector] using
          (memLp_two_truncPower (T' := T') hT hcs).coeFn_toLp
      have hval : ((fourierUnitary W : SoninL2) : ℝ → ℂ) u
          = 𝓕 (truncPower T T' ((starRingEnd ℂ) s)) u := by
        rw [show ((fourierUnitary W : SoninL2) : ℝ → ℂ) u = ((𝓕 W : SoninL2) : ℝ → ℂ) u from rfl,
          hu, fourierTransform_toLp]
        exact (Real.fourier_congr_ae hae) u
      rw [hval]
      have hb := norm_fourierIntegral_truncPower_le hT hTT' hcs hune
      have hnorms : ‖(starRingEnd ℂ) s‖ = ‖s‖ := by simp
      rw [Complex.conj_re, hnorms] at hb
      have habs : (0:ℝ) < |u| := abs_pos.2 hune
      have hmaj : ‖(C • invAbsTail a) u‖ = C * |u|⁻¹ := by
        rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, invAbsTail, if_pos hlt,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ C * |u|⁻¹)]
      rw [hmaj, hC]
      calc ‖𝓕 (truncPower T T' ((starRingEnd ℂ) s)) u‖
          ≤ (2 * T ^ (-s.re) + ‖s‖ * T ^ (-s.re) / s.re) / (2 * Real.pi * |u|) := hb
        _ = (2 * T ^ (-s.re) + ‖s‖ * T ^ (-s.re) / s.re) / (2 * Real.pi) * |u|⁻¹ := by
            rw [div_mul_eq_div_div]
            ring
    · rw [hAval0 u hlt]
      simp only [norm_zero, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
      positivity
  have hnormA : ‖hAmem.toLp A‖ ≤ C * invAbsTailNorm a := by
    rw [Lp.norm_toLp]
    have h1 : eLpNorm A 2 volume ≤ eLpNorm ((C : ℝ) • invAbsTail a) 2 volume :=
      eLpNorm_mono_ae hAbound
    have h2 : eLpNorm ((C : ℝ) • invAbsTail a) 2 volume
        ≤ ‖(C : ℝ)‖ₑ * eLpNorm (invAbsTail a) 2 volume := eLpNorm_const_smul_le
    have h3 : (‖(C : ℝ)‖ₑ * eLpNorm (invAbsTail a) 2 volume) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ?_ (eLpNorm_invAbsTail_ne_top ha)
      simp [enorm_eq_nnnorm]
    have h4 := ENNReal.toReal_mono h3 (h1.trans h2)
    rw [ENNReal.toReal_mul] at h4
    refine h4.trans (le_of_eq ?_)
    rw [invAbsTailNorm]
    congr 1
    simp [enorm_eq_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC0]
  -- assemble
  rw [← inner_truncPowerVector_eq_truncMellin hT hs f, ← hW, hplanch, hinnerA]
  refine hcs2.trans ?_
  rw [fourierUnitary.norm_map f]
  have hfn : (0:ℝ) ≤ ‖f‖ := norm_nonneg f
  have := mul_le_mul_of_nonneg_right hnormA hfn
  exact this

end RHTower
