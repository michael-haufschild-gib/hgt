import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma411
import GaloisForLFunctions.RHTower.SuzukiGramDominationRepair
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Suzuki (2012), Lemma 4.10: the left-endpoint compact-uniform limit

This module proves the published limit

`A_a -> A^omega`, `B_a -> B^omega` as `a -> 1+`,

uniformly on every compact subset of the complex plane.  The main analytic point is not formal
algebra: the logarithmic Fredholm sources live on the collapsing interval
`[-log a, log a]`.  Fixed-window resolvent continuity gives a uniform `L²` bound, while a sharp
Cauchy--Schwarz estimate contributes the vanishing factor `sqrt (2 log a)`.  Hence both compact
Fourier terms vanish uniformly on compact spectral sets.

The right-hand families below are total representatives only so Lean can put them under the
ordinary filter `nhdsWithin 1 (Ioi 1)`.  On that filter their `if` branches are definitionally the
published `a > 1` functions; values away from the source domain play no role.
-/

open Complex Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

set_option maxHeartbeats 1000000

/-! ## Shrinking-support and fixed-window bounds -/

/-- Orthogonal cutoff does not increase the ambient `L²` norm. -/
theorem norm_suzukiCutoff_le (a : ℝ) (f : SoninL2) :
    ‖suzukiCutoff a f‖ ≤ ‖f‖ := by
  change ‖lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Icc (-a) a) measurableSet_Icc
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-a) a) f)‖ ≤ ‖f‖
  rw [show lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Icc (-a) a) measurableSet_Icc
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-a) a) f) =
        lpExtendByZero (F := ℂ) (volume : Measure ℝ) 2
          (Icc (-a) a) measurableSet_Icc
          (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-a) a) f) by rfl,
    norm_lpExtendByZero]
  exact norm_Lp_toLp_restrict_le (Icc (-a) a) f

/-- The exact `L² -> L¹` collapse estimate for an arbitrary aperture cutoff. -/
theorem integral_norm_suzukiCutoff_sq_le
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) :
    (∫ x : ℝ, ‖(suzukiCutoff a f) x‖) ^ 2 ≤
      (2 * a) * ‖f‖ ^ 2 := by
  let g : SoninL2 := suzukiCutoff a f
  have hg2 : Integrable (fun x : ℝ => ‖g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
  have hg2I : Integrable (fun x : ℝ => ‖g x‖ ^ 2)
      (volume.restrict (Icc (-a) a)) := hg2.mono_measure Measure.restrict_le_self
  have hgaemeas : AEStronglyMeasurable (g : ℝ → ℂ)
      (volume.restrict (Icc (-a) a)) := (Lp.memLp g).1.restrict
  have hCS := integral_Icc_norm_sq_l1_bound ha hgaemeas hg2I
  have hL1 : (∫ x : ℝ, ‖g x‖) = ∫ x in Icc (-a) a, ‖g x‖ := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc f] with x hx
    by_cases hmem : x ∈ Icc (-a) a
    · simp only [indicator_of_mem hmem]
    · have hgzero : g x = 0 := by
        dsimp only [g, suzukiCutoff]
        rw [hx, indicator_of_notMem hmem]
      rw [indicator_of_notMem hmem, hgzero, norm_zero]
  have hE : (∫ x in Icc (-a) a, ‖g x‖ ^ 2) = ‖g‖ ^ 2 := by
    rw [norm_sq_lp_eq_integral_norm_sq g]
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc f] with x hx
    by_cases hmem : x ∈ Icc (-a) a
    · simp only [indicator_of_mem hmem]
    · have hgzero : g x = 0 := by
        dsimp only [g, suzukiCutoff]
        rw [hx, indicator_of_notMem hmem]
      rw [indicator_of_notMem hmem, hgzero, norm_zero, zero_pow]
  rw [← hL1, hE] at hCS
  have hnorm := norm_suzukiCutoff_le a f
  have hfac : 0 ≤ 2 * a := by positivity
  exact hCS.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm) hfac)

/-- Zero extension into a larger physical interval preserves the `L²` norm. -/
theorem norm_suzukiPhysicalIntervalInclusion
    {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) (f : IntervalL2 0 a) :
    ‖suzukiPhysicalIntervalInclusion a B f‖ = ‖f‖ := by
  have h := congrArg norm
    (suzukiPhysicalIntervalInclusion_positiveExtension ha haB f)
  simpa using h

/-- A varying-aperture Fredholm solution is bounded by its fixed-window realization. -/
theorem norm_suzukiHankelPhi_le_fixedWindowPhi
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hB : 1 < B) (haB : a ≤ B) :
    ‖suzukiHankelPhi epsilon omega a homega ha‖ ≤
      ‖suzukiFixedWindowPhi epsilon omega B homega hB a‖ := by
  let u := suzukiFixedWindowPhi epsilon omega B homega hB a
  let p := suzukiHankelPhi epsilon omega a homega ha
  have hres : suzukiPhysicalIntervalRestrictionBetween a B u = p := by
    dsimp only [u, p]
    rw [suzukiFixedWindowPhi_eq_extended epsilon homega ha hB haB,
      suzukiHankelPhiExtended_restriction]
  have hinc : suzukiPhysicalIntervalInclusion a B p =
      suzukiApertureCutoff a B u := by
    rw [suzukiApertureCutoff_eq_inclusion_restriction, hres]
  calc
    ‖p‖ = ‖suzukiPhysicalIntervalInclusion a B p‖ :=
      (norm_suzukiPhysicalIntervalInclusion (by linarith) haB p).symm
    _ = ‖suzukiApertureCutoff a B u‖ := by rw [hinc]
    _ ≤ ‖u‖ := norm_suzukiApertureCutoff_apply_le a B u

/-- Uniform `L²` bound for the logarithmic Fredholm sum on `1 < a < 2`. -/
theorem exists_uniform_norm_bound_suzukiHankelPhiSumLog
    {omega : ℝ} (homega : 1 < omega) :
    ∃ C > 0, ∀ (a : ℝ) (ha : 1 < a) (ha2 : a < 2),
      ‖suzukiHankelPhiSumLog omega a homega ha‖ ≤ C ∧
      ‖suzukiHankelPhiSumHankelLog omega a homega ha‖ ≤ C := by
  let hp : ℝ → IntervalL2 0 2 :=
    suzukiFixedWindowPhi SuzukiHankelSign.positive omega 2 (by linarith) (by norm_num)
  let hm : ℝ → IntervalL2 0 2 :=
    suzukiFixedWindowPhi SuzukiHankelSign.negative omega 2 (by linarith) (by norm_num)
  obtain ⟨Cp, hCp⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_suzukiFixedWindowPhi SuzukiHankelSign.positive
      (show 1 / 2 < omega by linarith) (by norm_num : (1 : ℝ) < 2))
  obtain ⟨Cm, hCm⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_suzukiFixedWindowPhi SuzukiHankelSign.negative
      (show 1 / 2 < omega by linarith) (by norm_num : (1 : ℝ) < 2))
  let C := max 1 (Cp + Cm)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro a ha ha2
  have haI : a ∈ Icc (0 : ℝ) 2 := ⟨(lt_trans zero_lt_one ha).le, ha2.le⟩
  have hpBound : ‖suzukiHankelPhi SuzukiHankelSign.positive omega a
      (by linarith) ha‖ ≤ Cp :=
    (norm_suzukiHankelPhi_le_fixedWindowPhi SuzukiHankelSign.positive
      (show 1 / 2 < omega by linarith) ha (by norm_num) ha2.le).trans (hCp a haI)
  have hmBound : ‖suzukiHankelPhi SuzukiHankelSign.negative omega a
      (by linarith) ha‖ ≤ Cm :=
    (norm_suzukiHankelPhi_le_fixedWindowPhi SuzukiHankelSign.negative
      (show 1 / 2 < omega by linarith) ha (by norm_num) ha2.le).trans (hCm a haI)
  have hsum : ‖suzukiHankelPhiSum omega a homega ha‖ ≤ Cp + Cm := by
    exact (norm_add_le _ _).trans (add_le_add hpBound hmBound)
  have hq : ‖suzukiHankelPhiSumLog omega a homega ha‖ ≤ C := by
    calc
      ‖suzukiHankelPhiSumLog omega a homega ha‖ =
          ‖suzukiHankelPhiSum omega a homega ha‖ := by
        rw [suzukiHankelPhiSumLog, suzukiHankelPhiSumPositive,
          (suzukiPositiveLogUnitary.norm_map),
          (suzukiPhysicalIntervalPositiveIsometry a).norm_map]
      _ ≤ Cp + Cm := hsum
      _ ≤ C := le_max_right _ _
  refine ⟨hq, ?_⟩
  calc
    ‖suzukiHankelPhiSumHankelLog omega a homega ha‖ =
        ‖suzukiHankelPhiSumLog omega a homega ha‖ := by
      rw [suzukiHankelPhiSumHankelLog,
        (suzukiCanonicalLogHankelUnitary omega _).norm_map]
    _ ≤ C := hq

/-! ## Continuous normalization at the endpoint -/

theorem continuousAt_suzukiHankelMuScalar_of_lt_one
    {omega a : ℝ} (homega : 1 < omega) (ha : a < 1) :
    ContinuousAt (suzukiHankelMuScalar omega homega) a := by
  have heq : suzukiHankelMuScalar omega homega =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ha] with b hb
    simp [suzukiHankelMuScalar, suzukiHankelMuReal,
      suzukiHankelBoundaryTraceReal, not_lt.mpr hb.le]
  exact continuousAt_const.congr_of_eventuallyEq heq.symm

/-- The literal normalization in equation (4.17) tends to one at `a=1`. -/
theorem continuousAt_suzukiHankelM_one
    {omega : ℝ} (homega : 1 < omega) :
    ContinuousAt (suzukiHankelM omega homega) 1 := by
  let g : ℝ → ℝ := fun b => suzukiHankelMuScalar omega homega b / b
  have hg : ContinuousOn g (Icc (1 / 2 : ℝ) (3 / 2)) := by
    intro b hb
    have hmu : ContinuousAt (suzukiHankelMuScalar omega homega) b := by
      rcases lt_trichotomy b 1 with hlt | rfl | hgt
      · exact continuousAt_suzukiHankelMuScalar_of_lt_one homega hlt
      · exact continuousAt_suzukiHankelMuScalar_one homega
      · exact continuousAt_suzukiHankelMuScalar_of_one_lt homega hgt
    exact (hmu.div continuousAt_id (by linarith [hb.1])).continuousWithinAt
  have hgInt : IntervalIntegrable g volume (1 / 2 : ℝ) (3 / 2) :=
    hg.intervalIntegrable_of_Icc (by norm_num)
  have hprim : ContinuousAt (fun a => ∫ b in (1 : ℝ)..a, g b) 1 :=
    (intervalIntegral.continuousWithinAt_primitive (measure_singleton 1) (by
      simpa using hgInt)).continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hexp := Real.continuous_exp.continuousAt.comp hprim
  simpa [suzukiHankelM, g] using hexp

theorem tendsto_suzukiHankelM_right_one
    {omega : ℝ} (homega : 1 < omega) :
    Tendsto (suzukiHankelM omega homega) (𝓝[Ioi (1 : ℝ)] 1) (𝓝 1) :=
  (continuousAt_suzukiHankelM_one homega).mono_left inf_le_left

/-! ## Right-hand compact Fourier families -/

def suzukiHankelPhiSumFourierRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) (z : ℂ) : ℂ :=
  if ha : 1 < a then
    suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumLog omega a homega ha) z
  else 0

def suzukiHankelPhiSumHankelFourierRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) (z : ℂ) : ℂ :=
  if ha : 1 < a then
    suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumHankelLog omega a homega ha) z
  else 0

private theorem integral_norm_cutoff_lt_of_log_small
    {C delta a : ℝ} (hC : 0 < C) (hdelta : 0 < delta)
    (ha : 1 < a) (hsmall : 2 * Real.log a * C ^ 2 < delta ^ 2)
    {f : SoninL2} (hf : ‖f‖ ≤ C) :
    ∫ x : ℝ, ‖(suzukiCutoff (Real.log a) f) x‖ < delta := by
  have hlog : 0 ≤ Real.log a := (Real.log_pos ha).le
  have hsq := integral_norm_suzukiCutoff_sq_le hlog f
  have hfac : 0 ≤ 2 * Real.log a := by positivity
  have hnormsq : ‖f‖ ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hC.le).2 hf
  have hupper :
      (∫ x : ℝ, ‖(suzukiCutoff (Real.log a) f) x‖) ^ 2 < delta ^ 2 :=
    lt_of_le_of_lt (hsq.trans (mul_le_mul_of_nonneg_left hnormsq hfac)) (by
      simpa [mul_assoc] using hsmall)
  nlinarith [integral_nonneg (fun _ => norm_nonneg _)]

/-- Both compact logarithmic Fredholm transforms vanish uniformly on every compact spectral set. -/
theorem tendstoUniformlyOn_suzukiHankelFourierRight_zero
    {omega : ℝ} (homega : 1 < omega) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (suzukiHankelPhiSumFourierRight omega homega)
        (fun _ => 0) (𝓝[Ioi (1 : ℝ)] 1) K ∧
      TendstoUniformlyOn (suzukiHankelPhiSumHankelFourierRight omega homega)
        (fun _ => 0) (𝓝[Ioi (1 : ℝ)] 1) K := by
  obtain ⟨C0, hC0, hbound⟩ :=
    exists_uniform_norm_bound_suzukiHankelPhiSumLog homega
  obtain ⟨R0, hR0⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  let R := max 1 R0
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let D := Real.exp (Real.log 2 * R)
  have hD : 0 < D := Real.exp_pos _
  have hlog : Tendsto (fun a : ℝ => Real.log a)
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).mono_left inf_le_left
    simpa using h
  have hsmall : Tendsto (fun a : ℝ => 2 * Real.log a * C0 ^ 2)
      (𝓝[Ioi (1 : ℝ)] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hlog).mul tendsto_const_nhds
  constructor <;> rw [Metric.tendstoUniformlyOn_iff] <;> intro epsilon hepsilon
  · have hdelta : 0 < epsilon / D := div_pos hepsilon hD
    have hsquare : 0 < (epsilon / D) ^ 2 := sq_pos_of_pos hdelta
    have hevSmall : ∀ᶠ a in 𝓝[Ioi (1 : ℝ)] 1,
        2 * Real.log a * C0 ^ 2 < (epsilon / D) ^ 2 :=
      hsmall.eventually (Iio_mem_nhds hsquare)
    have hevTwo : ∀ᶠ a in 𝓝[Ioi (1 : ℝ)] 1, a < 2 :=
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono inf_le_left
    filter_upwards [eventually_mem, hevSmall, hevTwo] with a haMem haSmall ha2 z hz
    have ha : 1 < a := haMem
    have hqNorm := (hbound a ha ha2).1
    have hL1 := integral_norm_cutoff_lt_of_log_small hC0 hdelta ha haSmall hqNorm
    have hfourier := norm_suzukiCompactL2Fourier_le (Real.log_pos ha).le
      (suzukiHankelPhiSumLog omega a homega ha) z
    have hzR : |z.im| ≤ R :=
      (Complex.abs_im_le_norm z).trans ((hR0 z hz).trans (le_max_right _ _))
    have hlog2 : Real.log a ≤ Real.log 2 := Real.strictMonoOn_log ha (by norm_num) ha2.le
    have hexp : Real.exp (Real.log a * |z.im|) ≤ D := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul hlog2 hzR (abs_nonneg _) (Real.log_nonneg (by norm_num))).trans_eq rfl
    have hnonneg : 0 ≤ ∫ x : ℝ,
        ‖(suzukiCutoff (Real.log a)
          (suzukiHankelPhiSumLog omega a homega ha)) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have hnormlt : ‖suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) z‖ < epsilon := by
      calc
        _ ≤ (∫ x : ℝ, ‖(suzukiCutoff (Real.log a)
              (suzukiHankelPhiSumLog omega a homega ha)) x‖) *
              Real.exp (Real.log a * |z.im|) := hfourier
        _ ≤ (∫ x : ℝ, ‖(suzukiCutoff (Real.log a)
              (suzukiHankelPhiSumLog omega a homega ha)) x‖) * D :=
          mul_le_mul_of_nonneg_left hexp hnonneg
        _ < (epsilon / D) * D := mul_lt_mul_of_pos_right hL1 hD
        _ = epsilon := div_mul_cancel₀ epsilon hD.ne'
    simpa [suzukiHankelPhiSumFourierRight, ha, dist_eq_norm] using hnormlt
  · have hdelta : 0 < epsilon / D := div_pos hepsilon hD
    have hsquare : 0 < (epsilon / D) ^ 2 := sq_pos_of_pos hdelta
    have hevSmall : ∀ᶠ a in 𝓝[Ioi (1 : ℝ)] 1,
        2 * Real.log a * C0 ^ 2 < (epsilon / D) ^ 2 :=
      hsmall.eventually (Iio_mem_nhds hsquare)
    have hevTwo : ∀ᶠ a in 𝓝[Ioi (1 : ℝ)] 1, a < 2 :=
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono inf_le_left
    filter_upwards [eventually_mem, hevSmall, hevTwo] with a haMem haSmall ha2 z hz
    have ha : 1 < a := haMem
    have hpNorm := (hbound a ha ha2).2
    have hL1 := integral_norm_cutoff_lt_of_log_small hC0 hdelta ha haSmall hpNorm
    have hfourier := norm_suzukiCompactL2Fourier_le (Real.log_pos ha).le
      (suzukiHankelPhiSumHankelLog omega a homega ha) z
    have hzR : |z.im| ≤ R :=
      (Complex.abs_im_le_norm z).trans ((hR0 z hz).trans (le_max_right _ _))
    have hlog2 : Real.log a ≤ Real.log 2 := Real.strictMonoOn_log ha (by norm_num) ha2.le
    have hexp : Real.exp (Real.log a * |z.im|) ≤ D := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul hlog2 hzR (abs_nonneg _) (Real.log_nonneg (by norm_num))).trans_eq rfl
    have hnonneg : 0 ≤ ∫ x : ℝ,
        ‖(suzukiCutoff (Real.log a)
          (suzukiHankelPhiSumHankelLog omega a homega ha)) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have hnormlt : ‖suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumHankelLog omega a homega ha) z‖ < epsilon := by
      calc
        _ ≤ (∫ x : ℝ, ‖(suzukiCutoff (Real.log a)
              (suzukiHankelPhiSumHankelLog omega a homega ha)) x‖) *
              Real.exp (Real.log a * |z.im|) := hfourier
        _ ≤ (∫ x : ℝ, ‖(suzukiCutoff (Real.log a)
              (suzukiHankelPhiSumHankelLog omega a homega ha)) x‖) * D :=
          mul_le_mul_of_nonneg_left hexp hnonneg
        _ < (epsilon / D) * D := mul_lt_mul_of_pos_right hL1 hD
        _ = epsilon := div_mul_cancel₀ epsilon hD.ne'
    simpa [suzukiHankelPhiSumHankelFourierRight, ha, dist_eq_norm] using hnormlt

/-! ## Compact-open algebra and elementary endpoint limits -/

/-- Multiplication preserves uniform convergence on a compact set for continuous complex-valued
families.  Multiplication is not globally uniformly continuous on `ℂ × ℂ`; compact-open
continuity is the correct infrastructure here. -/
theorem tendstoUniformlyOn_mul_of_compact
    {ι : Type*} {l : Filter ι} {F G : ι → ℂ → ℂ} {f g : ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K)
    (hFc : ∀ i, ContinuousOn (F i) K) (hGc : ∀ i, ContinuousOn (G i) K)
    (hfc : ContinuousOn f K) (hgc : ContinuousOn g K)
    (hF : TendstoUniformlyOn F f l K) (hG : TendstoUniformlyOn G g l K) :
    TendstoUniformlyOn (fun i z => F i z * G i z) (fun z => f z * g z) l K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let FC : ι → C(K, ℂ) := fun i =>
    ⟨fun z => F i z, continuousOn_iff_continuous_restrict.mp (hFc i)⟩
  let GC : ι → C(K, ℂ) := fun i =>
    ⟨fun z => G i z, continuousOn_iff_continuous_restrict.mp (hGc i)⟩
  let fc : C(K, ℂ) :=
    ⟨fun z => f z, continuousOn_iff_continuous_restrict.mp hfc⟩
  let gc : C(K, ℂ) :=
    ⟨fun z => g z, continuousOn_iff_continuous_restrict.mp hgc⟩
  have hFC : Tendsto FC l (𝓝 fc) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    simpa [FC, fc] using
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hF)
  have hGC : Tendsto GC l (𝓝 gc) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    simpa [GC, gc] using
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hG)
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simpa [FC, GC, fc, gc] using
    (ContinuousMap.tendsto_iff_tendstoUniformly.mp (hFC.mul hGC))

theorem continuous_suzukiHankelPhiSumFourierRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) :
    Continuous (suzukiHankelPhiSumFourierRight omega homega a) := by
  unfold suzukiHankelPhiSumFourierRight
  split_ifs with ha
  · exact (differentiable_suzukiCompactL2Fourier (Real.log_pos ha).le _).continuous
  · exact continuous_const

theorem continuous_suzukiHankelPhiSumHankelFourierRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) :
    Continuous (suzukiHankelPhiSumHankelFourierRight omega homega a) := by
  unfold suzukiHankelPhiSumHankelFourierRight
  split_ifs with ha
  · exact (differentiable_suzukiCompactL2Fourier (Real.log_pos ha).le _).continuous
  · exact continuous_const

private theorem tendstoUniformlyOn_comp_neg_of_compact
    {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K)
    (hF : TendstoUniformlyOn F f l ((fun z : ℂ => -z) '' K)) :
    TendstoUniformlyOn (fun i z => F i (-z)) (fun z => f (-z)) l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro epsilon hepsilon
  filter_upwards [hF epsilon hepsilon] with i hi z hz
  exact hi (-z) ⟨z, hz, rfl⟩

/-- The elementary exponential `a^(iz)` tends to one uniformly on every compact spectral set. -/
theorem tendstoUniformlyOn_suzukiHankelAiz_one
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a z => suzukiHankelAiz a z) (fun _ => 1)
      (𝓝[Ioi (1 : ℝ)] 1) K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℝ → K → ℂ := fun a z => suzukiHankelAiz a z
  have hlog : ContinuousOn (fun p : ℝ × K => Real.log p.1)
      (Ioi (0 : ℝ) ×ˢ (univ : Set K)) :=
    Real.continuousOn_log.comp continuousOn_fst (fun p hp => hp.1)
  have harg : ContinuousOn (fun p : ℝ × K =>
      I * (p.2 : ℂ) * (Real.log p.1 : ℂ))
      (Ioi (0 : ℝ) ×ˢ (univ : Set K)) :=
    (continuousOn_const.mul continuousOn_snd).mul
      (Complex.continuous_ofReal.comp_continuousOn hlog)
  have hFcont : ContinuousOn ↿F
      (Ioi (0 : ℝ) ×ˢ (univ : Set K)) := by
    simpa [F, suzukiHankelAiz] using
      Complex.continuous_exp.comp_continuousOn harg
  have hfull : TendstoUniformly F (F 1) (𝓝 (1 : ℝ)) :=
    hFcont.tendstoUniformly (Ioi_mem_nhds zero_lt_one)
  have hright : TendstoUniformly F (F 1) (𝓝[Ioi (1 : ℝ)] 1) :=
    tendstoUniformly_iff_tendstoUniformlyOnFilter.mpr
      (hfull.tendstoUniformlyOnFilter.mono_left inf_le_left)
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simpa [F, suzukiHankelAiz] using hright

theorem tendsto_suzukiHankelTildeCoefficient_right
    : Tendsto suzukiHankelTildeCoefficient (𝓝[Ioi (1 : ℝ)] 1)
        (𝓝 ((1 / 2 : ℝ) : ℂ)) := by
  have hcont : ContinuousAt suzukiHankelTildeCoefficient 1 := by
    unfold suzukiHankelTildeCoefficient
    exact Complex.continuous_ofReal.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.div_const 2)
  have h := hcont.mono_left inf_le_left
  simpa using h

/-! ## Total right representatives of the cleared and completed pairs -/

def suzukiHankelTildeEClearedRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) (z : ℂ) : ℂ :=
  suzukiCanonicalE omega z *
      (suzukiHankelAiz a z + suzukiHankelTildeCoefficient a *
        suzukiHankelPhiSumHankelFourierRight omega homega a z) +
    suzukiCanonicalE omega (-z) *
      (-suzukiHankelTildeCoefficient a *
        suzukiHankelPhiSumFourierRight omega homega a (-z))

def suzukiHankelTildeEStarClearedRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) (z : ℂ) : ℂ :=
  suzukiCanonicalE omega z *
      (-suzukiHankelTildeCoefficient a *
        suzukiHankelPhiSumFourierRight omega homega a z) +
    suzukiCanonicalE omega (-z) *
      (suzukiHankelAiz a (-z) + suzukiHankelTildeCoefficient a *
        suzukiHankelPhiSumHankelFourierRight omega homega a (-z))

def suzukiHankelCompletedARight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) (z : ℂ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ) *
    ((suzukiHankelTildeEClearedRight omega homega a z +
      suzukiHankelTildeEStarClearedRight omega homega a z) / 2)

def suzukiHankelCompletedBRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) (z : ℂ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ)⁻¹ *
    ((suzukiHankelTildeEStarClearedRight omega homega a z -
      suzukiHankelTildeEClearedRight omega homega a z) / (2 * I))

theorem suzukiHankelTildeEClearedRight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelTildeEClearedRight omega homega a =
      suzukiHankelTildeECleared omega a homega ha := by
  funext z
  simp [suzukiHankelTildeEClearedRight, suzukiHankelTildeECleared,
    suzukiHankelTildeERegularPart, suzukiHankelTildeEThetaPart,
    suzukiHankelPhiSumFourierRight,
    suzukiHankelPhiSumHankelFourierRight, ha]

theorem suzukiHankelTildeEStarClearedRight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelTildeEStarClearedRight omega homega a =
      suzukiHankelTildeEStarCleared omega a homega ha := by
  funext z
  simp [suzukiHankelTildeEStarClearedRight, suzukiHankelTildeEStarCleared,
    suzukiHankelPhiSumFourierRight,
    suzukiHankelPhiSumHankelFourierRight, ha]

theorem suzukiHankelCompletedARight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelCompletedARight omega homega a =
      suzukiHankelCompletedA omega a homega ha := by
  funext z
  rw [suzukiHankelCompletedARight, suzukiHankelCompletedA,
    suzukiHankelTildeACleared,
    suzukiHankelTildeEClearedRight_of_one_lt homega ha,
    suzukiHankelTildeEStarClearedRight_of_one_lt homega ha]

theorem suzukiHankelCompletedBRight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelCompletedBRight omega homega a =
      suzukiHankelCompletedB omega a homega ha := by
  funext z
  rw [suzukiHankelCompletedBRight, suzukiHankelCompletedB,
    suzukiHankelTildeBCleared,
    suzukiHankelTildeEClearedRight_of_one_lt homega ha,
    suzukiHankelTildeEStarClearedRight_of_one_lt homega ha]

theorem continuous_suzukiHankelTildeEClearedRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) :
    Continuous (suzukiHankelTildeEClearedRight omega homega a) := by
  unfold suzukiHankelTildeEClearedRight
  fun_prop

theorem continuous_suzukiHankelTildeEStarClearedRight
    (omega : ℝ) (homega : 1 < omega) (a : ℝ) :
    Continuous (suzukiHankelTildeEStarClearedRight omega homega a) := by
  unfold suzukiHankelTildeEStarClearedRight
  fun_prop

/-! ## Compact-uniform convergence of the two cleared numerators -/

theorem tendstoUniformlyOn_suzukiHankelClearedRight
    {omega : ℝ} (homega : 1 < omega) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (suzukiHankelTildeEClearedRight omega homega)
        (suzukiCanonicalE omega) (𝓝[Ioi (1 : ℝ)] 1) K ∧
      TendstoUniformlyOn (suzukiHankelTildeEStarClearedRight omega homega)
        (fun z => suzukiCanonicalE omega (-z)) (𝓝[Ioi (1 : ℝ)] 1) K := by
  let l : Filter ℝ := 𝓝[Ioi (1 : ℝ)] 1
  have hfourier := tendstoUniformlyOn_suzukiHankelFourierRight_zero homega hK
  have hKneg : IsCompact ((fun z : ℂ => -z) '' K) := hK.image continuous_neg
  have hfourierNeg := tendstoUniformlyOn_suzukiHankelFourierRight_zero homega hKneg
  have hq : TendstoUniformlyOn (suzukiHankelPhiSumFourierRight omega homega)
      (fun _ => 0) l K := hfourier.1
  have hp : TendstoUniformlyOn (suzukiHankelPhiSumHankelFourierRight omega homega)
      (fun _ => 0) l K := hfourier.2
  have hqNeg : TendstoUniformlyOn
      (fun a z => suzukiHankelPhiSumFourierRight omega homega a (-z))
      (fun _ => 0) l K := by
    simpa using tendstoUniformlyOn_comp_neg_of_compact hK hfourierNeg.1
  have hpNeg : TendstoUniformlyOn
      (fun a z => suzukiHankelPhiSumHankelFourierRight omega homega a (-z))
      (fun _ => 0) l K := by
    simpa using tendstoUniformlyOn_comp_neg_of_compact hK hfourierNeg.2
  have hAiz := tendstoUniformlyOn_suzukiHankelAiz_one hK
  have hAizNeg : TendstoUniformlyOn (fun a z => suzukiHankelAiz a (-z))
      (fun _ => 1) l K := by
    have hbase := tendstoUniformlyOn_suzukiHankelAiz_one hKneg
    simpa using tendstoUniformlyOn_comp_neg_of_compact hK hbase
  have hcoeff : TendstoUniformlyOn
      (fun a (_ : ℂ) => suzukiHankelTildeCoefficient a)
      (fun _ => ((1 / 2 : ℝ) : ℂ)) l K :=
    tendsto_suzukiHankelTildeCoefficient_right.tendstoUniformlyOn_const K
  have hE : TendstoUniformlyOn
      (fun _ z => suzukiCanonicalE omega z) (suzukiCanonicalE omega) l K :=
    tendsto_const_nhds.tendstoUniformlyOn_const K
  have hEneg : TendstoUniformlyOn
      (fun _ z => suzukiCanonicalE omega (-z))
      (fun z => suzukiCanonicalE omega (-z)) l K :=
    tendsto_const_nhds.tendstoUniformlyOn_const K
  have hcoeffP := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => continuous_const.continuousOn)
    (fun a => (continuous_suzukiHankelPhiSumHankelFourierRight omega homega a).continuousOn)
    continuous_const.continuousOn continuous_const.continuousOn hcoeff hp
  have hcoeffQ := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => continuous_const.continuousOn)
    (fun a => (continuous_suzukiHankelPhiSumFourierRight omega homega a).continuousOn)
    continuous_const.continuousOn continuous_const.continuousOn hcoeff hq
  have hcoeffPNeg := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => continuous_const.continuousOn)
    (fun a => ((continuous_suzukiHankelPhiSumHankelFourierRight omega homega a).comp
      continuous_neg).continuousOn)
    continuous_const.continuousOn continuous_const.continuousOn hcoeff hpNeg
  have hcoeffQNeg := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => continuous_const.continuousOn)
    (fun a => ((continuous_suzukiHankelPhiSumFourierRight omega homega a).comp
      continuous_neg).continuousOn)
    continuous_const.continuousOn continuous_const.continuousOn hcoeff hqNeg
  have hreg := hAiz.add hcoeffP
  have hregNeg := hAizNeg.add hcoeffPNeg
  have hEreg := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => (differentiable_suzukiCanonicalE omega).continuous.continuousOn)
    (fun a => ((differentiable_suzukiHankelAiz a).continuous.add
      (continuous_const.mul
        (continuous_suzukiHankelPhiSumHankelFourierRight omega homega a))).continuousOn)
    (differentiable_suzukiCanonicalE omega).continuous.continuousOn
    continuous_const.continuousOn hE hreg
  have hEregNeg := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => ((differentiable_suzukiCanonicalE omega).continuous.comp
      continuous_neg).continuousOn)
    (fun a => (((differentiable_suzukiHankelAiz a).continuous.comp continuous_neg).add
      (continuous_const.mul
        ((continuous_suzukiHankelPhiSumHankelFourierRight omega homega a).comp
          continuous_neg))).continuousOn)
    ((differentiable_suzukiCanonicalE omega).continuous.comp continuous_neg).continuousOn
    continuous_const.continuousOn hEneg hregNeg
  have hEQNeg := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => ((differentiable_suzukiCanonicalE omega).continuous.comp
      continuous_neg).continuousOn)
    (fun a => (continuous_const.mul
      ((continuous_suzukiHankelPhiSumFourierRight omega homega a).comp
        continuous_neg)).continuousOn)
    ((differentiable_suzukiCanonicalE omega).continuous.comp continuous_neg).continuousOn
    continuous_const.continuousOn hEneg hcoeffQNeg.neg
  have hEQ := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => (differentiable_suzukiCanonicalE omega).continuous.continuousOn)
    (fun a => (continuous_const.mul
      (continuous_suzukiHankelPhiSumFourierRight omega homega a)).continuousOn)
    (differentiable_suzukiCanonicalE omega).continuous.continuousOn
    continuous_const.continuousOn hE hcoeffQ.neg
  constructor
  · simpa [suzukiHankelTildeEClearedRight] using hEreg.add hEQNeg
  · simpa [suzukiHankelTildeEStarClearedRight] using hEQ.add hEregNeg

/-! ## Suzuki's published Lemma 4.10 -/

theorem tendstoUniformlyOn_suzukiHankelCompletedARight
    {omega : ℝ} (homega : 1 < omega) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (suzukiHankelCompletedARight omega homega)
      (suzukiCanonicalA omega) (𝓝[Ioi (1 : ℝ)] 1) K := by
  let l : Filter ℝ := 𝓝[Ioi (1 : ℝ)] 1
  have hcleared := tendstoUniformlyOn_suzukiHankelClearedRight homega hK
  have hsum := hcleared.1.add hcleared.2
  have hhalf : TendstoUniformlyOn
      (fun _ (_ : ℂ) => ((2 : ℂ)⁻¹)) (fun _ => ((2 : ℂ)⁻¹)) l K :=
    tendsto_const_nhds.tendstoUniformlyOn_const K
  have havg := tendstoUniformlyOn_mul_of_compact hK
    (fun a => ((continuous_suzukiHankelTildeEClearedRight omega homega a).add
      (continuous_suzukiHankelTildeEStarClearedRight omega homega a)).continuousOn)
    (fun _ => continuous_const.continuousOn)
    ((differentiable_suzukiCanonicalE omega).continuous.add
      ((differentiable_suzukiCanonicalE omega).continuous.comp continuous_neg)).continuousOn
    continuous_const.continuousOn hsum hhalf
  have hmComplex : Tendsto (fun a => (suzukiHankelM omega homega a : ℂ)) l (𝓝 1) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_suzukiHankelM_right_one homega)
  have hm := hmComplex.tendstoUniformlyOn_const (α := ℂ) K
  have hmul := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => continuous_const.continuousOn)
    (fun a => (((continuous_suzukiHankelTildeEClearedRight omega homega a).add
      (continuous_suzukiHankelTildeEStarClearedRight omega homega a)).div_const 2).continuousOn)
    continuous_const.continuousOn
    ((differentiable_suzukiCanonicalE omega).continuous.add
      ((differentiable_suzukiCanonicalE omega).continuous.comp continuous_neg) |>.div_const 2
      |>.continuousOn) hm havg
  simpa [suzukiHankelCompletedARight,
    suzukiCanonicalA_eq_E_ESharp_average, suzukiCanonicalESharp_eq_E_neg,
    div_eq_mul_inv] using hmul

theorem tendstoUniformlyOn_suzukiHankelCompletedBRight
    {omega : ℝ} (homega : 1 < omega) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (suzukiHankelCompletedBRight omega homega)
      (suzukiCanonicalB omega) (𝓝[Ioi (1 : ℝ)] 1) K := by
  let l : Filter ℝ := 𝓝[Ioi (1 : ℝ)] 1
  have hcleared := tendstoUniformlyOn_suzukiHankelClearedRight homega hK
  have hdiff := hcleared.2.sub hcleared.1
  have hden : (2 * I : ℂ) ≠ 0 := by norm_num [Complex.I_ne_zero]
  have hinvDen : TendstoUniformlyOn
      (fun _ (_ : ℂ) => (2 * I : ℂ)⁻¹) (fun _ => (2 * I : ℂ)⁻¹) l K :=
    tendsto_const_nhds.tendstoUniformlyOn_const K
  have hquot := tendstoUniformlyOn_mul_of_compact hK
    (fun a => ((continuous_suzukiHankelTildeEStarClearedRight omega homega a).sub
      (continuous_suzukiHankelTildeEClearedRight omega homega a)).continuousOn)
    (fun _ => continuous_const.continuousOn)
    (((differentiable_suzukiCanonicalE omega).continuous.comp continuous_neg).sub
      (differentiable_suzukiCanonicalE omega).continuous).continuousOn
    continuous_const.continuousOn hdiff hinvDen
  have hmComplex : Tendsto (fun a => (suzukiHankelM omega homega a : ℂ)) l (𝓝 1) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_suzukiHankelM_right_one homega)
  have hmInv : Tendsto (fun a => (suzukiHankelM omega homega a : ℂ)⁻¹) l (𝓝 1) := by
    simpa using hmComplex.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hm := hmInv.tendstoUniformlyOn_const (α := ℂ) K
  have hmul := tendstoUniformlyOn_mul_of_compact hK
    (fun _ => continuous_const.continuousOn)
    (fun a => (((continuous_suzukiHankelTildeEStarClearedRight omega homega a).sub
      (continuous_suzukiHankelTildeEClearedRight omega homega a)).div_const (2 * I)).continuousOn)
    continuous_const.continuousOn
    ((((differentiable_suzukiCanonicalE omega).continuous.comp continuous_neg).sub
      (differentiable_suzukiCanonicalE omega).continuous).div_const (2 * I)).continuousOn
    hm hquot
  simpa [suzukiHankelCompletedBRight,
    suzukiCanonicalB_eq_E_ESharp_difference, suzukiCanonicalESharp_eq_E_neg,
    div_eq_mul_inv, hden] using hmul

/-- **Suzuki (2012), Lemma 4.10, closed theorem.**  The exact completed Fredholm pair converges
to the shifted-Xi pair as `a -> 1+`, uniformly on every compact subset of `ℂ`. -/
theorem suzuki2012_lemma_four_ten :
    ∀ (omega : ℝ) (homega : 1 < omega) (K : Set ℂ), IsCompact K →
      TendstoUniformlyOn (suzukiHankelCompletedARight omega homega)
        (suzukiCanonicalA omega) (𝓝[Ioi (1 : ℝ)] 1) K ∧
      TendstoUniformlyOn (suzukiHankelCompletedBRight omega homega)
        (suzukiCanonicalB omega) (𝓝[Ioi (1 : ℝ)] 1) K := by
  intro omega homega K hK
  exact ⟨tendstoUniformlyOn_suzukiHankelCompletedARight homega hK,
    tendstoUniformlyOn_suzukiHankelCompletedBRight homega hK⟩

end RHTower
