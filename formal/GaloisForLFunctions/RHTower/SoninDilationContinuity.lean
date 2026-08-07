import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Strong continuity of the normalized dilation group on `L²(ℝ)`

The normalized dilations `(D_v f)(t) = sqrt v * f (v t)` form a group of isometries of `L²(ℝ)`.
This module proves that the group acts strongly continuously: `v ↦ D_v f` is continuous from the
positive ray into `L²(ℝ)` for every fixed `f`.

The proof is the standard three-epsilon argument.  Continuity at an arbitrary scale reduces by the
group law and isometry to continuity at the scale `1`.  There it holds for a continuous compactly
supported vector by dominated convergence, with the two-sided dilate of one compact support as the
dominating set, and transfers to an arbitrary vector because such functions are dense in `L²`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Normalized dilation of `L²(ℝ)`, extended by zero to non-positive scales. -/
def rayDilate (v : ℝ) (f : SoninL2) : SoninL2 :=
  if h : 0 < v then dilation v h f else 0

theorem rayDilate_of_pos {v : ℝ} (hv : 0 < v) (f : SoninL2) :
    rayDilate v f = dilation v hv f := dif_pos hv

@[simp] theorem norm_rayDilate {v : ℝ} (hv : 0 < v) (f : SoninL2) :
    ‖rayDilate v f‖ = ‖f‖ := by
  rw [rayDilate_of_pos hv]
  exact (dilation v hv).norm_map f

theorem rayDilate_sub {v : ℝ} (hv : 0 < v) (f g : SoninL2) :
    rayDilate v f - rayDilate v g = rayDilate v (f - g) := by
  rw [rayDilate_of_pos hv, rayDilate_of_pos hv, rayDilate_of_pos hv, ← map_sub]

theorem dilation_dilation {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (f : SoninL2) :
    dilation r hr (dilation s hs f) = dilation (r * s) (mul_pos hr hs) f := by
  apply Lp.ext
  have hinner := (dilation_ae s hs f).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [dilation_ae r hr (dilation s hs f), hinner,
    dilation_ae (r * s) (mul_pos hr hs) f] with x hout hin htarget
  rw [hout, htarget]
  have hin' : dilation s hs f (r * x) =
      (Real.sqrt s : ℂ) * f (s * (r * x)) := by
    simpa only [Function.comp_apply] using hin
  rw [hin']
  have hsqrt : Real.sqrt (r * s) = Real.sqrt r * Real.sqrt s :=
    Real.sqrt_mul hr.le s
  rw [hsqrt]
  push_cast
  ring_nf

theorem rayDilate_ae {v : ℝ} (hv : 0 < v) (f : SoninL2) :
    (rayDilate v f : ℝ → ℂ) =ᵐ[volume] fun t : ℝ => (Real.sqrt v : ℂ) * f (v * t) := by
  rw [rayDilate_of_pos hv]
  exact dilation_ae v hv f

/-- The squared `L²` distance between a dilate and its vector as an explicit integral. -/
theorem norm_sq_rayDilate_sub_self {v : ℝ} (hv : 0 < v) (f : SoninL2) :
    ‖rayDilate v f - f‖ ^ 2 =
      ∫ t : ℝ, ‖(Real.sqrt v : ℂ) * f (v * t) - f t‖ ^ 2 := by
  rw [norm_sq_lp_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (rayDilate v f) f, rayDilate_ae hv f] with t hsub hdil
  rw [hsub, Pi.sub_apply, hdil]

/-! ## Continuity at the scale one for a continuous compactly supported vector -/

private theorem tendsto_integral_dilate_sub_sq
    {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Tendsto (fun v : ℝ => ∫ t : ℝ, ‖(Real.sqrt v : ℂ) * g (v * t) - g t‖ ^ 2)
      (𝓝 (1 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hgs.exists_bound_of_continuous hgc
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  obtain ⟨R, hR⟩ := hgs.isBounded.subset_closedBall (0 : ℝ)
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : ∀ t : ℝ, g t ≠ 0 → |t| ≤ R' := by
    intro t ht
    have h1 : t ∈ tsupport g := subset_tsupport g ht
    have h2 : t ∈ Metric.closedBall (0 : ℝ) R := hR h1
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
    exact le_trans h2 (le_max_left _ _)
  set K : ℝ := (Real.sqrt 2 * C + C) ^ 2 with hK
  set bound : ℝ → ℝ := (Icc (-(2 * R')) (2 * R')).indicator (fun _ => K) with hbound
  have hboundint : Integrable bound volume := by
    rw [hbound]
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp) (by simp)
  have hzero : (∫ t : ℝ, ‖(Real.sqrt (1 : ℝ) : ℂ) * g (1 * t) - g t‖ ^ 2) = 0 := by
    simp
  rw [← hzero]
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hboundint ?_
  · filter_upwards with v
    exact (((Complex.continuous_ofReal.comp
      (continuous_const : Continuous fun _ : ℝ => Real.sqrt v)).mul
        (hgc.comp (continuous_const.mul continuous_id))).sub hgc).norm.pow 2
        |>.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ)/2 < 1) (by norm_num : (1:ℝ) < 2)] with v hv
    filter_upwards with t
    have hv0 : 0 < v := lt_trans (by norm_num) hv.1
    have hsq : Real.sqrt v ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hv.2.le
    have hpt : ‖(Real.sqrt v : ℂ) * g (v * t) - g t‖ ≤ Real.sqrt 2 * C + C := by
      refine le_trans (norm_sub_le _ _) ?_
      gcongr
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg v)]
        exact mul_le_mul hsq (hC _) (norm_nonneg _) (Real.sqrt_nonneg 2)
      · exact hC t
    by_cases hmem : t ∈ Icc (-(2 * R')) (2 * R')
    · rw [hbound, Set.indicator_of_mem hmem]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hpt 2
    · have hzero1 : g t = 0 := by
        by_contra h
        exact hmem (by
          have := hsupp t h
          rw [mem_Icc]
          constructor <;> [linarith [abs_le.mp this |>.1, hR'pos];
            linarith [abs_le.mp this |>.2, hR'pos]])
      have hzero2 : g (v * t) = 0 := by
        by_contra h
        have habs := hsupp _ h
        rw [abs_mul, abs_of_pos hv0] at habs
        have hvt : |t| ≤ R' / v := by
          rw [le_div_iff₀ hv0]
          linarith [habs]
        have : |t| ≤ 2 * R' := by
          have hvinv : R' / v ≤ 2 * R' := by
            rw [div_le_iff₀ hv0]
            nlinarith [hv.1, hR'pos]
          linarith
        exact hmem (by rw [mem_Icc]; constructor <;>
          [linarith [abs_le.mp this |>.1]; linarith [abs_le.mp this |>.2]])
      rw [hzero1, hzero2, hbound, Set.indicator_of_notMem hmem]
      simp
  · filter_upwards with t
    have hcont : Tendsto (fun v : ℝ => (Real.sqrt v : ℂ) * g (v * t) - g t)
        (𝓝 (1 : ℝ)) (𝓝 ((Real.sqrt (1:ℝ) : ℂ) * g (1 * t) - g t)) := by
      refine Tendsto.sub (Tendsto.mul ?_ ?_) tendsto_const_nhds
      · exact (Complex.continuous_ofReal.tendsto _).comp
          (Real.continuous_sqrt.tendsto (1 : ℝ))
      · exact (hgc.tendsto _).comp
          ((continuous_id.mul continuous_const).tendsto (1 : ℝ))
    exact (hcont.norm.pow 2)

private theorem tendsto_norm_rayDilate_sub_self_of_compactSupport
    {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgm : MemLp g 2 volume) :
    Tendsto (fun v : ℝ => ‖rayDilate v (hgm.toLp g) - hgm.toLp g‖) (𝓝 (1 : ℝ)) (𝓝 0) := by
  have hsq : Tendsto (fun v : ℝ => ‖rayDilate v (hgm.toLp g) - hgm.toLp g‖ ^ 2)
      (𝓝 (1 : ℝ)) (𝓝 0) := by
    have hev : (fun v : ℝ => ‖rayDilate v (hgm.toLp g) - hgm.toLp g‖ ^ 2) =ᶠ[𝓝 (1 : ℝ)]
        (fun v : ℝ => ∫ t : ℝ, ‖(Real.sqrt v : ℂ) * g (v * t) - g t‖ ^ 2) := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (0:ℝ) < 1)] with v hv
      rw [norm_sq_rayDilate_sub_self hv]
      apply integral_congr_ae
      have hae := hgm.coeFn_toLp
      have hae2 : (fun t : ℝ => (hgm.toLp g : ℝ → ℂ) (v * t)) =ᵐ[volume]
          fun t : ℝ => g (v * t) := by
        have hqmp := (realMul_quasiMeasurePreserving v (ne_of_gt hv)).tendsto_ae
        simpa only [Function.comp_def] using hae.comp_tendsto hqmp
      filter_upwards [hae, hae2] with t h1 h2
      rw [h1, h2]
    exact Tendsto.congr' (Filter.EventuallyEq.symm hev)
      (tendsto_integral_dilate_sub_sq hgc hgs)
  have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at this
  refine this.congr fun v => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-! ## Strong continuity -/

/-- **Strong continuity at the scale one.** -/
theorem tendsto_norm_rayDilate_sub_self (f : SoninL2) :
    Tendsto (fun v : ℝ => ‖rayDilate v f - f‖) (𝓝 (1 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hgs, hgle, hgc, hgm⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (μ := volume) (p := 2)
      (by norm_num) (ε := ENNReal.ofReal (ε / 4))
      (by simp [ENNReal.ofReal_eq_zero]; linarith)
  set G : SoninL2 := hgm.toLp g with hG
  have hFG : ‖f - G‖ ≤ ε / 4 := by
    rw [Lp.norm_def]
    have hcong : (fun x => (f : ℝ → ℂ) x - g x) =ᵐ[volume] ((f - G : SoninL2) : ℝ → ℂ) := by
      filter_upwards [Lp.coeFn_sub f G, hgm.coeFn_toLp] with x h1 h2
      rw [h1, Pi.sub_apply, h2]
    rw [← eLpNorm_congr_ae hcong]
    have : eLpNorm ((f : ℝ → ℂ) - g) 2 volume ≤ ENNReal.ofReal (ε / 4) := hgle
    calc (eLpNorm (fun x => (f : ℝ → ℂ) x - g x) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 4)).toReal := by
          apply ENNReal.toReal_mono (by simp)
          exact this
      _ = ε / 4 := ENNReal.toReal_ofReal (by linarith)
  have hGtend := tendsto_norm_rayDilate_sub_self_of_compactSupport hgc hgs hgm
  rw [Metric.tendsto_nhds] at hGtend
  have hev := hGtend (ε / 4) (by linarith)
  filter_upwards [hev, Ioi_mem_nhds (by norm_num : (0:ℝ) < 1)] with v hvG hv
  have hsplit : ‖rayDilate v f - f‖ ≤
      ‖rayDilate v (f - G)‖ + ‖rayDilate v G - G‖ + ‖G - f‖ := by
    calc ‖rayDilate v f - f‖
        = ‖(rayDilate v f - rayDilate v G) + (rayDilate v G - G) + (G - f)‖ := by
          congr 1; abel
      _ ≤ ‖rayDilate v f - rayDilate v G‖ + ‖rayDilate v G - G‖ + ‖G - f‖ := by
          exact le_trans (norm_add_le _ _) (by gcongr; exact norm_add_le _ _)
      _ = ‖rayDilate v (f - G)‖ + ‖rayDilate v G - G‖ + ‖G - f‖ := by
          rw [rayDilate_sub hv]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hvG
  have h1 : ‖rayDilate v (f - G)‖ = ‖f - G‖ := norm_rayDilate hv _
  have h2 : ‖G - f‖ = ‖f - G‖ := norm_sub_rev _ _
  rw [h1, h2] at hsplit
  linarith

/-- **Strong continuity of the dilation group.** -/
theorem continuousOn_rayDilate (f : SoninL2) :
    ContinuousOn (fun v : ℝ => rayDilate v f) (Ioi (0 : ℝ)) := by
  intro v₀ hv₀
  have hv₀pos : 0 < v₀ := hv₀
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hkey := tendsto_norm_rayDilate_sub_self f
  rw [Metric.tendsto_nhds] at hkey
  have hev := hkey ε hε
  have hcont : Tendsto (fun v : ℝ => v / v₀) (𝓝[Ioi (0:ℝ)] v₀) (𝓝 (1 : ℝ)) := by
    have : Tendsto (fun v : ℝ => v / v₀) (𝓝 v₀) (𝓝 (v₀ / v₀)) :=
      (continuous_id.div_const v₀).tendsto v₀
    rw [div_self (ne_of_gt hv₀pos)] at this
    exact this.mono_left nhdsWithin_le_nhds
  filter_upwards [hcont.eventually hev, self_mem_nhdsWithin] with v hvq hvpos
  have hvpos' : 0 < v := hvpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hvq
  have hq : 0 < v / v₀ := div_pos hvpos' hv₀pos
  have hcomp : rayDilate v₀ (rayDilate (v / v₀) f) = rayDilate v f := by
    rw [rayDilate_of_pos hv₀pos, rayDilate_of_pos hq, rayDilate_of_pos hvpos',
      dilation_dilation hv₀pos hq f]
    congr 1
    field_simp
  have hfactor : rayDilate v f - rayDilate v₀ f =
      rayDilate v₀ (rayDilate (v / v₀) f - f) := by
    rw [← rayDilate_sub hv₀pos, hcomp]
  rw [dist_eq_norm, hfactor, norm_rayDilate hv₀pos]
  exact hvq

end RHTower
