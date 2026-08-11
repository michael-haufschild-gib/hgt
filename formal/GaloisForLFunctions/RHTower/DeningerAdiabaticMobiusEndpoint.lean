import GaloisForLFunctions.RHTower.DeningerAdiabaticMobiusPreimage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strict critical endpoint of the adiabatic Möbius inverse

The exact gauge `M_a h(x) = x^a f_(exp(-a·)h)(x)` has two simultaneous singular effects at
`a = 0`: the source moves in Meyer's projective topology and the physical multiplier `x^a`
loses uniform boundedness on the full ray.  This file closes that gap without truncating the
integer series.

The source motion is carried by the existing continuous moment maps.  The physical multiplier is
controlled by two adjacent moments, since `0 ≤ a ≤ 1` gives `x^a ≤ 1 + x`.  A separate dominated
convergence argument kills the multiplier defect on the fixed critical preimage.  Together these
give strict `L¹` convergence in every polynomial moment.
-/

namespace RHTower

open Filter Topology MeasureTheory SchwartzMap

noncomputable section

/-- Subtraction law for the canonical Möbius preimage on Meyer's source. -/
theorem deningerMobiusPreimage_sub_meyer
    (h₁ h₂ : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    deningerMobiusPreimage
        (((DeningerMeyerSource.toSource (h₁ - h₂) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ))) x =
      deningerMobiusPreimage
          (((DeningerMeyerSource.toSource h₁ : DeningerExpSchwartz) :
            𝓢(ℝ, ℂ))) x -
        deningerMobiusPreimage
          (((DeningerMeyerSource.toSource h₂ : DeningerExpSchwartz) :
            𝓢(ℝ, ℂ))) x := by
  have hadd := deningerMobiusPreimage_add
    (DeningerMeyerSource.toSource (h₁ - h₂)).2
    (DeningerMeyerSource.toSource h₂).2 hx
  have hsource :
      (((DeningerMeyerSource.toSource (h₁ - h₂) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ))) +
        (((DeningerMeyerSource.toSource h₂ : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ))) =
      (((DeningerMeyerSource.toSource h₁ : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ))) := by
    apply SchwartzMap.ext
    intro t
    change ((DeningerMeyerSource.toSource h₁ : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ)) t -
      ((DeningerMeyerSource.toSource h₂ : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ)) t +
      ((DeningerMeyerSource.toSource h₂ : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ)) t = _
    abel
  rw [hsource] at hadd
  exact eq_sub_of_add_eq hadd.symm

/-- Defect made by replacing the physical multiplier `x^a` by its critical value `1`. -/
def deningerAdiabaticBoundaryError
    (a : ℝ) (r : ℕ) (h : DeningerMeyerSource) (x : ℝ) : ℂ :=
  (((x ^ a - 1 : ℝ)) : ℂ) * deningerMomentFun r h x

theorem deningerAdiabaticBoundaryError_aestronglyMeasurable
    (a : ℝ) (r : ℕ) (h : DeningerMeyerSource) :
    AEStronglyMeasurable (deningerAdiabaticBoundaryError a r h)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hpow : AEStronglyMeasurable (fun x : ℝ => ((x ^ a : ℝ) : ℂ))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun _ hx => Or.inl hx.ne')).aestronglyMeasurable
        measurableSet_Ioi
  have hone : AEStronglyMeasurable (fun _ : ℝ => (1 : ℂ))
      (volume.restrict (Set.Ioi (0 : ℝ))) := aestronglyMeasurable_const
  refine ((hpow.sub hone).mul (deningerMomentFun_memLp r h).1).congr ?_
  filter_upwards with x
  simp only [deningerAdiabaticBoundaryError, Pi.sub_apply, Pi.mul_apply]
  push_cast
  rfl

/-- Two-adjacent-moment domination of the physical multiplier defect. -/
theorem deningerAdiabaticBoundaryError_norm_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℕ)
    (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    ‖deningerAdiabaticBoundaryError a r h x‖ ≤
      2 * ‖deningerMomentFun r h x‖ + ‖deningerMomentFun (r + 1) h x‖ := by
  have hpow : x ^ a ≤ 1 + x := by
    have ha1' : a ≤ ((1 : ℕ) : ℝ) := by simpa using ha1
    simpa using deninger_rpow_le_one_add_pow ha0 (N := 1) ha1' hx
  have habs : |x ^ a - 1| ≤ 2 + x := by
    calc
      |x ^ a - 1| ≤ |x ^ a| + |(1 : ℝ)| := abs_sub _ _
      _ = x ^ a + 1 := by
        rw [abs_of_nonneg (Real.rpow_nonneg hx.le _), abs_one]
      _ ≤ (1 + x) + 1 := by linarith
      _ = 2 + x := by ring
  let f : ℂ := deningerMobiusPreimage
    (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x
  simp only [deningerAdiabaticBoundaryError, deningerMomentFun, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hx.le r),
    abs_of_nonneg (pow_nonneg hx.le (r + 1))]
  change |x ^ a - 1| * (x ^ r * ‖f‖) ≤
    2 * (x ^ r * ‖f‖) + x ^ (r + 1) * ‖f‖
  calc
    |x ^ a - 1| * (x ^ r * ‖f‖) ≤ (2 + x) * (x ^ r * ‖f‖) := by
      gcongr
    _ = 2 * (x ^ r * ‖f‖) + x ^ (r + 1) * ‖f‖ := by
      rw [pow_succ]
      ring

/-- The adjacent-moment majorant is integrable on the full positive ray. -/
theorem deningerAdiabaticBoundaryMajorant_integrable
    (r : ℕ) (h : DeningerMeyerSource) :
    Integrable
      (fun x : ℝ => 2 * ‖deningerMomentFun r h x‖ +
        ‖deningerMomentFun (r + 1) h x‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hr : Integrable (deningerMomentFun r h)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    memLp_one_iff_integrable.mp (deningerMomentFun_memLp r h)
  have hr1 : Integrable (deningerMomentFun (r + 1) h)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    memLp_one_iff_integrable.mp (deningerMomentFun_memLp (r + 1) h)
  exact (hr.norm.const_mul 2).add hr1.norm

/-- The fixed-critical-source physical multiplier defect vanishes in every `L¹` moment. -/
theorem tendsto_integral_norm_deningerAdiabaticBoundaryError
    (r : ℕ) (h : DeningerMeyerSource) :
    Tendsto
      (fun a : ℝ => ∫ x in Set.Ioi (0 : ℝ),
        ‖deningerAdiabaticBoundaryError a r h x‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let B : ℝ → ℝ := fun x => 2 * ‖deningerMomentFun r h x‖ +
    ‖deningerMomentFun (r + 1) h x‖
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (G := ℝ) B
    (F := fun a x => ‖deningerAdiabaticBoundaryError a r h x‖)
    (f := fun _ => 0)
    (by
      filter_upwards with a
      exact (deningerAdiabaticBoundaryError_aestronglyMeasurable a r h).norm)
    (by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with a ha
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [B, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        deningerAdiabaticBoundaryError_norm_le ha.1.le ha.2.le r h hx)
    (deningerAdiabaticBoundaryMajorant_integrable r h)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hrpow : Tendsto (fun a : ℝ => x ^ a) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hfull := (Real.continuousAt_const_rpow (a := x) (b := 0) hx.ne').tendsto
        simpa only [Real.rpow_zero] using hfull.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
      have hcomplex : Tendsto (fun a : ℝ => (((x ^ a - 1 : ℝ)) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp
          (hrpow.sub_const 1)
        convert hc using 1
        · funext a
          simp only [Function.comp_apply]
        · norm_num
      simpa only [deningerAdiabaticBoundaryError, norm_zero, zero_mul] using
        (hcomplex.mul_const (deningerMomentFun r h x)).norm)
  simpa only [μ, integral_zero] using hDCT

/-- The tilted source converges to the original source in Meyer's projective topology. -/
theorem tendsto_deningerAdiabaticSource_zero (h : DeningerMeyerSource) :
    Tendsto (fun a : ℝ => deningerAdiabaticSource a h) (𝓝 0) (𝓝 h) := by
  simpa only [deningerAdiabaticSource] using tendsto_deningerExpMul_neg_zero h

/-- Multiplying a moving critical moment by `x^a`, for `0 ≤ a ≤ 1`, costs at most its two
adjacent moment norms. -/
theorem deningerAdiabaticMovingMoment_norm_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℕ)
    (q : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    ‖((x ^ a : ℝ) : ℂ) * deningerMomentFun r q x‖ ≤
      ‖deningerMomentFun r q x‖ + ‖deningerMomentFun (r + 1) q x‖ := by
  have hpow : x ^ a ≤ 1 + x := by
    have ha1' : a ≤ ((1 : ℕ) : ℝ) := by simpa using ha1
    simpa using deninger_rpow_le_one_add_pow ha0 (N := 1) ha1' hx
  let f : ℂ := deningerMobiusPreimage
    (((DeningerMeyerSource.toSource q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x
  simp only [deningerMomentFun, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le a),
    abs_of_nonneg (pow_nonneg hx.le r),
    abs_of_nonneg (pow_nonneg hx.le (r + 1))]
  change x ^ a * (x ^ r * ‖f‖) ≤ x ^ r * ‖f‖ + x ^ (r + 1) * ‖f‖
  calc
    x ^ a * (x ^ r * ‖f‖) ≤ (1 + x) * (x ^ r * ‖f‖) := by gcongr
    _ = x ^ r * ‖f‖ + x ^ (r + 1) * ‖f‖ := by
      rw [pow_succ]
      ring

/-- Pointwise decomposition of the full moving adiabatic moment into source motion and the fixed
physical multiplier defect. -/
theorem deningerAdiabaticMoment_difference_norm_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℕ)
    (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    ‖deningerAdiabaticMomentFun a r h x - deningerMomentFun r h x‖ ≤
      ‖deningerMomentFun r (deningerAdiabaticSource a h - h) x‖ +
        ‖deningerMomentFun (r + 1) (deningerAdiabaticSource a h - h) x‖ +
        ‖deningerAdiabaticBoundaryError a r h x‖ := by
  let q : DeningerMeyerSource := deningerAdiabaticSource a h - h
  have hpre := deningerMobiusPreimage_sub_meyer
    (deningerAdiabaticSource a h) h hx
  have hdecomp :
      deningerAdiabaticMomentFun a r h x - deningerMomentFun r h x =
        ((x ^ a : ℝ) : ℂ) * deningerMomentFun r q x +
          deningerAdiabaticBoundaryError a r h x := by
    simp only [deningerAdiabaticMomentFun, deningerAdiabaticMobiusPreimage,
      deningerMomentFun, deningerAdiabaticBoundaryError, q]
    rw [hpre]
    push_cast
    ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  simpa only [q, add_assoc] using add_le_add
    (deningerAdiabaticMovingMoment_norm_le ha0 ha1 r q hx)
    (le_refl ‖deningerAdiabaticBoundaryError a r h x‖)

/-- Quantitative strict-endpoint estimate.  It separates source motion (two continuous critical
moment maps) from the fixed-source multiplier defect (dominated convergence). -/
theorem deningerAdiabaticMomentLp_dist_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℕ)
    (h : DeningerMeyerSource) :
    dist (deningerAdiabaticMomentLp ha0 r h) (deningerMomentLp r h) ≤
      ‖deningerMomentLp r (deningerAdiabaticSource a h - h)‖ +
        ‖deningerMomentLp (r + 1) (deningerAdiabaticSource a h - h)‖ +
        ∫ x in Set.Ioi (0 : ℝ), ‖deningerAdiabaticBoundaryError a r h x‖ := by
  rw [L1.dist_eq_integral_dist]
  have hleft : Integrable
      (fun x : ℝ => dist ((deningerAdiabaticMomentLp ha0 r h) x)
        ((deningerMomentLp r h) x))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    by
      simpa only [dist_eq_norm, Pi.sub_apply] using
        ((L1.integrable_coeFn (deningerAdiabaticMomentLp ha0 r h)).sub
          (L1.integrable_coeFn (deningerMomentLp r h))).norm
  have hq0 : Integrable
      (deningerMomentFun r (deningerAdiabaticSource a h - h))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    memLp_one_iff_integrable.mp
      (deningerMomentFun_memLp r (deningerAdiabaticSource a h - h))
  have hq1 : Integrable
      (deningerMomentFun (r + 1) (deningerAdiabaticSource a h - h))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    memLp_one_iff_integrable.mp
      (deningerMomentFun_memLp (r + 1) (deningerAdiabaticSource a h - h))
  have hb : Integrable (deningerAdiabaticBoundaryError a r h)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Integrable.mono'
      (deningerAdiabaticBoundaryMajorant_integrable r h)
      (deningerAdiabaticBoundaryError_aestronglyMeasurable a r h) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deningerAdiabaticBoundaryError_norm_le ha0 ha1 r h hx
  have hright : Integrable
      (fun x : ℝ => ‖deningerMomentFun r (deningerAdiabaticSource a h - h) x‖ +
        ‖deningerMomentFun (r + 1) (deningerAdiabaticSource a h - h) x‖ +
        ‖deningerAdiabaticBoundaryError a r h x‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hq0.norm.add hq1.norm).add hb.norm
  have hmono := integral_mono_ae hleft hright (by
    filter_upwards [
      MemLp.coeFn_toLp (deningerAdiabaticMomentFun_memLp ha0 r h),
      MemLp.coeFn_toLp (deningerMomentFun_memLp r h),
      ae_restrict_mem measurableSet_Ioi] with x hxa hx0 hx
    change dist
      (((deningerAdiabaticMomentFun_memLp ha0 r h).toLp
        (deningerAdiabaticMomentFun a r h)) x)
      (((deningerMomentFun_memLp r h).toLp (deningerMomentFun r h)) x) ≤ _
    rw [hxa, hx0]
    simpa only [dist_eq_norm] using
      deningerAdiabaticMoment_difference_norm_le ha0 ha1 r h hx)
  refine hmono.trans_eq ?_
  calc
    (∫ x in Set.Ioi (0 : ℝ),
        (‖deningerMomentFun r (deningerAdiabaticSource a h - h) x‖ +
          ‖deningerMomentFun (r + 1) (deningerAdiabaticSource a h - h) x‖) +
          ‖deningerAdiabaticBoundaryError a r h x‖) =
        (∫ x in Set.Ioi (0 : ℝ),
          ‖deningerMomentFun r (deningerAdiabaticSource a h - h) x‖ +
            ‖deningerMomentFun (r + 1) (deningerAdiabaticSource a h - h) x‖) +
          ∫ x in Set.Ioi (0 : ℝ), ‖deningerAdiabaticBoundaryError a r h x‖ := by
            exact integral_add (hq0.norm.add hq1.norm) hb.norm
    _ = ((∫ x in Set.Ioi (0 : ℝ),
          ‖deningerMomentFun r (deningerAdiabaticSource a h - h) x‖) +
        (∫ x in Set.Ioi (0 : ℝ),
          ‖deningerMomentFun (r + 1) (deningerAdiabaticSource a h - h) x‖)) +
        ∫ x in Set.Ioi (0 : ℝ), ‖deningerAdiabaticBoundaryError a r h x‖ := by
          rw [integral_add hq0.norm hq1.norm]
    _ = _ := by
      rw [← deningerMomentLp_norm r (deningerAdiabaticSource a h - h),
        ← deningerMomentLp_norm (r + 1) (deningerAdiabaticSource a h - h)]

/-- **Strict all-prime critical endpoint.**  For every polynomial moment, the full adiabatic
Möbius inverse converges in `L¹(0,∞)` to the canonical critical inverse as `a ↓ 0`. -/
theorem tendsto_deningerAdiabaticMomentLp_zero
    (r : ℕ) (h : DeningerMeyerSource) :
    Tendsto
      (fun a : Set.Ioi (0 : ℝ) =>
        deningerAdiabaticMomentLp a.property.le r h)
      atBot (𝓝 (deningerMomentLp r h)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  let q : ℝ → DeningerMeyerSource := fun a => deningerAdiabaticSource a h - h
  have hsource : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hs : Tendsto (fun a : ℝ => deningerAdiabaticSource a h)
        (𝓝[>] (0 : ℝ)) (𝓝 h) :=
      (tendsto_deningerAdiabaticSource_zero h).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    have hh : Tendsto (fun _ : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 h) :=
      tendsto_const_nhds
    simpa only [q, sub_self] using hs.sub hh
  have hr : Tendsto (fun a : ℝ => ‖deningerMomentLp r (q a)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hm := (deningerMomentCLM r).continuous.continuousAt.tendsto.comp hsource
    have happ : ∀ u : DeningerMeyerSource,
        deningerMomentCLM r u = deningerMomentLp r u := fun _ => rfl
    have hzero : deningerMomentLp r 0 = 0 := by
      rw [← happ]
      exact map_zero _
    simpa only [Function.comp_apply, happ, hzero, norm_zero] using hm.norm
  have hr1 : Tendsto (fun a : ℝ => ‖deningerMomentLp (r + 1) (q a)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hm := (deningerMomentCLM (r + 1)).continuous.continuousAt.tendsto.comp hsource
    have happ : ∀ u : DeningerMeyerSource,
        deningerMomentCLM (r + 1) u = deningerMomentLp (r + 1) u := fun _ => rfl
    have hzero : deningerMomentLp (r + 1) 0 = 0 := by
      rw [← happ]
      exact map_zero _
    simpa only [Function.comp_apply, happ, hzero, norm_zero] using hm.norm
  have hb := tendsto_integral_norm_deningerAdiabaticBoundaryError r h
  have hmajor : Tendsto
      (fun a : ℝ => ‖deningerMomentLp r (q a)‖ +
        ‖deningerMomentLp (r + 1) (q a)‖ +
        ∫ x in Set.Ioi (0 : ℝ), ‖deningerAdiabaticBoundaryError a r h x‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hr.add hr1).add hb
  have hcoe : Tendsto ((↑) : Set.Ioi (0 : ℝ) → ℝ) atBot (𝓝[>] (0 : ℝ)) :=
    (tendsto_Ioi_atBot (a := (0 : ℝ))).mp tendsto_id
  apply squeeze_zero'
  · filter_upwards with a
    exact dist_nonneg
  · have hsmall := hcoe.eventually (Ioo_mem_nhdsGT zero_lt_one)
    filter_upwards [hsmall] with a ha
    simpa only [q] using
      deningerAdiabaticMomentLp_dist_le a.property.le ha.2.le r h
  · exact hmajor.comp hcoe

end

end RHTower
