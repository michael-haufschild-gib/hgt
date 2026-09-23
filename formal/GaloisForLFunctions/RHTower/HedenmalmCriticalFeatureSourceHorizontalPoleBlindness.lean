import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSourcePlemeljTrace
import GaloisForLFunctions.RHTower.XiWeilCriterionConverse

/-!
# Horizontal-pole blindness of the HCF source density

The HCF positive-shift source uses the imaginary part of a logarithmic
derivative while its observation variable moves horizontally.  At a zero on
that horizontal line, the local logarithmic pole is `m / (x - x₀)`, which is
real.  Therefore the source density annihilates the entire positive
multiplicity residue and agrees off the zero with the imaginary part of the
analytic cofactor.

This closes a source-side no-go relevant to the HCF `L¹` producer gate:
horizontal zero crossings cannot be detected by an `L¹` bound on this scalar
source.  A useful replacement must retain transverse information, for
example a quadratic frame across the shift parameter.
-/

open Complex Filter Topology Metric Set MeasureTheory
open RHTower.RealBoundaryDivisor

namespace RHTower

noncomputable section

private theorem im_div_ofReal_mul_I (m r : ℝ) :
    ((m : ℂ) / ((r : ℂ) * I)).im = -m / r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  simp [div_eq_mul_inv, hr]

/-- On a horizontal positive-shift scan, the continued pole--Gamma source
annihilates the complete local logarithmic pole.  Away from the zero, it is
exactly the imaginary logarithmic derivative of the analytic nonvanishing
cofactor. -/
theorem criticalFeaturePositiveShiftPoleGammaDensity_eq_cofactor_im_of_horizontal_factor
    {x x0 eta R : ℝ} {g : ℂ → ℂ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hgan : AnalyticOnNhd ℂ g
      (ball ((x0 : ℂ) + (eta : ℂ) * I) R))
    (hg0 : ∀ z ∈ ball ((x0 : ℂ) + (eta : ℂ) * I) R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ((x0 : ℂ) + (eta : ℂ) * I) R,
      XiC z = (z - ((x0 : ℂ) + (eta : ℂ) * I)) ^
        (analyticOrderAt XiC ((x0 : ℂ) + (eta : ℂ) * I)).toNat * g z)
    (hx : (x : ℂ) + (eta : ℂ) * I ∈
      ball ((x0 : ℂ) + (eta : ℂ) * I) R)
    (hne : x ≠ x0) :
    criticalFeaturePositiveShiftPoleGammaDensity eta x =
      -(Real.pi)⁻¹ * (logDeriv g ((x : ℂ) + (eta : ℂ) * I)).im := by
  let z : ℂ := (x : ℂ) + (eta : ℂ) * I
  let p : ℂ := (x0 : ℂ) + (eta : ℂ) * I
  have hzne : z ≠ p := by
    intro h
    apply hne
    simpa [z, p] using congrArg Complex.re h
  have hXi : XiC z ≠ 0 := by
    rw [hfact z (by simpa [z, p] using hx)]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzne))
      (hg0 z (by simpa [z, p] using hx))
  have hXiLower : XiC ((x : ℂ) - (eta : ℂ) * I) ≠ 0 := by
    have hconj := XiC_ne_zero_conj hXi
    have hcoord : (starRingEnd ℂ) z = (x : ℂ) - (eta : ℂ) * I := by
      simp only [z, map_add, map_mul, conj_ofReal, conj_I]
      ring
    rwa [hcoord] at hconj
  have hsource := boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
    heta0 hetaHalf hXiLower
  have hpole := logDeriv_XiC_eq_pole_add hgan hg0 hfact
    (by simpa [z, p] using hx) hzne
  have hdiff : z - p = ((x - x0 : ℝ) : ℂ) := by
    simp [z, p]
  rw [← hsource, boundaryDensity, hpole, Complex.add_im, hdiff]
  rw [div_eq_mul_inv]
  simp [z]

/-- On a vertical scan through a positive-shift Xi zero, the source retains
the complete logarithmic pole.  Its signed coefficient is the positive
multiplicity divided by `π`; only the analytic cofactor remains after this
principal part. -/
theorem criticalFeaturePositiveShiftPoleGammaDensity_eq_transverse_pole_sub_cofactor_im_of_vertical_factor
    {eta eta0 x0 R : ℝ} {g : ℂ → ℂ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hgan : AnalyticOnNhd ℂ g
      (ball ((x0 : ℂ) + (eta0 : ℂ) * I) R))
    (hg0 : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R,
      XiC z = (z - ((x0 : ℂ) + (eta0 : ℂ) * I)) ^
        (analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat * g z)
    (hmem : (x0 : ℂ) + (eta : ℂ) * I ∈
      ball ((x0 : ℂ) + (eta0 : ℂ) * I) R)
    (hne : eta ≠ eta0) :
    criticalFeaturePositiveShiftPoleGammaDensity eta x0 =
      (Real.pi)⁻¹ *
        ((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℝ) /
          (eta - eta0) -
      (Real.pi)⁻¹ * (logDeriv g ((x0 : ℂ) + (eta : ℂ) * I)).im := by
  let z : ℂ := (x0 : ℂ) + (eta : ℂ) * I
  let p : ℂ := (x0 : ℂ) + (eta0 : ℂ) * I
  have hzne : z ≠ p := by
    intro h
    apply hne
    simpa [z, p] using congrArg Complex.im h
  have hXi : XiC z ≠ 0 := by
    rw [hfact z (by simpa [z, p] using hmem)]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzne))
      (hg0 z (by simpa [z, p] using hmem))
  have hXiLower : XiC ((x0 : ℂ) - (eta : ℂ) * I) ≠ 0 := by
    have hconj := XiC_ne_zero_conj hXi
    have hcoord : (starRingEnd ℂ) z = (x0 : ℂ) - (eta : ℂ) * I := by
      simp only [z, map_add, map_mul, conj_ofReal, conj_I]
      ring
    rwa [hcoord] at hconj
  have hsource := boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
    heta0 hetaHalf hXiLower
  have hpole := logDeriv_XiC_eq_pole_add hgan hg0 hfact
    (by simpa [z, p] using hmem) hzne
  have hdiff : z - p = (eta - eta0 : ℝ) * I := by
    simp [z, p]
    ring
  have hpole_im :
      (((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℂ) /
          (((eta - eta0 : ℝ) : ℂ) * I)).im =
        -((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℝ) /
          (eta - eta0) := by
    simpa using
      (im_div_ofReal_mul_I
        ((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℝ)
        (eta - eta0))
  rw [← hsource, boundaryDensity, hpole, Complex.add_im, hdiff, hpole_im]
  ring

/-- The transverse HCF source has a quantized residue at each locally factored Xi zero.
Multiplication by the shift displacement removes the analytic cofactor and leaves exactly
the zero multiplicity divided by `π`. -/
theorem tendsto_sub_mul_criticalFeaturePositiveShiftPoleGammaDensity_of_vertical_factor
    {eta0 x0 R : ℝ} {g : ℂ → ℂ}
    (heta0 : 0 < eta0) (hetaHalf : eta0 < 1 / 2)
    (hR : 0 < R)
    (hgan : AnalyticOnNhd ℂ g
      (ball ((x0 : ℂ) + (eta0 : ℂ) * I) R))
    (hg0 : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R,
      XiC z = (z - ((x0 : ℂ) + (eta0 : ℂ) * I)) ^
        (analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat * g z) :
    Tendsto
      (fun eta : ℝ => (eta - eta0) *
        criticalFeaturePositiveShiftPoleGammaDensity eta x0)
      (𝓝[>] eta0)
      (𝓝 ((Real.pi)⁻¹ *
        ((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℝ))) := by
  let p : ℂ := (x0 : ℂ) + (eta0 : ℂ) * I
  let path : ℝ → ℂ := fun eta => (x0 : ℂ) + (eta : ℂ) * I
  have hpathcont : Continuous path := by
    dsimp only [path]
    fun_prop
  have hpathlim : Tendsto path (𝓝[>] eta0) (𝓝 p) := by
    have h := (hpathcont.tendsto eta0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi eta0))
    simpa [path, p] using h
  have hpos : ∀ᶠ eta : ℝ in 𝓝[>] eta0, 0 < eta := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (eventually_gt_nhds heta0)
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] eta0, eta < 1 / 2 := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds hetaHalf)
  have hmem : ∀ᶠ eta : ℝ in 𝓝[>] eta0, path eta ∈ ball p R := by
    exact hpathlim.eventually (Metric.ball_mem_nhds p hR)
  have hne : ∀ᶠ eta : ℝ in 𝓝[>] eta0, eta ≠ eta0 := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    change eta0 < eta at heta
    exact ne_of_gt heta
  have hform : ∀ᶠ eta : ℝ in 𝓝[>] eta0,
      criticalFeaturePositiveShiftPoleGammaDensity eta x0 =
        (Real.pi)⁻¹ *
          ((analyticOrderAt XiC p).toNat : ℝ) / (eta - eta0) -
        (Real.pi)⁻¹ * (logDeriv g (path eta)).im := by
    filter_upwards [hpos, hhalf, hmem, hne] with eta heta hhalf hmem hne
    simpa only [path, p] using
      (criticalFeaturePositiveShiftPoleGammaDensity_eq_transverse_pole_sub_cofactor_im_of_vertical_factor
        heta hhalf hgan hg0 hfact (by simpa [path, p] using hmem) hne)
  have hlogg : ContinuousAt (logDeriv g) p := by
    have hpball : p ∈ ball p R := mem_ball_self hR
    have hpana : AnalyticAt ℂ g p := by
      apply hgan p
      simpa [p] using hpball
    have hpnonzero : g p ≠ 0 := by
      apply hg0 p
      simpa [p] using hpball
    have hd1 : ContinuousAt (deriv g) p := hpana.deriv.continuousAt
    have hd2 : ContinuousAt g p := hpana.continuousAt
    unfold logDeriv
    exact ContinuousAt.div hd1 hd2 hpnonzero
  have hlog : Tendsto (fun eta : ℝ => (logDeriv g (path eta)).im)
      (𝓝[>] eta0) (𝓝 (logDeriv g p).im) := by
    exact (Complex.continuous_im.tendsto _).comp
      (hlogg.tendsto.comp hpathlim)
  have hsub : Tendsto (fun eta : ℝ => eta - eta0) (𝓝[>] eta0) (𝓝 0) := by
    have h := ((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun eta : ℝ => eta) (𝓝[>] eta0) (𝓝 eta0)).sub_const eta0)
    simpa using h
  let c : ℝ := (Real.pi)⁻¹ * (analyticOrderAt XiC p).toNat
  have hregular : Tendsto (fun eta : ℝ =>
      c - (Real.pi)⁻¹ * ((eta - eta0) * (logDeriv g (path eta)).im))
      (𝓝[>] eta0) (𝓝 c) := by
    have hmul := hsub.mul hlog
    have hmul0 : Tendsto (fun eta : ℝ =>
        (eta - eta0) * (logDeriv g (path eta)).im)
        (𝓝[>] eta0) (𝓝 0) := by
      simpa using hmul
    simpa using tendsto_const_nhds.sub (hmul0.const_mul (Real.pi)⁻¹)
  refine hregular.congr' ?_
  filter_upwards [hform, hne] with eta hform hne
  rw [hform]
  dsimp only [c, p]
  field_simp

/-- A positive local Xi multiplicity forces the reciprocal transverse HCF source lower
asymptotic.  This is the exact hypothesis needed to turn any finite cross-shift quadratic
source bound into exclusion of an off-line zero. -/
theorem sub_inv_isBigO_criticalFeaturePositiveShiftPoleGammaDensity_of_vertical_factor
    {eta0 x0 R : ℝ} {g : ℂ → ℂ}
    (heta0 : 0 < eta0) (hetaHalf : eta0 < 1 / 2)
    (hR : 0 < R)
    (hgan : AnalyticOnNhd ℂ g
      (ball ((x0 : ℂ) + (eta0 : ℂ) * I) R))
    (hg0 : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R,
      XiC z = (z - ((x0 : ℂ) + (eta0 : ℂ) * I)) ^
        (analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat * g z)
    (hm : 0 < (analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat) :
    (fun eta : ℝ => (eta - eta0)⁻¹) =O[𝓝[>] eta0]
      fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x0 := by
  let p : ℂ := (x0 : ℂ) + (eta0 : ℂ) * I
  let c : ℝ := (Real.pi)⁻¹ * (analyticOrderAt XiC p).toNat
  have hlim : Tendsto
      (fun eta : ℝ => (eta - eta0) *
        criticalFeaturePositiveShiftPoleGammaDensity eta x0)
      (𝓝[>] eta0) (𝓝 c) := by
    simpa only [p, c] using
      (tendsto_sub_mul_criticalFeaturePositiveShiftPoleGammaDensity_of_vertical_factor
        heta0 hetaHalf hR hgan hg0 hfact)
  have hratio : Tendsto
      (fun eta : ℝ =>
        criticalFeaturePositiveShiftPoleGammaDensity eta x0 /
          (eta - eta0)⁻¹)
      (𝓝[>] eta0) (𝓝 c) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with eta heta
    change eta0 < eta at heta
    have hsubne : eta - eta0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt heta)
    field_simp
  have hcpos : 0 < c := by
    dsimp only [c]
    exact mul_pos (inv_pos.mpr Real.pi_pos) (by exact_mod_cast hm)
  exact Asymptotics.isBigO_of_div_tendsto_nhds_of_ne_zero hratio (ne_of_gt hcpos)

private theorem not_intervalIntegrable_sq_of_sub_inv_isBigO
    {y b : ℝ} {wall : ℝ → ℝ}
    (hbig : (fun v => (v - y)⁻¹) =O[𝓝[>] y] wall) (hb : y < b) :
    ¬ IntervalIntegrable (fun v => wall v ^ (2 : ℕ)) volume y b := by
  let kernel : ℝ → ℝ := fun v => (v - y)⁻¹
  have hbig' : kernel =O[𝓝[>] y] wall := by
    simpa only [kernel] using hbig
  have hderiv : ∀ᶠ v in 𝓝[>] y,
      HasDerivAt (-kernel) (kernel v ^ (2 : ℕ)) v := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    change y < v at hv
    have hlinear : HasDerivAt (fun z : ℝ => z - y) 1 v := by
      simpa using (hasDerivAt_id v).sub_const y
    have hbase : HasDerivAt kernel (-(kernel v ^ (2 : ℕ))) v := by
      have hbase' := hlinear.inv (sub_ne_zero.mpr hv.ne')
      have hkernel : kernel = (fun z : ℝ => z - y)⁻¹ := by
        funext z
        rfl
      rw [← hkernel] at hbase'
      simpa only [kernel, one_div, inv_pow, neg_div] using hbase'
    simpa only [neg_neg] using hbase.neg
  have hsubN : Tendsto (fun v : ℝ => v - y) (𝓝 y) (𝓝 0) := by
    have h : Tendsto (fun v : ℝ => v - y) (𝓝 y) (𝓝 (y - y)) :=
      ((hasDerivAt_id y).sub_const y).continuousAt
    simpa using h
  have hsub : Tendsto (fun v : ℝ => v - y) (𝓝[>] y) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsubN.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    change y < v at hv
    exact sub_pos.mpr hv
  have hinv : Tendsto kernel (𝓝[>] y) atTop := by
    change Tendsto ((fun x : ℝ => x⁻¹) ∘ fun v => v - y) (𝓝[>] y) atTop
    exact tendsto_inv_nhdsGT_zero.comp hsub
  have hnorm : Tendsto (fun v => ‖-kernel v‖) (𝓝[>] y) atTop := by
    apply hinv.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    change y < v at hv
    have hpos : 0 < kernel v := by
      dsimp only [kernel]
      exact inv_pos.mpr (sub_pos.mpr hv)
    rw [Real.norm_eq_abs, abs_of_neg (neg_lt_zero.mpr hpos)]
    ring
  have hderivBig : deriv (-kernel) =O[𝓝[>] y]
      (fun v => wall v ^ (2 : ℕ)) :=
    (hbig'.pow 2).congr' (hderiv.mono fun v hv => hv.deriv.symm) EventuallyEq.rfl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    (𝓝[>] y) (Ioc_mem_nhdsGT hb)
      (hderiv.mono fun v hv => hv.differentiableAt) hnorm hderivBig

/-- A transverse positive-shift Xi pole has infinite local squared HCF source energy.
This is a source statement: no spectral positivity, zero-density bound, or RH-equivalent
premise is used. -/
theorem not_intervalIntegrable_sq_criticalFeaturePositiveShiftPoleGammaDensity_of_vertical_factor
    {eta0 x0 R b : ℝ} {g : ℂ → ℂ}
    (heta0 : 0 < eta0) (hetaHalf : eta0 < 1 / 2)
    (hR : 0 < R)
    (hgan : AnalyticOnNhd ℂ g
      (ball ((x0 : ℂ) + (eta0 : ℂ) * I) R))
    (hg0 : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R,
      XiC z = (z - ((x0 : ℂ) + (eta0 : ℂ) * I)) ^
        (analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat * g z)
    (hm : 0 < (analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat)
    (hb : eta0 < b) :
    ¬ IntervalIntegrable
      (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x0 ^ (2 : ℕ))
      volume eta0 b := by
  apply not_intervalIntegrable_sq_of_sub_inv_isBigO _ hb
  exact sub_inv_isBigO_criticalFeaturePositiveShiftPoleGammaDensity_of_vertical_factor
    heta0 hetaHalf hR hgan hg0 hfact hm

/-- Every genuine positive-shift XiC zero forces infinite local squared HCF source energy
on each interval immediately above its shift. -/
theorem not_intervalIntegrable_sq_criticalFeaturePositiveShiftPoleGammaDensity_of_XiC_zero
    {eta0 x0 b : ℝ}
    (heta0 : 0 < eta0) (hetaHalf : eta0 < 1 / 2)
    (hzero : XiC ((x0 : ℂ) + (eta0 : ℂ) * I) = 0)
    (hb : eta0 < b) :
    ¬ IntervalIntegrable
      (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x0 ^ (2 : ℕ))
      volume eta0 b := by
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ :=
    XiC_peel_ball ((x0 : ℂ) + (eta0 : ℂ) * I)
  exact not_intervalIntegrable_sq_criticalFeaturePositiveShiftPoleGammaDensity_of_vertical_factor
    heta0 hetaHalf hR hgan hg0 hfact (XiC_order_toNat_pos hzero) hb

/-- At every positive-shift Xi zero, the source has a punctured horizontal
factorization with a positive residue that is completely absent from the
scalar source density. -/
theorem exists_criticalFeaturePositiveShiftPoleGamma_horizontal_pole_blindness
    {x0 eta : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hzero : XiC ((x0 : ℂ) + (eta : ℂ) * I) = 0) :
    ∃ R > 0, ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball ((x0 : ℂ) + (eta : ℂ) * I) R) ∧
      (∀ z ∈ ball ((x0 : ℂ) + (eta : ℂ) * I) R, g z ≠ 0) ∧
      0 < (analyticOrderAt XiC ((x0 : ℂ) + (eta : ℂ) * I)).toNat ∧
      ∀ {x : ℝ},
        (x : ℂ) + (eta : ℂ) * I ∈
            ball ((x0 : ℂ) + (eta : ℂ) * I) R →
        x ≠ x0 →
        criticalFeaturePositiveShiftPoleGammaDensity eta x =
          -(Real.pi)⁻¹ * (logDeriv g ((x : ℂ) + (eta : ℂ) * I)).im := by
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ :=
    XiC_peel_ball ((x0 : ℂ) + (eta : ℂ) * I)
  refine ⟨R, hR, g, hgan, hg0,
    XiC_order_toNat_pos hzero, ?_⟩
  intro x hx hne
  exact criticalFeaturePositiveShiftPoleGammaDensity_eq_cofactor_im_of_horizontal_factor
    heta0 hetaHalf hgan hg0 hfact hx hne

end

end RHTower
