import GaloisForLFunctions.RHTower.ProlateRadialNormalization
import GaloisForLFunctions.RHTower.CCMRadialProlateProfileMeasure

/-!
# Exact bridge from endpoint-normalized prolate modes to the Dunster transform

The two radial constructions use apparently different amplitudes.  This file proves their exact
identity.  Consequently the comparison-equation unknown is literally the radial profile divided
by Dunster's Liouville--Green amplitude; no normalization constant or asymptotic replacement is
hidden in the passage.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The normal-form weight times Dunster's displayed amplitude is exactly the comparison
amplitude. -/
theorem nfWeight_mul_xiAmplitude_eq_lgAmplitude {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    nfWeight x * xiAmplitude s x = lgAmplitude s x := by
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hphase := xiEndpointPhase_pos hs0 hs1 hx
  have hspeed := xiSpeed_pos hs1 hx
  have hnf : 0 < nfWeight x := by
    rw [nfWeight]
    positivity
  have hamp := xiAmplitude_pos hs0 hs1 hx
  have hlg := lgAmplitude_pos hs0 hs1 hx
  have hnf_sq : nfWeight x ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := by
    rw [nfWeight]
    exact Real.sq_sqrt hd.le
  have hamp_sq : xiAmplitude s x ^ (2 : ℕ) =
      xiEndpointPhase s x / Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := by
    rw [xiAmplitude, div_pow]
    rw [Real.sq_sqrt hphase.le]
    rw [Real.sq_sqrt (Real.sqrt_pos.mpr (mul_pos hd hn)).le]
  have hlg_sq : lgAmplitude s x ^ (2 : ℕ) = xiEndpointPhase s x / xiSpeed s x := by
    rw [lgAmplitude, Real.sq_sqrt (lgWeight_pos hs0 hs1 hx).le, lgWeight]
  have hroot : xiSpeed s x * (x ^ (2 : ℕ) - 1) =
      Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := by
    rw [xiSpeed_mul_sub_one hs1 hx, Real.sqrt_mul hd.le]
    ring
  apply (sq_eq_sq₀ (mul_nonneg hnf.le hamp.le) hlg.le).mp
  rw [mul_pow, hnf_sq, hamp_sq, hlg_sq]
  field_simp [hspeed.ne', (Real.sqrt_pos.mpr (mul_pos hd hn)).ne']
  nlinarith

/-- The pole-uniform comparison unknown is exactly `R / A_s`. -/
theorem comparisonSol_prolateNormalForm_eq_div_xiAmplitude
    {s x : ℝ} {R : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    comparisonSol (prolateNormalFormSol R) s x = R x / xiAmplitude s x := by
  rw [comparisonSol, prolateNormalFormSol]
  have hamp := xiAmplitude_pos hs0 hs1 hx
  have hnf : 0 < nfWeight x := by
    rw [nfWeight]
    have : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
    positivity
  rw [← nfWeight_mul_xiAmplitude_eq_lgAmplitude hs0 hs1 hx]
  field_simp [hamp.ne', hnf.ne']

/-- Derivative of Dunster's amplitude, written in the form whose endpoint boundedness is visible. -/
def xiAmplitudeDeriv (s x : ℝ) : ℝ :=
  xiAmplitude s x * (phaseLogDefect s x / 2 - x / (2 * (x ^ (2 : ℕ) - s)))

theorem lgAmplitude_nfWeight_logDeriv_eq {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    lgFirstOrderCoeff s x / 2 - nfWeightDeriv x / nfWeight x =
      phaseLogDefect s x / 2 - x / (2 * (x ^ (2 : ℕ) - s)) := by
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hspeed := xiSpeed_pos hs1 hx
  have hphase := xiEndpointPhase_pos hs0 hs1 hx
  have hsqrt : Real.sqrt (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt hd.le
  have hv := xiSpeedDeriv_div_xiSpeed_eq hs1 hx
  rw [lgFirstOrderCoeff, phaseLogDefect, nfWeightDeriv, nfWeight, hv]
  field_simp [hspeed.ne', hphase.ne', (Real.sqrt_pos.mpr hd).ne', hn.ne']
  rw [hsqrt]
  ring

/-- Dunster's amplitude is differentiable throughout the exterior ray. -/
theorem hasDerivAt_xiAmplitude {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (xiAmplitude s) (xiAmplitudeDeriv s x) x := by
  have hnf : 0 < nfWeight x := by
    rw [nfWeight]
    have : 0 < x ^ (2 : ℕ) - 1 := by nlinarith
    positivity
  have heq : ∀ y : ℝ, 1 < y → xiAmplitude s y = lgAmplitude s y / nfWeight y := by
    intro y hy
    have hnf_y : 0 < nfWeight y := by
      rw [nfWeight]
      have : 0 < y ^ (2 : ℕ) - 1 := by nlinarith
      positivity
    have h := nfWeight_mul_xiAmplitude_eq_lgAmplitude hs0 hs1 hy
    rw [eq_div_iff hnf_y.ne']
    simpa only [mul_comm] using h
  have hlocal : xiAmplitude s =ᶠ[nhds x] fun y => lgAmplitude s y / nfWeight y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact heq y hy
  have hquot := (hasDerivAt_lgAmplitude hs0 hs1 hx).fun_div
    (hasDerivAt_nfWeight hx) hnf.ne'
  have hder := hquot.congr_of_eventuallyEq hlocal
  have hval :
      (lgAmplitudeDeriv s x * nfWeight x - lgAmplitude s x * nfWeightDeriv x)
          / nfWeight x ^ (2 : ℕ) = xiAmplitudeDeriv s x := by
    rw [xiAmplitudeDeriv]
    have hlog := lgAmplitude_nfWeight_logDeriv_eq hs0 hs1 hx
    rw [lgAmplitudeDeriv]
    field_simp [hnf.ne']
    rw [← nfWeight_mul_xiAmplitude_eq_lgAmplitude hs0 hs1 hx]
    have hbr : lgFirstOrderCoeff s x * nfWeight x - 2 * nfWeightDeriv x =
        nfWeight x * (phaseLogDefect s x - x / (x ^ (2 : ℕ) - s)) := by
      field_simp [hnf.ne'] at hlog
      linarith
    rw [hbr]
    ring
  rw [hval] at hder
  exact hder

/-- Derivative of the endpoint-normalized radial comparison unknown `R / A_s`. -/
def radialComparisonDeriv (R DR : ℝ → ℝ) (s x : ℝ) : ℝ :=
  (DR x * xiAmplitude s x - R x * xiAmplitudeDeriv s x) / xiAmplitude s x ^ (2 : ℕ)

theorem hasDerivAt_radialComparison {s x : ℝ} {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hR : HasDerivAt R (DR x) x) :
    HasDerivAt (comparisonSol (prolateNormalFormSol R) s)
      (radialComparisonDeriv R DR s x) x := by
  have hamp := xiAmplitude_pos hs0 hs1 hx
  have hquot := hR.fun_div (hasDerivAt_xiAmplitude hs0 hs1 hx) hamp.ne'
  have heq : comparisonSol (prolateNormalFormSol R) s =ᶠ[nhds x]
      fun y => R y / xiAmplitude s y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact comparisonSol_prolateNormalForm_eq_div_xiAmplitude hs0 hs1 hy
  exact hquot.congr_of_eventuallyEq heq

theorem comparisonSolDeriv_prolateNormalForm_eq_radialComparisonDeriv
    {s x : ℝ} {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hR : HasDerivAt R (DR x) x) :
    comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x =
      radialComparisonDeriv R DR s x := by
  have hnf := hasDerivAt_prolateNormalFormSol hx hR
  exact HasDerivAt.unique
    (hasDerivAt_comparisonSol hs0 hs1 hx hnf)
    (hasDerivAt_radialComparison hs0 hs1 hx hR)

open Filter Set

/-- Quantitative endpoint squeeze for the fourth power of Dunster's amplitude. -/
theorem xiAmplitude_pow_four_endpoint_bounds {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hd1 : x ^ (2 : ℕ) - 1 ≤ 1) :
    (1 - s) / (x ^ (2 : ℕ) - s) * (1 - (x ^ (2 : ℕ) - 1) / 6) ^ (2 : ℕ)
        ≤ xiAmplitude s x ^ (4 : ℕ) ∧
      xiAmplitude s x ^ (4 : ℕ) ≤ 1 := by
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hspos : (0 : ℝ) < 1 - s := by linarith
  have hfac : 0 ≤ 1 - (x ^ (2 : ℕ) - 1) / 6 := by linarith
  have hsqrtd : Real.sqrt (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 :=
    Real.sq_sqrt hd.le
  have hsqrtn : Real.sqrt (x ^ (2 : ℕ) - s) ^ (2 : ℕ) = x ^ (2 : ℕ) - s :=
    Real.sq_sqrt hn.le
  have hsqrts : Real.sqrt (1 - s) ^ (2 : ℕ) = 1 - s :=
    Real.sq_sqrt hspos.le
  have hloglow :=
    GaloisForLFunctions.HTGeometry.sqrt_mul_one_sub_le_endpointLog hx.le
  have hlogup := GaloisForLFunctions.HTGeometry.endpointLog_le_sqrt hx.le
  have hlog0 : 0 ≤ GaloisForLFunctions.HTGeometry.endpointLog x := by
    have : 0 ≤ Real.sqrt (x ^ (2 : ℕ) - 1) * (1 - (x ^ (2 : ℕ) - 1) / 6) := by positivity
    linarith
  have hphase0 := (xiEndpointPhase_pos hs0 hs1 hx).le
  have hphaselow := sqrt_one_sub_mul_endpointLog_le_xiEndpointPhase hs0 hs1 hx.le
  have hphaseup := xiEndpointPhase_le_sqrt_mul_endpointLog hs0 hs1 hx.le
  have hloglow_sq : (x ^ (2 : ℕ) - 1) * (1 - (x ^ (2 : ℕ) - 1) / 6) ^ (2 : ℕ)
      ≤ GaloisForLFunctions.HTGeometry.endpointLog x ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (x ^ (2 : ℕ) - 1)) hfac]
  have hlogup_sq : GaloisForLFunctions.HTGeometry.endpointLog x ^ (2 : ℕ) ≤ x ^ (2 : ℕ) - 1 := by
    nlinarith [Real.sqrt_nonneg (x ^ (2 : ℕ) - 1)]
  have hphase_low_sq :
      (1 - s) * GaloisForLFunctions.HTGeometry.endpointLog x ^ (2 : ℕ)
        ≤ xiEndpointPhase s x ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (1 - s)) hlog0]
  have hphase_up_sq : xiEndpointPhase s x ^ (2 : ℕ)
      ≤ (x ^ (2 : ℕ) - s) * GaloisForLFunctions.HTGeometry.endpointLog x ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (x ^ (2 : ℕ) - s)) hlog0]
  rw [xiAmplitude_pow_four hs0 hs1 hx]
  constructor
  · rw [div_mul_eq_mul_div]
    rw [div_le_div_iff₀ hn (mul_pos hd hn)]
    nlinarith [mul_le_mul_of_nonneg_left hloglow_sq hspos.le]
  · rw [div_le_one (mul_pos hd hn)]
    nlinarith [mul_le_mul_of_nonneg_left hlogup_sq hn.le]

/-- Dunster's amplitude tends to one at the regular singular endpoint. -/
theorem xiAmplitude_tendsto_one_at_endpoint {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Tendsto (xiAmplitude s) (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have h4 : Tendsto (fun x : ℝ => xiAmplitude s x ^ (4 : ℕ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    let lower : ℝ → ℝ := fun x =>
      (1 - s) / (x ^ (2 : ℕ) - s) * (1 - (x ^ (2 : ℕ) - 1) / 6) ^ (2 : ℕ)
    have hsne : (1 : ℝ) ^ (2 : ℕ) - s ≠ 0 := by nlinarith
    have hlowerCont : ContinuousAt lower 1 := by
      dsimp [lower]
      fun_prop
    have hlowerVal : lower 1 = 1 := by
      dsimp [lower]
      norm_num only [one_pow, sub_self, zero_div, sub_zero, one_mul]
      simpa only [mul_one] using div_self (by linarith : (1 : ℝ) - s ≠ 0)
    have hlower : Tendsto lower (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
      have h := hlowerCont.tendsto.mono_left
        (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
      simpa only [hlowerVal] using h
    have hdlim : Tendsto (fun x : ℝ => x ^ (2 : ℕ) - 1)
        (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
      have hcont : ContinuousAt (fun x : ℝ => x ^ (2 : ℕ) - 1) 1 := by fun_prop
      simpa only [one_pow, sub_self] using hcont.tendsto.mono_left
        (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
    have hdsmall : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1), x ^ (2 : ℕ) - 1 ≤ 1 :=
      (hdlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
    have hxright : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1), 1 < x := by
      exact self_mem_nhdsWithin
    have hbounds : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1),
        lower x ≤ xiAmplitude s x ^ (4 : ℕ) ∧ xiAmplitude s x ^ (4 : ℕ) ≤ 1 := by
      filter_upwards [hxright, hdsmall] with x hx hd
      exact xiAmplitude_pow_four_endpoint_bounds hs0 hs1 hx hd
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.sqrt (xiAmplitude s x ^ (4 : ℕ))))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    have hfirst : Tendsto (fun x : ℝ => Real.sqrt (xiAmplitude s x ^ (4 : ℕ)))
        (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
      simpa only [Function.comp_def, Real.sqrt_one] using
        Real.continuous_sqrt.continuousAt.tendsto.comp h4
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hfirst
  apply hsqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hamp := xiAmplitude_pos hs0 hs1 hx
  rw [show xiAmplitude s x ^ (4 : ℕ) = (xiAmplitude s x ^ (2 : ℕ)) ^ (2 : ℕ) by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq hamp.le]

/-- The derivative of the endpoint-normalized comparison solution stays bounded at the
regular singular endpoint. -/
theorem eventually_bounded_comparisonSolDeriv {s : ℝ} {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hRc : ContinuousAt R 1) (hDRc : ContinuousAt DR 1)
    (hR : ∀ x : ℝ, 1 < x → HasDerivAt R (DR x) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1),
      |comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x| ≤ C := by
  let C : ℝ := 100 * (|R 1| + |DR 1| + 1)
  refine ⟨C, by positivity, ?_⟩
  have hRt : Tendsto R (nhdsWithin 1 (Ioi 1)) (nhds (R 1)) :=
    hRc.tendsto.mono_left inf_le_left
  have hDRt : Tendsto DR (nhdsWithin 1 (Ioi 1)) (nhds (DR 1)) :=
    hDRc.tendsto.mono_left inf_le_left
  have hRb : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1), |R x - R 1| < 1 := by
    simpa only [Real.dist_eq] using hRt.eventually (Metric.ball_mem_nhds (R 1) one_pos)
  have hDRb : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1), |DR x - DR 1| < 1 := by
    simpa only [Real.dist_eq] using hDRt.eventually (Metric.ball_mem_nhds (DR 1) one_pos)
  have hAb : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1),
      xiAmplitude s x ∈ Ioo (1 / 2 : ℝ) 2 :=
    (xiAmplitude_tendsto_one_at_endpoint hs0 hs1).eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hxb : ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1), x < 2 := by
    have hid : Tendsto (fun x : ℝ => x) (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
      tendsto_id.mono_left inf_le_left
    exact hid.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hxb, hRb, hDRb, hAb] with x hxmem hx2 hRx hDRx hAx
  have hx : (1 : ℝ) < x := hxmem
  rw [comparisonSolDeriv_prolateNormalForm_eq_radialComparisonDeriv hs0 hs1 hx (hR x hx),
    radialComparisonDeriv]
  have hRabs : |R x| ≤ |R 1| + 1 := by
    calc
      |R x| = |(R x - R 1) + R 1| := by ring_nf
      _ ≤ |R x - R 1| + |R 1| := abs_add_le _ _
      _ ≤ |R 1| + 1 := by linarith
  have hDRabs : |DR x| ≤ |DR 1| + 1 := by
    calc
      |DR x| = |(DR x - DR 1) + DR 1| := by ring_nf
      _ ≤ |DR x - DR 1| + |DR 1| := abs_add_le _ _
      _ ≤ |DR 1| + 1 := by linarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith [sq_nonneg (x - 1)]
  have hx0 : (0 : ℝ) < x := by linarith
  have hratio : |x / (x ^ (2 : ℕ) - s)| ≤ 4 := by
    rw [abs_of_pos (div_pos hx0 hn), div_le_iff₀ hn]
    nlinarith [sq_nonneg (x - 1)]
  have hphase := abs_phaseLogDefect_le_near hs0 hs1 hx hx2.le
  have hApos : 0 < xiAmplitude s x := lt_trans (by norm_num) hAx.1
  have hAabs : |xiAmplitude s x| ≤ 2 := by
    rw [abs_of_pos hApos]
    exact hAx.2.le
  have hAderiv : |xiAmplitudeDeriv s x| ≤ 6 := by
    rw [xiAmplitudeDeriv, abs_mul]
    have hsub := abs_sub (phaseLogDefect s x / 2) (x / (2 * (x ^ (2 : ℕ) - s)))
    have hhalf : x / (2 * (x ^ (2 : ℕ) - s)) = (x / (x ^ (2 : ℕ) - s)) / 2 := by
      field_simp [hn.ne']
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hhalf,
      abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsub
    have hsub' :
        |phaseLogDefect s x / 2 - x / (2 * (x ^ (2 : ℕ) - s))|
          ≤ |phaseLogDefect s x| / 2 + |x / (x ^ (2 : ℕ) - s)| / 2 := by
      rw [hhalf]
      exact hsub
    calc
      |xiAmplitude s x| * |phaseLogDefect s x / 2 - x / (2 * (x ^ (2 : ℕ) - s))|
          ≤ 2 * (|phaseLogDefect s x| / 2 + |x / (x ^ (2 : ℕ) - s)| / 2) :=
            mul_le_mul hAabs hsub' (abs_nonneg _) (by positivity)
      _ ≤ 6 := by linarith
  rw [abs_div, abs_pow]
  rw [abs_of_pos hApos, div_le_iff₀ (sq_pos_of_pos hApos)]
  have hnum : |DR x * xiAmplitude s x - R x * xiAmplitudeDeriv s x|
      ≤ 2 * (|DR 1| + 1) + 6 * (|R 1| + 1) := by
    calc
      |DR x * xiAmplitude s x - R x * xiAmplitudeDeriv s x|
          ≤ |DR x * xiAmplitude s x| + |R x * xiAmplitudeDeriv s x| := abs_sub _ _
      _ = |DR x| * |xiAmplitude s x| + |R x| * |xiAmplitudeDeriv s x| := by
        rw [abs_mul, abs_mul]
      _ ≤ (|DR 1| + 1) * 2 + (|R 1| + 1) * 6 := by gcongr
      _ = 2 * (|DR 1| + 1) + 6 * (|R 1| + 1) := by ring
  have hA2 : (1 / 4 : ℝ) ≤ xiAmplitude s x ^ (2 : ℕ) := by
    have hprod : 0 ≤ (xiAmplitude s x - 1 / 2) * (xiAmplitude s x + 1 / 2) := by
      exact mul_nonneg (by linarith [hAx.1]) (by linarith [hAx.1])
    nlinarith
  dsimp [C]
  nlinarith [abs_nonneg (R 1), abs_nonneg (DR 1)]

/-- Every continuous endpoint-normalized radial profile becomes the unit regular comparison
solution at the singular endpoint. -/
theorem comparisonSol_prolateNormalForm_tendsto_one_at_endpoint
    {s : ℝ} {R : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hR : ContinuousAt R 1) (hR1 : R 1 = 1) :
    Tendsto (comparisonSol (prolateNormalFormSol R) s)
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  have hRt : Tendsto R (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    simpa only [hR1] using hR.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
  have hdiv := hRt.div (xiAmplitude_tendsto_one_at_endpoint hs0 hs1) (by norm_num)
  norm_num at hdiv
  apply hdiv.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (comparisonSol_prolateNormalForm_eq_div_xiAmplitude hs0 hs1 hx).symm

end GaloisForLFunctions.RHTower

end
