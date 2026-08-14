import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The reciprocal coarea certificate and its optimal shell ratio

A cofactor-shell disintegration certified only through the local prime bounds pays

```text
c(r) = √(r (r-1)) / log r
```

per unit of logarithmic length, where `r` is the shell ratio.  The stationarity condition of `c`
is `log r = 2(r-1)/(2r-1)`; its defect `h(r) = log r - 2(r-1)/(2r-1)` vanishes at `1`, is
strictly negative on an initial interval and strictly positive from a unique further zero `r_*`
onwards.  Hence `c` decreases and then increases, so `r_*` is the unique global minimizer, and
every interval partition costs at least `c(r_*)` per unit logarithmic length.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The certificate cost of one shell of ratio `r`. -/
def coareaRatioCost (r : ℝ) : ℝ := Real.sqrt (r * (r - 1)) / Real.log r

/-- The stationarity defect of the certificate cost. -/
def coareaStationaryDefect (r : ℝ) : ℝ := Real.log r - 2 * (r - 1) / (2 * r - 1)

theorem coareaStationaryDefect_one : coareaStationaryDefect 1 = 0 := by
  rw [coareaStationaryDefect]
  norm_num

theorem hasDerivAt_coareaStationaryDefect {r : ℝ} (hr : 0 < r) (hr2 : 2 * r - 1 ≠ 0) :
    HasDerivAt coareaStationaryDefect
      ((4 * r ^ 2 - 6 * r + 1) / (r * (2 * r - 1) ^ 2)) r := by
  have hlog : HasDerivAt Real.log r⁻¹ r := Real.hasDerivAt_log (ne_of_gt hr)
  have hnum : HasDerivAt (fun s : ℝ => 2 * (s - 1)) 2 r := by
    have h := ((hasDerivAt_id r).sub_const 1).const_mul (2 : ℝ)
    simpa using h
  have hden : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 r := by
    have h := ((hasDerivAt_id r).const_mul (2 : ℝ)).sub_const 1
    simpa using h
  have hquot := hnum.div hden hr2
  have hsub := hlog.sub hquot
  refine hsub.congr_deriv ?_
  have hrne : r ≠ 0 := ne_of_gt hr
  have hsq : (2 * r - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hr2
  rw [inv_eq_one_div, div_sub_div _ _ hrne hsq]
  congr 1
  ring

/-- The stationarity defect is strictly increasing past the inner critical ratio. -/
theorem coareaStationaryDefect_deriv_pos {r : ℝ} (hr : (3 + Real.sqrt 5) / 4 < r) :
    0 < (4 * r ^ 2 - 6 * r + 1) / (r * (2 * r - 1) ^ 2) := by
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt5lt : Real.sqrt 5 < 3 := by
    nlinarith [hsqrt5, hsqrt5pos]
  have hr1 : 1 < r := by
    have : (3 + Real.sqrt 5) / 4 > 1 := by nlinarith [hsqrt5, hsqrt5pos]
    linarith
  have hr0 : 0 < r := by linarith
  have hden : 0 < r * (2 * r - 1) ^ 2 := by
    have : (0 : ℝ) < 2 * r - 1 := by linarith
    positivity
  have hnum : 0 < 4 * r ^ 2 - 6 * r + 1 := by
    have hfac : 4 * r ^ 2 - 6 * r + 1
        = 4 * (r - (3 + Real.sqrt 5) / 4) * (r - (3 - Real.sqrt 5) / 4) := by
      have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
      field_simp
      nlinarith [h5]
    rw [hfac]
    have h1 : 0 < r - (3 + Real.sqrt 5) / 4 := by linarith
    have h2 : 0 < r - (3 - Real.sqrt 5) / 4 := by
      have : (3 - Real.sqrt 5) / 4 < (3 + Real.sqrt 5) / 4 := by linarith
      linarith
    positivity
  exact div_pos hnum hden

/-- The stationarity defect is strictly negative just past `1`. -/
theorem coareaStationaryDefect_deriv_neg {r : ℝ} (hr1 : 1 < r) (hr : r < (3 + Real.sqrt 5) / 4) :
    (4 * r ^ 2 - 6 * r + 1) / (r * (2 * r - 1) ^ 2) < 0 := by
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hr0 : 0 < r := by linarith
  have hden : 0 < r * (2 * r - 1) ^ 2 := by
    have : (0 : ℝ) < 2 * r - 1 := by linarith
    positivity
  have hnum : 4 * r ^ 2 - 6 * r + 1 < 0 := by
    have hfac : 4 * r ^ 2 - 6 * r + 1
        = 4 * (r - (3 + Real.sqrt 5) / 4) * (r - (3 - Real.sqrt 5) / 4) := by
      have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
      field_simp
      nlinarith [h5]
    rw [hfac]
    have h1 : r - (3 + Real.sqrt 5) / 4 < 0 := by linarith
    have h2 : 0 < r - (3 - Real.sqrt 5) / 4 := by
      have hlt : (3 - Real.sqrt 5) / 4 < 1 := by nlinarith [hsqrt5, hsqrt5pos]
      linarith
    nlinarith [h1, h2]
  exact div_neg_of_neg_of_pos hnum hden

/-! ## Monotonicity of the stationarity defect -/

theorem sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h5, hpos]

theorem two_lt_sqrt5 : 2 < Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h5, hpos]

theorem one_lt_criticalRatio : (1 : ℝ) < (3 + Real.sqrt 5) / 4 := by
  have := two_lt_sqrt5
  linarith

theorem continuousOn_coareaStationaryDefect :
    ContinuousOn coareaStationaryDefect (Ici (1 : ℝ)) := by
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hne : 2 * r - 1 ≠ 0 := by
    intro h
    linarith
  have hcont : ContinuousAt coareaStationaryDefect r := by
    refine ContinuousAt.sub (Real.continuousAt_log (ne_of_gt hr0)) ?_
    refine ContinuousAt.div ?_ ?_ hne
    · exact continuousAt_const.mul (continuousAt_id.sub continuousAt_const)
    · exact (continuousAt_const.mul continuousAt_id).sub continuousAt_const
  exact hcont.continuousWithinAt

theorem deriv_coareaStationaryDefect {r : ℝ} (hr : 0 < r) (hr2 : 2 * r - 1 ≠ 0) :
    deriv coareaStationaryDefect r = (4 * r ^ 2 - 6 * r + 1) / (r * (2 * r - 1) ^ 2) :=
  (hasDerivAt_coareaStationaryDefect hr hr2).deriv

theorem strictAntiOn_coareaStationaryDefect :
    StrictAntiOn coareaStationaryDefect (Icc 1 ((3 + Real.sqrt 5) / 4)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuousOn_coareaStationaryDefect.mono (fun r hr => hr.1)) fun r hr => ?_
  rw [interior_Icc] at hr
  have hr1 : (1 : ℝ) < r := hr.1
  have hr0 : (0 : ℝ) < r := by linarith
  have hne : 2 * r - 1 ≠ 0 := by
    intro h
    linarith
  rw [deriv_coareaStationaryDefect hr0 hne]
  exact coareaStationaryDefect_deriv_neg hr1 hr.2

theorem strictMonoOn_coareaStationaryDefect :
    StrictMonoOn coareaStationaryDefect (Ici ((3 + Real.sqrt 5) / 4)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _)
    (continuousOn_coareaStationaryDefect.mono
      (fun r hr => le_trans one_lt_criticalRatio.le hr)) fun r hr => ?_
  rw [interior_Ici] at hr
  have hr1 : (1 : ℝ) < r := lt_trans one_lt_criticalRatio hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hne : 2 * r - 1 ≠ 0 := by
    intro h
    linarith
  rw [deriv_coareaStationaryDefect hr0 hne]
  exact coareaStationaryDefect_deriv_pos hr

theorem coareaStationaryDefect_neg_of_mem {r : ℝ} (hr1 : 1 < r)
    (hr : r ≤ (3 + Real.sqrt 5) / 4) : coareaStationaryDefect r < 0 := by
  have h := strictAntiOn_coareaStationaryDefect (a := 1) (b := r)
    ⟨le_rfl, one_lt_criticalRatio.le⟩ ⟨hr1.le, hr⟩ hr1
  rwa [coareaStationaryDefect_one] at h

/-! ## The unique stationary ratio -/

theorem tendsto_coareaStationaryDefect_atTop :
    Tendsto coareaStationaryDefect atTop atTop := by
  have hquot : Tendsto (fun r : ℝ => 2 * (r - 1) / (2 * r - 1)) atTop (nhds 1) := by
    have hrw : ∀ r : ℝ, 0 < r → 2 * (r - 1) / (2 * r - 1) = (2 - 2 / r) / (2 - 1 / r) := by
      intro r hr
      have hne : r ≠ 0 := ne_of_gt hr
      field_simp
      ring
    have hnum : Tendsto (fun r : ℝ => 2 - 2 / r) atTop (nhds 2) := by
      have h := tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id (a := (2 : ℝ)))
      simpa using h
    have hden : Tendsto (fun r : ℝ => 2 - 1 / r) atTop (nhds 2) := by
      have h := tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id (a := (1 : ℝ)))
      simpa using h
    have hdiv := hnum.div hden (by norm_num)
    have hval : (2 : ℝ) / 2 = 1 := by norm_num
    rw [hval] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (hrw r hr).symm
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have h := hlog.atTop_add (hquot.neg)
  refine h.congr fun r => ?_
  rw [coareaStationaryDefect]
  ring

/-- **The unique stationary shell ratio.** -/
theorem exists_unique_coareaStationaryRatio :
    ∃! r : ℝ, 1 < r ∧ coareaStationaryDefect r = 0 := by
  have hcrit := one_lt_criticalRatio
  have hneg : coareaStationaryDefect ((3 + Real.sqrt 5) / 4) < 0 :=
    coareaStationaryDefect_neg_of_mem hcrit le_rfl
  obtain ⟨b, hb⟩ := (tendsto_coareaStationaryDefect_atTop.eventually_ge_atTop 1).exists
  have hble : (3 + Real.sqrt 5) / 4 ≤ b := by
    by_contra hcon
    push_neg at hcon
    have hbneg : coareaStationaryDefect b < 0 := by
      rcases le_or_lt b 1 with h | h
      · have hmono := strictAntiOn_coareaStationaryDefect
        rcases eq_or_lt_of_le h with heq | hlt
        · rw [heq, coareaStationaryDefect_one] at hb
          linarith
        · -- `b < 1`: the defect is not covered; use the monotone branch instead
          exfalso
          have hlog : Real.log b < 0 := Real.log_neg (by nlinarith [hb]) hlt
          have hfrac : 0 ≤ 2 * (b - 1) / (2 * b - 1) → False := by
            intro _
            linarith [hb, hlog]
          have hbpos : 0 < b := by nlinarith [hb]
          have h2b : 2 * b - 1 ≠ 0 := by
            intro hz
            have : b = 1 / 2 := by linarith
            rw [this] at hb
            have : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
            simp [coareaStationaryDefect, this] at hb
            linarith
          have hval : coareaStationaryDefect b < 0 := by
            rw [coareaStationaryDefect]
            rcases lt_or_gt_of_ne h2b with hlt2 | hgt2
            · have hnum : 2 * (b - 1) < 0 := by linarith
              have hdiv : 0 < 2 * (b - 1) / (2 * b - 1) := div_pos_of_neg_of_neg hnum hlt2
              linarith
            · have hnum : 2 * (b - 1) < 0 := by linarith
              have hdiv : 2 * (b - 1) / (2 * b - 1) < 0 := div_neg_of_neg_of_pos hnum hgt2
              have : Real.log b < 0 := hlog
              nlinarith [hb, hdiv, hlog]
          linarith
      · exact coareaStationaryDefect_neg_of_mem h hcon.le
    linarith
  have hcont : ContinuousOn coareaStationaryDefect (Icc ((3 + Real.sqrt 5) / 4) b) :=
    continuousOn_coareaStationaryDefect.mono fun r hr => le_trans hcrit.le hr.1
  have hzero : ∃ r ∈ Icc ((3 + Real.sqrt 5) / 4) b, coareaStationaryDefect r = 0 := by
    have hmem : (0 : ℝ) ∈ Icc (coareaStationaryDefect ((3 + Real.sqrt 5) / 4))
        (coareaStationaryDefect b) := ⟨hneg.le, by linarith⟩
    exact intermediate_value_Icc hble hcont hmem
  obtain ⟨r, hrmem, hr0⟩ := hzero
  have hr1 : 1 < r := lt_of_lt_of_le hcrit hrmem.1
  refine ⟨r, ⟨hr1, hr0⟩, fun s hs => ?_⟩
  obtain ⟨hs1, hs0⟩ := hs
  rcases le_or_lt s ((3 + Real.sqrt 5) / 4) with hle | hlt
  · exact absurd hs0 (ne_of_lt (coareaStationaryDefect_neg_of_mem hs1 hle))
  · have hsmem : s ∈ Ici ((3 + Real.sqrt 5) / 4) := hlt.le
    have hrmem' : r ∈ Ici ((3 + Real.sqrt 5) / 4) := hrmem.1
    rcases lt_trichotomy s r with h | h | h
    · exact absurd (strictMonoOn_coareaStationaryDefect hsmem hrmem' h) (by rw [hr0, hs0]; simp)
    · exact h
    · exact absurd (strictMonoOn_coareaStationaryDefect hrmem' hsmem h) (by rw [hr0, hs0]; simp)

end

end RHTower
