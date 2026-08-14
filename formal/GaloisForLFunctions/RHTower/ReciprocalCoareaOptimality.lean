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
  have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun r : ℝ => 2 - 2 * r⁻¹) atTop (nhds 2) := by
    have h := hinv.const_mul (2 : ℝ)
    rw [mul_zero] at h
    have h2 : Tendsto (fun r : ℝ => (2 : ℝ) - 2 * r⁻¹) atTop (nhds ((2 : ℝ) - 0)) :=
      tendsto_const_nhds.sub h
    simpa using h2
  have hden : Tendsto (fun r : ℝ => 2 - r⁻¹) atTop (nhds 2) := by
    have h2 : Tendsto (fun r : ℝ => (2 : ℝ) - r⁻¹) atTop (nhds ((2 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hinv
    simpa using h2
  have hquot : Tendsto (fun r : ℝ => 2 * (r - 1) / (2 * r - 1)) atTop (nhds 1) := by
    have hdiv := hnum.div hden (by norm_num)
    have hval : (2 : ℝ) / 2 = 1 := by norm_num
    rw [hval] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hne : r ≠ 0 := ne_of_gt hr
    simp only [Pi.div_apply]
    field_simp
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have h := hlog.atTop_add hquot.neg
  refine h.congr fun r => ?_
  rw [coareaStationaryDefect]
  ring

/-- **The unique stationary shell ratio.** -/
theorem exists_unique_coareaStationaryRatio :
    ∃! r : ℝ, 1 < r ∧ coareaStationaryDefect r = 0 := by
  have hcrit := one_lt_criticalRatio
  have hneg : coareaStationaryDefect ((3 + Real.sqrt 5) / 4) < 0 :=
    coareaStationaryDefect_neg_of_mem hcrit le_rfl
  obtain ⟨b, hb, hble⟩ := ((tendsto_coareaStationaryDefect_atTop.eventually_ge_atTop 1).and
    (eventually_ge_atTop ((3 + Real.sqrt 5) / 4))).exists
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
  rcases le_or_gt s ((3 + Real.sqrt 5) / 4) with hle | hlt
  · exact absurd hs0 (ne_of_lt (coareaStationaryDefect_neg_of_mem hs1 hle))
  · have hsmem : s ∈ Ici ((3 + Real.sqrt 5) / 4) := hlt.le
    have hrmem' : r ∈ Ici ((3 + Real.sqrt 5) / 4) := hrmem.1
    rcases lt_trichotomy s r with h | h | h
    · exact absurd (strictMonoOn_coareaStationaryDefect hsmem hrmem' h) (by rw [hr0, hs0]; simp)
    · exact h
    · exact absurd (strictMonoOn_coareaStationaryDefect hrmem' hsmem h) (by rw [hr0, hs0]; simp)

/-! ## The certificate cost of a partition -/

theorem coareaRatioCost_pos {r : ℝ} (hr : 1 < r) : 0 < coareaRatioCost r := by
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hnum : 0 < Real.sqrt (r * (r - 1)) := by
    refine Real.sqrt_pos.mpr ?_
    have h1 : 0 < r := by linarith
    have h2 : 0 < r - 1 := by linarith
    positivity
  exact div_pos hnum hlog

/-- The optimal certificate coefficient. -/
def coareaMinCost : ℝ := sInf (coareaRatioCost '' Ioi 1)

theorem coareaMinCost_nonneg : 0 ≤ coareaMinCost := by
  refine Real.sInf_nonneg ?_
  rintro y ⟨r, hr, rfl⟩
  exact (coareaRatioCost_pos hr).le

theorem coareaMinCost_le {r : ℝ} (hr : 1 < r) : coareaMinCost ≤ coareaRatioCost r := by
  refine csInf_le ⟨0, ?_⟩ ⟨r, hr, rfl⟩
  rintro y ⟨s, hs, rfl⟩
  exact (coareaRatioCost_pos hs).le

/-- **The per-shell certificate inequality.**  Every shell of ratio `r > 1` costs at least
`c_* log r`. -/
theorem coareaMinCost_mul_log_le {r : ℝ} (hr : 1 < r) :
    coareaMinCost * Real.log r ≤ Real.sqrt (r * (r - 1)) := by
  have hlog : 0 < Real.log r := Real.log_pos hr
  have h := coareaMinCost_le hr
  rw [coareaRatioCost, le_div_iff₀ hlog] at h
  exact h

/-! ## Partitions -/

/-- **The shell-count theorem under a ratio cap.**  A partition whose consecutive ratios are at
most `R` needs at least `log(u_K/u_0)/log R` shells. -/
theorem log_le_card_mul_log_of_ratio_le {u : ℕ → ℝ} {K : ℕ} {R : ℝ}
    (hpos : ∀ j ≤ K, 0 < u j) (hratio : ∀ j < K, u (j + 1) ≤ R * u j) :
    Real.log (u K / u 0) ≤ (K : ℝ) * Real.log R := by
  induction K with
  | zero =>
      have h0 : 0 < u 0 := hpos 0 le_rfl
      rw [div_self (ne_of_gt h0), Real.log_one]
      norm_num
  | succ K ih =>
      have hposK : ∀ j ≤ K, 0 < u j := fun j hj => hpos j (by omega)
      have hratioK : ∀ j < K, u (j + 1) ≤ R * u j := fun j hj => hratio j (by omega)
      have hstep := ih hposK hratioK
      have hK1 : 0 < u (K + 1) := hpos (K + 1) le_rfl
      have hK0 : 0 < u K := hpos K (by omega)
      have h0 : 0 < u 0 := hpos 0 (by omega)
      have hlast := hratio K (by omega)
      have hsplit : Real.log (u (K + 1) / u 0)
          = Real.log (u (K + 1) / u K) + Real.log (u K / u 0) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      have hratiolog : Real.log (u (K + 1) / u K) ≤ Real.log R := by
        have hle : u (K + 1) / u K ≤ R := by
          rw [div_le_iff₀ hK0]
          linarith [hlast]
        have hpos' : 0 < u (K + 1) / u K := by positivity
        exact Real.log_le_log hpos' hle
      rw [hsplit]
      push_cast
      linarith

/-- The ratio-capped shell count in divided form. -/
theorem card_ge_log_div_log {u : ℕ → ℝ} {K : ℕ} {R : ℝ} (hR : 1 < R)
    (hpos : ∀ j ≤ K, 0 < u j) (hratio : ∀ j < K, u (j + 1) ≤ R * u j) :
    Real.log (u K / u 0) / Real.log R ≤ (K : ℝ) := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  rw [div_le_iff₀ hlogR]
  exact log_le_card_mul_log_of_ratio_le hpos hratio

/-- **The lower bound for every interval partition.**  Summing the per-shell inequality
telescopes to `c_* log(u_K/u_0)`. -/
theorem coareaMinCost_mul_log_le_sum {u : ℕ → ℝ} {K : ℕ}
    (hpos : ∀ j ≤ K, 0 < u j) (hmono : ∀ j < K, u j < u (j + 1)) :
    coareaMinCost * Real.log (u K / u 0)
      ≤ ∑ j ∈ Finset.range K,
        Real.sqrt ((u (j + 1) / u j) * (u (j + 1) / u j - 1)) := by
  induction K with
  | zero =>
      have h0 : 0 < u 0 := hpos 0 le_rfl
      rw [div_self (ne_of_gt h0), Real.log_one, mul_zero, Finset.range_zero,
        Finset.sum_empty]
  | succ K ih =>
      have hposK : ∀ j ≤ K, 0 < u j := fun j hj => hpos j (by omega)
      have hmonoK : ∀ j < K, u j < u (j + 1) := fun j hj => hmono j (by omega)
      have hstep := ih hposK hmonoK
      have hK1 : 0 < u (K + 1) := hpos (K + 1) le_rfl
      have hK0 : 0 < u K := hpos K (by omega)
      have h0 : 0 < u 0 := hpos 0 (by omega)
      have hlast := hmono K (by omega)
      have hratio : 1 < u (K + 1) / u K := by
        rw [lt_div_iff₀ hK0]
        linarith
      have hshell := coareaMinCost_mul_log_le hratio
      have hsplit : Real.log (u (K + 1) / u 0)
          = Real.log (u (K + 1) / u K) + Real.log (u K / u 0) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [hsplit, Finset.sum_range_succ, mul_add]
      linarith

/-! ## The optimal ratio attains the infimum -/

theorem hasDerivAt_coareaRatioCost {r : ℝ} (hr : 1 < r) :
    HasDerivAt coareaRatioCost
      ((2 * r - 1) * coareaStationaryDefect r
        / (2 * Real.sqrt (r * (r - 1)) * Real.log r ^ 2)) r := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hg : (0 : ℝ) < r * (r - 1) := by
    have : (0 : ℝ) < r - 1 := by linarith
    positivity
  have hsqrt : 0 < Real.sqrt (r * (r - 1)) := Real.sqrt_pos.mpr hg
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hlogne : Real.log r ≠ 0 := ne_of_gt hlog
  have hbase : HasDerivAt (fun s : ℝ => s * (s - 1)) (2 * r - 1) r := by
    have h := (hasDerivAt_id r).mul ((hasDerivAt_id r).sub_const 1)
    refine h.congr_deriv ?_
    simp
    ring
  have hsq : HasDerivAt (fun s : ℝ => Real.sqrt (s * (s - 1)))
      ((2 * r - 1) / (2 * Real.sqrt (r * (r - 1)))) r := by
    have h := (Real.hasDerivAt_sqrt (ne_of_gt hg)).comp r hbase
    refine h.congr_deriv ?_
    field_simp
  have hlogd : HasDerivAt Real.log r⁻¹ r := Real.hasDerivAt_log (ne_of_gt hr0)
  have hquot := hsq.div hlogd hlogne
  refine hquot.congr_deriv ?_
  rw [coareaStationaryDefect]
  have hSne : Real.sqrt (r * (r - 1)) ≠ 0 := ne_of_gt hsqrt
  have hSsq : Real.sqrt (r * (r - 1)) * Real.sqrt (r * (r - 1)) = r * (r - 1) :=
    Real.mul_self_sqrt hg.le
  have hSr : Real.sqrt (r * (r - 1)) * r⁻¹ = (r - 1) / Real.sqrt (r * (r - 1)) := by
    rw [eq_div_iff hSne]
    field_simp
    linear_combination hSsq
  rw [hSr]
  have h2r : (2 : ℝ) * r - 1 ≠ 0 := by
    intro h
    linarith
  field_simp

theorem criticalRatio_lt_of_defect_zero {r : ℝ} (hr : 1 < r)
    (hzero : coareaStationaryDefect r = 0) : (3 + Real.sqrt 5) / 4 < r := by
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd hzero (ne_of_lt (coareaStationaryDefect_neg_of_mem hr hcon))

theorem coareaRatioCost_deriv_sign {r r' : ℝ} (hr : 1 < r) (hr' : 1 < r')
    (hzero : coareaStationaryDefect r' = 0) :
    (r < r' → coareaStationaryDefect r < 0) ∧ (r' < r → 0 < coareaStationaryDefect r) := by
  have hcrit' := criticalRatio_lt_of_defect_zero hr' hzero
  constructor
  · intro hlt
    rcases le_or_gt r ((3 + Real.sqrt 5) / 4) with hle | hgt
    · exact coareaStationaryDefect_neg_of_mem hr hle
    · have hmono := strictMonoOn_coareaStationaryDefect hgt.le hcrit'.le hlt
      rw [hzero] at hmono
      exact hmono
  · intro hgt
    have hrge : (3 + Real.sqrt 5) / 4 < r := lt_trans hcrit' hgt
    have hmono := strictMonoOn_coareaStationaryDefect hcrit'.le hrge.le hgt
    rw [hzero] at hmono
    exact hmono

/-- **The stationary ratio is the global minimizer of the certificate cost.** -/
theorem coareaRatioCost_min {r' : ℝ} (hr' : 1 < r') (hzero : coareaStationaryDefect r' = 0)
    {r : ℝ} (hr : 1 < r) : coareaRatioCost r' ≤ coareaRatioCost r := by
  have hanti : StrictAntiOn coareaRatioCost (Ioc 1 r') := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc _ _) ?_ fun s hs => ?_
    · intro s hs
      have hs1 : (1 : ℝ) < s := hs.1
      refine ContinuousAt.continuousWithinAt ?_
      exact ((Real.continuous_sqrt.continuousAt).comp
        (by fun_prop : ContinuousAt (fun t : ℝ => t * (t - 1)) s)).div
        (Real.continuousAt_log (by linarith)) (ne_of_gt (Real.log_pos hs1))
    · rw [interior_Ioc] at hs
      have hs1 : (1 : ℝ) < s := hs.1
      have hderiv := hasDerivAt_coareaRatioCost hs1
      rw [hderiv.deriv]
      have hsign := (coareaRatioCost_deriv_sign hs1 hr' hzero).1 hs.2
      have hg : (0 : ℝ) < s * (s - 1) := by
        have : (0 : ℝ) < s - 1 := by linarith
        positivity
      have hsqrt : 0 < Real.sqrt (s * (s - 1)) := Real.sqrt_pos.mpr hg
      have hlog : 0 < Real.log s := Real.log_pos hs1
      have hden : 0 < 2 * Real.sqrt (s * (s - 1)) * Real.log s ^ 2 := by positivity
      have hnum : (2 * s - 1) * coareaStationaryDefect s < 0 := by
        have h2s : (0 : ℝ) < 2 * s - 1 := by linarith
        exact mul_neg_of_pos_of_neg h2s hsign
      exact div_neg_of_neg_of_pos hnum hden
  have hmono : StrictMonoOn coareaRatioCost (Ici r') := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun s hs => ?_
    · intro s hs
      have hs1 : (1 : ℝ) < s := lt_of_lt_of_le hr' hs
      refine ContinuousAt.continuousWithinAt ?_
      exact ((Real.continuous_sqrt.continuousAt).comp
        (by fun_prop : ContinuousAt (fun t : ℝ => t * (t - 1)) s)).div
        (Real.continuousAt_log (by linarith)) (ne_of_gt (Real.log_pos hs1))
    · rw [interior_Ici] at hs
      have hs1 : (1 : ℝ) < s := lt_trans hr' hs
      have hderiv := hasDerivAt_coareaRatioCost hs1
      rw [hderiv.deriv]
      have hsign := (coareaRatioCost_deriv_sign hs1 hr' hzero).2 hs
      have hg : (0 : ℝ) < s * (s - 1) := by
        have : (0 : ℝ) < s - 1 := by linarith
        positivity
      have hsqrt : 0 < Real.sqrt (s * (s - 1)) := Real.sqrt_pos.mpr hg
      have hlog : 0 < Real.log s := Real.log_pos hs1
      have hden : 0 < 2 * Real.sqrt (s * (s - 1)) * Real.log s ^ 2 := by positivity
      have hnum : 0 < (2 * s - 1) * coareaStationaryDefect s := by
        have h2s : (0 : ℝ) < 2 * s - 1 := by linarith
        exact mul_pos h2s hsign
      exact div_pos hnum hden
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · exact (hanti ⟨hr, hlt.le⟩ ⟨hr', le_rfl⟩ hlt).le
  · rw [heq]
  · exact (hmono Set.self_mem_Ici hgt.le hgt).le

/-- **The infimum is attained at the stationary ratio.** -/
theorem coareaMinCost_eq {r' : ℝ} (hr' : 1 < r') (hzero : coareaStationaryDefect r' = 0) :
    coareaMinCost = coareaRatioCost r' := by
  refine le_antisymm (coareaMinCost_le hr') ?_
  refine le_csInf ⟨coareaRatioCost r', r', hr', rfl⟩ ?_
  rintro y ⟨s, hs, rfl⟩
  exact coareaRatioCost_min hr' hzero hs

end

end RHTower
