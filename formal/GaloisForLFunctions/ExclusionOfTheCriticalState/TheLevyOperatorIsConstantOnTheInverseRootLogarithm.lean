import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateObeysAComparisonPrincipleAtTheWall
import GaloisForLFunctions.RHTower.SeparatedBumpPrimeBlindPositivity
import GaloisForLFunctions.RHTower.WeilLevyHarmonicDoublingPairCoupling

/-!
# The Lévy operator is constant on the inverse root logarithm

The cutoff Lévy operator of the Gamma form acts on a bounded profile by two rows,

`𝔏_δ ψ(u) = ∫_{h>δ} ω(h) (ψ(u) − ψ(u+h)) dh + ∫_{h>δ} ω(h) (ψ(u) − ψ(u−h)) dh`
(`cutoffLevy_eq_rows`).

Let `ψ_k(u) = 1/√(log(1/|u|))` on the collar `(−k, 0)` and `0` elsewhere, `k ≤ 1/4`.

**Theorem** (`abs_cutoffLevy_wallLogProfile_sub_le`). For `0 < δ ≤ t < k/2`,

`|𝔏_δ ψ_k(−t) − √(log(1/k))| ≤ 9`.

The value does not depend on the point: up to a bounded error, uniform in the cutoff, the
operator is constant on the inverse root logarithm.

Mechanism. `ω(h) = 1/(2h) + O(1)`. With `g(s) = 1/√(log(1/s))`: the jumps through the wall
contribute `g(t) · ½ log(1/t) = ½ √(log(1/t))`; the jumps past `−k` contribute
`g(t) · ½ log(1/k)`; the jumps into `(2t, k)` contribute
`−∫_{2t}^k (g(s) − g(t)) ds/(2s)`, which is exact because `g(s)/(2s)` is the derivative of
`−√(log(1/s))`; the jumps of length at most `t` are bounded since `|g(t ± h) − g(t)| ≲ h/t`.
In the sum the logarithms of the point cancel and `√(log(1/k))` remains. Among the profiles
`B(log(1/s))` only `B(ℓ) = ℓ^{-1/2}` has this cancellation: it solves `B ℓ − ½ ∫ B = const`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The kernel near the origin -/

theorem archLevyDensity_le_half_inv_add {h : ℝ} (hh : 0 < h) :
    archLevyDensity h ≤ 1 / (2 * h) + 1 / 4 := by
  have h1 := WeilLevyHarmonicDoubling.two_mul_archLevyDensity_le_inv_add_half hh
  have e : 1 / (2 * h) = 1 / h / 2 := by rw [div_div, mul_comm h 2]
  rw [e]
  linarith only [h1]

theorem half_inv_sub_le_archLevyDensity {h : ℝ} (hh : 0 < h) :
    1 / (2 * h) - 1 / 4 ≤ archLevyDensity h := by
  have h1 := SeparatedBump.archLevyDensity_ge hh
  have h2 : 1 - h / 2 ≤ Real.exp (-h / 2) := by
    have h := Real.add_one_le_exp (-h / 2)
    linarith only [h]
  have h3 : (1 - h / 2) * (2 * h)⁻¹ ≤ Real.exp (-h / 2) * (2 * h)⁻¹ :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv] at h3
  have e2 : h / 2 / (2 * h) = 1 / 4 := by
    rw [div_div, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  have e : (1 - h / 2) / (2 * h) = 1 / (2 * h) - 1 / 4 := by rw [sub_div, e2]
  linarith only [h1, h3, e]

theorem archLevyDensity_mul_self_le_one {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 2) :
    archLevyDensity h * h ≤ 1 := by
  have h1 := mul_le_mul_of_nonneg_right
    (WeilLevyHarmonicDoubling.two_mul_archLevyDensity_le_inv_add_half hh) hh.le
  rw [add_mul, one_div, inv_mul_cancel₀ hh.ne'] at h1
  linarith only [h1, hh2]

/-- The mass of the jumps longer than `x ≤ 1` is `½ log(2/x)` up to `2`. -/
theorem log_two_div_le_two_mul_levyTail {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log (2 / x) ≤ 2 * ∫ h in Ioi x, archLevyDensity h := by
  rw [WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hx]
  have h := ArithmeticIncidencePositivity.log_one_div_le_two_mul_archLevyAntideriv
    (w := x / 2) (by positivity) (by linarith only [hx1])
  rwa [show 2 * (x / 2) = x by ring, show 1 / (x / 2) = 2 / x by field_simp] at h

theorem two_mul_levyTail_le_log_two_div_add {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    2 * (∫ h in Ioi x, archLevyDensity h) ≤ Real.log (2 / x) + 4 := by
  rw [WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hx]
  have h := ArithmeticIncidencePositivity.two_mul_archLevyAntideriv_le_log_one_div_add_four
    (w := x / 2) (by positivity) (by linarith only [hx1])
  rwa [show 2 * (x / 2) = x by ring, show 1 / (x / 2) = 2 / x by field_simp] at h

/-! ### The two rows of the cutoff operator -/

theorem integrable_cutoffKernel_mul_of_bounded {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ}
    (hfm : Measurable f) {B : ℝ} (hB : ∀ h, |f h| ≤ B) :
    Integrable fun h => halfLineGammaCutoffKernel δ h * f h := by
  refine ((integrable_halfLineGammaCutoffKernel hδ).mul_const B).mono'
    ((measurable_halfLineGammaCutoffKernel δ).mul hfm).aestronglyMeasurable
    (Eventually.of_forall fun h => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (halfLineGammaCutoffKernel_nonneg hδ h)]
  exact mul_le_mul_of_nonneg_left (hB h) (halfLineGammaCutoffKernel_nonneg hδ h)

theorem integrableOn_archLevyDensity_mul_of_bounded {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ}
    (hfm : Measurable f) {B : ℝ} (hB : ∀ h, |f h| ≤ B) :
    IntegrableOn (fun h => archLevyDensity h * f h) (Ioi δ) := by
  have h := (integrable_cutoffKernel_mul_of_bounded hδ hfm hB).integrableOn (s := Ioi δ)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show halfLineGammaCutoffKernel δ x * f x = archLevyDensity x * f x
  unfold halfLineGammaCutoffKernel
  rw [indicator_of_mem hx]

/-- **The two rows.** On a bounded profile the cutoff operator is the sum of the jumps towards
the wall and of the jumps away from it. -/
theorem cutoffLevy_eq_rows {δ : ℝ} (hδ : 0 < δ) {ψ : ℝ → ℝ} (hψm : Measurable ψ) {B : ℝ}
    (hB : ∀ u, |ψ u| ≤ B) (u : ℝ) :
    cutoffLevy δ ψ u = (∫ h in Ioi δ, archLevyDensity h * (ψ u - ψ (u + h))) +
      ∫ h in Ioi δ, archLevyDensity h * (ψ u - ψ (u - h)) := by
  have hm1 : Measurable fun h => ψ (u - h) := hψm.comp (measurable_const.sub measurable_id)
  have hm2 : Measurable fun h => ψ (u + h) := hψm.comp (measurable_const.add measurable_id)
  have hK1 := integrable_cutoffKernel_mul_of_bounded hδ hm1 fun h => hB (u - h)
  have hK2 : Integrable fun h => halfLineGammaCutoffKernel δ h * ψ (u - -h) := by
    simpa only [sub_neg_eq_add] using
      integrable_cutoffKernel_mul_of_bounded hδ hm2 fun h => hB (u + h)
  have hconv : lineConvolution (symCutoffKernel δ) ψ u =
      (∫ h in Ioi δ, archLevyDensity h * ψ (u - h)) +
        ∫ h in Ioi δ, archLevyDensity h * ψ (u + h) := by
    have e := integral_symCutoffKernel_mul (f := fun s => ψ (u - s)) hK1 hK2
    simp only [sub_neg_eq_add] at e
    exact e
  have hω : IntegrableOn archLevyDensity (Ioi δ) :=
    WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ
  have h1 := integrableOn_archLevyDensity_mul_of_bounded hδ hm1 fun h => hB (u - h)
  have h2 := integrableOn_archLevyDensity_mul_of_bounded hδ hm2 fun h => hB (u + h)
  have e1 : ∫ h in Ioi δ, archLevyDensity h * (ψ u - ψ (u + h)) =
      (∫ h in Ioi δ, archLevyDensity h) * ψ u - ∫ h in Ioi δ, archLevyDensity h * ψ (u + h) := by
    rw [← integral_mul_const, ← integral_sub (hω.mul_const _) h2]
    exact integral_congr_ae (Eventually.of_forall fun h => mul_sub _ _ _)
  have e2 : ∫ h in Ioi δ, archLevyDensity h * (ψ u - ψ (u - h)) =
      (∫ h in Ioi δ, archLevyDensity h) * ψ u - ∫ h in Ioi δ, archLevyDensity h * ψ (u - h) := by
    rw [← integral_mul_const, ← integral_sub (hω.mul_const _) h1]
    exact integral_congr_ae (Eventually.of_forall fun h => mul_sub _ _ _)
  unfold cutoffLevy
  rw [hconv, e1, e2]
  ring

/-! ### The scale of the wall -/

/-- The scale of the wall, `√(log(1/t))`. -/
def wallRootLog (t : ℝ) : ℝ := Real.sqrt (Real.log (1 / t))

theorem log_one_div_eq_neg_log (t : ℝ) : Real.log (1 / t) = -Real.log t := by
  rw [one_div, Real.log_inv]

theorem one_le_neg_log {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4) : 1 ≤ -Real.log t := by
  have h4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [log_one_div_eq_neg_log, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1 : Real.log t ≤ Real.log (1 / 4) := Real.log_le_log ht ht4
  have h2 := Real.log_two_gt_d9
  linarith only [h1, h4, h2]

theorem one_le_wallRootLog {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4) : 1 ≤ wallRootLog t := by
  unfold wallRootLog
  rw [Real.one_le_sqrt, log_one_div_eq_neg_log]
  exact one_le_neg_log ht ht4

theorem wallRootLog_sq {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4) :
    wallRootLog t ^ 2 = -Real.log t := by
  unfold wallRootLog
  rw [log_one_div_eq_neg_log, Real.sq_sqrt (by linarith only [one_le_neg_log ht ht4])]

theorem wallRootLog_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : wallRootLog t ≤ wallRootLog s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  unfold wallRootLog
  exact Real.sqrt_le_sqrt (Real.log_le_log (one_div_pos.mpr ht) (one_div_le_one_div_of_le hs hst))

/-- `√(log(1/s)) − √(log(1/t)) ≤ ½ log(t/s)` for `s ≤ t ≤ 1/4`. -/
theorem wallRootLog_sub_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht4 : t ≤ 1 / 4) :
    wallRootLog s - wallRootLog t ≤ (Real.log t - Real.log s) / 2 := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have ha := one_le_wallRootLog hs (hst.trans ht4)
  have hb := one_le_wallRootLog ht ht4
  have hab := wallRootLog_anti hs hst
  have h2a := wallRootLog_sq hs (hst.trans ht4)
  have h2b := wallRootLog_sq ht ht4
  nlinarith only [h2a, h2b, mul_nonneg (sub_nonneg.mpr hab)
    (by linarith only [ha, hb] : (0 : ℝ) ≤ wallRootLog s + wallRootLog t - 2)]

theorem inv_wallRootLog_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht4 : t ≤ 1 / 4) :
    (wallRootLog s)⁻¹ ≤ (wallRootLog t)⁻¹ :=
  inv_anti₀ (lt_of_lt_of_le zero_lt_one (one_le_wallRootLog (lt_of_lt_of_le hs hst) ht4))
    (wallRootLog_anti hs hst)

/-- The increments of the inverse root logarithm: `g(t) − g(s) ≤ (t − s)/(2s)` for
`s ≤ t ≤ 1/4`. -/
theorem inv_wallRootLog_sub_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht4 : t ≤ 1 / 4) :
    (wallRootLog t)⁻¹ - (wallRootLog s)⁻¹ ≤ (t - s) / (2 * s) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have ha := one_le_wallRootLog hs (hst.trans ht4)
  have hb := one_le_wallRootLog ht ht4
  have hab := wallRootLog_anti hs hst
  have h1 := wallRootLog_sub_le hs hst ht4
  have hlog : Real.log t - Real.log s ≤ (t - s) / s := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht hs)
    rw [Real.log_div ht.ne' hs.ne'] at h
    have e : t / s - 1 = (t - s) / s := by rw [sub_div, div_self hs.ne']
    linarith only [h, e]
  have h2 : (wallRootLog t)⁻¹ - (wallRootLog s)⁻¹ ≤ wallRootLog s - wallRootLog t := by
    rw [inv_sub_inv (lt_of_lt_of_le zero_lt_one hb).ne' (lt_of_lt_of_le zero_lt_one ha).ne']
    exact div_le_self (sub_nonneg.mpr hab) (by nlinarith only [ha, hb])
  have e : (t - s) / (2 * s) = (t - s) / s / 2 := by rw [div_div, mul_comm s 2]
  rw [e]
  linarith only [h1, h2, hlog]

theorem hasDerivAt_wallRootLog {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1 / 4) :
    HasDerivAt wallRootLog (-((wallRootLog s)⁻¹ / (2 * s))) s := by
  have hpos : 1 ≤ -Real.log s := one_le_neg_log hs hs4
  have h1 : HasDerivAt (fun y : ℝ => -Real.log y) (-s⁻¹) s := (Real.hasDerivAt_log hs.ne').neg
  have h2 := h1.sqrt (lt_of_lt_of_le zero_lt_one hpos).ne'
  have e : wallRootLog = fun y : ℝ => Real.sqrt (-Real.log y) := by
    funext y
    unfold wallRootLog
    rw [log_one_div_eq_neg_log]
  have hR : wallRootLog s = Real.sqrt (-Real.log s) := congrFun e s
  have hRpos : 0 < Real.sqrt (-Real.log s) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hpos)
  have h3 : HasDerivAt wallRootLog (-s⁻¹ / (2 * Real.sqrt (-Real.log s))) s := by
    rw [e]
    exact h2
  refine h3.congr_deriv ?_
  rw [hR, neg_div, neg_inj, div_eq_div_iff (mul_pos two_pos hRpos).ne' (mul_pos two_pos hs).ne',
    mul_left_comm, inv_mul_cancel₀ hs.ne', mul_left_comm, inv_mul_cancel₀ hRpos.ne']

/-- `−√(log(1/s)) − (c/2) log s` is a primitive of `(g(s) − c)/(2s)`. -/
theorem hasDerivAt_wallPrimitive (c : ℝ) {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1 / 4) :
    HasDerivAt (fun y : ℝ => -wallRootLog y - c / 2 * Real.log y)
      (((wallRootLog s)⁻¹ - c) / (2 * s)) s := by
  have h1 := (hasDerivAt_wallRootLog hs hs4).neg
  have h2 := (Real.hasDerivAt_log hs.ne').const_mul (c / 2)
  refine (h1.sub h2).congr_deriv ?_
  rw [neg_neg, sub_div, ← div_eq_mul_inv, div_div]

/-! ### The inverse root logarithm on a collar -/

/-- The inverse root logarithm on the collar `(−k, 0)`, zero elsewhere. -/
def wallLogProfile (k u : ℝ) : ℝ := if -k < u ∧ u < 0 then (wallRootLog (-u))⁻¹ else 0

theorem wallLogProfile_of_mem {k u : ℝ} (h1 : -k < u) (h2 : u < 0) :
    wallLogProfile k u = (wallRootLog (-u))⁻¹ := if_pos ⟨h1, h2⟩

theorem wallLogProfile_of_le {k u : ℝ} (h : u ≤ -k) : wallLogProfile k u = 0 :=
  if_neg fun h' => absurd h'.1 (not_lt.mpr h)

theorem wallLogProfile_of_nonneg {k u : ℝ} (h : 0 ≤ u) : wallLogProfile k u = 0 :=
  if_neg fun h' => absurd h'.2 (not_lt.mpr h)

theorem measurable_wallLogProfile (k : ℝ) : Measurable (wallLogProfile k) := by
  show Measurable fun u : ℝ => if -k < u ∧ u < 0 then (wallRootLog (-u))⁻¹ else 0
  refine Measurable.ite (measurableSet_Ioo : MeasurableSet (Ioo (-k) (0 : ℝ))) ?_ measurable_const
  show Measurable fun u : ℝ => (Real.sqrt (Real.log (1 / -u)))⁻¹
  exact (Real.continuous_sqrt.measurable.comp
    (Real.measurable_log.comp (measurable_const.div measurable_neg))).inv

theorem wallLogProfile_nonneg (k u : ℝ) : 0 ≤ wallLogProfile k u := by
  by_cases h : -k < u ∧ u < 0
  · rw [wallLogProfile, if_pos h]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  · simp only [wallLogProfile, if_neg h, le_refl]

theorem wallLogProfile_le_one {k : ℝ} (hk4 : k ≤ 1 / 4) (u : ℝ) : wallLogProfile k u ≤ 1 := by
  by_cases h : -k < u ∧ u < 0
  · rw [wallLogProfile, if_pos h]
    exact inv_le_one_of_one_le₀
      (one_le_wallRootLog (by linarith only [h.2]) (by linarith only [h.1, hk4]))
  · simp only [wallLogProfile, if_neg h, zero_le_one]

theorem abs_wallLogProfile_le_one {k : ℝ} (hk4 : k ≤ 1 / 4) (u : ℝ) : |wallLogProfile k u| ≤ 1 := by
  rw [abs_of_nonneg (wallLogProfile_nonneg k u)]
  exact wallLogProfile_le_one hk4 u

/-- **The jumps towards the wall.** They carry the mass of the jumps through the wall,
`g(t) ∫_{h>t} ω`, up to `2`. -/
theorem wallLogProfile_inRow_bounds {k δ t : ℝ} (hk4 : k ≤ 1 / 4) (hδ : 0 < δ) (hδt : δ ≤ t)
    (htk : t < k / 2) :
    (wallRootLog t)⁻¹ * (∫ h in Ioi t, archLevyDensity h) ≤
        (∫ h in Ioi δ, archLevyDensity h *
          (wallLogProfile k (-t) - wallLogProfile k (-t + h))) ∧
      (∫ h in Ioi δ, archLevyDensity h *
          (wallLogProfile k (-t) - wallLogProfile k (-t + h))) ≤
        (wallRootLog t)⁻¹ * (∫ h in Ioi t, archLevyDensity h) + 2 := by
  have ht : 0 < t := lt_of_lt_of_le hδ hδt
  have hk : 0 < k := by linarith only [ht, htk]
  have ht4 : t ≤ 1 / 4 := by linarith only [htk, hk4, hk]
  have hR := one_le_wallRootLog ht ht4
  have hc : wallLogProfile k (-t) = (wallRootLog t)⁻¹ := by
    rw [wallLogProfile_of_mem (by linarith only [htk, hk]) (by linarith only [ht]), neg_neg]
  rw [hc]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (wallRootLog t)⁻¹ := ⟨_, rfl⟩
  rw [← hcdef]
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact inv_nonneg.mpr (le_trans zero_le_one hR)
  have hc1 : c ≤ 1 := by
    rw [hcdef]
    exact inv_le_one_of_one_le₀ hR
  have hψ0 := wallLogProfile_nonneg k
  have hψ1 := wallLogProfile_le_one hk4
  have hm : Measurable fun h : ℝ => c - wallLogProfile k (-t + h) :=
    measurable_const.sub ((measurable_wallLogProfile k).comp (measurable_const.add measurable_id))
  have hint : IntegrableOn (fun h : ℝ => archLevyDensity h * (c - wallLogProfile k (-t + h)))
      (Ioi δ) :=
    integrableOn_archLevyDensity_mul_of_bounded hδ hm (B := 1) fun h =>
      abs_le.mpr ⟨by linarith only [hc0, hψ1 (-t + h)], by linarith only [hc1, hψ0 (-t + h)]⟩
  have hint' := hint.mono_set (Ioi_subset_Ioi hδt)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint hint'
  -- beyond the wall the profile vanishes
  have hfar : ∫ h in Ioi t, archLevyDensity h * (c - wallLogProfile k (-t + h)) =
      c * ∫ h in Ioi t, archLevyDensity h := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
    have hh' : t < h := hh
    show archLevyDensity h * (c - wallLogProfile k (-t + h)) = c * archLevyDensity h
    rw [wallLogProfile_of_nonneg (by linarith only [hh']), sub_zero, mul_comm]
  have hni : IntervalIntegrable
      (fun h : ℝ => archLevyDensity h * (c - wallLogProfile k (-t + h))) volume δ t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδt).mpr (hint.mono_set Ioc_subset_Ioi_self)
  -- inside, the increment is at most `2h/t`
  have hpt : ∀ h ∈ Icc δ t, 0 ≤ archLevyDensity h * (c - wallLogProfile k (-t + h)) ∧
      archLevyDensity h * (c - wallLogProfile k (-t + h)) ≤ 2 / t := by
    intro h hh
    have hh0 : 0 < h := lt_of_lt_of_le hδ hh.1
    have hω0 := (archLevyDensity_pos hh0).le
    have hωh := archLevyDensity_mul_self_le_one hh0 (by linarith only [hh.2, ht4])
    have hv : 0 ≤ c - wallLogProfile k (-t + h) ∧ c - wallLogProfile k (-t + h) ≤ 2 * h / t := by
      rcases lt_or_ge (t / 2) h with hbig | hsmall
      · have h1 : 1 ≤ 2 * h / t := (le_div_iff₀ ht).mpr (by linarith only [hbig])
        have hle : wallLogProfile k (-t + h) ≤ c := by
          rcases eq_or_lt_of_le hh.2 with heq | hlt
          · rw [wallLogProfile_of_nonneg (by linarith only [heq])]
            exact hc0
          · rw [wallLogProfile_of_mem (by linarith only [hh0, htk, hk]) (by linarith only [hlt]),
              hcdef]
            exact inv_wallRootLog_mono (by linarith only [hlt]) (by linarith only [hh0]) ht4
        exact ⟨sub_nonneg.mpr hle, by linarith only [h1, hc1, hψ0 (-t + h)]⟩
      · have hlt : h < t := by linarith only [hsmall, ht]
        have hs : 0 < t - h := by linarith only [hlt]
        have e : -(-t + h) = t - h := by ring
        rw [wallLogProfile_of_mem (by linarith only [hh0, htk, hk]) (by linarith only [hlt]), e,
          hcdef]
        have h1 := inv_wallRootLog_mono hs (by linarith only [hh0]) ht4
        have h2 := inv_wallRootLog_sub_le hs (by linarith only [hh0]) ht4
        have h3 : (t - (t - h)) / (2 * (t - h)) ≤ 2 * h / t := by
          rw [div_le_div_iff₀ (mul_pos two_pos hs) ht]
          nlinarith only [mul_nonneg hh0.le
            (by linarith only [hsmall] : (0 : ℝ) ≤ 3 * t - 4 * h)]
        exact ⟨sub_nonneg.mpr h1, h2.trans h3⟩
    refine ⟨mul_nonneg hω0 hv.1, ?_⟩
    calc archLevyDensity h * (c - wallLogProfile k (-t + h))
        ≤ archLevyDensity h * (2 * h / t) := mul_le_mul_of_nonneg_left hv.2 hω0
      _ = archLevyDensity h * h * (2 / t) := by ring
      _ ≤ 1 * (2 / t) := mul_le_mul_of_nonneg_right hωh (by positivity)
      _ = 2 / t := one_mul _
  have hlow : 0 ≤ ∫ h in δ..t, archLevyDensity h * (c - wallLogProfile k (-t + h)) :=
    intervalIntegral.integral_nonneg hδt fun h hh => (hpt h hh).1
  have hup : ∫ h in δ..t, archLevyDensity h * (c - wallLogProfile k (-t + h)) ≤ 2 := by
    have h1 := intervalIntegral.integral_mono_on hδt hni
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 / t) volume δ t)
      fun h hh => (hpt h hh).2
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have h2 : (t - δ) * (2 / t) ≤ 2 := by
      rw [mul_div_assoc', div_le_iff₀ ht]
      linarith only [hδ]
    exact h1.trans h2
  rw [← hsplit, hfar]
  constructor
  · linarith only [hlow]
  · linarith only [hup]

/-- **The jumps away from the wall.** They carry the mass of the jumps past `−k`,
`g(t) ∫_{h>k−t} ω`, minus the exact logarithmic integral
`∫_{2t}^k (g(s) − g(t)) ds/(2s) = √(log(1/2t)) − √(log(1/k)) − ½ g(t) log(k/2t)`,
up to a bounded error. -/
theorem wallLogProfile_outRow_bounds {k δ t : ℝ} (hk4 : k ≤ 1 / 4) (hδ : 0 < δ) (hδt : δ ≤ t)
    (htk : t < k / 2) :
    (wallRootLog t)⁻¹ * (∫ h in Ioi (k - t), archLevyDensity h) -
        (wallRootLog (2 * t) - wallRootLog k -
          (wallRootLog t)⁻¹ / 2 * (Real.log k - Real.log (2 * t))) - 17 / 16 ≤
        (∫ h in Ioi δ, archLevyDensity h *
          (wallLogProfile k (-t) - wallLogProfile k (-t - h))) ∧
      (∫ h in Ioi δ, archLevyDensity h *
          (wallLogProfile k (-t) - wallLogProfile k (-t - h))) ≤
        (wallRootLog t)⁻¹ * (∫ h in Ioi (k - t), archLevyDensity h) -
          (wallRootLog (2 * t) - wallRootLog k -
            (wallRootLog t)⁻¹ / 2 * (Real.log k - Real.log (2 * t))) + 1 / 16 := by
  have ht : 0 < t := lt_of_lt_of_le hδ hδt
  have hk : 0 < k := by linarith only [ht, htk]
  have ht4 : t ≤ 1 / 4 := by linarith only [htk, hk4, hk]
  have hkt : t ≤ k - t := by linarith only [htk]
  have hR := one_le_wallRootLog ht ht4
  have hc : wallLogProfile k (-t) = (wallRootLog t)⁻¹ := by
    rw [wallLogProfile_of_mem (by linarith only [htk, hk]) (by linarith only [ht]), neg_neg]
  rw [hc]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (wallRootLog t)⁻¹ := ⟨_, rfl⟩
  rw [← hcdef]
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact inv_nonneg.mpr (le_trans zero_le_one hR)
  have hc1 : c ≤ 1 := by
    rw [hcdef]
    exact inv_le_one_of_one_le₀ hR
  have hψ0 := wallLogProfile_nonneg k
  have hψ1 := wallLogProfile_le_one hk4
  have hm : Measurable fun h : ℝ => c - wallLogProfile k (-t - h) :=
    measurable_const.sub ((measurable_wallLogProfile k).comp (measurable_const.sub measurable_id))
  have hint : IntegrableOn (fun h : ℝ => archLevyDensity h * (c - wallLogProfile k (-t - h)))
      (Ioi δ) :=
    integrableOn_archLevyDensity_mul_of_bounded hδ hm (B := 1) fun h =>
      abs_le.mpr ⟨by linarith only [hc0, hψ1 (-t - h)], by linarith only [hc1, hψ0 (-t - h)]⟩
  have hint' := hint.mono_set (Ioi_subset_Ioi (hδt.trans hkt))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint hint'
  -- past `−k` the profile vanishes
  have hfar : ∫ h in Ioi (k - t), archLevyDensity h * (c - wallLogProfile k (-t - h)) =
      c * ∫ h in Ioi (k - t), archLevyDensity h := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
    have hh' : k - t < h := hh
    show archLevyDensity h * (c - wallLogProfile k (-t - h)) = c * archLevyDensity h
    rw [wallLogProfile_of_le (by linarith only [hh']), sub_zero, mul_comm]
  have hi1 : IntervalIntegrable
      (fun h : ℝ => archLevyDensity h * (c - wallLogProfile k (-t - h))) volume δ t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδt).mpr (hint.mono_set Ioc_subset_Ioi_self)
  have hi2 : IntervalIntegrable
      (fun h : ℝ => archLevyDensity h * (c - wallLogProfile k (-t - h))) volume t (k - t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hkt).mpr
      (hint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hδt)))
  have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  -- the short jumps: the increment is at most `h/(2t)`
  have hpt1 : ∀ h ∈ Icc δ t,
      -(1 / (2 * t)) ≤ archLevyDensity h * (c - wallLogProfile k (-t - h)) ∧
      archLevyDensity h * (c - wallLogProfile k (-t - h)) ≤ 0 := by
    intro h hh
    have hh0 : 0 < h := lt_of_lt_of_le hδ hh.1
    have hω0 := (archLevyDensity_pos hh0).le
    have hωh := archLevyDensity_mul_self_le_one hh0 (by linarith only [hh.2, ht4])
    have e : -(-t - h) = t + h := by ring
    rw [wallLogProfile_of_mem (by linarith only [hh.2, htk]) (by linarith only [hh0, ht]), e,
      hcdef]
    have hth4 : t + h ≤ 1 / 4 := by linarith only [hh.2, htk, hk4]
    have h1 := inv_wallRootLog_mono ht (by linarith only [hh0] : t ≤ t + h) hth4
    have h2 := inv_wallRootLog_sub_le ht (by linarith only [hh0] : t ≤ t + h) hth4
    have e2 : (t + h - t) / (2 * t) = h * (1 / (2 * t)) := by ring
    rw [e2] at h2
    constructor
    · have h3 : archLevyDensity h * (-(h * (1 / (2 * t)))) ≤
          archLevyDensity h * ((wallRootLog t)⁻¹ - (wallRootLog (t + h))⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith only [h2]) hω0
      have h4 : archLevyDensity h * h * (1 / (2 * t)) ≤ 1 * (1 / (2 * t)) :=
        mul_le_mul_of_nonneg_right hωh (by positivity)
      have e3 : archLevyDensity h * (-(h * (1 / (2 * t)))) =
          -(archLevyDensity h * h * (1 / (2 * t))) := by ring
      linarith only [h3, h4, e3]
    · exact mul_nonpos_of_nonneg_of_nonpos hω0 (sub_nonpos.mpr h1)
  have hA1low : -(1 / 2) ≤
      ∫ h in δ..t, archLevyDensity h * (c - wallLogProfile k (-t - h)) := by
    have h1 := intervalIntegral.integral_mono_on hδt
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -(1 / (2 * t))) volume δ t)
      hi1 fun h hh => (hpt1 h hh).1
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have e1 : t * (1 / (2 * t)) = 1 / 2 := by
      rw [mul_one_div, div_eq_div_iff (mul_pos two_pos ht).ne' two_ne_zero]
      ring
    have e2 : (t - δ) * -(1 / (2 * t)) = -(t * (1 / (2 * t))) + δ * (1 / (2 * t)) := by ring
    have h0 : 0 ≤ δ * (1 / (2 * t)) := by positivity
    linarith only [h1, e1, e2, h0]
  have hA1up : ∫ h in δ..t, archLevyDensity h * (c - wallLogProfile k (-t - h)) ≤ 0 := by
    have h1 := intervalIntegral.integral_mono_on hδt hi1
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume δ t)
      fun h hh => (hpt1 h hh).2
    rwa [intervalIntegral.integral_const, smul_zero] at h1
  -- the long jumps: compare `ω(h)` with `1/(2(t+h))` and integrate exactly
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ → ℝ,
      W = fun h => ((wallRootLog (t + h))⁻¹ - c) / (2 * (t + h)) := ⟨_, rfl⟩
  have hWval : ∀ h, W h = ((wallRootLog (t + h))⁻¹ - c) / (2 * (t + h)) := fun h => by
    rw [hWdef]
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ → ℝ, T = fun h => -(t / 2) * -(h ^ 2)⁻¹ := ⟨_, rfl⟩
  have hTval : ∀ h, T h = -(t / 2) * -(h ^ 2)⁻¹ := fun h => by rw [hTdef]
  have hmemI : ∀ x ∈ uIcc t (k - t), t ≤ x ∧ x ≤ k - t := fun x hx => by
    rw [uIcc_of_le hkt] at hx
    exact hx
  have hΨ : ∀ x ∈ uIcc t (k - t),
      HasDerivAt (fun h : ℝ => -wallRootLog (t + h) - c / 2 * Real.log (t + h)) (W x) x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hmemI x hx
    rw [hWval]
    exact (hasDerivAt_wallPrimitive c (s := t + x) (by linarith only [ht, hx1])
      (by linarith only [hx2, hk4])).comp_const_add t x
  have hW0 : ∀ x, t ≤ x → x ≤ k - t → 0 ≤ W x := fun x hx1 hx2 => by
    rw [hWval, hcdef]
    exact div_nonneg (sub_nonneg.mpr (inv_wallRootLog_mono ht (by linarith only [hx1, ht])
      (by linarith only [hx2, hk4]))) (by linarith only [ht, hx1])
  have hWint : IntervalIntegrable W volume t (k - t) :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (fun x hx => (hΨ x hx).continuousAt.continuousWithinAt)
      (fun x hx => hΨ x (Ioo_subset_Icc_self hx))
      (fun x hx => by
        obtain ⟨h1, h2⟩ := hmemI x (Ioo_subset_Icc_self hx)
        exact hW0 x h1 h2)
  have hWI : ∫ h in t..(k - t), W h =
      (-wallRootLog (t + (k - t)) - c / 2 * Real.log (t + (k - t))) -
        (-wallRootLog (t + t) - c / 2 * Real.log (t + t)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hΨ hWint
  rw [show t + (k - t) = k by ring, show t + t = 2 * t by ring] at hWI
  have hΘ : ∀ x ∈ uIcc t (k - t), HasDerivAt (fun h : ℝ => -(t / 2) * h⁻¹) (T x) x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hmemI x hx
    rw [hTval]
    exact (hasDerivAt_inv (lt_of_lt_of_le ht hx1).ne').const_mul (-(t / 2))
  have hT0 : ∀ x, 0 ≤ T x := fun x => by
    rw [hTval, neg_mul_neg]
    exact mul_nonneg (by linarith only [ht]) (inv_nonneg.mpr (sq_nonneg x))
  have hTint : IntervalIntegrable T volume t (k - t) :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (fun x hx => (hΘ x hx).continuousAt.continuousWithinAt)
      (fun x hx => hΘ x (Ioo_subset_Icc_self hx)) (fun x _ => hT0 x)
  have hTI : ∫ h in t..(k - t), T h = -(t / 2) * (k - t)⁻¹ - -(t / 2) * t⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hΘ hTint
  have hTle : ∫ h in t..(k - t), T h ≤ 1 / 2 := by
    rw [hTI]
    have e : t / 2 * t⁻¹ = 1 / 2 := by rw [div_mul_eq_mul_div, mul_inv_cancel₀ ht.ne']
    have h0 : 0 ≤ t / 2 * (k - t)⁻¹ :=
      mul_nonneg (by linarith only [ht]) (inv_nonneg.mpr (by linarith only [hkt, ht]))
    linarith only [e, h0]
  have hpt2 : ∀ h ∈ Ioo t (k - t),
      -W h - T h - 1 / 4 ≤ archLevyDensity h * (c - wallLogProfile k (-t - h)) ∧
      archLevyDensity h * (c - wallLogProfile k (-t - h)) ≤ -W h + 1 / 4 := by
    intro h hh
    have hh0 : 0 < h := lt_trans ht hh.1
    have hth : 0 < t + h := by linarith only [ht, hh0]
    have hth4 : t + h ≤ 1 / 4 := by linarith only [hh.2, hk4]
    have e : -(-t - h) = t + h := by ring
    rw [wallLogProfile_of_mem (by linarith only [hh.2]) (by linarith only [hh0, ht]), e, hWval,
      hTval]
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (wallRootLog (t + h))⁻¹ - c := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by
      rw [hDdef, hcdef]
      exact sub_nonneg.mpr (inv_wallRootLog_mono ht (by linarith only [hh0]) hth4)
    have hD1 : D ≤ 1 := by
      rw [hDdef]
      have h1 := inv_le_one_of_one_le₀ (one_le_wallRootLog hth hth4)
      linarith only [h1, hc0]
    have eD : c - (wallRootLog (t + h))⁻¹ = -D := by
      rw [hDdef]
      ring
    rw [eD, ← hDdef]
    have hK1 := archLevyDensity_le_half_inv_add hh0
    have hK2 := half_inv_sub_le_archLevyDensity hh0
    have hq : 1 / (2 * (t + h)) ≤ 1 / (2 * h) :=
      one_div_le_one_div_of_le (by linarith only [hh0]) (by linarith only [ht])
    have hkey : 1 / (2 * h) = 1 / (2 * (t + h)) + t / (2 * h * (t + h)) := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    have hT' : t / (2 * h * (t + h)) ≤ t / (2 * h * h) :=
      div_le_div_of_nonneg_left ht.le (by positivity) (by nlinarith only [mul_pos hh0 ht])
    have eT : -(t / 2) * -(h ^ 2)⁻¹ = t / (2 * h * h) := by ring
    have eW : D / (2 * (t + h)) = 1 / (2 * (t + h)) * D := by ring
    have hT0' : 0 ≤ t / (2 * h * h) := by positivity
    constructor
    · have h1 : archLevyDensity h * D ≤ (1 / (2 * (t + h)) + t / (2 * h * h) + 1 / 4) * D :=
        mul_le_mul_of_nonneg_right (by linarith only [hK1, hkey, hT']) hD0
      have h2 : t / (2 * h * h) * D ≤ t / (2 * h * h) * 1 := mul_le_mul_of_nonneg_left hD1 hT0'
      rw [eT, eW]
      linarith only [h1, h2, hD1]
    · have h1 : (1 / (2 * (t + h)) - 1 / 4) * D ≤ archLevyDensity h * D :=
        mul_le_mul_of_nonneg_right (by linarith only [hK2, hq]) hD0
      rw [eW]
      linarith only [h1, hD1]
  have hWn : IntervalIntegrable (fun h => -W h) volume t (k - t) := hWint.neg
  have hU : IntervalIntegrable (fun h => -W h + 1 / 4) volume t (k - t) :=
    hWn.add intervalIntegrable_const
  have hV : IntervalIntegrable (fun h => -W h - T h - 1 / 4) volume t (k - t) :=
    (hWn.sub hTint).sub intervalIntegrable_const
  have hA2up := intervalIntegral.integral_mono_on_of_le_Ioo hkt hi2 hU fun h hh => (hpt2 h hh).2
  have hA2low := intervalIntegral.integral_mono_on_of_le_Ioo hkt hV hi2 fun h hh => (hpt2 h hh).1
  have hUI : ∫ h in t..(k - t), (-W h + 1 / 4) =
      -(∫ h in t..(k - t), W h) + (k - t - t) * (1 / 4) := by
    rw [intervalIntegral.integral_add hWn intervalIntegrable_const, intervalIntegral.integral_neg,
      intervalIntegral.integral_const, smul_eq_mul]
  have hVI : ∫ h in t..(k - t), (-W h - T h - 1 / 4) =
      -(∫ h in t..(k - t), W h) - (∫ h in t..(k - t), T h) - (k - t - t) * (1 / 4) := by
    rw [intervalIntegral.integral_sub (hWn.sub hTint) intervalIntegrable_const,
      intervalIntegral.integral_sub hWn hTint, intervalIntegral.integral_neg,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [hUI] at hA2up
  rw [hVI] at hA2low
  rw [← hsplit, hfar, ← hadj]
  constructor
  · linarith only [hA1low, hA2low, hWI, hTle, hk4, ht]
  · linarith only [hA1up, hA2up, hWI, hk4, ht]

/-- **The Lévy operator is constant on the inverse root logarithm**: on the collar `(−k, 0)`,
at every point `−t` with `δ ≤ t < k/2`, the cutoff operator of the profile equals
`√(log(1/k))` up to `9`. -/
theorem abs_cutoffLevy_wallLogProfile_sub_le {k δ t : ℝ} (hk4 : k ≤ 1 / 4) (hδ : 0 < δ)
    (hδt : δ ≤ t) (htk : t < k / 2) :
    |cutoffLevy δ (wallLogProfile k) (-t) - wallRootLog k| ≤ 9 := by
  have ht : 0 < t := lt_of_lt_of_le hδ hδt
  have hk : 0 < k := by linarith only [ht, htk]
  have ht4 : t ≤ 1 / 4 := by linarith only [htk, hk4, hk]
  have h2t4 : 2 * t ≤ 1 / 4 := by linarith only [htk, hk4]
  have hkt0 : 0 < k - t := by linarith only [htk, ht]
  rw [cutoffLevy_eq_rows hδ (measurable_wallLogProfile k) (abs_wallLogProfile_le_one hk4) (-t)]
  obtain ⟨hin1, hin2⟩ := wallLogProfile_inRow_bounds hk4 hδ hδt htk
  obtain ⟨hout1, hout2⟩ := wallLogProfile_outRow_bounds hk4 hδ hδt htk
  rw [Real.log_mul two_ne_zero ht.ne'] at hout1 hout2
  -- the masses of the jumps leaving the collar
  have hΩt1 := log_two_div_le_two_mul_levyTail ht (by linarith only [ht4])
  have hΩt2 := two_mul_levyTail_le_log_two_div_add ht (by linarith only [ht4])
  rw [Real.log_div two_ne_zero ht.ne'] at hΩt1 hΩt2
  have hlk1 : Real.log 2 - Real.log k ≤ Real.log (2 / (k - t)) := by
    rw [← Real.log_div two_ne_zero hk.ne']
    exact Real.log_le_log (div_pos two_pos hk)
      (div_le_div_of_nonneg_left zero_le_two hkt0 (by linarith only [ht]))
  have hlk2 : Real.log (2 / (k - t)) ≤ 2 * Real.log 2 - Real.log k := by
    have h4 : Real.log (4 / k) = 2 * Real.log 2 - Real.log k := by
      rw [Real.log_div (by norm_num) hk.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [← h4]
    refine Real.log_le_log (div_pos two_pos hkt0) ?_
    rw [div_le_div_iff₀ hkt0 hk]
    linarith only [htk]
  have hΩk1 : Real.log 2 - Real.log k ≤ 2 * ∫ h in Ioi (k - t), archLevyDensity h :=
    hlk1.trans (log_two_div_le_two_mul_levyTail hkt0 (by linarith only [hk4, ht]))
  have hΩk2 : 2 * (∫ h in Ioi (k - t), archLevyDensity h) ≤
      2 * Real.log 2 - Real.log k + 4 := by
    have h := two_mul_levyTail_le_log_two_div_add hkt0 (by linarith only [hk4, ht])
    linarith only [h, hlk2]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (wallRootLog t)⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hin1 hin2 hout1 hout2
  have hR := one_le_wallRootLog ht ht4
  have hRpos : 0 < wallRootLog t := lt_of_lt_of_le zero_lt_one hR
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact inv_nonneg.mpr hRpos.le
  have hc1 : c ≤ 1 := by
    rw [hcdef]
    exact inv_le_one_of_one_le₀ hR
  -- `g(t) log(1/t) = √(log(1/t))`
  have hcl : c * Real.log t = -wallRootLog t := by
    have h := wallRootLog_sq ht ht4
    have e : Real.log t = -(wallRootLog t ^ 2) := by linarith only [h]
    rw [e, hcdef, mul_neg, pow_two, ← mul_assoc, inv_mul_cancel₀ hRpos.ne', one_mul]
  have hd1 := wallRootLog_anti ht (by linarith only [ht] : t ≤ 2 * t)
  have hd2 := wallRootLog_sub_le ht (by linarith only [ht] : t ≤ 2 * t) h2t4
  rw [Real.log_mul two_ne_zero ht.ne'] at hd2
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have p1 := mul_le_mul_of_nonneg_left hΩt1 hc0
  have p2 := mul_le_mul_of_nonneg_left hΩt2 hc0
  have p3 := mul_le_mul_of_nonneg_left hΩk1 hc0
  have p4 := mul_le_mul_of_nonneg_left hΩk2 hc0
  have p5 : 0 ≤ c * Real.log 2 := mul_nonneg hc0 (by linarith only [hl2a])
  have p6 : c * Real.log 2 ≤ 1 * Real.log 2 :=
    mul_le_mul_of_nonneg_right hc1 (by linarith only [hl2a])
  rw [abs_le]
  constructor
  · linarith only [hin1, hout1, p1, p3, hcl, hd1, p5]
  · linarith only [hin2, hout2, p2, p4, hcl, hd2, p6, hc1, hl2b]

end GaloisForLFunctions.ExclusionOfTheCriticalState
