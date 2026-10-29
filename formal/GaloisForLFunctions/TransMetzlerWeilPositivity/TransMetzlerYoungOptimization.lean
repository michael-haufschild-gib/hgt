import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerReferenceFloor
import GaloisForLFunctions.HTGeometry.OptimalYoungDefectFloor
import Mathlib.Topology.Order.IntermediateValue

/-!
# The optimized positive range of the Trans-Metzler bounds

The conductor-one limit gives the exact reference floor. Optimizing the
center Young parameter gives a continuous, strictly decreasing certified
floor on the positive charge-reserve interval. Its unique zero is the
precise boundary of this bound family. Every smaller ratio yields eventual
positive definiteness of the actual complete Weil matrices.

The plateau variance and shape estimates certify the rational ratio
`1 + 10⁻¹⁶`, where the actual matrices eventually have floor `1 / 400`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix RHTower
open scoped Real RealInnerProductSpace

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics HTGeometry

/-- Defect reserve before the tunable Young cost. -/
def transMetzlerChargeReserve (c : ℝ) : ℝ :=
  1 - completeWeilPoleShift transMetzlerProfile c

/-- Squared charge cost in the optimized Young family. -/
def transMetzlerYoungSquareCost (c : ℝ) : ℝ :=
  (completeWeilPoleShift transMetzlerProfile c)^2 * psiConstant

/-- Mass cost independent of the Young parameter. -/
def transMetzlerYoungMassBase (c : ℝ) : ℝ :=
  1276 * c^2 + completeWeilPoleShift transMetzlerProfile c * (psiConstant + 15) -
    completeWeilSelfFinitePart transMetzlerProfile c

/-- Square root of the optimal defect ceiling on vectors at the reference floor. -/
def transMetzlerOptimalDefectRoot (c : ℝ) : ℝ :=
  YoungDefect.scale (transMetzlerChargeReserve c) (transMetzlerYoungSquareCost c)
    (transMetzlerYoungMassBase c + transMetzlerReferenceFloor c)

/-- Optimal positive-regime floor from the full certified Young family. -/
def transMetzlerOptimizedOverlapFloor (c : ℝ) : ℝ :=
  transMetzlerReferenceFloor c - 2000 * (c - 1) * (1 + (transMetzlerOptimalDefectRoot c)^2)

lemma transMetzlerYoungMassBase_add_floor (c : ℝ) :
    transMetzlerYoungMassBase c + transMetzlerReferenceFloor c =
      1276 * c^2 + completeWeilPoleShift transMetzlerProfile c * (psiConstant + 16) := by
  unfold transMetzlerYoungMassBase transMetzlerReferenceFloor
  ring

private lemma young_costs_pos {c : ℝ} (hc : 1 ≤ c) :
    0 < completeWeilPoleShift transMetzlerProfile c ∧
      0 < transMetzlerYoungSquareCost c ∧ 0 < transMetzlerYoungMassBase c ∧
      0 ≤ transMetzlerYoungMassBase c + transMetzlerReferenceFloor c := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hq0 : 0 < completeWeilPoleShift transMetzlerProfile 1 :=
    lt_of_lt_of_le (by norm_num) transMetzlerProfile_charge_bounds.1
  have hα : 0 < completeWeilPoleShift transMetzlerProfile c := by
    rw [transMetzlerPoleShift_eq_mul]
    exact mul_pos hc0 hq0
  have hA : 0 < transMetzlerYoungSquareCost c :=
    mul_pos (sq_pos_of_pos hα) psiConstant_pos
  have hR : 0 < transMetzlerYoungMassBase c := by
    have hs := transMetzlerSelfFinitePart_neg hc
    have hm := mul_pos hα (show 0 < psiConstant + 15 by linarith only [psiConstant_pos])
    unfold transMetzlerYoungMassBase
    nlinarith only [hs, hm, sq_nonneg c]
  refine ⟨hα, hA, hR, ?_⟩
  rw [transMetzlerYoungMassBase_add_floor]
  exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg c))
    (mul_nonneg hα.le (by linarith only [psiConstant_pos]))

private lemma young_domain {c : ℝ} (hc : 1 ≤ c)
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1) :
    0 < c ∧ c ≤ 5 / 4 ∧ 0 < completeWeilPoleShift transMetzlerProfile c ∧
      0 < transMetzlerChargeReserve c ∧ 0 < transMetzlerYoungSquareCost c ∧
      0 < transMetzlerYoungMassBase c ∧
      0 ≤ transMetzlerYoungMassBase c + transMetzlerReferenceFloor c := by
  obtain ⟨hα, hA, hR, hq⟩ := young_costs_pos hc
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hcmax : c ≤ 5 / 4 := by
    have hm := mul_le_mul_of_nonneg_left transMetzlerProfile_charge_bounds.1 hc0.le
    rw [← transMetzlerPoleShift_eq_mul] at hm
    linarith only [hm, hcharge]
  exact ⟨hc0, hcmax, hα, sub_pos.mpr hcharge, hA, hR, hq⟩

private lemma young_parameter_eq {c x : ℝ}
    (hα : 0 < completeWeilPoleShift transMetzlerProfile c) (hx : 0 < x) :
    transMetzlerYoungReserve c (completeWeilPoleShift transMetzlerProfile c / x) =
        transMetzlerChargeReserve c - x ∧
      transMetzlerYoungMassLoss c (completeWeilPoleShift transMetzlerProfile c / x) =
        transMetzlerYoungSquareCost c / x + transMetzlerYoungMassBase c := by
  constructor
  · unfold transMetzlerYoungReserve transMetzlerChargeReserve
    field_simp [hα.ne']
    ring
  · unfold transMetzlerYoungMassLoss transMetzlerYoungSquareCost transMetzlerYoungMassBase
    field_simp [hx.ne']
    ring

/-- Every strict relaxation of the optimized floor holds for the actual complete
Weil matrix wherever the certified floor is nonnegative. -/
theorem eventually_completeWeilMatrix_optimized_young_floor {c : ℝ} (hc : 1 ≤ c)
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1)
    (hfloor : 0 ≤ transMetzlerOptimizedOverlapFloor c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (transMetzlerOptimizedOverlapFloor c - ε) * ‖x‖^2 ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix transMetzlerProfile c N) x, x⟫ := by
  obtain ⟨hc0, hcmax, hα, hr, hA, hR, hq⟩ := young_domain hc hcharge
  let x₀ := Real.sqrt (transMetzlerYoungSquareCost c) / transMetzlerOptimalDefectRoot c
  let a := transMetzlerChargeReserve c - x₀
  let B := transMetzlerYoungSquareCost c / x₀ + transMetzlerYoungMassBase c
  let f := transMetzlerReferenceFloor c
  let e := 2000 * (c - 1)
  obtain ⟨hx₀, hx₀r, hopt⟩ := YoungDefect.optimal_parameter_properties hr hA hq
  change 0 < x₀ at hx₀
  change x₀ < transMetzlerChargeReserve c at hx₀r
  have ha : 0 < a := sub_pos.mpr hx₀r
  have he0 : 0 ≤ e := mul_nonneg (by norm_num) (sub_nonneg.mpr hc)
  have hea : e < a := YoungDefect.nonnegative_floor_implies_reserve hr hA hq hR.le hfloor
  have hopt' : (B + f) / a = (transMetzlerOptimalDefectRoot c)^2 := by
    simpa only [B, f, a, x₀, transMetzlerOptimalDefectRoot, add_assoc] using hopt
  have hL : f - e * (1 + (B + f) / a) = transMetzlerOptimizedOverlapFloor c := by
    rw [hopt']
    rfl
  obtain ⟨τ, hτ, hτa, hcoef⟩ := YoungDefect.exists_relaxed_floor_coefficient ha hL ε hε hea
  have haτ : 0 < a - τ := by linarith only [hτa, he0, hτ]
  have heτ : e + τ ≤ a - τ := by linarith only [hτa]
  let lam := completeWeilPoleShift transMetzlerProfile c / x₀
  have hlam : 0 < lam := div_pos hα hx₀
  obtain ⟨hreserve, hmass⟩ := young_parameter_eq hα hx₀
  obtain ⟨C, _, hpert⟩ := exists_perturbation_bound_transMetzler
  have htail : Tendsto (fun N : ℕ => C / Real.log ((N : ℝ) / 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 3)))
  have hμ : f - τ < transMetzlerReferenceFloor c := sub_lt_self f hτ
  filter_upwards [eventually_transMetzlerMainMatrix_reference_floor hc0
      (hcmax.trans (by norm_num)) hcharge hμ,
    eventually_transMetzlerMainMatrix_young_coercive hc0 (hcmax.trans (by norm_num)) hlam hτ,
    htail.eventually (gt_mem_nhds hτ), eventually_ge_atTop 27]
    with N hreference hcoerc htailN hN x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc' := hcoerc x
  rw [hreserve, hmass] at hc'
  change (a - τ) * poleDefect N (primeHorizonExtension x) - (B + τ) * ‖x‖^2 ≤ _ at hc'
  have hp := (abs_le.mp (hpert hN (sub_nonneg.mpr hc)
    (by linarith only [hcmax] : c - 1 ≤ 1 / 4) (by linarith only [hc] : 1 / 2 ≤ c)
    (w := c / N) (cStar := c)
    (by
      rw [show (1 : ℝ) / (2 * N) = (1 / 2) / N by ring]
      exact div_le_div_of_nonneg_right (by linarith only [hc]) hN0.le)
    (by rw [show (1 : ℝ) + (c - 1) = c by ring])
    (by rw [div_mul_cancel₀ _ hN0.ne', sub_self, abs_zero]; positivity) x)).1
  have herror : -(e + τ) * (poleDefect N (primeHorizonExtension x) + ‖x‖^2) ≤
      -((2000 * (c - 1) + C / Real.log ((N : ℝ) / 3)) *
        (poleDefect N (primeHorizonExtension x) + ‖x‖^2)) := by
    rw [neg_mul]
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_right (by dsimp only [e]; linarith only [htailN])
      (add_nonneg (poleDefect_nonneg N _) (sq_nonneg _))
  have hb := YoungDefect.floor_of_two_bounds haτ (add_nonneg he0 hτ.le) heτ
    (hreference x) hc' (herror.trans hp)
  have hcancel : B + τ + (f - τ) = B + f := by ring
  rw [hcancel] at hb
  exact (mul_le_mul_of_nonneg_right hcoef.le (sq_nonneg _)).trans hb
/-- The optimized floor strictly decreases throughout the positive charge-reserve
range. The growing perturbation cost dominates the reference energy's variation. -/
theorem transMetzlerOptimizedOverlapFloor_strictAnti {c d : ℝ} (hc : 1 ≤ c)
    (hdcharge : completeWeilPoleShift transMetzlerProfile d < 1) (hcd : c < d) :
    transMetzlerOptimizedOverlapFloor d < transMetzlerOptimizedOverlapFloor c := by
  obtain ⟨hq0, hq1⟩ := transMetzlerProfile_charge_bounds
  have hqpos : 0 < completeWeilPoleShift transMetzlerProfile 1 :=
    lt_of_lt_of_le (by norm_num) hq0
  have hαmono : completeWeilPoleShift transMetzlerProfile c ≤
      completeWeilPoleShift transMetzlerProfile d := by
    rw [transMetzlerPoleShift_eq_mul c, transMetzlerPoleShift_eq_mul d]
    exact mul_le_mul_of_nonneg_right hcd.le hqpos.le
  have hccharge := hαmono.trans_lt hdcharge
  obtain ⟨hc0, _, hαc, hrc, hAc, _, hqc⟩ := young_domain hc hccharge
  obtain ⟨hd0, _, hαd, hrd, hAd, _, hqd⟩ := young_domain (hc.trans hcd.le) hdcharge
  have hsqα : (completeWeilPoleShift transMetzlerProfile c)^2 ≤
      (completeWeilPoleShift transMetzlerProfile d)^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hαmono) (add_nonneg hαd.le hαc.le)
    nlinarith only [h]
  have hsqc : c^2 ≤ d^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hcd.le) (add_nonneg hd0.le hc0.le)
    nlinarith only [h]
  have hqmono : transMetzlerYoungMassBase c + transMetzlerReferenceFloor c ≤
      transMetzlerYoungMassBase d + transMetzlerReferenceFloor d := by
    rw [transMetzlerYoungMassBase_add_floor, transMetzlerYoungMassBase_add_floor]
    exact add_le_add (mul_le_mul_of_nonneg_left hsqc (by norm_num))
      (mul_le_mul_of_nonneg_right hαmono (by linarith only [psiConstant_pos]))
  have hD : (transMetzlerOptimalDefectRoot c)^2 ≤ (transMetzlerOptimalDefectRoot d)^2 :=
    YoungDefect.scale_sq_mono hrc hrd hAc hAd hqc hqd
      (sub_le_sub_left hαmono 1) (mul_le_mul_of_nonneg_right hsqα psiConstant_pos.le) hqmono
  have hf : transMetzlerReferenceFloor d - transMetzlerReferenceFloor c ≤ d - c := by
    have hlog := Real.log_le_log hc0 hcd.le
    have hq := mul_le_mul_of_nonneg_right hq1.le (sub_nonneg.mpr hcd.le)
    rw [transMetzlerReferenceFloor_eq d hd0, transMetzlerReferenceFloor_eq c hc0]
    linarith only [hlog, hq]
  have hec : 0 ≤ 2000 * (c - 1) := mul_nonneg (by norm_num) (sub_nonneg.mpr hc)
  have hed : 0 ≤ 2000 * (d - 1) := mul_nonneg (by norm_num)
    (sub_nonneg.mpr (hc.trans hcd.le))
  have hm := mul_le_mul_of_nonneg_left hD hed
  have hg := mul_nonneg (show 0 ≤ 2000 * (d - 1) - 2000 * (c - 1) by
    linarith only [hcd]) (sq_nonneg (transMetzlerOptimalDefectRoot c))
  unfold transMetzlerOptimizedOverlapFloor
  nlinarith only [hf, hm, hg, hcd]

/-- At overlap one no perturbation is spent and the reference margin is positive. -/
theorem transMetzlerOptimizedOverlapFloor_one_pos :
    0 < transMetzlerOptimizedOverlapFloor 1 := by
  have h := transMetzlerReferenceFloor_gt le_rfl transMetzlerProfile_charge_bounds.2
  simp only [transMetzlerOptimizedOverlapFloor, sub_self, mul_zero, zero_mul, sub_zero]
  linarith only [h]

/-- Halfway to loss of the charge reserve the optimized scalar floor is already
negative. This gives an analytic bracket for its unique zero. -/
theorem transMetzlerOptimizedOverlapFloor_midpoint_neg :
    transMetzlerOptimizedOverlapFloor
      ((1 + 1 / completeWeilPoleShift transMetzlerProfile 1) / 2) < 0 := by
  let k := completeWeilPoleShift transMetzlerProfile 1
  let c := (1 + 1 / k) / 2
  obtain ⟨hklo, hk1⟩ := transMetzlerProfile_charge_bounds
  have hk : 0 < k := lt_of_lt_of_le (by norm_num) hklo
  have hck : 2 * c * k = k + 1 := by dsimp only [c]; field_simp [hk.ne']
  have hc1 : 1 < c := by nlinarith only [hck, hk1, hk]
  have hccharge : completeWeilPoleShift transMetzlerProfile c < 1 := by
    rw [transMetzlerPoleShift_eq_mul]
    change c * k < 1
    linarith only [hck, hk1]
  obtain ⟨_, _, _, hr, hA, hR, hq⟩ := young_domain hc1.le hccharge
  have he : transMetzlerChargeReserve c ≤ 2000 * (c - 1) := by
    have hm := mul_le_mul_of_nonneg_right (show 2 * k ≤ 2000 by linarith only [hk1])
      (sub_nonneg.mpr hc1.le)
    unfold transMetzlerChargeReserve
    rw [transMetzlerPoleShift_eq_mul]
    change 1 - c * k ≤ _
    nlinarith only [hck, hm, hk1]
  change transMetzlerOptimizedOverlapFloor c < 0
  by_contra hnot
  have h := YoungDefect.nonnegative_floor_implies_reserve hr hA hq hR.le
    (le_of_not_gt hnot)
  obtain ⟨hx, _, _⟩ := YoungDefect.optimal_parameter_properties hr hA hq
  change 0 < Real.sqrt (transMetzlerYoungSquareCost c) / transMetzlerOptimalDefectRoot c at hx
  change 2000 * (c - 1) < transMetzlerChargeReserve c -
    Real.sqrt (transMetzlerYoungSquareCost c) / transMetzlerOptimalDefectRoot c at h
  linarith only [h, he, hx]
private lemma charge_lt_one_iff (c : ℝ) :
    completeWeilPoleShift transMetzlerProfile c < 1 ↔
      c < 1 / completeWeilPoleShift transMetzlerProfile 1 := by
  have hk : 0 < completeWeilPoleShift transMetzlerProfile 1 :=
    lt_of_lt_of_le (by norm_num) transMetzlerProfile_charge_bounds.1
  rw [transMetzlerPoleShift_eq_mul]
  exact (lt_div_iff₀ hk).symm

private lemma continuousAt_optimizedFloor {c : ℝ} (hc : 0 < c)
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1) :
    ContinuousAt transMetzlerOptimizedOverlapFloor c := by
  have hα : Continuous (completeWeilPoleShift transMetzlerProfile) := by
    unfold completeWeilPoleShift
    exact (continuous_id.mul continuous_const).div_const _
  have hs : ContinuousAt (completeWeilSelfFinitePart transMetzlerProfile) c := by
    have hd : ContinuousAt (fun x : ℝ => 2 * Real.pi * x) c :=
      continuousAt_const.mul continuousAt_id
    have hd0 : 0 < 2 * Real.pi * c := by positivity
    unfold completeWeilSelfFinitePart
    have hi : ContinuousAt (fun x : ℝ => 1 / (2 * Real.pi * x)) c :=
      continuousAt_const.div hd hd0.ne'
    have hi0 : (1 : ℝ) / (2 * Real.pi * c) ≠ 0 := (div_pos zero_lt_one hd0).ne'
    exact (hi.log hi0).add continuousAt_const
  have hf : ContinuousAt transMetzlerReferenceFloor c := hs.add hα.continuousAt
  have hA : ContinuousAt transMetzlerYoungSquareCost c :=
    (hα.continuousAt.pow 2).mul continuousAt_const
  have hR : ContinuousAt transMetzlerYoungMassBase c :=
    ((continuousAt_const.mul (continuousAt_id.pow 2)).add
      (hα.continuousAt.mul continuousAt_const)).sub hs
  have hr : ContinuousAt transMetzlerChargeReserve c := continuousAt_const.sub hα.continuousAt
  have hq := hR.add hf
  have hroot : ContinuousAt transMetzlerOptimalDefectRoot c := by
    unfold transMetzlerOptimalDefectRoot YoungDefect.scale
    exact (hA.sqrt.add ((hA.add (hr.mul hq)).sqrt)).div hr (sub_pos.mpr hcharge).ne'
  exact hf.sub ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).mul
    (continuousAt_const.add (hroot.pow 2)))

/-- The optimized certified floor has exactly one zero before the pole-defect
reserve disappears; its location is specified without numerical evaluation. -/
theorem exists_unique_transMetzlerCertifiedBoundary :
    ∃! c : ℝ, 1 < c ∧ c < 1 / completeWeilPoleShift transMetzlerProfile 1 ∧
      transMetzlerOptimizedOverlapFloor c = 0 := by
  let k := completeWeilPoleShift transMetzlerProfile 1
  let b := (1 + 1 / k) / 2
  obtain ⟨hklo, hk1⟩ := transMetzlerProfile_charge_bounds
  have hk : 0 < k := lt_of_lt_of_le (by norm_num) hklo
  have hkinv : 1 < 1 / k := (lt_div_iff₀ hk).mpr (by simpa only [one_mul] using hk1)
  have hb1 : 1 < b := by dsimp only [b]; linarith only [hkinv]
  have hbk : b < 1 / k := by dsimp only [b]; linarith only [hkinv]
  have hcont : ContinuousOn transMetzlerOptimizedOverlapFloor (Set.Icc 1 b) := by
    intro c hc
    exact (continuousAt_optimizedFloor (zero_lt_one.trans_le hc.1)
      ((charge_lt_one_iff c).mpr (hc.2.trans_lt hbk))).continuousWithinAt
  obtain ⟨c, hc, hzero⟩ := intermediate_value_Icc' hb1.le hcont
    ⟨transMetzlerOptimizedOverlapFloor_midpoint_neg.le,
      transMetzlerOptimizedOverlapFloor_one_pos.le⟩
  have hc1 : 1 < c := by
    rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h] at hzero
      exact False.elim (transMetzlerOptimizedOverlapFloor_one_pos.ne' hzero)
    · exact h
  have hck : c < 1 / k := hc.2.trans_lt hbk
  refine ⟨c, ⟨hc1, hck, hzero⟩, ?_⟩
  intro d hd
  rcases lt_trichotomy d c with hdc | hdc | hcd
  · have h := transMetzlerOptimizedOverlapFloor_strictAnti hd.1.le
      ((charge_lt_one_iff c).mpr hck) hdc
    rw [hzero, hd.2.2] at h
    exact False.elim (lt_irrefl _ h)
  · exact hdc
  · have h := transMetzlerOptimizedOverlapFloor_strictAnti hc1.le
      ((charge_lt_one_iff d).mpr hd.2.1) hcd
    rw [hzero, hd.2.2] at h
    exact False.elim (lt_irrefl _ h)

/-- Largest overlap admitted by the optimized certified Young estimates. -/
def transMetzlerCertifiedBoundary : ℝ :=
  Classical.choose exists_unique_transMetzlerCertifiedBoundary.exists

theorem transMetzlerCertifiedBoundary_spec :
    1 < transMetzlerCertifiedBoundary ∧
      transMetzlerCertifiedBoundary < 1 / completeWeilPoleShift transMetzlerProfile 1 ∧
      transMetzlerOptimizedOverlapFloor transMetzlerCertifiedBoundary = 0 :=
  Classical.choose_spec exists_unique_transMetzlerCertifiedBoundary.exists

/-- Inside the charge-reserve interval, the positive range ends exactly at the
unique certified boundary. -/
theorem transMetzlerOptimizedOverlapFloor_pos_iff {c : ℝ} (hc : 1 ≤ c)
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1) :
    0 < transMetzlerOptimizedOverlapFloor c ↔ c < transMetzlerCertifiedBoundary := by
  obtain ⟨hb1, hbk, hbzero⟩ := transMetzlerCertifiedBoundary_spec
  have hbcharge := (charge_lt_one_iff transMetzlerCertifiedBoundary).mpr hbk
  constructor
  · intro hpos
    by_contra hnot
    rcases eq_or_lt_of_le (le_of_not_gt hnot) with h | h
    · rw [← h, hbzero] at hpos
      exact lt_irrefl _ hpos
    · have hneg := transMetzlerOptimizedOverlapFloor_strictAnti hb1.le hcharge h
      rw [hbzero] at hneg
      exact (not_lt_of_ge hpos.le) hneg
  · intro h
    have hpos := transMetzlerOptimizedOverlapFloor_strictAnti hc hbcharge h
    rwa [hbzero] at hpos

theorem transMetzlerOptimizedOverlapFloor_nonneg_of_le {c : ℝ} (hc : 1 ≤ c)
    (hcb : c ≤ transMetzlerCertifiedBoundary) : 0 ≤ transMetzlerOptimizedOverlapFloor c := by
  rcases eq_or_lt_of_le hcb with h | h
  · rw [h, transMetzlerCertifiedBoundary_spec.2.2]
  · exact ((transMetzlerOptimizedOverlapFloor_pos_iff hc
      ((charge_lt_one_iff c).mpr (h.trans transMetzlerCertifiedBoundary_spec.2.1))).mpr h).le

/-- All strict relaxations of the exact certified floor hold up to its boundary. -/
theorem eventually_completeWeilMatrix_young_floor_to_boundary {c : ℝ} (hc : 1 ≤ c)
    (hcb : c ≤ transMetzlerCertifiedBoundary) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (transMetzlerOptimizedOverlapFloor c - ε) * ‖x‖^2 ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix transMetzlerProfile c N) x, x⟫ :=
  eventually_completeWeilMatrix_optimized_young_floor hc
    ((charge_lt_one_iff c).mpr (hcb.trans_lt transMetzlerCertifiedBoundary_spec.2.1))
    (transMetzlerOptimizedOverlapFloor_nonneg_of_le hc hcb) ε hε
/-- The actual complete matrix is eventually positive throughout the entire
open range certified by the optimized reference and Young bounds. -/
theorem eventually_completeWeilMatrix_posDef_before_young_boundary {c : ℝ} (hc : 1 ≤ c)
    (hcb : c < transMetzlerCertifiedBoundary) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix transMetzlerProfile c N).PosDef := by
  have hcharge := (charge_lt_one_iff c).mpr (hcb.trans transMetzlerCertifiedBoundary_spec.2.1)
  have hf : 0 < transMetzlerOptimizedOverlapFloor c :=
    (transMetzlerOptimizedOverlapFloor_pos_iff hc hcharge).mpr hcb
  filter_upwards [eventually_completeWeilMatrix_young_floor_to_boundary hc hcb.le
    (transMetzlerOptimizedOverlapFloor c / 2) (half_pos hf)] with N hfloor
  have hH := completeWeilMatrix_isHermitian transMetzlerProfile c N
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  have h := hfloor (hH.eigenvectorBasis i)
  rw [hH.eigenvectorBasis.orthonormal.1 i, one_pow, mul_one,
    hermitianEnergy_eq_sum hH] at h
  have horth (j : PrimeHorizonIndex N) :
      ⟪hH.eigenvectorBasis i, hH.eigenvectorBasis j⟫ = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) i j
  simp only [horth, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true] at h
  linarith only [h, hf]

/-- The unique boundary is the exact maximal positive range of the complete
scalar estimate family, including every Young parameter. Scalar witnesses
exclude a positive certificate beyond it; this is not a claim about actual
Weil-matrix signs beyond the certified range. -/
theorem transMetzler_young_positive_certificate_iff {c : ℝ} (hc : 1 ≤ c) :
    (∃ η : ℝ, 0 < η ∧ ∀ D E F : ℝ, 0 ≤ D → transMetzlerReferenceFloor c ≤ E →
      (∀ x : ℝ, 0 < x → (transMetzlerChargeReserve c - x) * D -
        (transMetzlerYoungSquareCost c / x + transMetzlerYoungMassBase c) ≤ E) →
      |F - E| ≤ 2000 * (c - 1) * (D + 1) → η ≤ F) ↔
      c < transMetzlerCertifiedBoundary := by
  obtain ⟨hα, hA, hR, hq⟩ := young_costs_pos hc
  by_cases hcharge : completeWeilPoleShift transMetzlerProfile c < 1
  · have he : 0 ≤ 2000 * (c - 1) := mul_nonneg (by norm_num) (sub_nonneg.mpr hc)
    exact (YoungDefect.positive_uniform_floor_iff (sub_pos.mpr hcharge) hA hq hR.le he).trans
      (transMetzlerOptimizedOverlapFloor_pos_iff hc hcharge)
  · constructor
    · rintro ⟨η, _, hcert⟩
      have hc1 : 1 < c := by
        rcases eq_or_lt_of_le hc with h | h
        · exfalso
          apply hcharge
          rw [← h]
          exact transMetzlerProfile_charge_bounds.2
        · exact h
      have he : 0 < 2000 * (c - 1) := mul_pos (by norm_num) (sub_pos.mpr hc1)
      have hr : transMetzlerChargeReserve c ≤ 2000 * (c - 1) :=
        (sub_nonpos.mpr (le_of_not_gt hcharge)).trans he.le
      obtain ⟨D, E, F, hD, hf, hfamily, hp, hF⟩ :=
        YoungDefect.young_family_unbounded_below (r := 2000 * (c - 1))
          (A := transMetzlerYoungSquareCost c) (R := transMetzlerYoungMassBase c)
          (f := transMetzlerReferenceFloor c) he hA hq le_rfl η
      have hactual : ∀ x : ℝ, 0 < x → (transMetzlerChargeReserve c - x) * D -
          (transMetzlerYoungSquareCost c / x + transMetzlerYoungMassBase c) ≤ E := by
        intro x hx
        exact (sub_le_sub_right
          (mul_le_mul_of_nonneg_right (sub_le_sub_right hr x) hD) _).trans (hfamily x hx)
      exact False.elim (hF.not_ge (hcert D E F hD hf hactual hp))
    · intro hcb
      exact False.elim (hcharge ((charge_lt_one_iff c).mpr
        (hcb.trans transMetzlerCertifiedBoundary_spec.2.1)))

/-- No eventual uniform reference floor exceeds the conductor-one energy:
test the bound on the actual conductor-one quasimode and pass to its limit. -/
theorem eventual_transMetzlerMainMatrix_floor_le_reference {c μ : ℝ}
    (hc : 0 < c) (hc2 : c ≤ 2)
    (hfloor : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      μ * ‖x‖^2 ≤ ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (c / N) c N) x, x⟫) :
    μ ≤ transMetzlerReferenceFloor c := by
  have hmass := (tendsto_normalizedRamanujanHorizonVector_norm_sq
    (show 0 < (1 : ℕ) by decide)).const_mul μ
  have henergy := tendsto_transMetzlerMainMatrix_pole_energy hc hc2
  apply le_of_tendsto_of_tendsto (by simpa only [mul_one] using hmass) henergy
  filter_upwards [hfloor] with N hN
  exact hN (normalizedRamanujanHorizonVector 1 N)

private lemma transMetzlerReferenceFloor_one_margin :
    (69 : ℝ) / 1000 < transMetzlerReferenceFloor 1 := by
  have hshape := plateau_completed_shape_ge (η := etaZero) (δ := 1 / 20)
    etaZero_pos (by norm_num [etaZero]) (by norm_num) (by norm_num)
  have hnum : (1908 : ℝ) / 1000 <
      (1 - (1 / 20 : ℝ)) * (1 - 2 * etaZero / (1 / 20)) + (1 - 2 * etaZero)^2 := by
    norm_num [etaZero]
  have hshape' : (1908 : ℝ) / 1000 <
      bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u^2) +
        completeWeilPoleShift transMetzlerProfile 1 := by
    rw [completeWeilPoleShift, one_mul]
    exact hnum.trans_le hshape
  unfold transMetzlerReferenceFloor
  rw [transMetzlerSelfFinitePart_eq zero_lt_one, Real.log_one]
  linarith only [hshape', log_two_pi_lt]

private lemma psiConstant_le_four : psiConstant ≤ 4 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hdiv : 4 / Real.exp 1 ≤ 2 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    linarith only [hexp]
  unfold psiConstant
  linarith only [hlog4, hdiv, Real.log_two_lt_d9]

/-- An explicit rational point inside the optimized interval, certified using
only the plateau's analytic shape and variance bounds. -/
theorem transMetzlerOptimizedOverlapFloor_explicit_margin :
    (1 : ℝ) / 200 ≤ transMetzlerOptimizedOverlapFloor (1 + 1 / 10000000000000000) := by
  let c : ℝ := 1 + 1 / 10000000000000000
  let α := completeWeilPoleShift transMetzlerProfile c
  have hc : 1 ≤ c := by norm_num [c]
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hqmax : completeWeilPoleShift transMetzlerProfile 1 ≤ 1 - 1 / 128000 := by
    linarith only [transMetzlerProfile_charge_deficit_ge]
  have hαmax : α ≤ c * (1 - 1 / 128000) := by
    change completeWeilPoleShift transMetzlerProfile c ≤ c * (1 - 1 / 128000)
    rw [transMetzlerPoleShift_eq_mul c]
    exact mul_le_mul_of_nonneg_left hqmax hc0.le
  have hα1 : α < 1 := hαmax.trans_lt (by norm_num [c])
  obtain ⟨_, _, hα0, hr, hA, hR, hq⟩ := young_domain hc hα1
  have hf : (3 : ℝ) / 50 < transMetzlerReferenceFloor c := by
    have hlog := Real.log_le_sub_one_of_pos hc0
    have hpos := mul_nonneg (sub_nonneg.mpr hc)
      (show 0 ≤ completeWeilPoleShift transMetzlerProfile 1 from
        le_trans (by norm_num) transMetzlerProfile_charge_bounds.1)
    rw [transMetzlerReferenceFloor_eq c hc0]
    have h1 := transMetzlerReferenceFloor_one_margin
    dsimp only [c] at hlog hpos ⊢
    linarith only [hlog, hpos, h1]
  let x₀ : ℝ := α / 256000
  have hx₀ : 0 < x₀ := div_pos hα0 (by norm_num)
  have ha : (1 : ℝ) / 257000 ≤ transMetzlerChargeReserve c - x₀ := by
    change 1 / 257000 ≤ 1 - α - α / 256000
    dsimp only [c] at hαmax
    linarith only [hαmax]
  have hAquot : transMetzlerYoungSquareCost c / x₀ = α * 256000 * psiConstant := by
    unfold transMetzlerYoungSquareCost
    change α^2 * psiConstant / (α / 256000) = _
    field_simp [hα0.ne']
  have hαψ : α * psiConstant ≤ 4 := by
    have h := mul_le_mul hα1.le psiConstant_le_four psiConstant_pos.le zero_le_one
    simpa only [one_mul] using h
  have hB : transMetzlerYoungSquareCost c / x₀ + transMetzlerYoungMassBase c ≤ 1026000 := by
    have htotal : transMetzlerYoungSquareCost c / x₀ + transMetzlerYoungMassBase c +
        transMetzlerReferenceFloor c = 1276 * c^2 + α * (256001 * psiConstant + 16) := by
      rw [add_assoc, transMetzlerYoungMassBase_add_floor, hAquot]
      change α * 256000 * psiConstant + (1276 * c^2 + α * (psiConstant + 16)) = _
      ring
    dsimp only [c] at htotal
    nlinarith only [htotal, hαψ, hα1, hf]
  let e : ℝ := 2000 * (c - 1)
  have he : 0 ≤ e := by norm_num [e, c]
  obtain ⟨D, E, F, hD, hE, hfamily, hp, hF⟩ :=
    YoungDefect.young_family_floor_attained hr hA hq e he
  have hcoerc : (1 / 257000 : ℝ) * D - 1026000 ≤ E := by
    have hm := mul_le_mul_of_nonneg_right ha hD
    have hb := hfamily x₀ hx₀
    linarith only [hm, hB, hb]
  have hfloor := YoungDefect.floor_of_two_bounds (M := 1)
    (by norm_num : (0 : ℝ) < 1 / 257000) he (by norm_num [e, c] : e ≤ 1 / 257000)
    (by simpa only [mul_one] using hf.le.trans hE)
    (by simpa only [mul_one] using hcoerc)
    (by simpa only [neg_mul] using (abs_le.mp hp).1)
  simp only [mul_one] at hfloor
  have hnum : (1 : ℝ) / 200 ≤ 3 / 50 - e * (1 + (1026000 + 3 / 50) / (1 / 257000)) := by
    norm_num [e, c]
  change 1 / 200 ≤ transMetzlerOptimizedOverlapFloor c
  rw [hF] at hfloor
  exact hnum.trans hfloor

/-- The optimized certified range extends strictly beyond overlap 1+10⁻¹⁶. -/
theorem transMetzlerCertifiedBoundary_explicit_lower :
    (1 : ℝ) + 1 / 10000000000000000 < transMetzlerCertifiedBoundary := by
  let c : ℝ := 1 + 1 / 10000000000000000
  have hc : 1 ≤ c := by norm_num [c]
  have hq : completeWeilPoleShift transMetzlerProfile 1 ≤ 1 - 1 / 128000 := by
    linarith only [transMetzlerProfile_charge_deficit_ge]
  have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ c by norm_num [c])
  have hcharge : completeWeilPoleShift transMetzlerProfile c < 1 := by
    rw [transMetzlerPoleShift_eq_mul]
    exact hm.trans_lt (by norm_num [c])
  exact (transMetzlerOptimizedOverlapFloor_pos_iff hc hcharge).mp
    (lt_of_lt_of_le (by norm_num) transMetzlerOptimizedOverlapFloor_explicit_margin)

/-- A fully rational eventual matrix floor at the explicit improved overlap. -/
theorem eventually_completeWeilMatrix_floor_at_explicit_young_ratio :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (1 / 400 : ℝ) * ‖x‖^2 ≤
        ⟪Matrix.toEuclideanLin
          (completeWeilMatrix transMetzlerProfile (1 + 1 / 10000000000000000) N) x, x⟫ := by
  filter_upwards [eventually_completeWeilMatrix_young_floor_to_boundary
    (by norm_num : (1 : ℝ) ≤ 1 + 1 / 10000000000000000)
    transMetzlerCertifiedBoundary_explicit_lower.le (1 / 400) (by norm_num)] with N hN x
  have hcoef : (1 : ℝ) / 400 ≤
      transMetzlerOptimizedOverlapFloor (1 + 1 / 10000000000000000) - 1 / 400 := by
    linarith only [transMetzlerOptimizedOverlapFloor_explicit_margin]
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans (hN x)


end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_unique_transMetzlerCertifiedBoundary
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrix_young_floor_to_boundary
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrix_posDef_before_young_boundary
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzler_young_positive_certificate_iff

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventual_transMetzlerMainMatrix_floor_le_reference

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzlerOptimizedOverlapFloor_explicit_margin

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrix_floor_at_explicit_young_ratio
