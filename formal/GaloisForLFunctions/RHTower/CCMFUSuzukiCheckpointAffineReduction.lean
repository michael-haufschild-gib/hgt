import GaloisForLFunctions.RHTower.CCMFUSuzukiPositiveMixture
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeAnchoredWallTransport
import GaloisForLFunctions.RHTower.SuzukiCheckpointEventDynamics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.Floor

/-!
# CCM-FU reduction to Suzuki's discrete affine checkpoint current

Integer logarithmic event cells shrink quadratically faster than Suzuki's archimedean reservoir
curvature grows. Consequently every within-cell reservoir Bregman remainder lies in `[0,1]`.
After floor-selecting the actual arithmetic event, the positive marked CCM-FU Suzuki mixture splits
exactly into a signed piecewise-affine checkpoint current and a positive curvature mixture bounded
by `96 / b^4`, uniformly in the moving upper wall.

Thus smooth intra-cell curvature is not RH-bearing. The remaining source problem is discrete:
uniform cancellation of the actual affine checkpoint current, retaining endpoint values and
cumulative Mangoldt slopes across all event cells.
-/

noncomputable section

namespace RHTower

open Set
open GaloisForLFunctions.RHTower

private theorem screwRegularKernel_le_exp_half {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t ≤ Real.exp (t / 2) := by
  unfold screwRegularKernel
  have hden : 0 < 1 - Real.exp (-(2 * t)) := one_sub_exp_neg_two_mul_pos ht
  have hq : 0 ≤ Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t))) := by
    positivity
  linarith

/-- On one logarithmic event cell, the reservoir Bregman remainder is nonnegative and bounded by
its endpoint exponential curvature times the squared cell displacement. -/
theorem suzukiCheckpointBregman_nonneg_le_exp_max_mul_sq
    {N : ℕ} (hN : 2 ≤ N) {u v : ℝ}
    (hu : u ∈ suzukiCheckpointCell N) (hv : v ∈ suzukiCheckpointCell N) :
    0 ≤ suzukiCheckpointBregman u v ∧
      suzukiCheckpointBregman u v ≤ Real.exp (max u v / 2) * (u - v) ^ 2 := by
  have hlog2u : Real.log 2 ≤ u := suzukiCheckpointCell_subset_Ici_log_two hN hu
  have hlog2v : Real.log 2 ≤ v := suzukiCheckpointCell_subset_Ici_log_two hN hv
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu0 : 0 < u := hlog2pos.trans_le hlog2u
  have hv0 : 0 < v := hlog2pos.trans_le hlog2v
  rcases lt_trichotomy v u with hvu | huv | huv
  · have hcontA : ContinuousOn suzukiCheckpointReservoir (Icc v u) := by
      intro x hx
      exact (hasDerivAt_suzukiCheckpointReservoir (hv0.trans_le hx.1)).continuousAt.continuousWithinAt
    have hderivA : ∀ x ∈ Ioo v u,
        HasDerivAt suzukiCheckpointReservoir (suzukiCheckpointReservoirDeriv x) x := by
      intro x hx
      exact hasDerivAt_suzukiCheckpointReservoir (hv0.trans hx.1)
    obtain ⟨c, hc, hcSlope⟩ :=
      exists_hasDerivAt_eq_slope suzukiCheckpointReservoir
        suzukiCheckpointReservoirDeriv hvu hcontA hderivA
    have hcontD : ContinuousOn suzukiCheckpointReservoirDeriv (Icc v c) := by
      intro x hx
      exact (hasDerivAt_suzukiCheckpointReservoirDeriv (hv0.trans_le hx.1)).continuousAt.continuousWithinAt
    have hderivD : ∀ x ∈ Ioo v c,
        HasDerivAt suzukiCheckpointReservoirDeriv (screwRegularKernel x) x := by
      intro x hx
      exact hasDerivAt_suzukiCheckpointReservoirDeriv (hv0.trans hx.1)
    obtain ⟨d, hd, hdSlope⟩ :=
      exists_hasDerivAt_eq_slope suzukiCheckpointReservoirDeriv
        screwRegularKernel hc.1 hcontD hderivD
    have hdlog2 : Real.log 2 ≤ d := hlog2v.trans hd.1.le
    have hd0 : 0 < d := hlog2pos.trans_le hdlog2
    have hK0 : 0 ≤ screwRegularKernel d :=
      (suzukiCheckpointReservoirDeriv_curvature_pos_of_log_two_le hdlog2).le
    have hKle : screwRegularKernel d ≤ Real.exp (max u v / 2) := by
      calc
        screwRegularKernel d ≤ Real.exp (d / 2) := screwRegularKernel_le_exp_half hd0
        _ ≤ Real.exp (max u v / 2) := by
          apply Real.exp_le_exp.mpr
          have hdu : d ≤ u := hd.2.le.trans hc.2.le
          have : d ≤ max u v := hdu.trans (le_max_left _ _)
          linarith
    have hcEq : suzukiCheckpointReservoir u - suzukiCheckpointReservoir v =
        suzukiCheckpointReservoirDeriv c * (u - v) := by
      rw [hcSlope]
      field_simp [sub_ne_zero.mpr hvu.ne']
    have hdEq : suzukiCheckpointReservoirDeriv c - suzukiCheckpointReservoirDeriv v =
        screwRegularKernel d * (c - v) := by
      rw [hdSlope]
      field_simp [sub_ne_zero.mpr hc.1.ne']
    have hB : suzukiCheckpointBregman u v =
        screwRegularKernel d * (c - v) * (u - v) := by
      unfold suzukiCheckpointBregman
      rw [hcEq, ← sub_mul, hdEq]
    rw [hB]
    constructor
    · exact mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hc.1.le))
        (sub_nonneg.mpr hvu.le)
    · have hcv : 0 ≤ c - v := sub_nonneg.mpr hc.1.le
      have huv0 : 0 ≤ u - v := sub_nonneg.mpr hvu.le
      have hcvle : c - v ≤ u - v := by linarith [hc.2]
      calc
        screwRegularKernel d * (c - v) * (u - v)
            ≤ Real.exp (max u v / 2) * (c - v) * (u - v) := by
              gcongr
        _ ≤ Real.exp (max u v / 2) * (u - v) * (u - v) := by
              gcongr
        _ = Real.exp (max u v / 2) * (u - v) ^ 2 := by ring
  · subst u
    simp [suzukiCheckpointBregman]
  · have hcontA : ContinuousOn suzukiCheckpointReservoir (Icc u v) := by
      intro x hx
      exact (hasDerivAt_suzukiCheckpointReservoir (hu0.trans_le hx.1)).continuousAt.continuousWithinAt
    have hderivA : ∀ x ∈ Ioo u v,
        HasDerivAt suzukiCheckpointReservoir (suzukiCheckpointReservoirDeriv x) x := by
      intro x hx
      exact hasDerivAt_suzukiCheckpointReservoir (hu0.trans hx.1)
    obtain ⟨c, hc, hcSlope⟩ :=
      exists_hasDerivAt_eq_slope suzukiCheckpointReservoir
        suzukiCheckpointReservoirDeriv huv hcontA hderivA
    have hcontD : ContinuousOn suzukiCheckpointReservoirDeriv (Icc c v) := by
      intro x hx
      exact (hasDerivAt_suzukiCheckpointReservoirDeriv (hu0.trans_le (hc.1.le.trans hx.1))).continuousAt.continuousWithinAt
    have hderivD : ∀ x ∈ Ioo c v,
        HasDerivAt suzukiCheckpointReservoirDeriv (screwRegularKernel x) x := by
      intro x hx
      exact hasDerivAt_suzukiCheckpointReservoirDeriv (hu0.trans (hc.1.trans hx.1))
    obtain ⟨d, hd, hdSlope⟩ :=
      exists_hasDerivAt_eq_slope suzukiCheckpointReservoirDeriv
        screwRegularKernel hc.2 hcontD hderivD
    have hdlog2 : Real.log 2 ≤ d := hlog2u.trans (hc.1.le.trans hd.1.le)
    have hd0 : 0 < d := hlog2pos.trans_le hdlog2
    have hK0 : 0 ≤ screwRegularKernel d :=
      (suzukiCheckpointReservoirDeriv_curvature_pos_of_log_two_le hdlog2).le
    have hKle : screwRegularKernel d ≤ Real.exp (max u v / 2) := by
      calc
        screwRegularKernel d ≤ Real.exp (d / 2) := screwRegularKernel_le_exp_half hd0
        _ ≤ Real.exp (max u v / 2) := by
          apply Real.exp_le_exp.mpr
          have hdv : d ≤ v := hd.2.le
          have : d ≤ max u v := hdv.trans (le_max_right _ _)
          linarith
    have hcEq : suzukiCheckpointReservoir v - suzukiCheckpointReservoir u =
        suzukiCheckpointReservoirDeriv c * (v - u) := by
      rw [hcSlope]
      field_simp [sub_ne_zero.mpr huv.ne']
    have hcEq' : suzukiCheckpointReservoir u - suzukiCheckpointReservoir v =
        suzukiCheckpointReservoirDeriv c * (u - v) := by
      linear_combination -hcEq
    have hdEq : suzukiCheckpointReservoirDeriv v - suzukiCheckpointReservoirDeriv c =
        screwRegularKernel d * (v - c) := by
      rw [hdSlope]
      field_simp [sub_ne_zero.mpr hc.2.ne']
    have hB : suzukiCheckpointBregman u v =
        screwRegularKernel d * (v - c) * (v - u) := by
      unfold suzukiCheckpointBregman
      rw [hcEq', ← sub_mul]
      have hdc : suzukiCheckpointReservoirDeriv c - suzukiCheckpointReservoirDeriv v =
          -(screwRegularKernel d * (v - c)) := by
        linear_combination -hdEq
      rw [hdc]
      ring
    rw [hB]
    constructor
    · exact mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hc.2.le))
        (sub_nonneg.mpr huv.le)
    · have hvc : 0 ≤ v - c := sub_nonneg.mpr hc.2.le
      have hvu0 : 0 ≤ v - u := sub_nonneg.mpr huv.le
      have hvcle : v - c ≤ v - u := by linarith [hc.1]
      calc
        screwRegularKernel d * (v - c) * (v - u)
            ≤ Real.exp (max u v / 2) * (v - c) * (v - u) := by
              gcongr
        _ ≤ Real.exp (max u v / 2) * (v - u) * (v - u) := by
              gcongr
        _ = Real.exp (max u v / 2) * (u - v) ^ 2 := by ring

/-- Integer logarithmic cells compress the exponentially growing reservoir curvature strongly
enough that every within-cell Bregman remainder is at most one. -/
theorem suzukiCheckpointBregman_mem_unitInterval
    {N : ℕ} (hN : 2 ≤ N) {u v : ℝ}
    (hu : u ∈ suzukiCheckpointCell N) (hv : v ∈ suzukiCheckpointCell N) :
    suzukiCheckpointBregman u v ∈ Set.Icc 0 1 := by
  have hbase := suzukiCheckpointBregman_nonneg_le_exp_max_mul_sq hN hu hv
  change Real.log (N : ℝ) ≤ u ∧
      u ≤ Real.log ((N + 1 : ℕ) : ℝ) at hu
  change Real.log (N : ℝ) ≤ v ∧
      v ≤ Real.log ((N + 1 : ℕ) : ℝ) at hv
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlogN0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hgap0 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) := by
    apply sub_nonneg.mpr
    apply Real.log_le_log hNpos
    exact_mod_cast Nat.le_succ N
  have hmax : max u v ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    max_le hu.2 hv.2
  have hexp : Real.exp (max u v / 2) ≤ (N + 1 : ℕ) := by
    calc
      Real.exp (max u v / 2)
          ≤ Real.exp (Real.log ((N + 1 : ℕ) : ℝ)) := by
            apply Real.exp_le_exp.mpr
            have hlogNp1 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) := by linarith
            nlinarith
      _ = (N + 1 : ℕ) := Real.exp_log hNp1pos
  have hdiffsq : (u - v) ^ 2 ≤
      (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) ^ 2 := by
    have hlo : -(Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) ≤ u - v := by
      linarith [hu.1, hv.2]
    have hhi : u - v ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) := by
      linarith [hu.2, hv.1]
    nlinarith
  have hgaple : Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hNp1pos hNpos)
    rw [Real.log_div hNp1pos.ne' hNpos.ne'] at hlog
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) / (N : ℝ) - 1 := hlog
      _ = 1 / (N : ℝ) := by
        push_cast
        field_simp [hNpos.ne']
        ring
  have hgapSq :
      (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) ^ 2 ≤ (1 / (N : ℝ)) ^ 2 := by
    nlinarith [hgaple]
  have hcast : (N + 1 : ℕ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast (show N + 1 ≤ N ^ 2 by nlinarith)
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  calc
    Real.exp (max u v / 2) * (u - v) ^ 2
        ≤ (N + 1 : ℕ) *
            (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) ^ 2 := by
          gcongr
    _ ≤ (N + 1 : ℕ) * (1 / (N : ℝ)) ^ 2 := by
          gcongr
    _ ≤ (N : ℝ) ^ 2 * (1 / (N : ℝ)) ^ 2 := by
          gcongr
    _ = 1 := by field_simp [hNpos.ne']

/-- Exact source split on one event cell: an arithmetic affine checkpoint jet plus the smooth
Bregman curvature remainder. No prime or polar term is estimated separately. -/
theorem suzukiPsi_eq_checkpointAffineJet_add_bregman
    {N : ℕ} (hN : 2 ≤ N) {u v : ℝ}
    (hu : u ∈ suzukiCheckpointCell N) (hv : v ∈ suzukiCheckpointCell N) :
    suzukiPsi u = suzukiPsi v +
        (suzukiCheckpointReservoirDeriv v - suzukiCheckpointMass N) * (u - v) +
      suzukiCheckpointBregman u v := by
  have hdiff := suzukiPsi_sub_eq_checkpoint_reservoir_difference hN hu hv
  unfold suzukiCheckpointBregman
  linarith

/-- Left-endpoint affine current on the `N`th integer logarithmic event cell. -/
def suzukiCheckpointLeftAffineJet (N : ℕ) (t : ℝ) : ℝ :=
  suzukiPsi (Real.log (N : ℝ)) +
    (suzukiCheckpointReservoirDeriv (Real.log (N : ℝ)) - suzukiCheckpointMass N) *
      (t - Real.log (N : ℝ))

/-- Every source value on an integer event cell is its left affine event current plus a positive
remainder of size at most one. This removes all smooth intra-cell curvature from the RH-bearing
signed source at a uniform, aperture-independent cost. -/
theorem suzukiPsi_eq_leftAffineJet_add_unitBregman
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ suzukiCheckpointCell N) :
    suzukiPsi t = suzukiCheckpointLeftAffineJet N t +
        suzukiCheckpointBregman t (Real.log (N : ℝ)) ∧
      suzukiCheckpointBregman t (Real.log (N : ℝ)) ∈ Set.Icc 0 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr hNle
  have hleft : Real.log (N : ℝ) ∈ suzukiCheckpointCell N := ⟨le_rfl, hlog⟩
  constructor
  · rw [suzukiPsi_eq_checkpointAffineJet_add_bregman hN ht hleft]
    rfl
  · exact suzukiCheckpointBregman_mem_unitInterval hN ht hleft

/-- Integer event selected by a positive Suzuki time. -/
def suzukiCheckpointEventIndex (t : ℝ) : ℕ := ⌊Real.exp t⌋₊

/-- Smooth within-cell curvature after selecting the actual integer event. -/
def suzukiCheckpointCellCurvatureRemainder (t : ℝ) : ℝ :=
  suzukiCheckpointBregman t
    (Real.log (suzukiCheckpointEventIndex t : ℝ))

/-- Signed piecewise-affine arithmetic current obtained by removing only within-cell curvature. -/
def suzukiCheckpointGlobalAffineCurrent (t : ℝ) : ℝ :=
  suzukiPsi t - suzukiCheckpointCellCurvatureRemainder t

/-- The floor-selected event really contains every time after the first prime wall. -/
theorem suzukiCheckpointEventIndex_two_le_and_mem_cell {t : ℝ}
    (ht : Real.log 2 ≤ t) :
    2 ≤ suzukiCheckpointEventIndex t ∧
      t ∈ suzukiCheckpointCell (suzukiCheckpointEventIndex t) := by
  let N := suzukiCheckpointEventIndex t
  have htwoexp : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hNtwo : 2 ≤ N := by
    exact Nat.le_floor htwoexp
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by omega) hNtwo)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hfloorle : (N : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  have hfloorlt : Real.exp t < ((N + 1 : ℕ) : ℝ) := by
    simpa only [N, suzukiCheckpointEventIndex, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Real.exp t)
  refine ⟨hNtwo, ?_⟩
  constructor
  · exact (Real.log_le_iff_le_exp hNpos).mpr hfloorle
  · exact (Real.le_log_iff_exp_le hNp1pos).mpr hfloorlt.le

/-- The floor-selected curvature is Borel measurable. -/
theorem measurable_suzukiCheckpointCellCurvatureRemainder :
    Measurable suzukiCheckpointCellCurvatureRemainder := by
  have hindex : Measurable suzukiCheckpointEventIndex := by
    unfold suzukiCheckpointEventIndex
    exact Real.measurable_exp.nat_floor
  have hlogIndex : Measurable fun t : ℝ =>
      Real.log (suzukiCheckpointEventIndex t : ℝ) := by
    have hcast : Measurable fun t : ℝ => (suzukiCheckpointEventIndex t : ℝ) := by
      exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hindex
    exact Real.measurable_log.comp hcast
  have htail : Measurable screwLerchTail := by
    unfold screwLerchTail
    exact Measurable.tsum fun k => by fun_prop
  have htail₁ : Measurable screwLerchTail₁ := by
    unfold screwLerchTail₁
    exact Measurable.tsum fun k => by fun_prop
  have hExpPos : Measurable fun t : ℝ => Real.exp (t / 2) := by fun_prop
  have hExpNeg : Measurable fun t : ℝ => Real.exp (-(t / 2)) := by fun_prop
  have hReservoir : Measurable suzukiCheckpointReservoir := by
    unfold suzukiCheckpointReservoir
    exact (((measurable_const.mul ((hExpPos.add hExpNeg).sub measurable_const)).add
      (measurable_const.mul measurable_id)).add measurable_const).sub htail
  have hReservoirDeriv : Measurable suzukiCheckpointReservoirDeriv := by
    unfold suzukiCheckpointReservoirDeriv
    exact (((measurable_const.mul hExpPos).sub
      (measurable_const.mul hExpNeg)).add measurable_const).sub htail₁
  unfold suzukiCheckpointCellCurvatureRemainder suzukiCheckpointBregman
  exact (hReservoir.sub (hReservoir.comp hlogIndex)).sub
    ((hReservoirDeriv.comp hlogIndex).mul (measurable_id.sub hlogIndex))

/-- Global exact event split. -/
theorem suzukiPsi_eq_globalAffineCurrent_add_curvature (t : ℝ) :
    suzukiPsi t = suzukiCheckpointGlobalAffineCurrent t +
      suzukiCheckpointCellCurvatureRemainder t := by
  unfold suzukiCheckpointGlobalAffineCurrent
  ring

/-- After the first prime wall the global current is literally the left affine event jet, and the
discarded curvature is positive and at most one. -/
theorem globalAffineCurrent_eq_leftJet_and_curvature_mem_unitInterval {t : ℝ}
    (ht : Real.log 2 ≤ t) :
    suzukiCheckpointGlobalAffineCurrent t =
        suzukiCheckpointLeftAffineJet (suzukiCheckpointEventIndex t) t ∧
      suzukiCheckpointCellCurvatureRemainder t ∈ Set.Icc 0 1 := by
  obtain ⟨hN, htcell⟩ := suzukiCheckpointEventIndex_two_le_and_mem_cell ht
  have hsplit := suzukiPsi_eq_leftAffineJet_add_unitBregman hN htcell
  unfold suzukiCheckpointGlobalAffineCurrent suzukiCheckpointCellCurvatureRemainder
  constructor
  · linarith [hsplit.1]
  · exact hsplit.2

end RHTower

namespace GaloisForLFunctions.RHTower

open Complex MeasureTheory Set
open _root_.RHTower

/-- FU marked average of the floor-selected signed affine checkpoint current. -/
def ccmFUSuzukiCheckpointAffineMixture (b H : ℝ) : ℝ :=
  (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
      suzukiCheckpointGlobalAffineCurrent t) +
    (32 / H ^ 4) * suzukiCheckpointGlobalAffineCurrent H

/-- FU marked average of the discarded positive within-cell curvature. -/
def ccmFUSuzukiCheckpointCurvatureMixture (b H : ℝ) : ℝ :=
  (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
      suzukiCheckpointCellCurvatureRemainder t) +
    (32 / H ^ 4) * suzukiCheckpointCellCurvatureRemainder H

private theorem intervalIntegrable_rectangularMixDensity_mul_checkpointCurvature
    {b H : ℝ} (hlogb : Real.log 2 ≤ b) (hbH : b ≤ H) :
    IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
        suzukiCheckpointCellCurvatureRemainder t) volume b H := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < b := hlog2pos.trans_le hlogb
  have hH : 0 < H := hb.trans_le hbH
  have hdensityCont : ContinuousOn
      (ccmThirdGradeCesaroRectangularMixDensity H) (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hρ : IntervalIntegrable
      (ccmThirdGradeCesaroRectangularMixDensity H) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbH] at hρ ⊢
  have hdensityMeas : Measurable (ccmThirdGradeCesaroRectangularMixDensity H) := by
    unfold ccmThirdGradeCesaroRectangularMixDensity
    fun_prop
  refine Integrable.mono' hρ
    ((hdensityMeas.mul measurable_suzukiCheckpointCellCurvatureRemainder).aestronglyMeasurable.restrict)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have htpos : 0 < t := hb.trans_le ht.1
  have hρ0 := ccmThirdGradeCesaroRectangularMixDensity_nonneg hH htpos ht.2
  have hrem :=
    (globalAffineCurrent_eq_leftJet_and_curvature_mem_unitInterval (hlogb.trans ht.1)).2
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0, abs_of_nonneg hrem.1] using
    (mul_le_of_le_one_right hρ0 hrem.2)

/-- The positive within-cell curvature has a fixed-wall FU budget independent of the moving upper
wall. Its entire contribution is bounded by the marked measure mass. -/
theorem ccmFUSuzukiCheckpointCurvatureMixture_mem_Icc
    {b H : ℝ} (hlogb : Real.log 2 ≤ b) (hbH : b ≤ H) :
    ccmFUSuzukiCheckpointCurvatureMixture b H ∈ Set.Icc 0 (96 / b ^ 4) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < b := hlog2pos.trans_le hlogb
  have hH : 0 < H := hb.trans_le hbH
  have hcurvInt :=
    intervalIntegrable_rectangularMixDensity_mul_checkpointCurvature hlogb hbH
  have hdensityCont : ContinuousOn
      (ccmThirdGradeCesaroRectangularMixDensity H) (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hρInt : IntervalIntegrable
      (ccmThirdGradeCesaroRectangularMixDensity H) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont
  have hbulk0 : 0 ≤ ∫ t in b..H,
      ccmThirdGradeCesaroRectangularMixDensity H t *
        suzukiCheckpointCellCurvatureRemainder t := by
    apply intervalIntegral.integral_nonneg hbH
    intro t ht
    exact mul_nonneg
      (ccmThirdGradeCesaroRectangularMixDensity_nonneg hH (hb.trans_le ht.1) ht.2)
      ((globalAffineCurrent_eq_leftJet_and_curvature_mem_unitInterval
        (hlogb.trans ht.1)).2.1)
  have hbulkLe : (∫ t in b..H,
      ccmThirdGradeCesaroRectangularMixDensity H t *
        suzukiCheckpointCellCurvatureRemainder t) ≤
      ∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t := by
    apply intervalIntegral.integral_mono_on hbH hcurvInt hρInt
    intro t ht
    have hρ0 := ccmThirdGradeCesaroRectangularMixDensity_nonneg
      hH (hb.trans_le ht.1) ht.2
    have hrem :=
      (globalAffineCurrent_eq_leftJet_and_curvature_mem_unitInterval
        (hlogb.trans ht.1)).2
    exact mul_le_of_le_one_right hρ0 hrem.2
  have hremH :=
    (globalAffineCurrent_eq_leftJet_and_curvature_mem_unitInterval
      (hlogb.trans hbH)).2
  have hendpoint0 : 0 ≤ (32 / H ^ 4) *
      suzukiCheckpointCellCurvatureRemainder H := mul_nonneg (by positivity) hremH.1
  have hendpointLe : (32 / H ^ 4) * suzukiCheckpointCellCurvatureRemainder H ≤
      32 / H ^ 4 := mul_le_of_le_one_right (by positivity) hremH.2
  have hmass := integral_rectangularMixDensity_add_endpoint_eq_errorKernel hb hbH
  have hk := ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds hb hbH
    (show b ∈ Set.Icc b H from ⟨le_rfl, hbH⟩)
  unfold ccmFUSuzukiCheckpointCurvatureMixture
  constructor
  · exact add_nonneg hbulk0 hendpoint0
  · calc
      _ ≤ (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t) +
          32 / H ^ 4 := add_le_add hbulkLe hendpointLe
      _ = ccmGuinandWeilThirdGradeCesaroErrorKernel H b := hmass
      _ ≤ 96 / b ^ 4 := hk.2

/-- Exact FU decomposition into a signed, piecewise-affine arithmetic checkpoint current and a
positive uniformly bounded curvature contribution. -/
theorem ccmFUCentralXiScrewPositiveMixture_eq_checkpointAffine_add_curvature
    {b H : ℝ} (hlogb : Real.log 2 ≤ b) (hbH : b ≤ H) :
    ccmFUCentralXiScrewPositiveMixture b H =
      ccmFUSuzukiCheckpointAffineMixture b H +
        ccmFUSuzukiCheckpointCurvatureMixture b H := by
  have hcurvInt :=
    intervalIntegrable_rectangularMixDensity_mul_checkpointCurvature hlogb hbH
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < b := hlog2pos.trans_le hlogb
  have hH : 0 < H := hb.trans_le hbH
  have hdensityCont : ContinuousOn
      (ccmThirdGradeCesaroRectangularMixDensity H) (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hψInt : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t)
      volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont.mul continuous_suzukiPsi.continuousOn
  have haffInt : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
        suzukiCheckpointGlobalAffineCurrent t) volume b H := by
    have hdiff := hψInt.sub hcurvInt
    apply hdiff.congr
    intro t _
    unfold suzukiCheckpointGlobalAffineCurrent
    ring
  have hbulk :
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t) =
        (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
          suzukiCheckpointGlobalAffineCurrent t) +
        (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
          suzukiCheckpointCellCurvatureRemainder t) := by
    rw [← intervalIntegral.integral_add haffInt hcurvInt]
    apply intervalIntegral.integral_congr
    intro t _
    change ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t =
      ccmThirdGradeCesaroRectangularMixDensity H t *
          suzukiCheckpointGlobalAffineCurrent t +
        ccmThirdGradeCesaroRectangularMixDensity H t *
          suzukiCheckpointCellCurvatureRemainder t
    rw [suzukiPsi_eq_globalAffineCurrent_add_curvature]
    ring
  unfold ccmFUCentralXiScrewPositiveMixture ccmFUSuzukiCheckpointAffineMixture
    ccmFUSuzukiCheckpointCurvatureMixture
  rw [hbulk, suzukiPsi_eq_globalAffineCurrent_add_curvature H]
  ring

/-- Uniform boundedness of the floor-selected signed affine checkpoint current. -/
def CCMFUSuzukiCheckpointAffineMixtureBound (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
    |ccmFUSuzukiCheckpointAffineMixture b H| ≤ C

/-- **Discrete-event reduction of CCM-FU.** Past the first prime wall, the RH-bearing positive
Suzuki-profile mixture is uniformly bounded exactly when its floor-selected affine checkpoint
current is uniformly bounded. Smooth intra-cell curvature is unconditionally absorbed. -/
theorem ccmFUCentralXiScrewPositiveMixtureBound_iff_checkpointAffineMixtureBound
    {b : ℝ} (hlogb : Real.log 2 ≤ b) :
    CCMFUCentralXiScrewPositiveMixtureBound b ↔
      CCMFUSuzukiCheckpointAffineMixtureBound b := by
  have hb : 0 < b := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hlogb
  let K : ℝ := 96 / b ^ 4
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + K, add_nonneg hC0 hK0, ?_⟩
    intro H hbH
    have hsplit :=
      ccmFUCentralXiScrewPositiveMixture_eq_checkpointAffine_add_curvature
        hlogb hbH.le
    have hcurv := ccmFUSuzukiCheckpointCurvatureMixture_mem_Icc hlogb hbH.le
    have haff : ccmFUSuzukiCheckpointAffineMixture b H =
        ccmFUCentralXiScrewPositiveMixture b H -
          ccmFUSuzukiCheckpointCurvatureMixture b H := by linarith
    rw [haff]
    exact (abs_sub _ _).trans
      (add_le_add (hC H hbH) (by rw [abs_of_nonneg hcurv.1]; exact hcurv.2))
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + K, add_nonneg hC0 hK0, ?_⟩
    intro H hbH
    rw [ccmFUCentralXiScrewPositiveMixture_eq_checkpointAffine_add_curvature
      hlogb hbH.le]
    have hcurv := ccmFUSuzukiCheckpointCurvatureMixture_mem_Icc hlogb hbH.le
    exact (abs_add_le _ _).trans
      (add_le_add (hC H hbH) (by rw [abs_of_nonneg hcurv.1]; exact hcurv.2))

/-- **Exact checkpoint/RH absorption law.**  Uniform control of the actual discrete affine
checkpoint current is unchanged by adjoining RH. -/
theorem ccmFUSuzukiCheckpointAffineMixtureBound_iff_and_riemannHypothesis
    {b : ℝ} (hlogb : Real.log 2 ≤ b) :
    CCMFUSuzukiCheckpointAffineMixtureBound b ↔
      CCMFUSuzukiCheckpointAffineMixtureBound b ∧ RiemannHypothesis := by
  have hb : 0 < b := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hlogb
  constructor
  · intro hbound
    refine ⟨hbound, ?_⟩
    have hpositive :=
      (ccmFUCentralXiScrewPositiveMixtureBound_iff_checkpointAffineMixtureBound hlogb).2
        hbound
    exact
      (ccmFUCentralXiScrewPositiveMixtureBound_iff_and_riemannHypothesis hb).mp
        hpositive |>.2
  · exact And.left

/-- Eventual uniform boundedness of the discrete affine checkpoint current. -/
def CCMFUSuzukiCheckpointAffineMixtureTailBound (b : ℝ) : Prop :=
  ∃ U C : ℝ, b < U ∧ 0 ≤ C ∧ ∀ H : ℝ, U ≤ H →
    |ccmFUSuzukiCheckpointAffineMixture b H| ≤ C

/-- The anchored prime--polar moment and discrete checkpoint current differ by a uniformly bounded
sum of curvature, affine-wall, and Gamma--Lerch terms. -/
theorem exists_nonnegative_uniform_bound_ccmFUSuzukiAnchoredCheckpointSum
    {b : ℝ} (hlogb : Real.log 2 ≤ b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ H : ℝ, b < H →
      |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H +
        ccmFUSuzukiCheckpointAffineMixture b H| ≤ D := by
  have hb : 0 < b := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hlogb
  obtain ⟨A, hA0, hA⟩ :=
    exists_nonnegative_uniform_bound_ccmFUCentralXiScrewAffineMemory hb
  obtain ⟨G, hG0, hG⟩ :=
    exists_nonnegative_uniform_bound_ccmFUCentralGammaLerchAffineMixture hb
  let K : ℝ := 96 / b ^ 4
  refine ⟨K + A + G,
    add_nonneg (add_nonneg (by dsimp only [K]; positivity) hA0) hG0, ?_⟩
  intro H hbH
  have hcurv := ccmFUSuzukiCheckpointCurvatureMixture_mem_Icc hlogb hbH.le
  have hdecomp :
      ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H +
          ccmFUSuzukiCheckpointAffineMixture b H =
        -ccmFUSuzukiCheckpointCurvatureMixture b H +
          ccmFUCentralXiScrewAffineMemory b H -
            ccmFUCentralGammaLerchAffineMixture b H := by
    rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_neg_xiScrewCodiagonalMixture_sub_gammaLerch
        hb hbH.le,
      ccmFUCentralXiScrewCodiagonalMixture_eq_positiveMixture_sub_affineMemory
        hb hbH.le,
      ccmFUCentralXiScrewPositiveMixture_eq_checkpointAffine_add_curvature
        hlogb hbH.le]
    ring
  rw [hdecomp]
  calc
    |-ccmFUSuzukiCheckpointCurvatureMixture b H +
          ccmFUCentralXiScrewAffineMemory b H -
        ccmFUCentralGammaLerchAffineMixture b H| ≤
        |-ccmFUSuzukiCheckpointCurvatureMixture b H +
          ccmFUCentralXiScrewAffineMemory b H| +
        |ccmFUCentralGammaLerchAffineMixture b H| := abs_sub _ _
    _ ≤ (|ccmFUSuzukiCheckpointCurvatureMixture b H| +
          |ccmFUCentralXiScrewAffineMemory b H|) +
        |ccmFUCentralGammaLerchAffineMixture b H| := by
      gcongr
      simpa only [abs_neg] using
        (abs_add_le (-ccmFUSuzukiCheckpointCurvatureMixture b H)
          (ccmFUCentralXiScrewAffineMemory b H))
    _ ≤ (K + A) + G := by
      have hcurvAbs : |ccmFUSuzukiCheckpointCurvatureMixture b H| ≤ K := by
        rw [abs_of_nonneg hcurv.1]
        exact hcurv.2
      exact add_le_add (add_le_add hcurvAbs (hA H hbH)) (hG H hbH)

/-- Eventual boundedness is unchanged after removing every smooth and archimedean defect from the
anchored moment, leaving only the floor-selected affine checkpoint current. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentTailBound_iff_checkpointAffineMixtureTailBound
    {b : ℝ} (hlogb : Real.log 2 ≤ b) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound b ↔
      CCMFUSuzukiCheckpointAffineMixtureTailBound b := by
  obtain ⟨D, hD0, hD⟩ :=
    exists_nonnegative_uniform_bound_ccmFUSuzukiAnchoredCheckpointSum hlogb
  constructor
  · rintro ⟨U, C, hbU, hC0, hC⟩
    refine ⟨U, C + D, hbU, add_nonneg hC0 hD0, ?_⟩
    intro H hUH
    have hbH : b < H := hbU.trans_le hUH
    have htri : |ccmFUSuzukiCheckpointAffineMixture b H| ≤
        |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H +
          ccmFUSuzukiCheckpointAffineMixture b H| +
        |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| := by
      calc
        |ccmFUSuzukiCheckpointAffineMixture b H| =
            |(ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H +
                ccmFUSuzukiCheckpointAffineMixture b H) -
              ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| := by ring
        _ ≤ _ := abs_sub _ _
    exact htri.trans (by linarith [hD H hbH, hC H hUH])
  · rintro ⟨U, C, hbU, hC0, hC⟩
    refine ⟨U, C + D, hbU, add_nonneg hC0 hD0, ?_⟩
    intro H hUH
    have hbH : b < H := hbU.trans_le hUH
    have htri : |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| ≤
        |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H +
          ccmFUSuzukiCheckpointAffineMixture b H| +
        |ccmFUSuzukiCheckpointAffineMixture b H| := by
      calc
        |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| =
            |(ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H +
                ccmFUSuzukiCheckpointAffineMixture b H) -
              ccmFUSuzukiCheckpointAffineMixture b H| := by ring
        _ ≤ _ := abs_sub _ _
    exact htri.trans (by linarith [hD H hbH, hC H hUH])

/-- Fixed-source tail bound for the actual affine checkpoint current. -/
def CCMFUSuzukiCanonicalCheckpointAffineTailBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
    |ccmFUSuzukiCheckpointAffineMixture 1 H| ≤ C

/-- **Exact canonical-tail/RH absorption law.**  The canonical discrete checkpoint tail is
unchanged by adjoining RH. -/
theorem ccmFUSuzukiCanonicalCheckpointAffineTailBound_iff_and_riemannHypothesis :
    CCMFUSuzukiCanonicalCheckpointAffineTailBound ↔
      CCMFUSuzukiCanonicalCheckpointAffineTailBound ∧ RiemannHypothesis := by
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  constructor
  · intro htail
    refine ⟨htail, ?_⟩
    have hcheckpointTail : CCMFUSuzukiCheckpointAffineMixtureTailBound 1 := by
      rcases htail with ⟨C, hC0, hC⟩
      exact ⟨2, C, by norm_num, hC0, hC⟩
    have hanchoredTail : CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound 1 :=
      (ccmGuinandWeilThirdGradeCesaroAnchoredMomentTailBound_iff_checkpointAffineMixtureTailBound
        hlog2).2 hcheckpointTail
    exact
      (ccmGuinandWeilThirdGradeCesaroAnchoredMomentTailBound_iff_and_riemannHypothesis
        (b := 1) (by norm_num)).mp hanchoredTail |>.2
  · exact And.left

/-- False RH forces the canonical checkpoint current above every ceiling after every later wall. -/
theorem ccmFUSuzukiCheckpointAffineMixture_cofinally_unbounded_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∀ U C : ℝ, 1 < U → ∃ H : ℝ, U ≤ H ∧
      C < |ccmFUSuzukiCheckpointAffineMixture 1 H| := by
  intro U C hU
  by_contra hescape
  push Not at hescape
  apply hRH
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hcheckpointTail : CCMFUSuzukiCheckpointAffineMixtureTailBound 1 := by
    refine ⟨U, max C 0, hU, le_max_right _ _, ?_⟩
    intro H hH
    exact (hescape H hH).trans (le_max_left _ _)
  have hanchoredTail : CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound 1 :=
    (ccmGuinandWeilThirdGradeCesaroAnchoredMomentTailBound_iff_checkpointAffineMixtureTailBound
      hlog2).2 hcheckpointTail
  exact
    (ccmGuinandWeilThirdGradeCesaroAnchoredMomentTailBound_iff_and_riemannHypothesis
      (b := 1) (by norm_num)).mp hanchoredTail |>.2

end GaloisForLFunctions.RHTower
