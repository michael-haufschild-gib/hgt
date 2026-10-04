import GaloisForLFunctions.RHTower.ThetaDiagonalWardForcing

/-! The literal diagonal Schur energy has one positive maximum.
Its exact zero-total Ward forcing crosses once from negative to positive. -/

noncomputable section
open Set Filter Topology MeasureTheory
namespace RHTower.ThetaDiagonalWard

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel
local notation "w" => ThetaGaussianCoarea.coareaWeight

def energy (x : ℝ) : ℝ := H x x-(H 0 x)^2/H 0 0

theorem energy_continuous : Continuous energy :=
  (ThetaJoint.source_kernel_continuous.comp (continuous_id.prodMk continuous_id)).sub
    (((ThetaJoint.source_kernel_continuous.comp (continuous_const.prodMk continuous_id)).pow 2).div_const _)

theorem energy_zero : energy 0=0 := by
  unfold energy
  field_simp [ThetaJoint.centerMass_pos.ne']
  ring

theorem energy_pos {x : ℝ} (hx : 0 < x) : 0 < energy x := by
  have hd := ThetaTailTwoPoint.kernel_two_point_det_pos hx.ne
  have he : energy x=ThetaSturm.determinant 0 x/H 0 0 := by
    unfold energy ThetaSturm.determinant
    field_simp [ThetaJoint.centerMass_pos.ne']
  rw [he]
  exact div_pos hd ThetaJoint.centerMass_pos

theorem energy_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ energy x := by
  rcases hx.eq_or_lt with he | hp
  · rw [← he,energy_zero]
  · exact (energy_pos hp).le

theorem energy_le_kernel (x : ℝ) : energy x ≤ H x x := by
  have h := div_nonneg (sq_nonneg (H 0 x)) ThetaJoint.centerMass_pos.le
  unfold energy
  linarith only [h]

theorem energy_limit_zero : Tendsto energy atTop (𝓝 0) := by
  have hk : Tendsto (fun x => H x x) atTop (𝓝 0) := by
    simpa only [zero_add] using ThetaTailCauchy.kernel_limit_zero 0 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hk
  · filter_upwards [Ici_mem_atTop (0:ℝ)] with x hx
    exact energy_nonneg hx
  · exact Eventually.of_forall energy_le_kernel

/-- Complete source-weighted Ward derivative, including the inverse-Gram correction. -/
theorem energy_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt energy (-(w x*forcing x)) x := by
  have hd : HasDerivAt (fun t => H t t) (-2*x*k x^2) x := by
    have h := hasDerivAt_thetaTailFirstMomentKernel_commonShift x 0 0
    simp only [thetaTailCommonTranslationGenerator,zero_add] at h
    convert! h using 1
    ring
  have hw : ThetaJoint.firstLeft x 0=-x*k 0*k x-ThetaConfluent.centerMixedRow x := by
    rw [centerMixedRow_eq_firstLeft]
    have h := kernel_first_sum 0 x
    simp only [zero_add] at h
    linarith only [h]
  convert! hd.sub (((ThetaJoint.source_hasDerivAt_right 0 x).pow 2).div_const (H 0 0)) using 1
  rw [hw]
  unfold ThetaGaussianCoarea.coareaWeight forcing mass row ThetaTailRow.normalized
    ThetaCoordinate.normalizedMixedRow
  field_simp [hx.ne',(thetaCuspFullSource_pos_all 0).ne',
    (thetaCuspFullSource_pos_all x).ne',ThetaJoint.centerMass_pos.ne']
  ring

theorem weighted_forcing_integrable : IntegrableOn (fun x => w x*forcing x) (Ioi 0) := by
  let M := 1+ThetaConfluent.centerEntry/k 0^2
  apply (ThetaGaussianCoarea.coareaWeight_integrable.const_mul M).mono'
    ((ThetaGaussianCoarea.coareaWeight_continuous.measurable.mul forcing_measurable).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖w x*forcing x‖ ≤ M*w x
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (ThetaGaussianCoarea.coareaWeight_pos hx)]
  have hb := forcing_bounds hx
  have hf : |forcing x| ≤ M := by
    rw [abs_le]
    dsimp only [M]
    constructor <;> linarith only [hb.1,hb.2,initialMixed_pos]
  have h := mul_le_mul_of_nonneg_left hf (ThetaGaussianCoarea.coareaWeight_pos hx).le
  linarith only [h]

/-- The actual diagonal forcing is centered over the entire source measure. -/
theorem weighted_forcing_integral_zero : (∫ x in Ioi 0, w x*forcing x)=0 := by
  have hi : IntegrableOn (fun x => -(w x*forcing x)) (Ioi 0) := by
    convert! weighted_forcing_integrable.neg using 1
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    energy_continuous.continuousWithinAt (fun x hx => energy_hasDerivAt hx) hi energy_limit_zero
  simp only [integral_neg,energy_zero,sub_self] at h
  linarith only [h]

theorem forcing_exists_positive : ∃ x : ℝ, 0 < x ∧ 0 < forcing x := by
  by_contra hh
  have hf (x : ℝ) (hx : 0 < x) : forcing x ≤ 0 := by
    by_contra hn
    exact hh ⟨x,hx,lt_of_not_ge hn⟩
  have hnn : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ -(w x*forcing x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (ThetaGaussianCoarea.coareaWeight_pos hx).le (hf x hx))
  have hi : IntegrableOn (fun x => -(w x*forcing x)) (Ioi 0) := by
    convert! weighted_forcing_integrable.neg using 1
  have hz : (∫ x in Ioi 0, -(w x*forcing x))=0 := by
    rw [integral_neg,weighted_forcing_integral_zero,neg_zero]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
    ((ThetaGaussianCoarea.coareaWeight_continuous.continuousOn.mul forcing_continuousOn).neg)
    continuousOn_const
  have he (x : ℝ) (hx : 0 < x) : forcing x=0 := by
    have h : w x*forcing x=0 := neg_eq_zero.mp (heq hx)
    exact (mul_eq_zero.mp h).resolve_left (ThetaGaussianCoarea.coareaWeight_pos hx).ne'
  have hm := forcing_strictMono (show (1:ℝ) ∈ Ioi 0 by norm_num)
    (show (2:ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1:ℝ)<2)
  rw [he 1 (by norm_num),he 2 (by norm_num)] at hm
  exact (lt_irrefl _) hm

theorem forcing_exists_negative : ∃ x : ℝ, 0 < x ∧ forcing x < 0 := by
  have h := forcing_limit_zero.eventually (gt_mem_nhds (neg_lt_zero.mpr initialMixed_pos))
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x ∧ forcing x < 0 := by
    filter_upwards [self_mem_nhdsWithin,h] with x hx hn
    exact ⟨hx,hn⟩
  exact he.exists

/-- Exactly one positive node separates the two signs of the complete Ward forcing. -/
theorem forcing_has_unique_positive_zero : ∃! r : ℝ, 0 < r ∧ forcing r=0 := by
  obtain ⟨u,hu,hfu⟩ := forcing_exists_negative
  obtain ⟨v,hv,hfv⟩ := forcing_exists_positive
  have huv : u < v := by
    by_contra! h
    have hm := forcing_strictMono.monotoneOn hv hu h
    linarith only [hm,hfu,hfv]
  have hc : ContinuousOn forcing (Icc u v) := forcing_continuousOn.mono
    (fun x hx => lt_of_lt_of_le hu hx.1)
  obtain ⟨r,hr,hfr⟩ := intermediate_value_Icc huv.le hc ⟨hfu.le,hfv.le⟩
  have hr0 := hu.trans_le hr.1
  refine ⟨r,⟨hr0,hfr⟩,?_⟩
  intro x hx
  exact forcing_strictMono.injOn hx.1 hr0 (hx.2.trans hfr.symm)

theorem forcing_single_crossing : ∃ r : ℝ, 0 < r ∧ forcing r=0 ∧
    (∀ x, 0 < x → x < r → forcing x<0) ∧
    (∀ x, r < x → 0 < forcing x) := by
  obtain ⟨r,hr,_⟩ := forcing_has_unique_positive_zero
  refine ⟨r,hr.1,hr.2,?_,?_⟩
  · intro x hx hxr
    simpa only [hr.2] using forcing_strictMono hx hr.1 hxr
  · intro x hrx
    simpa only [hr.2] using forcing_strictMono hr.1 (hr.1.trans hrx) hrx

/-- The actual diagonal Schur energy has a unique peak on the nonnegative ray. -/
theorem energy_unique_peak : ∃ r : ℝ, 0 < r ∧
    ∀ x : ℝ, 0 ≤ x → x ≠ r → energy x < energy r := by
  obtain ⟨r,hr,hfr,hbefore,hafter⟩ := forcing_single_crossing
  have hm : StrictMonoOn energy (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) energy_continuous.continuousOn
    intro x hx
    have hx0 : 0 < x ∧ x < r := by simpa only [interior_Icc,mem_Ioo] using hx
    rw [(energy_hasDerivAt hx0.1).deriv]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (ThetaGaussianCoarea.coareaWeight_pos hx0.1)
      (hbefore x hx0.1 hx0.2))
  have ha : StrictAntiOn energy (Ici r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _) energy_continuous.continuousOn
    intro x hx
    have hrx : r < x := by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(energy_hasDerivAt (hr.trans hrx)).deriv]
    exact neg_lt_zero.mpr (mul_pos (ThetaGaussianCoarea.coareaWeight_pos (hr.trans hrx)) (hafter x hrx))
  refine ⟨r,hr,?_⟩
  intro x hx hxr
  rcases lt_or_gt_of_ne hxr with h | h
  · exact hm ⟨hx,h.le⟩ ⟨hr.le,le_rfl⟩ h
  · exact ha (show r ∈ Ici r by simp) (show x ∈ Ici r from h.le) h

end RHTower.ThetaDiagonalWard
