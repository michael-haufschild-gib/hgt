import GaloisForLFunctions.RHTower.ThetaTailSmallNodeCoordinate
import GaloisForLFunctions.RHTower.ThetaTailOrderedRowMonotonicity
import GaloisForLFunctions.RHTower.ThetaTailConfluentCoordinateGlobal
import GaloisForLFunctions.RHTower.ThetaFinitePairPacketTail
import GaloisForLFunctions.RHTower.ThetaGaussianCovarianceMeasure

/-! The actual diagonal Ward forcing retains both normalized rows.
Its global strict increase is a source theorem, not a coefficient-sign premise. -/

noncomputable section
open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
namespace RHTower.ThetaDiagonalWard

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "H" => thetaTailFirstMomentKernel
local notation "n" => ThetaCoordinate.normalizedMixedRow

def row (x : ℝ) : ℝ := ThetaTailRow.normalized 0 x
def mass : ℝ := row 0
def forcing (x : ℝ) : ℝ := 1-row x*(1+n x)/mass

/-- Common translation identifies the sum of the two distinct endpoint derivatives. -/
theorem kernel_first_sum (x y : ℝ) :
    ThetaJoint.firstLeft x y+ThetaJoint.firstLeft y x=-(x+y)*k x*k y := by
  have hbase : HasFDerivAt (Function.uncurry H)
      ((toCLM (ThetaJoint.firstLeft x y)).coprod (toCLM (ThetaJoint.firstLeft y x))) (x,y) :=
    (hasStrictFDerivAt_uncurry_coprod
      (u := (x,y)) (f := H)
      (f₁ := fun a b => toCLM (ThetaJoint.firstLeft a b))
      (f₂ := fun a b => toCLM (ThetaJoint.firstLeft b a))
      (Eventually.of_forall fun z => (ThetaJoint.source_hasDerivAt_left z.1 z.2).hasFDerivAt)
      (Eventually.of_forall fun z => (ThetaJoint.source_hasDerivAt_right z.1 z.2).hasFDerivAt)
      (continuous_toCLM.continuousAt.comp ThetaJoint.firstLeft_continuous.continuousAt)
      (continuous_toCLM.continuousAt.comp
        (ThetaJoint.firstLeft_continuous.comp (continuous_snd.prodMk continuous_fst)).continuousAt)).hasFDerivAt
  have hbase' : HasFDerivAt (Function.uncurry H)
      ((toCLM (ThetaJoint.firstLeft x y)).coprod (toCLM (ThetaJoint.firstLeft y x))) (x+0,y+0) := by
    simpa only [add_zero] using hbase
  have hs : HasDerivAt (fun t : ℝ => H (x+t) (y+t))
      (ThetaJoint.firstLeft x y+ThetaJoint.firstLeft y x) 0 := by
    simpa only [Function.comp_def,Function.uncurry_apply_pair,ContinuousLinearMap.coprod_apply,
      toCLM_apply,one_mul,id_eq] using hbase'.comp_hasDerivAt 0
        (((hasDerivAt_id (0:ℝ)).const_add x).prodMk ((hasDerivAt_id (0:ℝ)).const_add y))
  have he := hs.unique (hasDerivAt_thetaTailFirstMomentKernel_commonShift 0 x y)
  simpa only [thetaTailCommonTranslationGenerator,mul_zero,add_zero,neg_mul] using he

theorem centerMixedRow_eq_firstLeft (x : ℝ) :
    ThetaConfluent.centerMixedRow x=ThetaJoint.firstLeft 0 x :=
  (ThetaConfluent.kernel_center_hasDerivAt x).unique (ThetaJoint.source_hasDerivAt_right x 0)

theorem mass_pos : 0 < mass := by
  exact div_pos ThetaJoint.centerMass_pos
    (mul_pos (thetaCuspFullSource_pos_all 0) (thetaCuspFullSource_pos_all 0))

theorem row_continuous : Continuous row := by
  unfold row ThetaTailRow.normalized
  exact (ThetaJoint.source_kernel_continuous.comp (continuous_const.prodMk continuous_id)).div
    (continuous_const.mul contDiff_thetaCuspFullSource.continuous)
    (fun x => mul_ne_zero (thetaCuspFullSource_pos_all 0).ne' (thetaCuspFullSource_pos_all x).ne')

theorem row_pos {x : ℝ} (hx : 0 < x) : 0 < row x := by
  rw [show row x=(∫ u in Ioi 0, ThetaGaussianCoarea.density 0 x u) from
    (ThetaGaussianCoarea.integral_density (le_refl 0) hx.le).symm]
  apply (integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun u => (ThetaGaussianCoarea.density_pos 0 x u).le)
    (ThetaGaussianCoarea.density_integrable (le_refl 0) hx.le)).mpr
  have hm : 0 < (volume.restrict (Ioi (0:ℝ))) (Ioi 0) := by
    simp only [Measure.restrict_apply measurableSet_Ioi,inter_self,Real.volume_Ioi,ENNReal.zero_lt_top]
  exact lt_of_lt_of_le hm (measure_mono fun u _ => (ThetaGaussianCoarea.density_pos 0 x u).ne')

theorem row_strictAnti : StrictAntiOn row (Ici 0) :=
  ThetaTailRow.strictAntiOn_normalized_row (le_refl 0)

theorem row_lt_mass {x : ℝ} (hx : 0 < x) : row x < mass :=
  row_strictAnti (show (0:ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx.le) hx

private theorem row_raw_derivative (x : ℝ) : HasDerivAt row
    ((ThetaJoint.firstLeft x 0+p x*H 0 x)/(k 0*k x)) x := by
  change HasDerivAt (fun t => H 0 t/(k 0*k t)) _ x
  convert! (ThetaJoint.source_hasDerivAt_right 0 x).div
    ((ThetaFiniteTransport.actualSource_hasDerivAt x).const_mul (k 0))
    (mul_ne_zero (thetaCuspFullSource_pos_all 0).ne' (thetaCuspFullSource_pos_all x).ne') using 1
  field_simp [(thetaCuspFullSource_pos_all 0).ne',(thetaCuspFullSource_pos_all x).ne']
  ring

/-- The moving-node derivative keeps the mixed-anchor feedback with its correct sign. -/
theorem row_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt row (p x*row x-x*(1+n x)) x := by
  have hw : ThetaJoint.firstLeft x 0=-x*k 0*k x-ThetaConfluent.centerMixedRow x := by
    rw [centerMixedRow_eq_firstLeft]
    have h := kernel_first_sum 0 x
    simp only [zero_add] at h
    linarith only [h]
  convert! row_raw_derivative x using 1
  rw [hw]
  unfold row ThetaTailRow.normalized ThetaCoordinate.normalizedMixedRow
  field_simp [hx.ne',(thetaCuspFullSource_pos_all 0).ne',(thetaCuspFullSource_pos_all x).ne']
  ring

theorem one_add_mixed_pos {x : ℝ} (hx : 0 < x) : 0 < 1+n x := by
  have hn : p x*row x-x*(1+n x)<0 := by
    rw [← (row_hasDerivAt hx).deriv]
    exact ThetaTailRow.deriv_normalized_neg (le_refl 0) hx.le hx
  have hp := mul_pos (ThetaSturmCrossing.slope_pos hx) (row_pos hx)
  by_contra hh
  have hm := mul_nonpos_of_nonneg_of_nonpos hx.le (not_lt.mp hh)
  linarith only [hn,hp,hm]

theorem forcing_continuousOn : ContinuousOn forcing (Ioi 0) := by
  have hn : ContinuousOn n (Ioi 0) := fun x hx =>
    (ThetaCoordinate.normalizedMixedRow_hasDerivAt hx).continuousAt.continuousWithinAt
  exact continuousOn_const.sub ((row_continuous.continuousOn.mul
    (continuousOn_const.add hn)).div_const mass)

theorem forcing_measurable : Measurable forcing := by
  have hm : Measurable ThetaConfluent.centerMixedRow := by
    simp_rw [show ThetaConfluent.centerMixedRow=(fun x => ThetaJoint.firstLeft 0 x) from
      funext centerMixedRow_eq_firstLeft]
    exact (ThetaJoint.firstLeft_continuous.comp (continuous_const.prodMk continuous_id)).measurable
  have hn : Measurable n := hm.div
    ((measurable_id.mul_const (k 0)).mul contDiff_thetaCuspFullSource.continuous.measurable)
  exact measurable_const.sub ((row_continuous.measurable.mul (measurable_const.add hn)).div_const mass)

/-- Global strict increase of the complete coupled diagonal forcing. -/
theorem forcing_strictMono : StrictMonoOn forcing (Ioi 0) := by
  intro x hx y hy hxy
  have hr := row_strictAnti (show x ∈ Ici 0 from (show 0 < x from hx).le)
    (show y ∈ Ici 0 from (show 0 < y from hy).le) hxy
  have hn := ThetaCoordinate.normalizedMixedRow_strictAnti hx hy hxy
  have hp : row y*(1+n y)<row x*(1+n x) :=
    (mul_lt_mul_of_pos_right hr (one_add_mixed_pos hy)).trans
      (mul_lt_mul_of_pos_left (by linarith only [hn]) (row_pos hx))
  have h := div_lt_div_of_pos_right hp mass_pos
  unfold forcing
  linarith only [h]

theorem initialMixed_pos : 0 < ThetaConfluent.centerEntry/k 0^2 :=
  div_pos ThetaConfluent.centerEntry_pos (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))

theorem forcing_limit_zero : Tendsto forcing (𝓝[>] 0)
    (𝓝 (-(ThetaConfluent.centerEntry/k 0^2))) := by
  have hg : Tendsto row (𝓝[>] 0) (𝓝 mass) :=
    row_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := ((hg.mul (ThetaCoordinate.normalizedMixedRow_limit.const_add 1)).div_const mass).const_sub 1
  convert! h using 1
  field_simp [mass_pos.ne']
  ring

theorem forcing_bounds {x : ℝ} (hx : 0 < x) :
    -(ThetaConfluent.centerEntry/k 0^2)<forcing x ∧ forcing x<1 := by
  have hn := ThetaCoordinate.normalizedMixedRow_lt_center hx
  have hp := mul_pos (row_pos hx) (one_add_mixed_pos hx)
  have hb : row x*(1+n x) < mass*(1+ThetaConfluent.centerEntry/k 0^2) :=
    (mul_lt_mul_of_pos_left (by linarith only [hn]) (row_pos hx)).trans
      (mul_lt_mul_of_pos_right (row_lt_mass hx) (by linarith only [initialMixed_pos]))
  have hdiv := (div_lt_iff₀ mass_pos).mpr (hb.trans_eq (mul_comm _ _))
  have hdpos := div_pos hp mass_pos
  unfold forcing
  constructor <;> linarith only [hdiv,hdpos]

end RHTower.ThetaDiagonalWard
