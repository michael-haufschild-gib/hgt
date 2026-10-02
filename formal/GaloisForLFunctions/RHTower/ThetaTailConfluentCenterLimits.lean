import GaloisForLFunctions.RHTower.ThetaTailConfluentCenterGram
import GaloisForLFunctions.RHTower.ThetaTwoNodeSignedSturmEnergy
import GaloisForLFunctions.RHTower.ThetaTailOrderedRowMonotonicity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LHopital

/-! Exact second-order center limits for the actual full theta tail kernel. -/

noncomputable section
open MeasureTheory Filter Topology Set
namespace RHTower.ThetaConfluent

private def weightedSource (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weightedSource_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) :
    weightedSource f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weightedSource, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private def correlation (f g : SchwartzMap ℝ ℝ) (y : ℝ) : ℝ :=
  ∫ t in Ioi 0, f t*g (y+t)

private theorem correlation_integrable (f g : SchwartzMap ℝ ℝ) (y : ℝ) :
    Integrable (fun t => f t*g (y+t)) :=
  f.integrable.mul_bdd (g.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => g.norm_le_seminorm ℝ (y+t))

private theorem correlation_hasDerivAt (f g : SchwartzMap ℝ ℝ) (y : ℝ) :
    HasDerivAt (correlation f g)
      (correlation f (SchwartzMap.derivCLM ℝ ℝ g) y) y := by
  let d := SchwartzMap.derivCLM ℝ ℝ g
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := fun y t => f t*g (y+t))
    (F' := fun y t => f t*d (y+t))
    (bound := fun t => ‖f t‖*SchwartzMap.seminorm ℝ 0 0 d)
    (s := univ) (x₀ := y) univ_mem
    (Filter.Eventually.of_forall fun z => (correlation_integrable f g z).integrableOn.aestronglyMeasurable)
    (correlation_integrable f g y).integrableOn
    (correlation_integrable f d y).integrableOn.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t z _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (d.norm_le_seminorm ℝ (z+t)) (norm_nonneg _))
    (f.integrable.norm.mul_const _).integrableOn
    (Filter.Eventually.of_forall fun t z _ => by
      convert! ((g.hasDerivAt (z+t)).comp z ((hasDerivAt_id z).add_const t)).const_mul (f t) using 1
      simp only [mul_one]
      rfl)
  exact h.2

private def shiftedSource (x : ℝ) : SchwartzMap ℝ ℝ :=
  thetaCuspSchwartzReal.compSubConstCLM ℝ (-x)

private theorem shiftedSource_apply (x t : ℝ) :
    shiftedSource x t = thetaCuspFullSource (x+t) := by
  simp only [shiftedSource, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add,
    thetaCuspSchwartzReal_apply, add_comm]

private abbrev dsource : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal
private abbrev ddsource : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ dsource

private theorem kernel_eq_correlation (x y : ℝ) :
    thetaTailFirstMomentKernel x y =
      (x+y)*correlation (shiftedSource x) thetaCuspSchwartzReal y+
        2*correlation (weightedSource (shiftedSource x)) thetaCuspSchwartzReal y := by
  have he := thetaTailFirstMomentKernel_commonShift_eq_tail 0 x y
  simp only [add_zero] at he
  rw [he]
  dsimp only [correlation]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((correlation_integrable (shiftedSource x) thetaCuspSchwartzReal y).const_mul _).integrableOn
      ((correlation_integrable (weightedSource (shiftedSource x)) thetaCuspSchwartzReal y).const_mul _).integrableOn]
  apply integral_congr_ae
  filter_upwards with t
  simp only [thetaTailCommonTranslationIntegrand, weightedSource_apply, shiftedSource_apply,
    thetaCuspSchwartzReal_apply]
  ring

private def rowFirst (x y : ℝ) : ℝ :=
  correlation (shiftedSource x) thetaCuspSchwartzReal y+
    (x+y)*correlation (shiftedSource x) dsource y+
    2*correlation (weightedSource (shiftedSource x)) dsource y

private def rowSecond (x y : ℝ) : ℝ :=
  2*correlation (shiftedSource x) dsource y+
    (x+y)*correlation (shiftedSource x) ddsource y+
    2*correlation (weightedSource (shiftedSource x)) ddsource y

private theorem kernel_hasDerivAt (x y : ℝ) :
    HasDerivAt (thetaTailFirstMomentKernel x) (rowFirst x y) y := by
  have he : thetaTailFirstMomentKernel x = fun y =>
      (x+y)*correlation (shiftedSource x) thetaCuspSchwartzReal y+
      2*correlation (weightedSource (shiftedSource x)) thetaCuspSchwartzReal y :=
    funext (kernel_eq_correlation x)
  rw [he]
  convert! (((hasDerivAt_id y).const_add x).mul
    (correlation_hasDerivAt (shiftedSource x) thetaCuspSchwartzReal y)).add
    ((correlation_hasDerivAt (weightedSource (shiftedSource x)) thetaCuspSchwartzReal y).const_mul 2) using 1
  simp only [rowFirst, one_mul, id_eq]

private theorem rowFirst_hasDerivAt (x y : ℝ) :
    HasDerivAt (rowFirst x) (rowSecond x y) y := by
  convert! ((correlation_hasDerivAt (shiftedSource x) thetaCuspSchwartzReal y).add
    (((hasDerivAt_id y).const_add x).mul (correlation_hasDerivAt (shiftedSource x) dsource y))).add
    ((correlation_hasDerivAt (weightedSource (shiftedSource x)) dsource y).const_mul 2) using 1
  simp only [rowSecond, one_mul, id_eq]
  ring

/-- Continuity of every literal row, including the coalescing-node endpoint. -/
theorem continuous_kernel_row (x : ℝ) : Continuous (thetaTailFirstMomentKernel x) :=
  continuous_iff_continuousAt.mpr fun y => (kernel_hasDerivAt x y).continuousAt

private theorem rowFirst_center : rowFirst 0 0 = 0 := by
  let f := thetaCuspSchwartzReal
  have hi : Integrable (fun t : ℝ => f t^2+2*(t*f t*deriv (f : ℝ → ℝ) t)) := by
    have h := (correlation_integrable f f 0).add
      ((correlation_integrable (weightedSource f) dsource 0).const_mul 2)
    convert! h using 1
    ext t
    simp only [zero_add, weightedSource_apply, SchwartzMap.derivCLM_apply, Pi.add_apply]
    ring
  have hd (t : ℝ) : HasDerivAt (fun t => t*f t^2)
      (f t^2+2*(t*f t*deriv (f : ℝ → ℝ) t)) t := by
    convert! (hasDerivAt_id t).mul ((f.hasDerivAt t).pow 2) using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have hl : Tendsto (fun t : ℝ => t*f t^2) atTop (𝓝 0) := by
    have h := ((weightedSource f).tendsto_cocompact.mono_left atTop_le_cocompact).mul
      (f.tendsto_cocompact.mono_left atTop_le_cocompact)
    simp only [weightedSource_apply, mul_zero] at h
    convert! h using 1
    ext t
    ring
  have hz := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun t _ => hd t) hi.integrableOn hl
  simp only [zero_mul, sub_zero] at hz
  have hc : shiftedSource 0 = f := by
    ext t
    simp only [shiftedSource_apply, zero_add]
    rfl
  dsimp only [rowFirst]
  rw [hc]
  simp only [zero_mul, add_zero]
  dsimp only [correlation]
  rw [← integral_const_mul,
    ← integral_add (correlation_integrable f f 0).integrableOn
      ((correlation_integrable (weightedSource f) dsource 0).const_mul 2).integrableOn]
  convert! hz using 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [weightedSource_apply, zero_add, SchwartzMap.derivCLM_apply]
  ring

private theorem rowSecond_center : rowSecond 0 0 = -2*derivativeMass := by
  have hc : shiftedSource 0 = thetaCuspSchwartzReal := by
    ext t
    simp only [shiftedSource_apply, zero_add, thetaCuspSchwartzReal_apply]
  dsimp only [rowSecond]
  rw [hc]
  simp only [zero_mul, add_zero]
  dsimp only [correlation]
  simp only [zero_add, weightedSource_apply, SchwartzMap.derivCLM_apply,
    thetaCuspSchwartzReal_apply]
  change 2*(∫ t in Ioi 0, thetaCuspFullSource t*deriv thetaCuspFullSource t)+
    2*(∫ t in Ioi 0, t*thetaCuspFullSource t*deriv (deriv thetaCuspFullSource) t) =
    -2*derivativeMass
  rw [ThetaGeometricBoundaryAudit.source_times_derivative_tail, weighted_second_integral]
  ring

private theorem second_quotient_limit {f g : ℝ → ℝ} {a : ℝ}
    (hf : ∀x, HasDerivAt f (g x) x) (hg : HasDerivAt g a 0) (hz : g 0 = 0) :
    Tendsto (fun z => (f z-f 0)/z^2) (𝓝[>] 0) (𝓝 (a/2)) := by
  have hq : Tendsto (fun z => g z/z) (𝓝[>] 0) (𝓝 a) := by
    simpa only [zero_add, hz, sub_zero, smul_eq_mul, inv_mul_eq_div] using hg.tendsto_slope_zero_right
  have hq' : Tendsto (fun z => g z/(2*z)) (𝓝[>] 0) (𝓝 (a/2)) := by
    convert! hq.div_const 2 using 1
    ext z
    ring
  apply HasDerivAt.lhopital_zero_nhdsGT
    (Filter.Eventually.of_forall fun z => (hf z).sub_const (f 0))
    (Filter.Eventually.of_forall fun z => by
      convert! (hasDerivAt_id z).pow 2 using 1; simp [id_eq])
    ?_ ?_ ?_ hq'
  · filter_upwards [self_mem_nhdsWithin] with z hz'
    exact mul_ne_zero (by norm_num) (ne_of_gt hz')
  · simpa only [sub_self] using ((hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub_const (f 0)
  · simpa using (tendsto_id : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝[>] 0)).mono_right nhdsWithin_le_nhds |>.pow 2

/-- The center off-diagonal second-order coefficient is the exact derivative mass. -/
theorem center_row_quotient_limit :
    Tendsto (fun z => (thetaTailFirstMomentKernel 0 z-thetaTailFirstMomentKernel 0 0)/z^2)
      (𝓝[>] 0) (𝓝 (-derivativeMass)) := by
  have h := second_quotient_limit (kernel_hasDerivAt 0) (rowFirst_hasDerivAt 0 0) rowFirst_center
  rw [rowSecond_center] at h
  convert! h using 1
  congr 1
  ring

/-- The source quotient needed for the actual inverse coefficients. -/
theorem center_source_quotient_limit :
    Tendsto (fun z => (thetaCuspFullSource z-thetaCuspFullSource 0)/z^2)
      (𝓝[>] 0) (𝓝 (deriv (deriv thetaCuspFullSource) 0/2)) := by
  have hf (z : ℝ) : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource z) z :=
    thetaCuspSchwartzReal.hasDerivAt z
  have hd : HasDerivAt (deriv thetaCuspFullSource)
      (deriv (deriv thetaCuspFullSource) 0) 0 :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).hasDerivAt 0
  apply second_quotient_limit hf hd
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) ⟨0,rfl⟩

/-- The diagonal second-order coefficient retains the exact endpoint square. -/
theorem center_diagonal_quotient_limit :
    Tendsto (fun z => (thetaTailFirstMomentKernel z z-thetaTailFirstMomentKernel 0 0)/z^2)
      (𝓝[>] 0) (𝓝 (-thetaCuspFullSource 0^2)) := by
  have hd : HasDerivAt (fun z => -(2*z*thetaCuspFullSource z^2))
      (-2*thetaCuspFullSource 0^2) 0 := by
    convert! (((hasDerivAt_id (0:ℝ)).const_mul 2).mul
      ((thetaCuspSchwartzReal.hasDerivAt 0).pow 2)).neg using 1
    simp only [Pi.pow_apply, thetaCuspSchwartzReal_apply, id_eq, zero_mul, mul_zero, add_zero]
    ring
  have h := second_quotient_limit ThetaSourceWard.hasDerivAt_thetaPrimeGammaCutEnergy hd
    (by simp only [mul_zero, zero_mul, neg_zero])
  simp only [ThetaTailTwoPoint.kernel_diag_eq_cut]
  convert! h using 1
  congr 1
  ring

private theorem kernel_center_pos : 0 < thetaTailFirstMomentKernel 0 0 := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0

private theorem center_row_limit :
    Tendsto (thetaTailFirstMomentKernel 0) (𝓝[>] 0) (𝓝 (thetaTailFirstMomentKernel 0 0)) :=
  (continuous_kernel_row 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem center_source_limit :
    Tendsto thetaCuspFullSource (𝓝[>] 0) (𝓝 (thetaCuspFullSource 0)) :=
  contDiff_thetaCuspFullSource.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- The coalescing determinant has a strictly positive exact quadratic coefficient. -/
theorem determinant_quotient_limit :
    Tendsto (fun z => ThetaSturm.determinant 0 z/z^2) (𝓝[>] 0)
      (𝓝 (thetaTailFirstMomentKernel 0 0*centerEntry)) := by
  have h := (center_diagonal_quotient_limit.const_mul (thetaTailFirstMomentKernel 0 0)).sub
    (center_row_quotient_limit.mul (center_row_limit.add_const (thetaTailFirstMomentKernel 0 0)))
  convert! h using 1
  · ext z
    dsimp only [ThetaSturm.determinant]
    ring
  · congr 1
    dsimp only [centerEntry]
    ring

private theorem right_numerator_limit :
    Tendsto (fun z =>
      (thetaTailFirstMomentKernel 0 0*thetaCuspFullSource z-
        thetaTailFirstMomentKernel 0 z*thetaCuspFullSource 0)/z^2) (𝓝[>] 0)
      (𝓝 (thetaTailFirstMomentKernel 0 0*(deriv (deriv thetaCuspFullSource) 0/2)+
        thetaCuspFullSource 0*derivativeMass)) := by
  have h := (center_source_quotient_limit.const_mul (thetaTailFirstMomentKernel 0 0)).sub
    (center_row_quotient_limit.const_mul (thetaCuspFullSource 0))
  convert! h using 1
  · ext z
    ring
  · congr 1
    ring

/-- The actual right inverse coefficient has a finite coalescing limit. -/
theorem representerRight_limit :
    Tendsto (ThetaSturm.representerRight 0) (𝓝[>] 0)
      (𝓝 ((thetaTailFirstMomentKernel 0 0*(deriv (deriv thetaCuspFullSource) 0/2)+
        thetaCuspFullSource 0*derivativeMass)/(thetaTailFirstMomentKernel 0 0*centerEntry))) := by
  have h := right_numerator_limit.div determinant_quotient_limit
    (mul_pos kernel_center_pos centerEntry_pos).ne'
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  dsimp only [ThetaSturm.representerRight]
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 (ne_of_gt hz)) _ _

/-- Individual inverse signs are unnecessary: their exact limiting sum is positive. -/
theorem representer_sum_limit :
    Tendsto (fun z => ThetaSturm.representerLeft 0 z+ThetaSturm.representerRight 0 z)
      (𝓝[>] 0) (𝓝 (thetaCuspFullSource 0/thetaTailFirstMomentKernel 0 0)) := by
  have hn := (center_diagonal_quotient_limit.const_mul (thetaCuspFullSource 0)).sub
    ((center_source_limit.add_const (thetaCuspFullSource 0)).mul center_row_quotient_limit)
  have hd := hn.div determinant_quotient_limit (mul_pos kernel_center_pos centerEntry_pos).ne'
  have hl : (thetaCuspFullSource 0*(-thetaCuspFullSource 0^2)-
      (thetaCuspFullSource 0+thetaCuspFullSource 0)*(-derivativeMass))/
      (thetaTailFirstMomentKernel 0 0*centerEntry) =
      thetaCuspFullSource 0/thetaTailFirstMomentKernel 0 0 := by
    field_simp [kernel_center_pos.ne', centerEntry_pos.ne']
    dsimp only [centerEntry]
    ring
  rw [hl] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Pi.div_apply]
  have he :
      thetaCuspFullSource 0*((thetaTailFirstMomentKernel z z-thetaTailFirstMomentKernel 0 0)/z^2)-
        (thetaCuspFullSource z+thetaCuspFullSource 0)*
          ((thetaTailFirstMomentKernel 0 z-thetaTailFirstMomentKernel 0 0)/z^2) =
      (thetaTailFirstMomentKernel z z*thetaCuspFullSource 0-
        thetaTailFirstMomentKernel 0 z*thetaCuspFullSource z+
        (thetaTailFirstMomentKernel 0 0*thetaCuspFullSource z-
          thetaTailFirstMomentKernel 0 z*thetaCuspFullSource 0))/z^2 := by ring
  rw [he, div_div_div_cancel_right₀ (pow_ne_zero 2 (ne_of_gt hz))]
  dsimp only [ThetaSturm.representerLeft, ThetaSturm.representerRight]
  ring

/-- The actual source residual, using the literal inverse-Gram representer. -/
def sourceResidual (z y : ℝ) : ℝ :=
  thetaCuspFullSource y-
    ThetaSturm.representerLeft 0 z*thetaTailFirstMomentKernel 0 y-
    ThetaSturm.representerRight 0 z*thetaTailFirstMomentKernel z y

/-- Coalescence controls the actual source projection without a coefficient-sign premise. -/
theorem sourceResidual_limit (y : ℝ) :
    Tendsto (fun z => sourceResidual z y) (𝓝[>] 0)
      (𝓝 (thetaCuspFullSource y-
        thetaCuspFullSource 0/thetaTailFirstMomentKernel 0 0*thetaTailFirstMomentKernel 0 y)) := by
  have hr : Tendsto (fun z => thetaTailFirstMomentKernel z y) (𝓝[>] 0)
      (𝓝 (thetaTailFirstMomentKernel 0 y)) := by
    have h : Tendsto (thetaTailFirstMomentKernel y) (𝓝[>] 0)
        (𝓝 (thetaTailFirstMomentKernel y 0)) :=
      (continuous_kernel_row y).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have he : thetaTailFirstMomentKernel y = fun z => thetaTailFirstMomentKernel z y :=
      funext (thetaTailFirstMomentKernel_comm y)
    rw [he] at h
    exact h
  have h := ((representer_sum_limit.mul_const (thetaTailFirstMomentKernel 0 y)).add
    (representerRight_limit.mul (hr.sub_const (thetaTailFirstMomentKernel 0 y)))).const_sub
      (thetaCuspFullSource y)
  simp only [sub_self, mul_zero, add_zero] at h
  convert! h using 1
  ext z
  dsimp only [sourceResidual]
  ring

/-- A fixed new node has positive actual source residual for all sufficiently close
positive old nodes. The coordinate residual and global continuation remain separate. -/
theorem eventually_sourceResidual_pos {y : ℝ} (hy : 0 < y) :
    ∀ᶠ z in 𝓝[>] 0, 0 < sourceResidual z y := by
  have hrow := ThetaTailRow.strictAntiOn_normalized_row (x := 0) (le_refl 0)
    (show (0:ℝ) ∈ Ici 0 by simp) hy.le hy
  change thetaTailFirstMomentKernel 0 y/(thetaCuspFullSource 0*thetaCuspFullSource y) <
    thetaTailFirstMomentKernel 0 0/(thetaCuspFullSource 0*thetaCuspFullSource 0) at hrow
  have hc := (div_lt_div_iff₀
    (mul_pos (thetaCuspFullSource_pos_all 0) (thetaCuspFullSource_pos_all y))
    (mul_pos (thetaCuspFullSource_pos_all 0) (thetaCuspFullSource_pos_all 0))).mp hrow
  have hcross : thetaCuspFullSource 0*thetaTailFirstMomentKernel 0 y <
      thetaTailFirstMomentKernel 0 0*thetaCuspFullSource y := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) (thetaCuspFullSource_pos_all 0).le
    nlinarith only [hc,hm]
  have hp : 0 < thetaCuspFullSource y-
      thetaCuspFullSource 0/thetaTailFirstMomentKernel 0 0*thetaTailFirstMomentKernel 0 y := by
    apply sub_pos.mpr
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ kernel_center_pos).mpr (by nlinarith only [hcross])
  exact (sourceResidual_limit y).eventually (isOpen_Ioi.mem_nhds hp)

/-- Differentiation of a half-line Schwartz correlation for higher mixed kernel jets. -/
theorem schwartzCorrelation_hasDerivAt (f g : SchwartzMap ℝ ℝ) (y : ℝ) :
    HasDerivAt (fun y => ∫ t in Ioi 0, f t*g (y+t))
      (∫ t in Ioi 0, f t*deriv (g : ℝ → ℝ) (y+t)) y :=
  correlation_hasDerivAt f g y

theorem schwartzCorrelation_integrable (f g : SchwartzMap ℝ ℝ) (y : ℝ) :
    Integrable (fun t => f t*g (y+t)) := correlation_integrable f g y

/-- The literal mixed row at the center endpoint. -/
def centerMixedRow (y : ℝ) : ℝ := ∫ t in Ioi 0,
  thetaCuspFullSource t*thetaCuspFullSource (y+t)+
    (y+2*t)*deriv thetaCuspFullSource t*thetaCuspFullSource (y+t)

/-- The row is the actual kernel derivative, including at the coalescing node. -/
theorem kernel_center_hasDerivAt (x : ℝ) :
    HasDerivAt (thetaTailFirstMomentKernel x) (centerMixedRow x) 0 := by
  have ha := (correlation_integrable (shiftedSource x) thetaCuspSchwartzReal 0).integrableOn (s := Ioi 0)
  have hb := ((correlation_integrable (shiftedSource x) dsource 0).const_mul x).integrableOn (s := Ioi 0)
  have hc := ((correlation_integrable (weightedSource (shiftedSource x)) dsource 0).const_mul 2).integrableOn (s := Ioi 0)
  have hab : IntegrableOn (fun t => shiftedSource x t*thetaCuspSchwartzReal (0+t)+
      x*(shiftedSource x t*dsource (0+t))) (Ioi 0) := ha.add hb
  have he : rowFirst x 0 = centerMixedRow x := by
    unfold rowFirst correlation centerMixedRow
    simp only [add_zero]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ha hb, ← integral_add hab hc]
    apply integral_congr_ae
    filter_upwards with t
    simp only [weightedSource_apply, shiftedSource_apply, thetaCuspSchwartzReal_apply,
      SchwartzMap.derivCLM_apply, zero_add]
    rw [show (thetaCuspSchwartzReal : ℝ → ℝ) = thetaCuspFullSource from
      funext thetaCuspSchwartzReal_apply]
    ring
  rw [← he]
  exact kernel_hasDerivAt x 0

theorem centerMixedRow_zero : centerMixedRow 0 = 0 := by
  have h : HasDerivAt (thetaTailFirstMomentKernel 0) 0 0 := by
    simpa only [rowFirst_center] using kernel_hasDerivAt 0 0
  exact (kernel_center_hasDerivAt 0).deriv.symm.trans h.deriv

/-- Third-order endpoint quotient retaining the exact first nonzero derivative. -/
theorem third_quotient_limit {f g h : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hh : HasDerivAt h a 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hh0 : h 0 = 0) :
    Tendsto (fun z => f z/z^3) (𝓝[>] 0) (𝓝 (a/6)) := by
  have hq := second_quotient_limit hg hh hh0
  rw [hg0] at hq
  simp only [sub_zero] at hq
  have hq' : Tendsto (fun z => g z/(3*z^2)) (𝓝[>] 0) (𝓝 (a/6)) := by
    convert! hq.div_const 3 using 1
    · ext z
      ring
    · congr 1
      ring
  apply HasDerivAt.lhopital_zero_nhdsGT
    (Filter.Eventually.of_forall hf)
    (Filter.Eventually.of_forall fun z => by
      convert! (hasDerivAt_id z).pow 3 using 1; simp only [id_eq]; ring)
    ?_ ?_ ?_ hq'
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hz))
  · simpa only [hf0] using (hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (tendsto_id : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝[>] 0)).mono_right
      nhdsWithin_le_nhds |>.pow 3

end RHTower.ThetaConfluent
