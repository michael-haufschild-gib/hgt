import GaloisForLFunctions.RHTower.ThetaTailConfluentCoordinatePort
import GaloisForLFunctions.RHTower.ThetaConfluentCoordinateEnergy

/-! The proved center energy produces an actual chamber with both Schur ports positive. -/

noncomputable section
open MeasureTheory Filter Topology Set
namespace RHTower.ThetaCoordinate
open ThetaConfluent

local notation "k" => thetaCuspFullSource
local notation "k₁" => deriv thetaCuspFullSource
local notation "k₂" => deriv (deriv thetaCuspFullSource)
local notation "k₃" => deriv (deriv (deriv thetaCuspFullSource))
local notation "q" => thetaCuspLogCurvature 0
private abbrev s := thetaCuspSchwartzReal
private abbrev d := SchwartzMap.derivCLM ℝ ℝ s
private abbrev dd := SchwartzMap.derivCLM ℝ ℝ d
private abbrev ddd := SchwartzMap.derivCLM ℝ ℝ dd

private def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) : weighted f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private def corr (f g : SchwartzMap ℝ ℝ) (y : ℝ) : ℝ := ∫ t in Ioi 0, f t*g (y+t)

private theorem corr_hasDerivAt (f g : SchwartzMap ℝ ℝ) (y : ℝ) :
    HasDerivAt (corr f g) (corr f (SchwartzMap.derivCLM ℝ ℝ g) y) y :=
  schwartzCorrelation_hasDerivAt f g y

private theorem product_integrable (f g : SchwartzMap ℝ ℝ) :
    Integrable (fun t : ℝ => f t*g t) :=
  (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g).integrable

private theorem corr_comm (f g : SchwartzMap ℝ ℝ) : corr f g 0 = corr g f 0 := by
  unfold corr
  simp only [zero_add, mul_comm]

private theorem corr_parts (f g : SchwartzMap ℝ ℝ) :
    corr f (SchwartzMap.derivCLM ℝ ℝ g) 0 =
      -f 0*g 0-corr (SchwartzMap.derivCLM ℝ ℝ f) g 0 := by
  let df := SchwartzMap.derivCLM ℝ ℝ f
  let dg := SchwartzMap.derivCLM ℝ ℝ g
  have hi : Integrable (fun t => df t*g t+f t*dg t) :=
    (product_integrable df g).add (product_integrable f dg)
  have hd (t : ℝ) : HasDerivAt (fun t => f t*g t) (df t*g t+f t*dg t) t :=
    (f.hasDerivAt t).mul (g.hasDerivAt t)
  have hl : Tendsto (fun t : ℝ => f t*g t) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (f.tendsto_cocompact.mono_left atTop_le_cocompact).mul
        (g.tendsto_cocompact.mono_left atTop_le_cocompact)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun t _ => hd t) hi.integrableOn hl
  rw [integral_add (product_integrable df g).integrableOn (product_integrable f dg).integrableOn] at h
  unfold corr
  simp only [zero_add]
  dsimp only [df, dg] at h
  linarith only [h]

private theorem weighted_diagonal (f : SchwartzMap ℝ ℝ) :
    corr f f 0+2*corr (weighted f) (SchwartzMap.derivCLM ℝ ℝ f) 0 = 0 := by
  let df := SchwartzMap.derivCLM ℝ ℝ f
  have hi1 : Integrable (fun t => f t*f t) := product_integrable f f
  have hi2 : Integrable (fun t => 2*(t*f t*df t)) := by
    simpa only [weighted_apply] using (product_integrable (weighted f) df).const_mul 2
  have hi : Integrable (fun t => f t*f t+2*(t*f t*df t)) := hi1.add hi2
  have hd (t : ℝ) : HasDerivAt (fun t => t*f t*f t)
      (f t*f t+2*(t*f t*df t)) t := by
    convert! ((hasDerivAt_id t).mul (f.hasDerivAt t)).mul (f.hasDerivAt t) using 1
    simp only [df, SchwartzMap.derivCLM_apply, Pi.mul_apply, id_eq]
    ring
  have hl : Tendsto (fun t : ℝ => t*f t*f t) atTop (𝓝 0) := by
    simpa only [weighted_apply, mul_zero] using
      ((weighted f).tendsto_cocompact.mono_left atTop_le_cocompact).mul
        (f.tendsto_cocompact.mono_left atTop_le_cocompact)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun t _ => hd t) hi.integrableOn hl
  simp only [zero_mul, sub_zero] at h
  unfold corr
  simp only [zero_add, weighted_apply]
  rw [← integral_const_mul, ← integral_add hi1.integrableOn hi2.integrableOn]
  exact h

private theorem d_zero : d 0 = 0 := by
  change k₁ 0 = 0
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) ⟨0,rfl⟩

private theorem corr_s_d : corr s d 0 = -k 0^2/2 := by
  change (∫ t in Ioi 0, k t*k₁ (0+t)) = -k 0^2/2
  simp only [zero_add]
  exact ThetaGeometricBoundaryAudit.source_times_derivative_tail 0

private theorem corr_wd_d : corr (weighted d) d 0 = derivativeMass := by
  unfold corr derivativeMass
  simp only [zero_add, weighted_apply]
  change (∫ t in Ioi 0, t*k₁ t*k₁ t) = ∫ t in Ioi 0, t*k₁ t^2
  apply integral_congr_ae
  filter_upwards with t
  ring

private theorem corr_d_dd : corr d dd 0 = 0 := by
  change (∫ t in Ioi 0, k₁ t*k₂ (0+t)) = 0
  simpa only [zero_add] using first_second_integral

private theorem corr_wd_ddd : corr (weighted d) ddd 0 = -secondMass := by
  unfold corr
  simp only [zero_add, weighted_apply]
  exact mixed_third_integral

private theorem mixedRow_eq (y : ℝ) :
    centerMixedRow y = corr s s y+y*corr d s y+2*corr (weighted d) s y := by
  have hi1 := (schwartzCorrelation_integrable s s y).integrableOn (s := Ioi 0)
  have hi2 := ((schwartzCorrelation_integrable d s y).const_mul y).integrableOn (s := Ioi 0)
  have hi3 := ((schwartzCorrelation_integrable (weighted d) s y).const_mul 2).integrableOn (s := Ioi 0)
  have hi12 : IntegrableOn (fun t => s t*s (y+t)+y*(d t*s (y+t))) (Ioi 0) := hi1.add hi2
  unfold centerMixedRow corr
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add hi1 hi2, ← integral_add hi12 hi3]
  apply integral_congr_ae
  filter_upwards with t
  simp only [weighted_apply]
  change k t*k (y+t)+(y+2*t)*k₁ t*k (y+t) =
    k t*k (y+t)+y*(k₁ t*k (y+t))+2*(t*k₁ t*k (y+t))
  ring

private def mixedOne (y : ℝ) : ℝ :=
  corr s d y+corr d s y+y*corr d d y+2*corr (weighted d) d y
private def mixedTwo (y : ℝ) : ℝ :=
  corr s dd y+2*corr d d y+y*corr d dd y+2*corr (weighted d) dd y
private def mixedThree (y : ℝ) : ℝ :=
  corr s ddd y+3*corr d dd y+y*corr d ddd y+2*corr (weighted d) ddd y

private theorem mixedRow_hasDerivAt (y : ℝ) : HasDerivAt centerMixedRow (mixedOne y) y := by
  rw [show centerMixedRow = fun y => corr s s y+y*corr d s y+2*corr (weighted d) s y from funext mixedRow_eq]
  convert! ((corr_hasDerivAt s s y).add
    ((hasDerivAt_id y).mul (corr_hasDerivAt d s y))).add
      ((corr_hasDerivAt (weighted d) s y).const_mul 2) using 1
  simp only [mixedOne, one_mul, id_eq]
  ring

private theorem mixedOne_hasDerivAt (y : ℝ) : HasDerivAt mixedOne (mixedTwo y) y := by
  convert! (((corr_hasDerivAt s d y).add (corr_hasDerivAt d s y)).add
    ((hasDerivAt_id y).mul (corr_hasDerivAt d d y))).add
      ((corr_hasDerivAt (weighted d) d y).const_mul 2) using 1
  simp only [mixedTwo, one_mul, id_eq]
  ring

private theorem mixedTwo_hasDerivAt (y : ℝ) : HasDerivAt mixedTwo (mixedThree y) y := by
  convert! (((corr_hasDerivAt s dd y).add ((corr_hasDerivAt d d y).const_mul 2)).add
    ((hasDerivAt_id y).mul (corr_hasDerivAt d dd y))).add
      ((corr_hasDerivAt (weighted d) dd y).const_mul 2) using 1
  simp only [mixedThree, one_mul, id_eq]
  ring

private theorem mixedOne_zero : mixedOne 0 = centerEntry := by
  simp only [mixedOne, zero_mul, add_zero, corr_comm d s, corr_s_d, corr_wd_d, centerEntry]
  ring

private theorem mixedTwo_zero : mixedTwo 0 = 0 := by
  have h1 := corr_parts s d
  have h2 := weighted_diagonal d
  simp only [d_zero, mul_zero, zero_sub] at h1
  simp only [mixedTwo, zero_mul, add_zero]
  linarith only [h1,h2]

private theorem mixedThree_zero : mixedThree 0 = q*k 0^2-2*secondMass := by
  have h := corr_parts s dd
  have he : dd 0 = -q*k 0 := source_second_center
  change corr s ddd 0 = -k 0*dd 0-corr d dd 0 at h
  rw [he, corr_d_dd] at h
  simp only [mixedThree, zero_mul, add_zero, corr_d_dd, corr_wd_ddd]
  rw [h]
  ring

private def residualOne (y : ℝ) : ℝ := k y+y*k₁ y-k 0*mixedOne y/centerEntry
private def residualTwo (y : ℝ) : ℝ := 2*k₁ y+y*k₂ y-k 0*mixedTwo y/centerEntry

private theorem residual_hasDerivAt (y : ℝ) :
    HasDerivAt confluentCoordinateResidual (residualOne y) y := by
  have hs : HasDerivAt k (k₁ y) y := s.hasDerivAt y
  convert! ((hasDerivAt_id y).mul hs).sub
    (((mixedRow_hasDerivAt y).const_mul (k 0)).div_const centerEntry) using 1
  simp only [residualOne, one_mul, id_eq]

private theorem residualOne_hasDerivAt (y : ℝ) : HasDerivAt residualOne (residualTwo y) y := by
  have hs : HasDerivAt k (k₁ y) y := s.hasDerivAt y
  have hd : HasDerivAt k₁ (k₂ y) y := d.hasDerivAt y
  convert! (hs.add ((hasDerivAt_id y).mul hd)).sub
    (((mixedOne_hasDerivAt y).const_mul (k 0)).div_const centerEntry) using 1
  simp only [residualTwo, one_mul, id_eq]
  ring

private theorem residualTwo_hasDerivAt_zero :
    HasDerivAt residualTwo (2*k 0*coordinateEnergy/centerEntry) 0 := by
  have hd : HasDerivAt k₁ (k₂ 0) 0 := d.hasDerivAt 0
  have hdd : HasDerivAt k₂ (k₃ 0) 0 := dd.hasDerivAt 0
  convert! ((hd.const_mul 2).add ((hasDerivAt_id (0:ℝ)).mul hdd)).sub
    (((mixedTwo_hasDerivAt 0).const_mul (k 0)).div_const centerEntry) using 1
  simp only [one_mul, id_eq, zero_mul, add_zero, mixedThree_zero, source_second_center]
  unfold coordinateEnergy centerEntry
  field_simp
  ring

private theorem residual_zero : confluentCoordinateResidual 0 = 0 := by
  simp only [confluentCoordinateResidual, zero_mul, centerMixedRow_zero, mul_zero, zero_div, sub_zero]

private theorem residualOne_zero : residualOne 0 = 0 := by
  simp only [residualOne, zero_mul, add_zero, mixedOne_zero]
  field_simp [centerEntry_pos.ne']

private theorem residualTwo_zero : residualTwo 0 = 0 := by
  have hd : k₁ 0 = 0 := d_zero
  simp only [residualTwo, hd, mul_zero, zero_mul, add_zero, mixedTwo_zero, zero_div, sub_zero]

/-- The positive center energy is the actual coordinate residual's cubic coefficient. -/
theorem confluentCoordinateResidual_cubic_limit :
    Tendsto (fun y => confluentCoordinateResidual y/y^3) (𝓝[>] 0)
      (𝓝 (k 0*coordinateEnergy/(3*centerEntry))) := by
  have h := third_quotient_limit residual_hasDerivAt residualOne_hasDerivAt
    residualTwo_hasDerivAt_zero residual_zero residualOne_zero residualTwo_zero
  convert! h using 1
  congr 1
  ring

/-- Actual confluent coordinate positivity on a nonempty center neighborhood. -/
theorem eventually_confluentCoordinateResidual_pos :
    ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < confluentCoordinateResidual y := by
  have hc : 0 < k 0*coordinateEnergy/(3*centerEntry) :=
    div_pos (mul_pos (thetaCuspFullSource_pos_all 0) coordinateEnergy_pos)
      (mul_pos (by norm_num) centerEntry_pos)
  have h := (tendsto_order.1 confluentCoordinateResidual_cubic_limit).1 0 hc
  filter_upwards [h,self_mem_nhdsWithin] with y hy hy0
  have hp := mul_pos hy (pow_pos hy0 3)
  have he : (confluentCoordinateResidual y/y^3)*y^3 = confluentCoordinateResidual y := by
    field_simp [(ne_of_gt hy0)]
  rwa [he] at hp

/-- Both literal Schur ports are positive for an actual ordered center chamber. -/
theorem eventually_actual_ports_pos :
    ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ᶠ z : ℝ in 𝓝[>] 0,
      z < y ∧ 0 < sourceResidual z y ∧ 0 < coordinateResidual z y := by
  filter_upwards [eventually_confluentCoordinateResidual_pos,self_mem_nhdsWithin] with y hy hy0
  have hb := (tendsto_order.1 (coordinateResidual_limit y)).1 0 hy
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hz := (tendsto_order.1 hid).2 y hy0
  filter_upwards [hz, eventually_sourceResidual_pos hy0, hb] with z hz ha hb
  exact ⟨hz,ha,hb⟩

end RHTower.ThetaCoordinate
