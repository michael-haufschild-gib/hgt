import GaloisForLFunctions.RHTower.FZZCigarHigherMarkedRemainder

/-!
# Original cubic marked finite-part extraction

Original local L1 admission is transported to the polar product measure by the
nonnegative change-of-variables theorem. Fubini then retains the actual
logarithmic source and every angular term of the differentiated subtraction.
The singular-factor and regular-factor marks have different finite tails and
different collision primitives; both endpoints are evaluated exactly.

Their sum, with the original exterior logarithmic integral retained, identifies
the independently defined original marked plane finite part with the complete
original remainder-source derivative and its finite polynomial in log(1/2).
This does not yet evaluate that value from the cleared mixed Gamma jet.
The second derivatives of the clearing factor and counterterms, fractional
screening continuation, physical normalization and full Ward producer remain
separate obligations. No RH conclusion is asserted.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def originalPolar (f : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1*f (circleMap 0 p.1 p.2)

private theorem original_polar_point (f : ℂ → ℝ) (p : ℝ × ℝ)
    (hp : p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :
    p.1*(ball (0:ℂ) (1/2)).indicator f (Complex.polarCoord.symm p) =
      (Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi).indicator (originalPolar f) p := by
  rcases p with ⟨r,θ⟩
  rcases hp with ⟨hr,hθ⟩
  change 0 < r at hr
  have hs : Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by
    simp [Complex.polarCoord_symm_apply,circleMap,Complex.exp_mul_I]
  have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero,abs_of_pos hr]
  have hm : circleMap 0 r θ ∈ ball (0:ℂ) (1/2) ↔ r ∈ Ioo (0:ℝ) (1/2) := by
    simp only [mem_ball_zero_iff,hn,mem_Ioo,hr,true_and]
  rw [hs]
  by_cases hx : r ∈ Ioo (0:ℝ) (1/2)
  · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem
      (show (r,θ) ∈ Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi from ⟨hx,hθ⟩)]
    rfl
  · rw [indicator_of_notMem (mt hm.mp hx),indicator_of_notMem (fun hh => hx hh.1),mul_zero]

private theorem original_polar_integrable (f : ℂ → ℝ) (hf : Measurable f)
    (hi : IntegrableOn f (ball 0 (1/2))) :
    IntegrableOn (originalPolar f) (Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi) := by
  let g := (ball (0:ℂ) (1/2)).indicator f
  have hgm : Measurable g := hf.indicator measurableSet_ball
  have hgi : Integrable g := hi.integrable_indicator measurableSet_ball
  have hpc : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have ht : IntegrableOn (fun p : ℝ × ℝ => p.1*g (Complex.polarCoord.symm p))
      (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    refine ⟨(measurable_fst.mul (hgm.comp hpc)).aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have he : (∫⁻ p : ℝ × ℝ in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ‖p.1*g (Complex.polarCoord.symm p)‖ₑ) =
        ∫⁻ z : ℂ, ‖g z‖ₑ := by
      calc
        _ = ∫⁻ p : ℝ × ℝ in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 • ‖g (Complex.polarCoord.symm p)‖ₑ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
          rw [← ofReal_norm,norm_mul,Real.norm_of_nonneg hp.1.le,
            ENNReal.ofReal_mul hp.1.le,ofReal_norm,smul_eq_mul]
        _ = _ := Complex.lintegral_comp_polarCoord_symm (fun z => ‖g z‖ₑ)
    rw [he]
    exact hasFiniteIntegral_iff_enorm.mp hgi.hasFiniteIntegral
  have ht' : IntegrableOn
      ((Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi).indicator (originalPolar f))
      (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    apply ht.congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    exact original_polar_point f p hp
  rw [integrableOn_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo)] at ht'
  have hs : (Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi) ∩
      (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) = Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi :=
    inter_eq_self_of_subset_left (Set.prod_mono (fun _ hr => hr.1) subset_rfl)
  rwa [hs] at ht'

private theorem original_disk_angular (f : ℂ → ℝ) (hf : Measurable f)
    (hi : IntegrableOn f (ball 0 (1/2))) :
    (∫ z : ℂ in ball 0 (1/2), f z) =
      ∫ r : ℝ in Ioo (0:ℝ) (1/2), ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, originalPolar f (r,θ) := by
  have h := Complex.integral_comp_polarCoord_symm ((ball (0:ℂ) (1/2)).indicator f)
  rw [integral_indicator measurableSet_ball] at h
  rw [← h,polarCoord_target]
  simp only [smul_eq_mul]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    (fun p hp => original_polar_point f p hp),
    setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have hs : (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ∩
      (Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi) = Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi) Real.pi :=
    inter_eq_self_of_subset_right (Set.prod_mono (fun _ hr => hr.1) subset_rfl)
  rw [hs,Measure.volume_eq_prod,setIntegral_prod _ (by
    rw [← Measure.volume_eq_prod]
    exact original_polar_integrable f hf hi)]

private theorem actual_angle_integral (f : ℂ → ℝ) (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      2*Real.pi*Real.circleAverage f 0 r := by
  have h := Real.circleAverage_eq_integral_add (f := f) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (fun θ : ℝ => f (circleMap 0 r θ)) (-Real.pi),
    zero_add,show 2*Real.pi+-Real.pi=Real.pi by ring,smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo] at h
  rw [h]
  field_simp [Real.pi_ne_zero]

private theorem rpow_neg_six (r : ℝ) (hr : 0 ≤ r) : r^(-6:ℝ) = (r^(6 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hr,show (6:ℝ)=((6:ℕ):ℝ) from rfl,Real.rpow_natCast]

private theorem regular_mark_angle (r : ℝ) (hr : 0 < r) (hR : r < 1/2) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
      originalPolar (fzzScreeningFifthRegularMark (-6) (-6)) (r,θ)) =
      2*Real.pi*(fzzScreeningCubicMarkedRadialRemainder r-
        ((788/3)*r+(1779/8)*r^(3 : ℕ)+(459/40)*r^(5 : ℕ))) := by
  have hc : Continuous (fun θ : ℝ => circleMap 0 r θ) := by unfold circleMap; fun_prop
  have hn : ∀ θ : ℝ, 1-circleMap 0 r θ ≠ 0 := by
    intro θ he
    have hz : circleMap 0 r θ = 1 := (sub_eq_zero.mp he).symm
    have hh : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero,abs_of_pos hr]
    rw [hz,norm_one] at hh
    linarith
  have hn0 θ : ‖1-circleMap 0 r θ‖ ≠ 0 := norm_ne_zero_iff.mpr (hn θ)
  have hcN : Continuous (fun θ : ℝ => ‖1-circleMap 0 r θ‖) := (continuous_const.sub hc).norm
  have hi : IntegrableOn (fun θ : ℝ => Real.log ‖1-circleMap 0 r θ‖*
      (‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) (Ioo (-Real.pi) Real.pi) :=
    ((hcN.log hn0).mul ((hcN.pow 6).inv₀ (fun θ => pow_ne_zero _ (hn0 θ)))).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioo_subset_Icc_self
  have ht : IntegrableOn (fun θ : ℝ => fzzScreeningFifthTaylorMark (-6) (circleMap 0 r θ))
      (Ioo (-Real.pi) Real.pi) := by
    have hh : Continuous (fun θ : ℝ => fzzScreeningFifthTaylorMark (-6) (circleMap 0 r θ)) := by
      unfold fzzScreeningFifthTaylorMark
      fun_prop
    exact hh.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioo_subset_Icc_self
  simp only [originalPolar,fzzScreeningFifthRegularMark,norm_circleMap_zero,abs_of_pos hr]
  have he (θ : ℝ) : Real.log ‖circleMap 0 r θ-1‖*‖circleMap 0 r θ-1‖^(-6:ℝ) =
      Real.log ‖1-circleMap 0 r θ‖*(‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹ := by
    rw [rpow_neg_six _ (norm_nonneg _),norm_sub_rev]
  simp_rw [he]
  rw [integral_const_mul,integral_const_mul,integral_sub hi ht,
    actual_angle_integral (fun z : ℂ => Real.log ‖1-z‖*(‖1-z‖^(6 : ℕ))⁻¹),
    actual_angle_integral (fzzScreeningFifthTaylorMark (-6)),
    fzzScreeningFifthTaylorMark_cubic_circleAverage,rpow_neg_six r hr.le]
  rw [← mul_assoc]
  change r*(r^(6 : ℕ))⁻¹*(2*Real.pi*fzzScreeningHigherMarkedAngular 3 r-
    2*Real.pi*(-3*r^(2 : ℕ)-21*r^(4 : ℕ)+(788/3)*r^(6 : ℕ)+(1779/8)*r^(8 : ℕ)+(459/40)*r^(10 : ℕ))) = _
  unfold fzzScreeningCubicMarkedRadialRemainder
  field_simp [hr.ne']
  ring

private def markedFiniteTail (r : ℝ) := (788/3)*r+(1779/8)*r^(3 : ℕ)+(459/40)*r^(5 : ℕ)

private theorem markedFiniteTail_integral :
    (∫ r : ℝ in (0:ℝ)..(1/2), markedFiniteTail r) = 558149/15360 := by
  let P : ℝ → ℝ := fun r => (394/3)*r^(2 : ℕ)+(1779/32)*r^(4 : ℕ)+(153/80)*r^(6 : ℕ)
  have hd (r : ℝ) : HasDerivAt P (markedFiniteTail r) r := by
    have h := ((((hasDerivAt_id r).pow 2).const_mul (394/3)).fun_add
      (((hasDerivAt_id r).pow 4).const_mul (1779/32))).fun_add
        (((hasDerivAt_id r).pow 6).const_mul (153/80))
    exact h.congr_deriv (by dsimp [markedFiniteTail]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (show IntervalIntegrable markedFiniteTail volume 0 (1/2) from
      (show Continuous markedFiniteTail by unfold markedFiniteTail; fun_prop).intervalIntegrable _ _)]
  norm_num [P]

private theorem regular_mark_disk_angular :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark (-6) (-6) z) =
      2*Real.pi*(∫ r : ℝ in Ioo (0:ℝ) (1/2),
        fzzScreeningCubicMarkedRadialRemainder r-markedFiniteTail r) := by
  have hi := fzzScreeningFifthRegularMark_integrable (Real.log 2) (-6)
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hi
  norm_num only at hi
  rw [original_disk_angular _ (by unfold fzzScreeningFifthRegularMark fzzScreeningFifthTaylorMark; fun_prop) hi,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  exact regular_mark_angle r hr.1 hr.2

/-- The original regular-factor marked finite part retains the entire finite
Taylor tail and its own collision primitive. -/
theorem fzzScreeningCubicRegularMarkedLocalFinitePart_eq_fifthMark :
    fzzScreeningCubicRegularMarkedLocalFinitePart =
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark (-6) (-6) z)+
        Real.pi*(-42*Real.log (1/2)+650309/7680) := by
  rw [regular_mark_disk_angular]
  have hi : IntegrableOn fzzScreeningCubicMarkedRadialRemainder (Ioo 0 (1/2:ℝ)) :=
    fzzScreeningHigherMarkedAngular_three_subtracted_integrable.mono_set Ioo_subset_Ioc_self
  have ht : IntegrableOn markedFiniteTail (Ioo 0 (1/2:ℝ)) :=
    (show Continuous markedFiniteTail by unfold markedFiniteTail; fun_prop).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioo_subset_Icc_self
  rw [integral_sub hi ht]
  have he : (∫ r : ℝ in Ioo (0:ℝ) (1/2),markedFiniteTail r) = 558149/15360 := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/2)]
    exact markedFiniteTail_integral
  rw [he]
  unfold fzzScreeningCubicRegularMarkedLocalFinitePart
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/2),integral_Ioc_eq_integral_Ioo]
  norm_num [fzzScreeningCubicMarkedCollisionPrimitive]
  ring

private theorem taylor_angle_integral (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,fzzScreeningFifthTaylor (-6) (circleMap 0 r θ)) =
      2*Real.pi*fzzScreeningFifthAngularPolynomial (-6) r := by
  have h := Real.circleAverage_eq_integral_add
    (f := fzzScreeningFifthTaylor (-6)) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => fzzScreeningFifthTaylor (-6) (circleMap 0 r θ)) (-Real.pi),zero_add,
    show 2*Real.pi+-Real.pi=Real.pi by ring,smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo,fzzScreeningFifthTaylor_circleAverage] at h
  rw [h]
  field_simp [Real.pi_ne_zero]

private theorem kernel_angle_integral (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,(‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) =
      2*Real.pi*fzzScreeningHigherAngular 3 r := by
  have h := Real.circleAverage_eq_integral_add
    (f := fun z : ℂ => (‖1-z‖^(6 : ℕ))⁻¹) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => (‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) (-Real.pi),zero_add,
    show 2*Real.pi+-Real.pi=Real.pi by ring,smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo] at h
  change fzzScreeningHigherAngular 3 r = _ at h
  rw [h]
  field_simp [Real.pi_ne_zero]

private theorem angular_remainder (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    fzzScreeningHigherAngular 3 r =
      1+9*r^(2 : ℕ)+36*r^(4 : ℕ)+r^(6 : ℕ)*fzzScreeningCubicAngularRemainder r := by
  have he : fzzScreeningAngularRadius (Real.log ((1-r)/r)) = r := by
    rw [fzzScreeningAngularRadius,Real.exp_log (div_pos (sub_pos.mpr hr1) hr)]
    field_simp [hr.ne']
    ring
  have h := fzzScreeningHigherAngular_three_remainder (Real.log ((1-r)/r))
  rwa [he] at h

private theorem remainder_angle_integral (r : ℝ) (hr : 0 < r) (hrR : r < 1/2) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,originalPolar (fzzScreeningFifthSubtracted (-6) (-6)) (r,θ)) =
      2*Real.pi*(r*fzzScreeningCubicAngularRemainder r+460*r+405*r^(3 : ℕ)+21*r^(5 : ℕ)) := by
  have hc : Continuous (fun θ : ℝ => circleMap 0 r θ) := by unfold circleMap; fun_prop
  have hn : ∀ θ : ℝ,1-circleMap 0 r θ ≠ 0 := by
    intro θ he
    have hz : circleMap 0 r θ = 1 := (sub_eq_zero.mp he).symm
    have hnorm : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero,abs_of_pos hr]
    rw [hz,norm_one] at hnorm
    linarith
  have hi : IntegrableOn (fun θ : ℝ => (‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) (Ioo (-Real.pi) Real.pi) :=
    (((continuous_const.sub hc).norm.pow 6).inv₀ (fun θ => pow_ne_zero _
      (norm_ne_zero_iff.mpr (hn θ)))).continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioo_subset_Icc_self
  have ht : IntegrableOn (fun θ : ℝ => fzzScreeningFifthTaylor (-6) (circleMap 0 r θ))
      (Ioo (-Real.pi) Real.pi) := by
    have hh : Continuous (fun θ : ℝ => fzzScreeningFifthTaylor (-6) (circleMap 0 r θ)) := by
      unfold fzzScreeningFifthTaylor
      fun_prop
    exact hh.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioo_subset_Icc_self
  simp only [originalPolar,fzzScreeningFifthSubtracted,norm_circleMap_zero,abs_of_pos hr]
  have he (θ : ℝ) : ‖circleMap 0 r θ-1‖^(-6:ℝ) = (‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹ := by
    rw [rpow_neg_six _ (norm_nonneg _),norm_sub_rev]
  simp_rw [he]
  rw [integral_const_mul,integral_const_mul,integral_sub hi ht,kernel_angle_integral,
    taylor_angle_integral,fzzScreeningFifthAngularPolynomial_cubic,
    angular_remainder r hr (by linarith),rpow_neg_six r hr.le]
  field_simp [hr.ne']
  ring


private def singularFiniteTail (r : ℝ) :=
  (r*Real.log r)*(460+405*r^(2 : ℕ)+21*r^(4 : ℕ))

private theorem singularFiniteTail_continuous : Continuous singularFiniteTail := by
  exact Real.continuous_mul_log.mul (by fun_prop)

private theorem singularFiniteTail_integral :
    (∫ r : ℝ in (0:ℝ)..(1/2),singularFiniteTail r) =
      (8177/128)*Real.log (1/2)-11651/384 := by
  let P : ℝ → ℝ := fun r =>
    230*r^(2 : ℕ)*Real.log r-115*r^(2 : ℕ)+(405/4)*r^(4 : ℕ)*Real.log r-(405/16)*r^(4 : ℕ)+
      (7/2)*r^(6 : ℕ)*Real.log r-(7/12)*r^(6 : ℕ)
  have hC : Continuous P := by
    have he : P = fun r : ℝ =>
        230*r*(r*Real.log r)-115*r^(2 : ℕ)+(405/4)*r^(3 : ℕ)*(r*Real.log r)-(405/16)*r^(4 : ℕ)+
          (7/2)*r^(5 : ℕ)*(r*Real.log r)-(7/12)*r^(6 : ℕ) := by
      funext r
      dsimp [P]
      ring
    rw [he]
    have hc := Real.continuous_mul_log
    fun_prop
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt P (singularFiniteTail r) r := by
    have hl := Real.hasDerivAt_log hr.ne'
    have h := ((((((((hasDerivAt_id r).pow 2).const_mul 230).fun_mul hl).fun_sub
      (((hasDerivAt_id r).pow 2).const_mul 115)).fun_add
      ((((hasDerivAt_id r).pow 4).const_mul (405/4)).fun_mul hl)).fun_sub
      (((hasDerivAt_id r).pow 4).const_mul (405/16))).fun_add
      ((((hasDerivAt_id r).pow 6).const_mul (7/2)).fun_mul hl)).fun_sub
      (((hasDerivAt_id r).pow 6).const_mul (7/12))
    exact h.congr_deriv (by dsimp [singularFiniteTail]; field_simp [hr.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1/2)
    hC.continuousOn (fun r hr => hd r hr.1) (singularFiniteTail_continuous.intervalIntegrable _ _)]
  norm_num [P]
  ring

private theorem singular_mark_disk_angular :
    (∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningFifthSubtracted (-6) (-6) z) =
      2*Real.pi*(∫ r : ℝ in Ioo (0:ℝ) (1/2),
        (r*Real.log r)*fzzScreeningCubicAngularRemainder r+singularFiniteTail r) := by
  have hi := fzzScreeningFifthSubtracted_singularMark_integrable (Real.log 2) (-6)
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hi
  norm_num only at hi
  rw [original_disk_angular _ (by unfold fzzScreeningFifthSubtracted fzzScreeningFifthTaylor; fun_prop) hi,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have he : (fun θ : ℝ => originalPolar
      (fun z : ℂ => Real.log ‖z‖*fzzScreeningFifthSubtracted (-6) (-6) z) (r,θ)) =
      (fun θ : ℝ => Real.log r *
        originalPolar (fzzScreeningFifthSubtracted (-6) (-6)) (r,θ)) := by
    funext θ
    simp only [originalPolar,norm_circleMap_zero,abs_of_pos hr.1]
    ring
  change (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
    originalPolar (fun z : ℂ => Real.log ‖z‖*fzzScreeningFifthSubtracted (-6) (-6) z) (r,θ)) =
      2*Real.pi*((r*Real.log r)*fzzScreeningCubicAngularRemainder r+singularFiniteTail r)
  rw [he,integral_const_mul,remainder_angle_integral r hr.1 hr.2]
  dsimp [singularFiniteTail]
  ring

private theorem singular_radial_continuousOn :
    ContinuousOn (fun r : ℝ => (r*Real.log r)*fzzScreeningCubicAngularRemainder r)
      (Icc 0 (1/2:ℝ)) := by
  apply Real.continuous_mul_log.continuousOn.mul
  unfold fzzScreeningCubicAngularRemainder
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro r hr
  apply pow_ne_zero
  nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (show 0 ≤ 1/2+r by linarith [hr.1])]

/-- The original singular-factor finite part retains the logarithmic Taylor tail
and the endpoint of its distinct logarithmic collision primitive. -/
theorem fzzScreeningCubicSingularMarkedLocalFinitePart_eq_fifthMark :
    fzzScreeningCubicSingularMarkedLocalFinitePart =
      (∫ z : ℂ in ball 0 (1/2),Real.log ‖z‖*fzzScreeningFifthSubtracted (-6) (-6) z)+
        Real.pi*(36*(Real.log (1/2))^(2 : ℕ)-(10993/64)*Real.log (1/2)+7811/192) := by
  rw [singular_mark_disk_angular]
  have hi : IntegrableOn (fun r : ℝ => (r*Real.log r)*fzzScreeningCubicAngularRemainder r)
      (Ioo (0:ℝ) (1/2)) :=
    (singular_radial_continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have ht : IntegrableOn singularFiniteTail (Ioo (0:ℝ) (1/2)) :=
    (singularFiniteTail_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  rw [integral_add hi ht]
  have he : (∫ r : ℝ in Ioo (0:ℝ) (1/2),singularFiniteTail r) =
      (8177/128)*Real.log (1/2)-11651/384 := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/2)]
    exact singularFiniteTail_integral
  rw [he]
  unfold fzzScreeningCubicSingularMarkedLocalFinitePart
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/2),integral_Ioc_eq_integral_Ioo]
  norm_num [fzzScreeningCubicSingularMarkedCollisionPrimitive]
  ring

theorem fzzScreeningCubicMarkedPlaneFinitePart_eq_fifthMarks :
    fzzScreeningCubicMarkedPlaneFinitePart =
      (∫ z : ℂ in ball 0 (1/2),Real.log ‖z‖*fzzScreeningFifthSubtracted (-6) (-6) z)+
      (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthRegularMark (-6) (-6) z)+
      (∫ z : ℂ in fzzScreeningPlaneExterior,Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)+
      Real.pi*(36*(Real.log (1/2))^(2 : ℕ)-(13681/64)*Real.log (1/2)+962749/7680) := by
  rw [fzzScreeningCubicMarkedPlaneFinitePart,
    fzzScreeningCubicSingularMarkedLocalFinitePart_eq_fifthMark,
    fzzScreeningCubicRegularMarkedLocalFinitePart_eq_fifthMark]
  ring

end GaloisForLFunctions.RHTower
