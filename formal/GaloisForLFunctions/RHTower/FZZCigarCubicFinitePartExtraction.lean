import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningGammaUnit
import GaloisForLFunctions.RHTower.FZZCigarCubicScreeningCutoff

/-!
# Original cubic cutoff finite part and its exact value

The complete fifth subtraction is integrated on the original half disk using
an admitted polar product. All finite Taylor terms survive the comparison with
the independently defined circular-cutoff finite part. The original exterior
has local parameter analyticity from its admitted positive exponential moments.

Differentiating both clearing factors and every restored counterterm gives the
exact mixed-jet extraction. The source-derived Gamma jet then fixes the original
whole-plane finite part at `-84*pi`, with both punctures removed independently.

The marked finite-part value, physical normalization, fractional screening
multiplicity, independent phase frame and complete mixed Ward law remain open.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem binomial_succ (β : ℝ) (n : ℕ) :
    fzzScreeningFifthBinomial β (n+1) =
      fzzScreeningFifthBinomial β n * (β/2-n)/(n+1) := by
  unfold fzzScreeningFifthBinomial
  rw [descPochhammer_succ_right]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The complete original fifth polynomial retains three finite radial terms at the cubic pole. -/
theorem fzzScreeningFifthAngularPolynomial_cubic (r : ℝ) :
    fzzScreeningFifthAngularPolynomial (-6) r =
      1+9*r^(2 : ℕ)+36*r^(4 : ℕ)-460*r^(6 : ℕ)-405*r^(8 : ℕ)-21*r^(10 : ℕ) := by
  simp only [fzzScreeningFifthAngularPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
    zero_add,fzzScreeningFifthAngularCoefficient]
  simp only [binomial_succ (-6) 4,binomial_succ (-6) 3,binomial_succ (-6) 2,
    binomial_succ (-6) 1,binomial_succ (-6) 0]
  norm_num [fzzScreeningFifthBinomial]
  ring

private theorem rpow_neg_six (r : ℝ) (hr : 0 ≤ r) : r^(-6:ℝ) = (r^(6 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hr,show (6:ℝ)=((6:ℕ):ℝ) from rfl,Real.rpow_natCast]

private def remainderPolar (p : ℝ × ℝ) : ℝ :=
  p.1*fzzScreeningFifthSubtracted (-6) (-6) (circleMap 0 p.1 p.2)

private theorem remainder_polar_integrable :
    IntegrableOn remainderPolar (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi) := by
  obtain ⟨C,hC0,hC⟩ := fzzScreeningFifthTaylor_uniform_remainder (-6)
  have hr : IntegrableOn (fun r : ℝ => r) (Ioo 0 (1/2)) :=
    (continuous_id.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hi := hr.mul_prod (integrable_const (1:ℝ) :
    Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ioo (-Real.pi) Real.pi)))
  simp only [mul_one] at hi
  rw [Measure.volume_eq_prod]
  change Integrable remainderPolar ((volume.prod volume).restrict
    (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi))
  rw [← Measure.prod_restrict]
  apply (hi.const_mul C).mono' (by
    unfold remainderPolar fzzScreeningFifthSubtracted fzzScreeningFifthTaylor circleMap
    fun_prop)
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le (by
    unfold remainderPolar fzzScreeningFifthSubtracted fzzScreeningFifthTaylor circleMap
    fun_prop) (by fun_prop))]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero,abs_of_pos hr.1]
  have hb : circleMap 0 r θ ∈ closedBall (0:ℂ) (1/2) := by
    rw [mem_closedBall_zero_iff,hn]
    exact hr.2.le
  have h := hC (-6) (by norm_num) _ hb
  rw [hn] at h
  have hsub : ‖fzzScreeningFifthSubtracted (-6) (-6) (circleMap 0 r θ)‖ ≤ C := by
    rw [fzzScreeningFifthSubtracted,norm_mul,hn,
      Real.norm_of_nonneg (Real.rpow_nonneg hr.1.le _),rpow_neg_six r hr.1.le]
    calc
      (r^(6 : ℕ))⁻¹*‖‖circleMap 0 r θ-1‖^(-6:ℝ)-fzzScreeningFifthTaylor (-6) (circleMap 0 r θ)‖
          ≤ (r^(6 : ℕ))⁻¹*(C*r^(6 : ℕ)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg hr.1.le _))
      _ = C := by field_simp [hr.1.ne']
  change ‖r*fzzScreeningFifthSubtracted (-6) (-6) (circleMap 0 r θ)‖ ≤ C*r
  rw [norm_mul,Real.norm_of_nonneg hr.1.le]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsub hr.1.le

private theorem remainder_disk_polar :
    (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted (-6) (-6) z) =
      ∫ p : ℝ × ℝ in Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi,remainderPolar p := by
  let B := ball (0:ℂ) (1/2)
  have hB : MeasurableSet B := measurableSet_ball
  have h := Complex.integral_comp_polarCoord_symm
    (B.indicator (fzzScreeningFifthSubtracted (-6) (-6)))
  rw [integral_indicator hB] at h
  rw [← h,polarCoord_target]
  have he : ∀ p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • B.indicator (fzzScreeningFifthSubtracted (-6) (-6)) (Complex.polarCoord.symm p) =
      (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi).indicator remainderPolar p := by
    rintro ⟨r,θ⟩ ⟨hr,hθ⟩
    change 0 < r at hr
    have hs : Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by
      simp [Complex.polarCoord_symm_apply,circleMap,Complex.exp_mul_I]
    have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero,abs_of_pos hr]
    have hm : circleMap 0 r θ ∈ B ↔ r ∈ Ioo 0 (1/2) := by
      simp only [B,mem_ball_zero_iff,hn,mem_Ioo,hr,true_and]
    rw [hs]
    by_cases hx : r ∈ Ioo 0 (1/2)
    · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem
        (show (r,θ) ∈ Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi from ⟨hx,hθ⟩),smul_eq_mul]
      rfl
    · rw [indicator_of_notMem (mt hm.mp hx),indicator_of_notMem (fun hh => hx hh.1),smul_zero]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) he,
    setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have hs : (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ∩
      (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi) = Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi :=
    inter_eq_self_of_subset_right (Set.prod_mono (fun _ hr => hr.1) subset_rfl)
  rw [hs]

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
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,remainderPolar (r,θ)) =
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
  simp only [remainderPolar,fzzScreeningFifthSubtracted,norm_circleMap_zero,abs_of_pos hr]
  have he (θ : ℝ) : ‖circleMap 0 r θ-1‖^(-6:ℝ) = (‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹ := by
    rw [rpow_neg_six _ (norm_nonneg _),norm_sub_rev]
  simp_rw [he]
  rw [integral_const_mul,integral_const_mul,integral_sub hi ht,kernel_angle_integral,
    taylor_angle_integral,fzzScreeningFifthAngularPolynomial_cubic,
    angular_remainder r hr (by linarith),rpow_neg_six r hr.le]
  field_simp [hr.ne']
  ring

private theorem remainder_disk_angular :
    (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted (-6) (-6) z) =
      2*Real.pi*(∫ r : ℝ in Ioo 0 (1/2),
        r*fzzScreeningCubicAngularRemainder r+460*r+405*r^(3 : ℕ)+21*r^(5 : ℕ)) := by
  rw [remainder_disk_polar,Measure.volume_eq_prod,setIntegral_prod _ (by
    rw [← Measure.volume_eq_prod]
    exact remainder_polar_integrable)]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  exact remainder_angle_integral r hr.1 hr.2

private def finiteTail (r : ℝ) := 460*r+405*r^(3 : ℕ)+21*r^(5 : ℕ)
private theorem finiteTail_integral : (∫ r : ℝ in (0:ℝ)..(1/2),finiteTail r) = 8177/128 := by
  let P := fun r : ℝ => 230*r^(2 : ℕ)+405*r^(4 : ℕ)/4+7*r^(6 : ℕ)/2
  have hd (r : ℝ) : HasDerivAt P (finiteTail r) r := by
    have h := ((((hasDerivAt_id r).pow 2).const_mul 230).add
      ((((hasDerivAt_id r).pow 4).const_mul 405).div_const 4)).add
      ((((hasDerivAt_id r).pow 6).const_mul 7).div_const 2)
    exact h.congr_deriv (by dsimp [finiteTail]; ring)
  have hi : IntervalIntegrable finiteTail volume (0:ℝ) (1/2) := by
    apply Continuous.intervalIntegrable
    unfold finiteTail
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  norm_num [P]

private theorem radial_remainder_integrable :
    IntervalIntegrable (fun r : ℝ => r*fzzScreeningCubicAngularRemainder r) volume 0 (1/2) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  apply continuousOn_id.mul
  unfold fzzScreeningCubicAngularRemainder
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro r hr
  apply pow_ne_zero
  nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (show 0 ≤ 1/2+r by linarith [hr.1])]

/-- Exact comparison with the original circular-cutoff finite part retains every finite Taylor term. -/
theorem fzzScreeningCubicLocalFinitePart_eq_fifthRemainder :
    fzzScreeningCubicLocalFinitePart =
      (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted (-6) (-6) z)-
        10993*Real.pi/64+72*Real.pi*Real.log (1/2) := by
  have h := remainder_disk_angular
  have hp : IntervalIntegrable finiteTail volume (0:ℝ) (1/2) := by
    apply Continuous.intervalIntegrable
    unfold finiteTail
    fun_prop
  have he (r : ℝ) : r*fzzScreeningCubicAngularRemainder r+460*r+405*r^(3 : ℕ)+21*r^(5 : ℕ) =
      r*fzzScreeningCubicAngularRemainder r+finiteTail r := by unfold finiteTail; ring
  simp_rw [he] at h
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
    intervalIntegral.integral_add radial_remainder_integrable hp,finiteTail_integral] at h
  rw [h,fzzScreeningCubicLocalFinitePart]
  norm_num [fzzScreeningCubicCollisionPrimitive]
  ring

/-- Both original punctures and the actual exterior retain the same finite-part comparison. -/
theorem fzzScreeningCubicPlaneFinitePart_eq_fifthRemainders :
    fzzScreeningCubicPlaneFinitePart =
      2*(∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted (-6) (-6) z)+
      (∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel (-6) (-6) z)-
        10993*Real.pi/32+144*Real.pi*Real.log (1/2) := by
  rw [fzzScreeningCubicPlaneFinitePart,fzzScreeningCubicLocalFinitePart_eq_fifthRemainder]
  ring


private def exteriorWeight (α β : ℝ) : Measure ℂ :=
  (volume.restrict fzzScreeningPlaneExterior).withDensity
    (fun z => ENNReal.ofReal (fzzScreeningPlaneKernel α β z))

private theorem kernel_nonnegative (α β : ℝ) (z : ℂ) :
    0 ≤ fzzScreeningPlaneKernel α β z :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)

private theorem exterior_admission (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior := by
  have h := fzzScreeningPlaneExterior_integrable α (Real.log (-2-α-β))
  rw [Real.exp_log (by linarith : 0 < -2-α-β)] at h
  simpa only [show -2-α-(-2-α-β)=β by ring] using h

private theorem plane_kernel_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningPlaneKernel (α+δ) β z := by
  have hn := norm_pos_iff.mpr hz
  rw [show Real.exp (δ*Real.log ‖z‖)=‖z‖^δ by rw [Real.rpow_def_of_pos hn,mul_comm]]
  unfold fzzScreeningPlaneKernel
  rw [Real.rpow_add hn]
  ring

private theorem exterior_mgf (α β δ : ℝ) :
    ProbabilityTheory.mgf (fun z : ℂ => Real.log ‖z‖) (exteriorWeight α β) δ =
      ∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel (α+δ) β z := by
  rw [ProbabilityTheory.mgf,exteriorWeight,integral_withDensity_eq_integral_toReal_smul
    (by unfold fzzScreeningPlaneKernel; fun_prop)
    (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (kernel_nonnegative α β _),smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℂ))] with z hz
  exact plane_kernel_shift α β δ hz

private theorem exterior_analytic (α β : ℝ) (hs : α+β < -2) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel s β z) α := by
  have hmem : (0:ℝ) ∈ interior (ProbabilityTheory.integrableExpSet
      (fun z : ℂ => Real.log ‖z‖) (exteriorWeight α β)) := by
    apply mem_interior_iff_mem_nhds.mpr
    have hn : ∀ᶠ δ : ℝ in 𝓝 0,(α+δ)+β < -2 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hs)
    filter_upwards [hn] with δ hδ
    change Integrable (fun z : ℂ => Real.exp (δ*Real.log ‖z‖)) (exteriorWeight α β)
    rw [exteriorWeight,integrable_withDensity_iff_integrable_smul'
      (by unfold fzzScreeningPlaneKernel; fun_prop)
      (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (kernel_nonnegative α β _),smul_eq_mul]
    apply (exterior_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℂ))] with z hz
    exact (plane_kernel_shift α β δ hz).symm
  have h := (ProbabilityTheory.analyticAt_mgf hmem).comp_sub α
  simpa only [zero_add,exterior_mgf,show ∀ s : ℝ,α+(s-α)=s by intro s; ring] using h

private theorem exterior_reflection (α β : ℝ) :
    (∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel α β z) =
      ∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel β α z := by
  have hp : (fun z : ℂ => 1-z) ⁻¹' fzzScreeningPlaneExterior = fzzScreeningPlaneExterior := by
    ext z
    simp only [fzzScreeningPlaneExterior,mem_preimage,mem_compl_iff,mem_union,
      mem_ball,dist_eq_norm,sub_zero,sub_sub_cancel_left,norm_neg,norm_sub_rev (1:ℂ) z,or_comm]
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1:ℂ)).measurableEmbedding (fzzScreeningPlaneKernel α β)
      fzzScreeningPlaneExterior
  rw [hp] at h
  simpa only [fzzScreeningPlaneKernel_reflection] using h.symm

private theorem fifth_singular_analytic (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted s β z) α := by
  have h := fzzScreeningFifthSubtracted_singular_analytic (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  rw [show -8+(α+8)=α by ring] at h
  have ht := h.comp_sub α
  simpa only [zero_add,show ∀ s : ℝ,α+(s-α)=s by intro s; ring] using ht

private theorem fifth_regular_analytic (α β : ℝ) (ha : -8 < α) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted α s z) β := by
  have h := fzzScreeningFifthSubtracted_regular_analytic (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  simpa only [show -8+(α+8)=α by ring] using h

private def originalRegularPart (α β : ℝ) : ℝ :=
  (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted α β z)+
  (∫ z : ℂ in ball 0 (1/2),fzzScreeningFifthSubtracted β α z)+
  (∫ z : ℂ in fzzScreeningPlaneExterior,fzzScreeningPlaneKernel α β z)

private theorem regularPart_symm (α β : ℝ) : originalRegularPart α β = originalRegularPart β α := by
  unfold originalRegularPart
  rw [exterior_reflection α β]
  ring
private theorem regularPart_analytic (α β : ℝ) (ha : -8 < α) (hb : -8 < β) (hs : α+β < -2) :
    AnalyticAt ℝ (fun s => originalRegularPart s β) α :=
  ((fifth_singular_analytic α β ha).add (fifth_regular_analytic β α hb)).add
    (exterior_analytic α β hs)
private theorem regularPart_analytic_right (α β : ℝ) (ha : -8 < α) (hb : -8 < β) (hs : α+β < -2) :
    AnalyticAt ℝ (originalRegularPart α) β := by
  apply (regularPart_analytic β α hb ha (by linarith)).congr
  filter_upwards with s
  exact regularPart_symm s α

private theorem factor_deriv : HasDerivAt fzzScreeningHigherPoleFactor 8 (-6) := by
  have h := (((hasDerivAt_id (-6:ℝ)).add_const 2).mul
    ((hasDerivAt_id (-6:ℝ)).add_const 4)).mul ((hasDerivAt_id (-6:ℝ)).add_const 6)
  exact h.congr_deriv (by norm_num)
private theorem factor_zero : fzzScreeningHigherPoleFactor (-6) = 0 := by
  norm_num [fzzScreeningHigherPoleFactor]
private theorem half_power_deriv (α c : ℝ) :
    HasDerivAt (fun s : ℝ => (1/2:ℝ)^(s+c))
      (Real.log (1/2)*(1/2:ℝ)^(α+c)) α := by
  simpa only [mul_one,id_eq] using HasDerivAt.const_rpow (by norm_num : (0:ℝ)<1/2)
    ((hasDerivAt_id α).add_const c)

private def radialSlope : ℕ → ℝ
  | 0 => -32
  | 1 => -16
  | 2 => -6+8*Real.log (1/2)
  | n+3 => 8*(1/2:ℝ)^(2*((n+3:ℕ):ℝ)-4)/(2*((n+3:ℕ):ℝ)-4)

private theorem radial_deriv (k : ℕ) :
    HasDerivAt (fun α => fzzScreeningHigherClearedRadial α k) (radialSlope k) (-6) := by
  rcases k with _ | (_ | (_ | n))
  · have h := ((((hasDerivAt_id (-6:ℝ)).add_const 4).mul
      ((hasDerivAt_id (-6:ℝ)).add_const 6)).mul (half_power_deriv (-6) 2))
    exact h.congr_deriv (by norm_num [radialSlope,Real.rpow_neg])
  · have h := ((((hasDerivAt_id (-6:ℝ)).add_const 2).mul
      ((hasDerivAt_id (-6:ℝ)).add_const 6)).mul (half_power_deriv (-6) 4))
    exact h.congr_deriv (by norm_num [radialSlope,Real.rpow_neg])
  · have h := ((((hasDerivAt_id (-6:ℝ)).add_const 2).mul
      ((hasDerivAt_id (-6:ℝ)).add_const 4)).mul (half_power_deriv (-6) 6))
    exact h.congr_deriv (by norm_num [radialSlope])
  · have hn : -6+2*((n+3:ℕ):ℝ)+2 ≠ 0 := by
      push_cast
      linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]
    have h := (factor_deriv.fun_mul (half_power_deriv (-6) (2*((n+3:ℕ):ℝ)+2))).fun_div
      ((hasDerivAt_id (-6:ℝ)).add_const (2*((n+3:ℕ):ℝ)+2))
      (by simpa only [add_assoc,id_eq] using hn)
    have he (α : ℝ) : α+(2*((n+3:ℕ):ℝ)+2)=α+2*((n+3:ℕ):ℝ)+2 := by ring
    simp only [he,id_eq,factor_zero,zero_mul,sub_zero,mul_one,add_zero] at h
    change HasDerivAt (fun α : ℝ => fzzScreeningHigherPoleFactor α *
      (1/2:ℝ)^(α+2*((n+3:ℕ):ℝ)+2)/(α+2*((n+3:ℕ):ℝ)+2))
      (8*(1/2:ℝ)^(2*((n+3:ℕ):ℝ)-4)/(2*((n+3:ℕ):ℝ)-4)) (-6)
    exact h.congr_deriv (by
      rw [show -6+2*((n+3:ℕ):ℝ)+2=2*((n+3:ℕ):ℝ)-4 by ring]
      field_simp [show 2*((n+3:ℕ):ℝ)-4 ≠ 0 by
        push_cast
        linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]])

private def countertermSlope (β : ℝ) : ℝ :=
  2*Real.pi*∑ k ∈ Finset.range 6,fzzScreeningFifthAngularCoefficient β k*radialSlope k

private theorem counterterm_deriv (β : ℝ) :
    HasDerivAt (fun α => fzzScreeningHigherClearedCounterterm α β) (countertermSlope β) (-6) := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro k hk
  exact (radial_deriv k).const_mul (fzzScreeningFifthAngularCoefficient β k)

private theorem countertermSlope_analytic (β : ℝ) : AnalyticAt ℝ countertermSlope β := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (fzzScreeningFifthAngularCoefficient_analytic β k).mul analyticAt_const

private theorem counterterm_analytic_right (α β : ℝ) :
    AnalyticAt ℝ (fun s => fzzScreeningHigherClearedCounterterm α s) β := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (fzzScreeningFifthAngularCoefficient_analytic β k).mul analyticAt_const

private theorem countertermSlope_cubic :
    countertermSlope (-6) = -14449*Real.pi/8+576*Real.pi*Real.log (1/2) := by
  simp only [countertermSlope,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    fzzScreeningFifthAngularCoefficient,radialSlope]
  simp only [binomial_succ (-6) 4,binomial_succ (-6) 3,binomial_succ (-6) 2,
    binomial_succ (-6) 1,binomial_succ (-6) 0]
  norm_num [fzzScreeningFifthBinomial]
  ring

private theorem source_right_deriv (α : ℝ) (ha : α ∈ Ioo (-7) (-5)) :
    deriv (fun β => fzzScreeningHigherClearedSource α β) (-6) =
      8*fzzScreeningHigherPoleFactor α*originalRegularPart α (-6)+
      8*fzzScreeningHigherClearedCounterterm α (-6)+fzzScreeningHigherPoleFactor α*countertermSlope α := by
  have hr := (regularPart_analytic_right α (-6) (by linarith [ha.1]) (by norm_num)
    (by linarith [ha.2])).differentiableAt.hasDerivAt
  have h := (((factor_deriv.const_mul (fzzScreeningHigherPoleFactor α)).fun_mul hr).fun_add
    (factor_deriv.fun_mul (counterterm_analytic_right α (-6)).differentiableAt.hasDerivAt)).fun_add
    ((counterterm_deriv α).const_mul (fzzScreeningHigherPoleFactor α))
  change deriv (fun β =>
    fzzScreeningHigherPoleFactor α*fzzScreeningHigherPoleFactor β*originalRegularPart α β+
    fzzScreeningHigherPoleFactor β*fzzScreeningHigherClearedCounterterm α β+
    fzzScreeningHigherPoleFactor α*fzzScreeningHigherClearedCounterterm β α) (-6) = _
  rw [h.deriv]
  simp only [factor_zero,mul_zero,zero_mul,add_zero]
  ring

/-- The exact clearing-factor derivative retains both original remainders and all six counterterms. -/
theorem fzzScreeningHigherClearedSource_cubic_second_extraction :
    deriv (fun a => deriv (fun b => fzzScreeningHigherClearedSource (-6+a) (-6+b)) 0) 0 =
      64*fzzScreeningCubicPlaneFinitePart-6912*Real.pi := by
  simp_rw [deriv_comp_const_add,add_zero]
  rw [deriv_comp_const_add (fun α => deriv (fzzScreeningHigherClearedSource α) (-6)) (-6) 0,add_zero]
  change deriv (fun α => deriv (fun β => fzzScreeningHigherClearedSource α β) (-6)) (-6) = _
  have he : (fun α => deriv (fun β => fzzScreeningHigherClearedSource α β) (-6)) =ᶠ[𝓝 (-6)]
      fun α => 8*fzzScreeningHigherPoleFactor α*originalRegularPart α (-6)+
        8*fzzScreeningHigherClearedCounterterm α (-6)+fzzScreeningHigherPoleFactor α*countertermSlope α := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (-6:ℝ) ∈ Ioo (-7) (-5))] with α hα
    exact source_right_deriv α hα
  rw [he.deriv_eq]
  have hr := (regularPart_analytic (-6) (-6) (by norm_num) (by norm_num) (by norm_num)).differentiableAt.hasDerivAt
  have h := (((factor_deriv.const_mul 8).fun_mul hr).fun_add
    ((counterterm_deriv (-6)).const_mul 8)).fun_add
    (factor_deriv.fun_mul (countertermSlope_analytic (-6)).differentiableAt.hasDerivAt)
  rw [h.deriv]
  simp only [factor_zero,zero_mul,mul_zero,add_zero,countertermSlope_cubic]
  rw [fzzScreeningCubicPlaneFinitePart_eq_fifthRemainders]
  unfold originalRegularPart
  ring

/-- The value follows from the admitted original cutoff and the source-derived mixed jet. -/
theorem fzzScreeningCubicPlaneFinitePart_value :
    fzzScreeningCubicPlaneFinitePart = -84*Real.pi := by
  have h := fzzScreeningHigherClearedSource_cubic_second_extraction
  rw [fzzScreeningHigherClearedSource_cubic_second_value] at h
  linarith

/-- The actual original plane cutoff converges to the derived value with both punctures removed independently. -/
theorem fzzScreeningCubicPlane_independent_cutoff_value :
    Tendsto (fun P : ℝ × ℝ => fzzScreeningPlaneCutoff (-6) (-6) P.1 P.2+
      2*Real.pi*fzzScreeningCubicCollisionPrimitive (Real.exp (-P.1))+
      2*Real.pi*fzzScreeningCubicCollisionPrimitive (Real.exp (-P.2))) (atTop ×ˢ atTop)
      (𝓝 (-84*Real.pi)) := by
  simpa only [fzzScreeningCubicPlaneFinitePart_value] using
    fzzScreeningCubicPlane_independent_cutoff_limit

end GaloisForLFunctions.RHTower
