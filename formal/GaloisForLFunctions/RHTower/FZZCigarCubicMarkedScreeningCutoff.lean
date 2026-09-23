import GaloisForLFunctions.RHTower.FZZCigarHigherMarkedAngular
import GaloisForLFunctions.RHTower.FZZCigarCubicScreeningCutoff
import GaloisForLFunctions.RHTower.FZZCigarMarkedScreeningCutoff

/-!
# Original cubic logarithmic screening cutoff on the plane

The original logarithmic insertion at exponents `(-6,-6)` is integrated over
finite annuli using polar change of variables and compact-product Fubini. The
zero puncture carries the singular-factor mark; reflection transports the second
puncture to the distinct regular-factor mark. Their forced local corrections
therefore differ. The actual exterior is admitted by comparison with two
neighboring original power kernels, using `|log t| <= t + t⁻¹`.

Both ordinary local integrals and the exterior assemble before the two cutoffs
are removed independently. The resulting value retains the two distinct local
finite parts and the original exterior. It is not assigned a Gamma value.

All public statements are unconditional, with domains discharged from real data.
Physical parameter differentiation, higher parameter continuation, complete CFT
normalization, phase-frame identification, mixed Ward vanishing and RH remain
separate obligations.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def cubicPolar (p : ℝ × ℝ) : ℝ :=
  (p.1^(5 : ℕ))⁻¹*(‖1-circleMap 0 p.1 p.2‖^(6 : ℕ))⁻¹

private theorem cubicKernel_circleMap (r θ : ℝ) (hr : 0 < r) :
    r*fzzScreeningPlaneKernel (-6) (-6) (circleMap 0 r θ) = cubicPolar (r,θ) := by
  rw [fzzScreeningPlaneKernel, norm_circleMap_zero, abs_of_pos hr, norm_sub_rev]
  have hp (a : ℝ) (ha : 0 ≤ a) : a^(-6 : ℝ) = (a^(6 : ℕ))⁻¹ := by
    rw [Real.rpow_neg ha, show (6 : ℝ) = ((6 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  rw [hp r hr.le, hp _ (norm_nonneg _)]
  unfold cubicPolar
  dsimp
  field_simp [hr.ne']

private theorem cubicPolar_continuousOn (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn cubicPolar (Icc ε (1/2) ×ˢ Icc (-Real.pi) Real.pi) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hn : ∀ p ∈ Icc ε (1/2) ×ˢ Icc (-Real.pi) Real.pi,
      1-circleMap 0 p.1 p.2 ≠ 0 := by
    intro p hp he
    have hnorm : ‖circleMap 0 p.1 p.2‖ = p.1 := by
      rw [norm_circleMap_zero, abs_of_pos (hε.trans_le hp.1.1)]
    have hz : circleMap 0 p.1 p.2 = 1 := (sub_eq_zero.mp he).symm
    rw [hz, norm_one] at hnorm
    linarith [hp.1.2]
  exact ((continuous_fst.continuousOn.pow 5).inv₀
      (fun p hp => pow_ne_zero _ (hε.trans_le hp.1.1).ne')).mul
    ((((continuous_const.sub hc).norm.continuousOn).pow 6).inv₀
      (fun p hp => pow_ne_zero _ (norm_ne_zero_iff.mpr (hn p hp))))

private theorem cubicPolar_integrable (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn cubicPolar (Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  have hi : IntegrableOn cubicPolar (Icc ε (1/2) ×ˢ Icc (-Real.pi) Real.pi) :=
    (cubicPolar_continuousOn ε hε).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [← Measure.volume_eq_prod]
  exact hi.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)


private def cubicMarkedKernel (b : Bool) (z : ℂ) : ℝ :=
  (if b then Real.log ‖1-z‖ else Real.log ‖z‖)*fzzScreeningPlaneKernel (-6) (-6) z

private def cubicMarkedPolar (b : Bool) (p : ℝ × ℝ) : ℝ :=
  (if b then Real.log ‖1-circleMap 0 p.1 p.2‖ else Real.log p.1)*cubicPolar p

private def cubicMarkedAngular (b : Bool) (r : ℝ) : ℝ :=
  if b then fzzScreeningHigherMarkedAngular 3 r else Real.log r*fzzScreeningHigherAngular 3 r

private theorem cubicMarkedKernel_circleMap (b : Bool) (r θ : ℝ) (hr : 0 < r) :
    r*cubicMarkedKernel b (circleMap 0 r θ) = cubicMarkedPolar b (r,θ) := by
  have h := cubicKernel_circleMap r θ hr
  unfold cubicMarkedKernel cubicMarkedPolar
  dsimp only
  rw [norm_circleMap_zero, abs_of_pos hr]
  linear_combination (if b then Real.log ‖1-circleMap 0 r θ‖ else Real.log r)*h

private theorem cubicMarkedPolar_continuousOn (b : Bool) (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (cubicMarkedPolar b) (Icc ε (1/2) ×ˢ Icc (-Real.pi) Real.pi) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hn : ∀ p ∈ Icc ε (1/2) ×ˢ Icc (-Real.pi) Real.pi,
      1-circleMap 0 p.1 p.2 ≠ 0 := by
    intro p hp he
    have hnorm : ‖circleMap 0 p.1 p.2‖ = p.1 := by
      rw [norm_circleMap_zero, abs_of_pos (hε.trans_le hp.1.1)]
    have hz : circleMap 0 p.1 p.2 = 1 := (sub_eq_zero.mp he).symm
    rw [hz, norm_one] at hnorm
    linarith [hp.1.2]
  cases b
  · exact (continuous_fst.continuousOn.log
      (fun p hp => (hε.trans_le hp.1.1).ne')).mul (cubicPolar_continuousOn ε hε)
  · exact (((continuous_const.sub hc).norm.continuousOn).log
      (fun p hp => norm_ne_zero_iff.mpr (hn p hp))).mul (cubicPolar_continuousOn ε hε)

private theorem cubicMarkedPolar_integrable (b : Bool) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (cubicMarkedPolar b) (Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  have hi : IntegrableOn (cubicMarkedPolar b) (Icc ε (1/2) ×ˢ Icc (-Real.pi) Real.pi) :=
    (cubicMarkedPolar_continuousOn b ε hε).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [← Measure.volume_eq_prod]
  exact hi.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

private theorem cubicMarked_annulus_polar (b : Bool) (ε : ℝ) (hε : 0 < ε) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 ε, cubicMarkedKernel b z) =
      ∫ p : ℝ × ℝ in Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi, cubicMarkedPolar b p := by
  let A : Set ℂ := ball 0 (1/2) \ closedBall 0 ε
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hpolar := Complex.integral_comp_polarCoord_symm
    (A.indicator (cubicMarkedKernel b))
  rw [integral_indicator hA] at hpolar
  rw [← hpolar, polarCoord_target]
  have he : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • A.indicator (cubicMarkedKernel b) (Complex.polarCoord.symm p) =
        (Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi).indicator (cubicMarkedPolar b) p := by
    rintro ⟨r,θ⟩ ⟨hr,hθ⟩
    have hs : Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
    have hn : ‖circleMap 0 r θ‖ = r := by
      rw [norm_circleMap_zero, abs_of_pos hr]
    have hm : circleMap 0 r θ ∈ A ↔ r ∈ Ioo ε (1/2) := by
      simp only [A, Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, hn, not_le,
        mem_Ioo, and_comm]
    rw [hs]
    by_cases hx : r ∈ Ioo ε (1/2)
    · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem
        (show (r,θ) ∈ Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi from ⟨hx,hθ⟩), smul_eq_mul]
      exact cubicMarkedKernel_circleMap b r θ hr
    · rw [indicator_of_notMem (mt hm.mp hx), indicator_of_notMem
        (fun hh => hx hh.1), smul_zero]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) he,
    setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have hs : (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ∩
      (Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi) =
        Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi :=
    inter_eq_self_of_subset_right (Set.prod_mono (fun r hr => hε.trans hr.1) subset_rfl)
  rw [hs]


private theorem cubic_angle_integral (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, (‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) =
      2*Real.pi*fzzScreeningHigherAngular 3 r := by
  have h := Real.circleAverage_eq_integral_add
    (f := fun z : ℂ => (‖1-z‖^(6 : ℕ))⁻¹) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => (‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) (-Real.pi), zero_add,
    show 2*Real.pi+-Real.pi = Real.pi by ring, smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo] at h
  change fzzScreeningHigherAngular 3 r = _ at h
  rw [h]
  field_simp [Real.pi_ne_zero]


private theorem cubic_marked_angle_integral (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
      Real.log ‖1-circleMap 0 r θ‖*(‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) =
      2*Real.pi*fzzScreeningHigherMarkedAngular 3 r := by
  have h := Real.circleAverage_eq_integral_add
    (f := fun z : ℂ => Real.log ‖1-z‖*(‖1-z‖^(6 : ℕ))⁻¹) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => Real.log ‖1-circleMap 0 r θ‖*(‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹)
        (-Real.pi), zero_add,
    show 2*Real.pi+-Real.pi = Real.pi by ring, smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo] at h
  change fzzScreeningHigherMarkedAngular 3 r = _ at h
  rw [h]
  field_simp [Real.pi_ne_zero]

private theorem cubicMarked_polar_angle (b : Bool) (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, cubicMarkedPolar b (r,θ)) =
      2*Real.pi*((r^(5 : ℕ))⁻¹*cubicMarkedAngular b r) := by
  cases b
  · unfold cubicMarkedPolar cubicPolar cubicMarkedAngular
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp_rw [← mul_assoc]
    rw [integral_const_mul, cubic_angle_integral]
    ring
  · have he : (fun θ : ℝ => cubicMarkedPolar true (r,θ)) =
        fun θ : ℝ => (r^(5 : ℕ))⁻¹*(Real.log ‖1-circleMap 0 r θ‖*(‖1-circleMap 0 r θ‖^(6 : ℕ))⁻¹) := by
      funext θ
      unfold cubicMarkedPolar cubicPolar
      dsimp
      ring
    rw [he, integral_const_mul, cubic_marked_angle_integral]
    simp only [cubicMarkedAngular, ↓reduceIte]
    ring

private theorem cubicMarked_annulus_angular (b : Bool) (ε : ℝ) (hε : 0 < ε) (hεR : ε ≤ 1/2) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 ε, cubicMarkedKernel b z) =
      2*Real.pi*(∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*cubicMarkedAngular b r) := by
  rw [cubicMarked_annulus_polar b ε hε, Measure.volume_eq_prod,
    setIntegral_prod _ (cubicMarkedPolar_integrable b ε hε)]
  simp_rw [cubicMarked_polar_angle]
  rw [intervalIntegral.integral_of_le hεR, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]

private theorem cubicMarked_annulus_integrable (b : Bool) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (cubicMarkedKernel b) (ball 0 (1/2) \ closedBall 0 ε) := by
  let K : Set ℂ := closedBall 0 (1/2) \ ball 0 ε
  have hk : IsCompact K := (isCompact_closedBall (0 : ℂ) (1/2)).diff isOpen_ball
  have hn : ∀ z ∈ K, z ≠ 0 ∧ z-1 ≠ 0 := by
    intro z hz
    constructor
    · intro he
      subst z
      exact hz.2 (by simpa using hε)
    · intro he
      have he' := sub_eq_zero.mp he
      subst z
      norm_num [K, mem_closedBall, dist_eq_norm] at hz
  have hc : ContinuousOn (fzzScreeningPlaneKernel (-6) (-6)) K :=
    (continuous_norm.continuousOn.rpow_const
      (fun z hz => Or.inl (norm_ne_zero_iff.mpr (hn z hz).1))).mul
    ((show Continuous (fun z : ℂ => ‖z-1‖) by fun_prop).continuousOn.rpow_const
      (fun z hz => Or.inl (norm_ne_zero_iff.mpr (hn z hz).2)))
  have hm : ContinuousOn (cubicMarkedKernel b) K := by
    cases b
    · exact (continuous_norm.continuousOn.log
        (fun z hz => norm_ne_zero_iff.mpr (hn z hz).1)).mul hc
    · exact ((show Continuous (fun z : ℂ => ‖1-z‖) by fun_prop).continuousOn.log
        (fun z hz => by rw [norm_sub_rev]; exact norm_ne_zero_iff.mpr (hn z hz).2)).mul hc
  apply (hm.integrableOn_compact hk).mono_set
  intro z hz
  exact ⟨ball_subset_closedBall hz.1,fun hh => hz.2 (ball_subset_closedBall hh)⟩

private theorem markedExterior_admission (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior := by
  have h := fzzScreeningPlaneExterior_integrable α (Real.log (-2-α-β))
  rw [Real.exp_log (by linarith : 0 < -2-α-β)] at h
  simpa only [show -2-α-(-2-α-β) = β by ring] using h

private theorem markedExterior_log_bound (t : ℝ) (ht : 0 < t) :
    ‖Real.log t‖ ≤ t+t⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [inv_pos.mpr ht]

/-- Direct admission of the original higher marked exterior by two neighboring power sources. -/
theorem fzzScreeningCubicMarkedExterior_integrable :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)
      fzzScreeningPlaneExterior := by
  have hi := (markedExterior_admission (-5) (-6) (by norm_num)).add
    (markedExterior_admission (-7) (-6) (by norm_num))
  apply hi.mono' (by unfold fzzScreeningPlaneKernel; fun_prop)
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
  have hn := norm_pos_iff.mpr hz
  have hK : 0 ≤ fzzScreeningPlaneKernel (-6) (-6) z := by
    unfold fzzScreeningPlaneKernel
    positivity
  rw [norm_mul, Real.norm_of_nonneg hK]
  have hb := mul_le_mul_of_nonneg_right (markedExterior_log_bound ‖z‖ hn) hK
  apply hb.trans_eq
  dsimp only [Pi.add_apply]
  unfold fzzScreeningPlaneKernel
  have hp : ‖z‖^(-5 : ℝ) = ‖z‖*‖z‖^(-6 : ℝ) := by
    rw [show (-5 : ℝ) = 1+(-6) by ring, Real.rpow_add hn, Real.rpow_one]
  have hm : ‖z‖^(-7 : ℝ) = ‖z‖⁻¹*‖z‖^(-6 : ℝ) := by
    rw [show (-7 : ℝ) = -1+(-6) by ring, Real.rpow_add hn, Real.rpow_neg_one]
  rw [hp,hm]
  ring


/-- The original marked local value where the insertion hits the singular radial factor. -/
def fzzScreeningCubicSingularMarkedLocalFinitePart : ℝ :=
  2*Real.pi*((∫ r : ℝ in (0 : ℝ)..(1/2), (r*Real.log r)*fzzScreeningCubicAngularRemainder r)+
    fzzScreeningCubicSingularMarkedCollisionPrimitive (1/2))

/-- The original marked local value where the insertion hits the regular collision factor. -/
def fzzScreeningCubicRegularMarkedLocalFinitePart : ℝ :=
  2*Real.pi*((∫ r : ℝ in (0 : ℝ)..(1/2), fzzScreeningCubicMarkedRadialRemainder r)+
    fzzScreeningCubicMarkedCollisionPrimitive (1/2))

/-- The original marked annulus is admitted before any cutoff is removed. -/
theorem fzzScreeningCubicMarkedAnnulus_integrable (T : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)
      (ball 0 (1/2) \ closedBall 0 (Real.exp (-T))) :=
  cubicMarked_annulus_integrable false _ (Real.exp_pos _)

/-- The original zero-puncture source retains both power-log corrections and the squared log. -/
theorem fzzScreeningCubicZeroMark_cutoff_limit :
    Tendsto (fun T : ℝ =>
      (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)),
        Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)+
          2*Real.pi*fzzScreeningCubicSingularMarkedCollisionPrimitive (Real.exp (-T))) atTop
      (𝓝 fzzScreeningCubicSingularMarkedLocalFinitePart) := by
  apply fzzScreeningHigherAngular_three_log_cutoff_limit.congr'
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))] with T hT
  have he := cubicMarked_annulus_angular false _ (Real.exp_pos (-T)) hT.le
  change (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)),
    Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z) = _ at he
  rw [he]
  simp only [cubicMarkedAngular, Bool.false_eq_true, ↓reduceIte]
  have hi : (∫ r : ℝ in Real.exp (-T)..(1/2), (r^(5 : ℕ))⁻¹*(Real.log r*fzzScreeningHigherAngular 3 r)) =
      ∫ r : ℝ in Real.exp (-T)..(1/2), (r^(5 : ℕ))⁻¹*Real.log r*fzzScreeningHigherAngular 3 r := by
    apply intervalIntegral.integral_congr
    intro r _
    ring
  rw [hi]
  ring

private theorem cubicMarked_annulus_reflection (ε : ℝ) :
    (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 ε, cubicMarkedKernel false z) =
      ∫ z : ℂ in ball 0 (1/2) \ closedBall 0 ε, cubicMarkedKernel true z := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding (cubicMarkedKernel false)
    (ball 1 (1/2) \ closedBall 1 ε)
  have he : (fun z : ℂ => 1-z) ⁻¹' (ball 1 (1/2) \ closedBall 1 ε) =
      ball 0 (1/2) \ closedBall 0 ε := by
    ext z
    simp [mem_ball, mem_closedBall, dist_eq_norm]
  rw [he] at h
  simpa only [cubicMarkedKernel, Bool.false_eq_true, ↓reduceIte,
    fzzScreeningPlaneKernel_reflection] using h.symm

private theorem cubicMarked_one_annulus_integrable (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (cubicMarkedKernel false) (ball 1 (1/2) \ closedBall 1 ε) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).integrableOn_comp_preimage
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding
    (f := cubicMarkedKernel false) (s := ball 1 (1/2) \ closedBall 1 ε)
  have he : (fun z : ℂ => 1-z) ⁻¹' (ball 1 (1/2) \ closedBall 1 ε) =
      ball 0 (1/2) \ closedBall 0 ε := by
    ext z
    simp [mem_ball, mem_closedBall, dist_eq_norm]
  have hf : cubicMarkedKernel false ∘ (fun z : ℂ => 1-z) = cubicMarkedKernel true := by
    funext z
    simp only [Function.comp_apply, cubicMarkedKernel, Bool.false_eq_true, ↓reduceIte,
      fzzScreeningPlaneKernel_reflection]
  rw [he,hf] at h
  exact h.mp (cubicMarked_annulus_integrable true ε hε)

/-- At the second original puncture, the same insertion forces a different local correction. -/
theorem fzzScreeningCubicOneMark_cutoff_limit :
    Tendsto (fun T : ℝ =>
      (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 (Real.exp (-T)),
        Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)+
          2*Real.pi*fzzScreeningCubicMarkedCollisionPrimitive (Real.exp (-T))) atTop
      (𝓝 fzzScreeningCubicRegularMarkedLocalFinitePart) := by
  apply fzzScreeningHigherMarkedAngular_three_cutoff_limit.congr'
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))] with T hT
  change 2*Real.pi*((∫ r : ℝ in Real.exp (-T)..(1/2),
    (r^(5 : ℕ))⁻¹*fzzScreeningHigherMarkedAngular 3 r)+
      fzzScreeningCubicMarkedCollisionPrimitive (Real.exp (-T))) =
    (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 (Real.exp (-T)), cubicMarkedKernel false z)+
      2*Real.pi*fzzScreeningCubicMarkedCollisionPrimitive (Real.exp (-T))
  rw [cubicMarked_annulus_reflection, cubicMarked_annulus_angular true _ (Real.exp_pos _) hT.le]
  simp only [cubicMarkedAngular, ↓reduceIte]
  ring

/-- The original marked source is integrable at every pair of finite cutoffs. -/
theorem fzzScreeningCubicMarkedPlaneCutoff_integrable (T U : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)
      (fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U))) := by
  apply (((cubicMarked_annulus_integrable false _ (Real.exp_pos _)).union
    (cubicMarked_one_annulus_integrable _ (Real.exp_pos _))).union fzzScreeningCubicMarkedExterior_integrable).mono_set
  intro z hz
  by_cases hz0 : z ∈ ball (0 : ℂ) (1/2)
  · exact Or.inl (Or.inl ⟨hz0,fun hh => hz (Or.inl hh)⟩)
  · by_cases hz1 : z ∈ ball (1 : ℂ) (1/2)
    · exact Or.inl (Or.inr ⟨hz1,fun hh => hz (Or.inr hh)⟩)
    · exact Or.inr (by rintro (h|h); exact hz0 h; exact hz1 h)

private theorem cubic_collision_disks_disjoint :
    Disjoint (ball (0 : ℂ) (1/2)) (ball 1 (1/2)) :=
  ball_disjoint_ball (by norm_num [dist_eq_norm])

private theorem cubic_cutoff_domain_split (r s : ℝ) (hr : r < 1/2) (hs : s < 1/2) :
    fzzScreeningPlaneCutoffDomain r s =
      ((ball 0 (1/2) \ closedBall 0 r) ∪ (ball 1 (1/2) \ closedBall 1 s)) ∪
        fzzScreeningPlaneExterior := by
  have h0 : closedBall (0 : ℂ) r ⊆ ball 0 (1/2) := closedBall_subset_ball hr
  have h1 : closedBall (1 : ℂ) s ⊆ ball 1 (1/2) := closedBall_subset_ball hs
  have hd := Set.disjoint_left.mp cubic_collision_disks_disjoint
  ext z
  constructor
  · intro hz
    by_cases hz0 : z ∈ ball (0 : ℂ) (1/2)
    · exact Or.inl (Or.inl ⟨hz0,fun hh => hz (Or.inl hh)⟩)
    · by_cases hz1 : z ∈ ball (1 : ℂ) (1/2)
      · exact Or.inl (Or.inr ⟨hz1,fun hh => hz (Or.inr hh)⟩)
      · exact Or.inr (by rintro (h|h); exact hz0 h; exact hz1 h)
  · rintro ((hz|hz)|hz) (h|h)
    · exact hz.2 h
    · exact hd hz.1 (h1 h)
    · exact hd (h0 h) hz.1
    · exact hz.2 h
    · exact hz (Or.inl (h0 h))
    · exact hz (Or.inr (h1 h))

private theorem cubic_cutoff_integral_split (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hrR : r < 1/2) (hsR : s < 1/2) :
    (∫ z : ℂ in fzzScreeningPlaneCutoffDomain r s, cubicMarkedKernel false z) =
      ((∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, cubicMarkedKernel false z)+
       (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 s, cubicMarkedKernel false z))+
       (∫ z : ℂ in fzzScreeningPlaneExterior, cubicMarkedKernel false z) := by
  rw [cubic_cutoff_domain_split r s hrR hsR]
  have ha := cubicMarked_annulus_integrable false r hr
  have hb := cubicMarked_one_annulus_integrable s hs
  have hd : Disjoint ((ball (0 : ℂ) (1/2) \ closedBall 0 r) ∪
      (ball 1 (1/2) \ closedBall 1 s)) fzzScreeningPlaneExterior := by
    apply Set.disjoint_left.mpr
    rintro z (hz|hz) he
    · exact he (Or.inl hz.1)
    · exact he (Or.inr hz.1)
  have hm : MeasurableSet fzzScreeningPlaneExterior :=
    (isOpen_ball.union isOpen_ball).isClosed_compl.measurableSet
  rw [setIntegral_union hd hm (ha.union hb) fzzScreeningCubicMarkedExterior_integrable,
    setIntegral_union (cubic_collision_disks_disjoint.mono Set.sdiff_subset Set.sdiff_subset)
      (measurableSet_ball.diff measurableSet_closedBall) ha hb]

/-- The full higher marked finite part retains the distinct local values and actual exterior. -/
def fzzScreeningCubicMarkedPlaneFinitePart : ℝ :=
  fzzScreeningCubicSingularMarkedLocalFinitePart+fzzScreeningCubicRegularMarkedLocalFinitePart+
    ∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z

/-- Both original marked punctures shrink independently with their different corrections retained. -/
theorem fzzScreeningCubicMarkedPlane_independent_cutoff_limit :
    Tendsto (fun P : ℝ × ℝ => fzzScreeningPlaneMarkedCutoff (-6) (-6) P.1 P.2+
      2*Real.pi*fzzScreeningCubicSingularMarkedCollisionPrimitive (Real.exp (-P.1))+
      2*Real.pi*fzzScreeningCubicMarkedCollisionPrimitive (Real.exp (-P.2))) (atTop ×ˢ atTop)
      (𝓝 fzzScreeningCubicMarkedPlaneFinitePart) := by
  have hf : Tendsto (fun P : ℝ × ℝ => P.1) (atTop ×ˢ atTop) atTop := tendsto_fst
  have hg : Tendsto (fun P : ℝ × ℝ => P.2) (atTop ×ˢ atTop) atTop := tendsto_snd
  have hd := ((fzzScreeningCubicZeroMark_cutoff_limit.comp hf).add
    (fzzScreeningCubicOneMark_cutoff_limit.comp hg)).add_const
      (∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)
  change Tendsto _ _ (𝓝 fzzScreeningCubicMarkedPlaneFinitePart) at hd
  apply hd.congr'
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < (1/2 : ℝ) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hf.eventually he,hg.eventually he] with P hP hQ
  dsimp only [Function.comp_def, fzzScreeningPlaneMarkedCutoff]
  have hs := cubic_cutoff_integral_split _ _ (Real.exp_pos (-P.1)) (Real.exp_pos (-P.2)) hP hQ
  change (∫ z : ℂ in fzzScreeningPlaneCutoffDomain (Real.exp (-P.1)) (Real.exp (-P.2)),
    Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z) = _ at hs
  rw [hs]
  simp only [cubicMarkedKernel, Bool.false_eq_true, ↓reduceIte]
  ring

end GaloisForLFunctions.RHTower
