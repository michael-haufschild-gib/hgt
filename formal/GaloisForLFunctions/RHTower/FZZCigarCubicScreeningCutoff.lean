import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningAngular
import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningCutoff
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Original cubic screening cutoff at both punctures

The original plane kernel at exponents `(-6,-6)` is integrated over finite
annuli by polar change of variables and compact-product Fubini. The previously
proved angular recurrence supplies all three divergent coefficients. Reflection
retains the same exact local correction at the other puncture. Both admitted
annuli and the fixed exterior assemble into an independently convergent original
whole-plane cutoff, with no numerical experiment or prescribed Gamma value.

Every public statement is unconditional, with finite cutoffs discharged by
exponentiation. This defines the original circular-cutoff finite part; it does
not yet evaluate that finite value, identify the complete CFT normalization,
or prove the higher marked responses, mixed Ward identity, phase frame or RH.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

/-- The exact local finite part for the fixed exponent `-6` at both source punctures. -/
def fzzScreeningCubicLocalFinitePart : ℝ :=
  2*Real.pi*((∫ r : ℝ in (0 : ℝ)..(1/2), r*fzzScreeningCubicAngularRemainder r)+
    fzzScreeningCubicCollisionPrimitive (1/2))

private def cubicPolar (p : ℝ × ℝ) : ℝ :=
  (p.1^5)⁻¹*(‖1-circleMap 0 p.1 p.2‖^6)⁻¹

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

private theorem cubic_annulus_polar (ε : ℝ) (hε : 0 < ε) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 ε, fzzScreeningPlaneKernel (-6) (-6) z) =
      ∫ p : ℝ × ℝ in Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi, cubicPolar p := by
  let A : Set ℂ := ball 0 (1/2) \ closedBall 0 ε
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hpolar := Complex.integral_comp_polarCoord_symm
    (A.indicator (fzzScreeningPlaneKernel (-6) (-6)))
  rw [integral_indicator hA] at hpolar
  rw [← hpolar, polarCoord_target]
  have he : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • A.indicator (fzzScreeningPlaneKernel (-6) (-6)) (Complex.polarCoord.symm p) =
        (Ioo ε (1/2) ×ˢ Ioo (-Real.pi) Real.pi).indicator cubicPolar p := by
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
      exact cubicKernel_circleMap r θ hr
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
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, (‖1-circleMap 0 r θ‖^6)⁻¹) =
      2*Real.pi*fzzScreeningHigherAngular 3 r := by
  have h := Real.circleAverage_eq_integral_add
    (f := fun z : ℂ => (‖1-z‖^6)⁻¹) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => (‖1-circleMap 0 r θ‖^6)⁻¹) (-Real.pi), zero_add,
    show 2*Real.pi+-Real.pi = Real.pi by ring, smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo] at h
  change fzzScreeningHigherAngular 3 r = _ at h
  rw [h]
  field_simp [Real.pi_ne_zero]

private theorem cubic_annulus_angular (ε : ℝ) (hε : 0 < ε) (hεR : ε ≤ 1/2) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 ε, fzzScreeningPlaneKernel (-6) (-6) z) =
      2*Real.pi*(∫ r : ℝ in ε..(1/2), (r^5)⁻¹*fzzScreeningHigherAngular 3 r) := by
  rw [cubic_annulus_polar ε hε, Measure.volume_eq_prod,
    setIntegral_prod _ (cubicPolar_integrable ε hε)]
  simp_rw [cubicPolar, integral_const_mul, cubic_angle_integral]
  rw [intervalIntegral.integral_of_le hεR, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  ring

private theorem cubic_annulus_integrable (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fzzScreeningPlaneKernel (-6) (-6))
      (ball 0 (1/2) \ closedBall 0 ε) := by
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
  apply (hc.integrableOn_compact hk).mono_set
  intro z hz
  exact ⟨ball_subset_closedBall hz.1,fun hh => hz.2 (ball_subset_closedBall hh)⟩

/-- Every original finite annulus is an ordinary integrable source at exponent `-6`. -/
theorem fzzScreeningCubicAnnulus_integrable (T : ℝ) :
    IntegrableOn (fzzScreeningPlaneKernel (-6) (-6))
      (ball 0 (1/2) \ closedBall 0 (Real.exp (-T))) :=
  cubic_annulus_integrable _ (Real.exp_pos _)

/-- Original planar cutoff at zero, with both power corrections and the logarithmic correction. -/
theorem fzzScreeningCubicZero_cutoff_limit :
    Tendsto (fun T : ℝ =>
      (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)),
        fzzScreeningPlaneKernel (-6) (-6) z)+
          2*Real.pi*fzzScreeningCubicCollisionPrimitive (Real.exp (-T))) atTop
      (𝓝 fzzScreeningCubicLocalFinitePart) := by
  apply fzzScreeningHigherAngular_three_cutoff_limit.congr'
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))] with T hT
  rw [cubic_annulus_angular _ (Real.exp_pos _) hT.le]
  ring

private theorem cubic_annulus_reflection (ε : ℝ) :
    (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 ε, fzzScreeningPlaneKernel (-6) (-6) z) =
      ∫ z : ℂ in ball 0 (1/2) \ closedBall 0 ε, fzzScreeningPlaneKernel (-6) (-6) z := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding (fzzScreeningPlaneKernel (-6) (-6))
    (ball 1 (1/2) \ closedBall 1 ε)
  have he : (fun z : ℂ => 1-z) ⁻¹' (ball 1 (1/2) \ closedBall 1 ε) =
      ball 0 (1/2) \ closedBall 0 ε := by
    ext z
    simp [mem_ball, mem_closedBall, dist_eq_norm]
  rw [he] at h
  simpa only [fzzScreeningPlaneKernel_reflection] using h.symm

/-- Reflection retains the same complete local correction at the second original puncture. -/
theorem fzzScreeningCubicOne_cutoff_limit :
    Tendsto (fun T : ℝ =>
      (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 (Real.exp (-T)),
        fzzScreeningPlaneKernel (-6) (-6) z)+
          2*Real.pi*fzzScreeningCubicCollisionPrimitive (Real.exp (-T))) atTop
      (𝓝 fzzScreeningCubicLocalFinitePart) := by
  simp_rw [cubic_annulus_reflection]
  exact fzzScreeningCubicZero_cutoff_limit


private theorem cubic_one_annulus_integrable (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fzzScreeningPlaneKernel (-6) (-6))
      (ball 1 (1/2) \ closedBall 1 ε) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).integrableOn_comp_preimage
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding
    (f := fzzScreeningPlaneKernel (-6) (-6)) (s := ball 1 (1/2) \ closedBall 1 ε)
  have he : (fun z : ℂ => 1-z) ⁻¹' (ball 1 (1/2) \ closedBall 1 ε) =
      ball 0 (1/2) \ closedBall 0 ε := by
    ext z
    simp [mem_ball, mem_closedBall, dist_eq_norm]
  have hf : fzzScreeningPlaneKernel (-6) (-6) ∘ (fun z : ℂ => 1-z) =
      fzzScreeningPlaneKernel (-6) (-6) := by
    funext z
    exact fzzScreeningPlaneKernel_reflection (-6) (-6) z
  rw [he,hf] at h
  exact h.mp (cubic_annulus_integrable ε hε)

private theorem cubic_exterior_integrable :
    IntegrableOn (fzzScreeningPlaneKernel (-6) (-6)) fzzScreeningPlaneExterior := by
  have h := fzzScreeningPlaneExterior_integrable (-6) (Real.log 10)
  norm_num [Real.exp_log (by positivity : (0 : ℝ) < 10)] at h
  exact h

/-- The higher collision source is integrable at every pair of finite original cutoffs. -/
theorem fzzScreeningCubicPlaneCutoff_integrable (T U : ℝ) :
    IntegrableOn (fzzScreeningPlaneKernel (-6) (-6))
      (fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U))) := by
  apply (((cubic_annulus_integrable _ (Real.exp_pos _)).union
    (cubic_one_annulus_integrable _ (Real.exp_pos _))).union cubic_exterior_integrable).mono_set
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
    (∫ z : ℂ in fzzScreeningPlaneCutoffDomain r s, fzzScreeningPlaneKernel (-6) (-6) z) =
      ((∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, fzzScreeningPlaneKernel (-6) (-6) z)+
       (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 s, fzzScreeningPlaneKernel (-6) (-6) z))+
       (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel (-6) (-6) z) := by
  rw [cubic_cutoff_domain_split r s hrR hsR]
  have ha := cubic_annulus_integrable r hr
  have hb := cubic_one_annulus_integrable s hs
  have hd : Disjoint ((ball (0 : ℂ) (1/2) \ closedBall 0 r) ∪
      (ball 1 (1/2) \ closedBall 1 s)) fzzScreeningPlaneExterior := by
    apply Set.disjoint_left.mpr
    rintro z (hz|hz) he
    · exact he (Or.inl hz.1)
    · exact he (Or.inr hz.1)
  have hm : MeasurableSet fzzScreeningPlaneExterior :=
    (isOpen_ball.union isOpen_ball).isClosed_compl.measurableSet
  rw [setIntegral_union hd hm (ha.union hb) cubic_exterior_integrable,
    setIntegral_union (cubic_collision_disks_disjoint.mono Set.sdiff_subset Set.sdiff_subset)
      (measurableSet_ball.diff measurableSet_closedBall) ha hb]

/-- The full higher finite part retains both local values and the original exterior. -/
def fzzScreeningCubicPlaneFinitePart : ℝ :=
  2*fzzScreeningCubicLocalFinitePart+
    ∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel (-6) (-6) z

/-- Both original punctures may shrink independently with all three local corrections retained. -/
theorem fzzScreeningCubicPlane_independent_cutoff_limit :
    Tendsto (fun P : ℝ × ℝ => fzzScreeningPlaneCutoff (-6) (-6) P.1 P.2+
      2*Real.pi*fzzScreeningCubicCollisionPrimitive (Real.exp (-P.1))+
      2*Real.pi*fzzScreeningCubicCollisionPrimitive (Real.exp (-P.2))) (atTop ×ˢ atTop)
      (𝓝 fzzScreeningCubicPlaneFinitePart) := by
  have hf : Tendsto (fun P : ℝ × ℝ => P.1) (atTop ×ˢ atTop) atTop := tendsto_fst
  have hg : Tendsto (fun P : ℝ × ℝ => P.2) (atTop ×ˢ atTop) atTop := tendsto_snd
  have hd := ((fzzScreeningCubicZero_cutoff_limit.comp hf).add
    (fzzScreeningCubicOne_cutoff_limit.comp hg)).add_const
      (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel (-6) (-6) z)
  have hvalue : fzzScreeningCubicLocalFinitePart+fzzScreeningCubicLocalFinitePart+
      (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel (-6) (-6) z) =
      fzzScreeningCubicPlaneFinitePart := by
    unfold fzzScreeningCubicPlaneFinitePart
    ring
  rw [hvalue] at hd
  apply hd.congr'
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < (1/2 : ℝ) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hf.eventually he,hg.eventually he] with P hP hQ
  dsimp only [Function.comp_def, fzzScreeningPlaneCutoff]
  rw [cubic_cutoff_integral_split _ _ (Real.exp_pos _) (Real.exp_pos _) hP hQ]
  ring


end GaloisForLFunctions.RHTower
