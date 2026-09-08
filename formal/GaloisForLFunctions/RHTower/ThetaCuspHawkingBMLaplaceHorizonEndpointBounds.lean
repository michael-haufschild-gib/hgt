import GaloisForLFunctions.HTGeometry.HypergeometricEndpointBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceEndpoint

/-! Parameter-uniform first endpoint remainder for the original horizon-source product. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem horizon_parameter_neighborhood (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R B δ : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < B ∧ 0 < δ ∧
      ∀ u ∈ ball w R, ‖gaussA u chi‖ ≤ B ∧ ‖gaussB u chi‖ ≤ B ∧ ‖gaussC u‖ ≤ B ∧ δ ≤ |u.im| := by
  let B := ‖gaussA w chi‖+‖gaussB w chi‖+‖gaussC w‖+1
  let δ := |w.im|/2
  have hδ : 0 < δ := div_pos (abs_pos.mpr hw) (by norm_num)
  have hA : ∀ᶠ u in 𝓝 w, ‖gaussA u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussA u chi‖) w by unfold gaussA; fun_prop).eventually_lt
      continuousAt_const (by dsimp [B]; linarith [norm_nonneg (gaussB w chi),norm_nonneg (gaussC w)])
  have hB : ∀ᶠ u in 𝓝 w, ‖gaussB u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussB u chi‖) w by unfold gaussB; fun_prop).eventually_lt
      continuousAt_const (by dsimp [B]; linarith [norm_nonneg (gaussA w chi),norm_nonneg (gaussC w)])
  have hC : ∀ᶠ u in 𝓝 w, ‖gaussC u‖ < B :=
    (show ContinuousAt (fun u => ‖gaussC u‖) w by unfold gaussC; fun_prop).eventually_lt
      continuousAt_const (by dsimp [B]; linarith [norm_nonneg (gaussA w chi),norm_nonneg (gaussB w chi)])
  have hi : ∀ᶠ u : ℂ in 𝓝 w, δ < |u.im| := continuousAt_const.eventually_lt
    (by fun_prop) (by dsimp [δ]; linarith [abs_pos.mpr hw])
  obtain ⟨R,hR,hall⟩ := Metric.eventually_nhds_iff.mp (hA.and (hB.and (hC.and hi)))
  refine ⟨min R 1,B,δ,lt_min hR (by norm_num),min_le_right _ _,by dsimp [B]; positivity,hδ,?_⟩
  intro u hu
  obtain ⟨ha,hb,hc,hd⟩ := hall ((mem_ball.mp hu).trans_le (min_le_left _ _))
  exact ⟨ha.le,hb.le,hc.le,hd.le⟩

/-- The original horizon-source product after removing only its explicit Mellin power. -/
def horizonMellinCore (s chi a J K : ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  gaussFactor w chi false (t:ℂ)*sourceRemainder s w a J K 1 t

/-- Spatial measurability holds before any frequency chamber is imposed. -/
theorem horizonMellinCore_measurable (s chi a J K w : ℂ) : Measurable (horizonMellinCore s chi a J K w) := by
  have hg : Measurable (fun t : ℝ => gaussFactor w chi false (t:ℂ)) := by
    have ht : Measurable (fun t : ℝ => ∑' n : ℕ, ordinaryHypergeometricCoefficient
        (gaussA w chi) (gaussB w chi) (gaussC w) n*(t:ℂ)^n) :=
      Measurable.tsum (fun n : ℕ => show Measurable
      (fun t : ℝ => ordinaryHypergeometricCoefficient (gaussA w chi) (gaussB w chi) (gaussC w) n*(t:ℂ)^n) by fun_prop)
    simpa only [gaussFactor,radialSeries,Bool.false_eq_true,↓reduceIte,horizonSeries,
      ordinaryHypergeometric_sum_eq,smul_eq_mul] using ht
  exact hg.mul (sourceRemainder_continuous s w a J K 1).measurable

/-- The undressed product is holomorphic in frequency through the spatial horizon. -/
theorem horizonMellinCore_frequency_differentiableAt (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    {t : ℝ} (ht : ‖(t:ℂ)‖ < 1) :
    DifferentiableAt ℂ (fun u => horizonMellinCore s chi a J K u t) w :=
  (horizonGauss_frequency_differentiableAt w chi (t:ℂ) hw ht).mul
    (sourceRemainder_frequency_entire s a J K 1 t w)

/-- A single frequency neighborhood controls the actual source's endpoint difference.
No remainder estimate is supplied as a hypothesis. -/
theorem horizonMellinCore_uniform_first_bound (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ (∀ u ∈ ball w R, u.im ≠ 0) ∧
      ∀ u ∈ ball w R, ∀ t ∈ Icc (0:ℝ) b,
        ‖horizonMellinCore s chi a J K u t-horizonMellinCore s chi a J K u 0‖ ≤ C*t := by
  obtain ⟨R,B,δ,hR,hR1,hB,hδ,hp⟩ := horizon_parameter_neighborhood w chi hw
  obtain ⟨N,hN⟩ := exists_nat_ge (B+1)
  have hsep (u : ℂ) (hu : u ∈ ball w R) (j : ℕ) : δ ≤ ‖gaussC u+j‖ := by
    have hh := Complex.abs_im_le_norm (gaussC u+j)
    simp only [gaussC,Complex.add_im,Complex.one_im,Complex.natCast_im,zero_add,add_zero] at hh
    exact (hp u hu).2.2.2.trans hh
  let Cg := ∑' n, gaussParameterMajorant B δ N (n+1)*b^n
  have hCg : 0 ≤ Cg := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg ((norm_nonneg _).trans (gaussParameterMajorant_bound hB hδ
      (hp w (mem_ball_self hR)).1 (hp w (mem_ball_self hR)).2.1
      (hp w (mem_ball_self hR)).2.2.1 (hsep w (mem_ball_self hR)) N hN (n+1))) (pow_nonneg hb.le _)
  have hg (u : ℂ) (hu : u ∈ ball w R) (t : ℝ) (ht : t ∈ Icc (0:ℝ) b) :
      ‖gaussFactor u chi false (t:ℂ)-1‖ ≤ Cg*t := by
    have hn : ‖(t:ℂ)‖ ≤ b := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] using ht.2
    have hh := hypergeometric_sub_one_bound hB hδ hb hb1 (hp u hu).1 (hp u hu).2.1
      (hp u hu).2.2.1 (hsep u hu) N hN hn
    simpa only [ordinaryHypergeometric,gaussFactor,radialSeries,Bool.false_eq_true,↓reduceIte,horizonSeries,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] using hh
  obtain ⟨Cr,hCr,hsource⟩ := sourceRemainder_uniform_first_bound s w a J K 1 hb.le hb1
  obtain ⟨A,hA⟩ := (isCompact_closedBall w 1).exists_bound_of_continuousOn
    (sourceRemainder_frequency_entire s a J K 1 0).continuous.continuousOn
  let Ar := max A 0
  have hAr : 0 ≤ Ar := le_max_right _ _
  refine ⟨R,Cg*(Ar+Cr*b)+Cr,hR,by positivity,?_,?_⟩
  · intro u hu
    exact abs_pos.mp (hδ.trans_le (hp u hu).2.2.2)
  intro u hu t ht
  have hu1 : u ∈ ball w 1 := ball_subset_ball hR1 hu
  have hr0 : ‖sourceRemainder s u a J K 1 0‖ ≤ Ar :=
    (hA u (ball_subset_closedBall hu1)).trans (le_max_left _ _)
  have hrt : ‖sourceRemainder s u a J K 1 t‖ ≤ Ar+Cr*b := by
    have hnorm := norm_add_le (sourceRemainder s u a J K 1 t-sourceRemainder s u a J K 1 0)
      (sourceRemainder s u a J K 1 0)
    rw [sub_add_cancel] at hnorm
    have hdiff := hsource u hu1 t ht
    have hbnd := mul_le_mul_of_nonneg_left ht.2 hCr
    linarith
  have he : horizonMellinCore s chi a J K u t-horizonMellinCore s chi a J K u 0 =
      (gaussFactor u chi false (t:ℂ)-1)*sourceRemainder s u a J K 1 t +
      (sourceRemainder s u a J K 1 t-sourceRemainder s u a J K 1 0) := by
    simp only [horizonMellinCore,Complex.ofReal_zero,gaussFactor_zero,one_mul]
    ring
  rw [he]
  calc
    _ ≤ ‖gaussFactor u chi false (t:ℂ)-1‖*‖sourceRemainder s u a J K 1 t‖ +
        ‖sourceRemainder s u a J K 1 t-sourceRemainder s u a J K 1 0‖ := by
      simpa only [norm_mul] using norm_add_le
        ((gaussFactor u chi false (t:ℂ)-1)*sourceRemainder s u a J K 1 t)
        (sourceRemainder s u a J K 1 t-sourceRemainder s u a J K 1 0)
    _ ≤ (Cg*t)*(Ar+Cr*b)+Cr*t := add_le_add
      (mul_le_mul (hg u hu t ht) hrt (norm_nonneg _) (mul_nonneg hCg ht.1)) (hsource u hu1 t ht)
    _ = _ := by ring

end
end RHTower.D4BMLaplaceRadial
