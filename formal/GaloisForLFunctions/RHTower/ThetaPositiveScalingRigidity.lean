import GaloisForLFunctions.RHTower.ThetaPositiveScalingEnergies
import GaloisForLFunctions.RHTower.ThetaPrimeScalingRigidity

/-!
# No nonzero Schwartz profile has zero positive jump energy

Each continuous kernel is strictly positive at every positive lag. Vanishing
energy forces every forward increment to vanish. Decay at infinity then
removes the constant mode. The same conclusion holds for the prime energy.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped SchwartzMap BoundedContinuousFunction

namespace RHTower.ThetaSourceWard

private theorem schwartz_zero_of_constant (chi : 𝓢(ℝ, ℂ))
    (hc : ∀ x : ℝ, chi x = chi 0) : chi = 0 := by
  have hl : Tendsto (fun _ : ℝ => chi 0) (cocompact ℝ) (𝓝 0) := by
    have he : (chi : ℝ → ℂ) = fun _ => chi 0 := funext hc
    rw [← he]
    exact chi.tendsto_cocompact
  have hz : chi 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hl
  ext x
  exact (hc x).trans hz

private theorem schwartz_zero_of_forward (chi : 𝓢(ℝ, ℂ))
    (hc : ∀ (x h : ℝ), 0 < h → chi (x + h) = chi x) : chi = 0 := by
  apply schwartz_zero_of_constant
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := hc x (-x) (neg_pos.mpr hx)
    simpa only [add_neg_cancel] using h.symm
  · rfl
  · simpa only [zero_add] using hc 0 x hx

private theorem continuousLinkMeasure_eq : thetaContinuousLinkMeasure =
    (volume.prod volume).restrict ((Ioi (0 : ℝ)) ×ˢ (univ : Set ℝ)) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

private theorem jump_zero_everywhere {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f ((Ioi (0 : ℝ)) ×ˢ (univ : Set ℝ)))
    (he : f =ᵐ[thetaContinuousLinkMeasure] 0) :
    ∀ x h : ℝ, 0 < h → f (h, x) = 0 := by
  rw [continuousLinkMeasure_eq] at he
  have h := MeasureTheory.Measure.eqOn_open_of_ae_eq he (isOpen_Ioi.prod isOpen_univ) hf continuousOn_const
  exact fun x u hu => h ⟨hu, mem_univ x⟩

theorem thetaPolarScalingEnergy_eq_zero_iff (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    thetaPolarScalingEnergy S chi = 0 ↔ chi = 0 := by
  constructor
  · intro h
    have he := (integral_eq_zero_iff_of_nonneg (thetaPolarScalingDensity_nonneg S chi)
      (integrable_thetaPolarScalingDensity S chi)).mp h
    have hc : Continuous (thetaPolarScalingDensity S chi) := by
      have hs := S.cont
      have hchi := chi.continuous
      unfold thetaPolarScalingDensity
      fun_prop
    have hz := jump_zero_everywhere hc.continuousOn he
    apply schwartz_zero_of_forward
    intro x u hu
    have hp : 0 < 2 * Real.cosh (u / 2) * S.k x * S.k (x + u) := by
      have hx := S.pos x
      have hy := S.pos (x + u)
      positivity
    have hzero := hz x u hu
    change (2 * Real.cosh (u / 2) * S.k x * S.k (x + u)) * ‖chi (x + u) - chi x‖ ^ 2 = 0 at hzero
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp
      ((mul_eq_zero.mp hzero).resolve_left hp.ne')))
  · rintro rfl
    simp [thetaPolarScalingEnergy, thetaPolarScalingDensity]

theorem thetaGammaScalingEnergy_eq_zero_iff (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    thetaGammaScalingEnergy S chi = 0 ↔ chi = 0 := by
  constructor
  · intro h
    have hn : ∀ᵐ p ∂thetaContinuousLinkMeasure, 0 ≤ thetaGammaScalingDensity S chi p := by
      filter_upwards [thetaContinuousLinkMeasure_ae_pos] with p hp
      exact thetaGammaScalingDensity_nonneg S chi hp
    have he := (integral_eq_zero_iff_of_nonneg_ae hn (integrable_thetaGammaScalingDensity S chi)).mp h
    have hc : ContinuousOn (thetaGammaScalingDensity S chi) ((Ioi (0 : ℝ)) ×ˢ (univ : Set ℝ)) := by
      have hs := S.cont
      have hchi := chi.continuous
      have hnum : Continuous (fun p : ℝ × ℝ => Real.exp (-p.1 / 2)) := by fun_prop
      have hden : Continuous (fun p : ℝ × ℝ => 1 - Real.exp (-2 * p.1)) := by fun_prop
      have hk := hnum.continuousOn.div hden.continuousOn (s := (Ioi (0 : ℝ)) ×ˢ (univ : Set ℝ))
        (fun p hp => ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by
          have hh : 0 < p.1 := hp.1
          linarith))))
      exact ((hk.mul (hs.comp continuous_snd).continuousOn).mul
        (hs.comp (continuous_snd.add continuous_fst)).continuousOn).mul
          (((hchi.comp (continuous_snd.add continuous_fst)).sub
            (hchi.comp continuous_snd)).norm.continuousOn.pow 2)
    have hz := jump_zero_everywhere hc he
    apply schwartz_zero_of_forward
    intro x u hu
    have hp : 0 < Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) * S.k x * S.k (x + u) := by
      have hd : 0 < 1 - Real.exp (-2 * u) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      have hx := S.pos x
      have hy := S.pos (x + u)
      positivity
    have hzero := hz x u hu
    change (Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) * S.k x * S.k (x + u)) *
      ‖chi (x + u) - chi x‖ ^ 2 = 0 at hzero
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp
      ((mul_eq_zero.mp hzero).resolve_left hp.ne')))
  · rintro rfl
    simp [thetaGammaScalingEnergy, thetaGammaScalingDensity]

theorem thetaPolarScalingEnergy_pos_iff (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    0 < thetaPolarScalingEnergy S chi ↔ chi ≠ 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (thetaPolarScalingEnergy_nonneg S chi), ne_comm,
    ne_eq, thetaPolarScalingEnergy_eq_zero_iff]

theorem thetaGammaScalingEnergy_pos_iff (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    0 < thetaGammaScalingEnergy S chi ↔ chi ≠ 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (thetaGammaScalingEnergy_nonneg S chi), ne_comm,
    ne_eq, thetaGammaScalingEnergy_eq_zero_iff]

/-- The complete prime energy has no nonzero Schwartz null mode either. -/
theorem thetaPrimeScalingEnergy_schwartz_eq_zero_iff (S T : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    thetaPrimeScalingEnergy S T chi.toBoundedContinuousFunction = 0 ↔ chi = 0 := by
  rw [thetaPrimeScalingEnergy_eq_zero_iff]
  constructor
  · intro h
    apply schwartz_zero_of_constant
    intro x
    simpa only [SchwartzMap.toBoundedContinuousFunction_apply, BoundedContinuousFunction.const_apply] using
      congrArg (fun f : ℝ →ᵇ ℂ => f x) h
  · rintro rfl
    ext x
    simp

end RHTower.ThetaSourceWard
