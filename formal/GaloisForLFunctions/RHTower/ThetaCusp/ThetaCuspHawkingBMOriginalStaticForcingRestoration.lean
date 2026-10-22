import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalStaticForcingTriangle

open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalStaticForcingRestoration
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore D4BMJointWave
open D4BMOriginalStaticForcingPrimitive D4BMOriginalStaticForcingTriangle
noncomputable section
set_option autoImplicit false

/-- The literal causal forcing triangle, with its original radial counterterm
transported along the moving boundary, restores uniformly over all onset,
time and lower radial cutoffs. The original finite-cusp weights alone control
this error; no relative time/horizon/cusp rates are prescribed. -/
theorem static_forcing_uniform_restoration (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im ≠ 0) (hwr : -2 < w.re) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 1/2 ∧ ∀ b : ℝ, b < 0 → horizonCoordinate b ≤ B →
      ∃ η : ℝ → ℝ, (∀ k, 0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
        ∀ a ξ T k : ℝ, 0 ≤ a → ξ ≤ b →
          ‖staticForcingCut q br amp w a ξ b T k-staticForcingCounterterm q br amp w a ξ b T k‖ ≤ η k := by
  obtain ⟨B,hB,hBh,h⟩ := forcing_primitive_uniform_restoration q br amp w hwi hwr
  refine ⟨B,hB,hBh,?_⟩
  intro b hb hbB
  have hbI := horizonCoordinate_interior b hb
  obtain ⟨η,hη,hηlim,hηbound⟩ := h (horizonCoordinate b) hbI.1 hbB
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hi : IntegrableOn (onsetDensity q br w) (Ioi (0:ℝ)) :=
    timeOnset_integrable (2*physicalRate q br) w (hs.trans hwr)
  have hin : IntegrableOn (fun p => ‖onsetDensity q br w p‖) (Ioi (0:ℝ)) := hi.norm
  let M := ∫ p in Ioi (0:ℝ),‖onsetDensity q br w p‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨fun k => M*η k,fun k => mul_nonneg hM (hη k),?_,?_⟩
  · simpa only [mul_zero] using hηlim.const_mul M
  · intro a ξ T k ha hξ
    rw [static_forcing_counterterm_identity q br amp w a ξ b T k hξ hb]
    by_cases hT : T+b ≤ a
    · rw [max_eq_left hT,intervalIntegral.integral_same,norm_zero]
      exact mul_nonneg hM (hη k)
    · have hau : a ≤ T+b := (lt_of_not_ge hT).le
      rw [max_eq_right hau]
      have hfg : IntervalIntegrable (fun p => ‖onsetDensity q br w p‖*η k) volume a (T+b) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hau]
        exact (hin.mono_set (fun p hp => ha.trans_lt hp.1)).mul_const _
      have hbound : ∀ p ∈ Ioc a (T+b),
          ‖onsetDensity q br w p*primitiveDifference q br amp w b k (max ξ (p-T))‖ ≤
            ‖onsetDensity q br w p‖*η k := by
        intro p hp
        have hxb : max ξ (p-T) ≤ b := max_le hξ (by linarith [hp.2])
        have hx0 : max ξ (p-T) < 0 := hxb.trans_lt hb
        have hxI := horizonCoordinate_interior _ hx0
        have hxe : horizonCoordinate (max ξ (p-T)) ≤ horizonCoordinate b :=
          horizonCoordinate_strictMonoOn.monotoneOn hx0 hb hxb
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hηbound k _ ⟨hxI.1,hxe⟩) (norm_nonneg _)
      have hbnd := intervalIntegral.norm_integral_le_of_norm_le hau
        (Filter.Eventually.of_forall hbound) hfg
      apply hbnd.trans
      rw [intervalIntegral.integral_mul_const]
      apply mul_le_mul_of_nonneg_right _ (hη k)
      rw [intervalIntegral.integral_of_le hau]
      exact setIntegral_mono_set hi.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (Filter.Eventually.of_forall (fun p hp => ha.trans_lt hp.1))

end
end RHTower.D4BMOriginalStaticForcingRestoration
