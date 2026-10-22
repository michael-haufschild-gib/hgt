import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRampMoments

/-!
# Exponential moments of the causal factorial source

The causal source `sourceFactorialCausal N` is the average of the shifted ramps `e^(t/2) R_N(x - t)` over
the exponential tent density on `[0, 2 δ_N]`. By Fubini and translation, each exponential moment
`∫ e^(s x) C_N` factors as a tent moment times the same moment of the ramp `R_N`. At `s = ± 1/2` this gives
closed forms in terms of the harmonic correction and the Chebyshev bi-null producer.

## Main results

- `integral_exp_sourceFactorialCausal`: for every real `s`,
  `∫ e^(s x) C_N(x) dx = (∫_0^(2 δ_N) τ(t) e^((s + 1/2) t) dt) · ∫ e^(s x) R_N(x) dx`.
- `integral_exp_half_sourceFactorialCausal`:
  `∫ e^(x/2) C_N = sourceFactorialCoefficient N · harmonicCorrection N / sqrt N`.
- `integral_exp_neg_half_sourceFactorialCausal`:
  `∫ e^(-x/2) C_N = -chebyshevBiNullProducer N / sqrt N`.

## Hypotheses

All results are unconditional; the only side condition is `1 ≤ N`.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower
noncomputable section
set_option autoImplicit false

private theorem finite_rectangle_swap (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) (a b c d : ℝ) :
    (∫ x in Icc a b, ∫ y in Icc c d, F x y) =
      ∫ y in Icc c d, ∫ x in Icc a b, F x y := by
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- Since the causal source vanishes on `x ≤ 0`, every weighted integral over `ℝ` equals the integral
over `[0, ∞)`. -/
theorem integral_weight_sourceFactorialCausal_eq_halfLine {N : ℕ} (hN : 1 ≤ N) (w : ℝ → ℝ) :
    (∫ x : ℝ, w x*sourceFactorialCausal N x) = ∫ x in Ici 0, w x*sourceFactorialCausal N x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hneg : x ≤ 0 := by by_contra! hh; exact hx hh.le
  rw [sourceFactorialCausal_zero_of_nonpos hN hneg, mul_zero]

/-- Moment factorization: for `N ≥ 1` and real `s`, the exponential moment of the causal source is the
tent moment `∫_0^(2 δ_N) τ(t) e^((s + 1/2) t) dt` times the exponential moment `∫ e^(s x) R_N(x) dx` of
the ramp. -/
theorem integral_exp_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    (∫ x : ℝ, Real.exp (s*x)*sourceFactorialCausal N x) =
      (∫ t in Icc 0 (2*sourceFactorialWidth N), exponentialTentDensity (sourceFactorialWidth N) t *
        Real.exp ((s+1/2)*t)) * (∫ x : ℝ, Real.exp (s*x)*sourceFactorialRamp N x) := by
  let δ := sourceFactorialWidth N
  let L := Real.log (4*(N : ℝ)+1)
  let F := fun x t : ℝ => Real.exp (s*x)*
    (exponentialTentDensity δ t*(Real.exp (t/2)*sourceFactorialRamp N (x-t)))
  have hc : Continuous (Function.uncurry F) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (((continuous_exponentialTentDensity δ).comp continuous_snd).mul
        ((Real.continuous_exp.comp (continuous_snd.div_const 2)).mul
          ((continuous_sourceFactorialRamp N).comp (continuous_fst.sub continuous_snd))))
  have hcut : (∫ x : ℝ, Real.exp (s*x)*sourceFactorialCausal N x) =
      ∫ x in Icc 0 L, ∫ t in Icc 0 (2*δ), F x t := by
    have he : (∫ x : ℝ, Real.exp (s*x)*sourceFactorialCausal N x) =
        ∫ x in Icc 0 L, Real.exp (s*x)*sourceFactorialCausal N x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_cases h0 : 0 ≤ x
      · have ht : L ≤ x := by by_contra! hh; exact hx ⟨h0, hh.le⟩
        rw [sourceFactorialCausal_tail hN ht, mul_zero]
      · rw [sourceFactorialCausal_zero_of_nonpos hN (by linarith), mul_zero]
    rw [he]
    apply integral_congr_ae
    filter_upwards [] with x
    exact (integral_const_mul _ _).symm
  rw [hcut, finite_rectangle_swap F hc]
  have hi (t : ℝ) (ht : t ∈ Icc 0 (2*δ)) :
      (∫ x in Icc 0 L, F x t) =
        (exponentialTentDensity δ t*Real.exp ((s+1/2)*t)) *
          (∫ x : ℝ, Real.exp (s*x)*sourceFactorialRamp N x) := by
    have he : (∫ x in Icc 0 L, F x t) = ∫ x : ℝ, F x t := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_cases h0 : 0 ≤ x
      · have ht' : L ≤ x := by by_contra! hh; exact hx ⟨h0, hh.le⟩
        dsimp [F]
        rw [sourceFactorialRamp_shift_tail hN ht ht', mul_zero, mul_zero, mul_zero]
      · dsimp [F]
        rw [sourceFactorialRamp_zero_of_nonpos hN (by linarith [ht.1]), mul_zero, mul_zero, mul_zero]
    rw [he, ← integral_add_right_eq_self (fun x => F x t) t]
    have hp (x : ℝ) : F (x+t) t =
        (exponentialTentDensity δ t*Real.exp ((s+1/2)*t)) *
          (Real.exp (s*x)*sourceFactorialRamp N x) := by
      dsimp [F]
      rw [add_sub_cancel_right, mul_add, Real.exp_add]
      have hexp : Real.exp (s*t)*Real.exp (t/2) = Real.exp ((s+1/2)*t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (exponentialTentDensity δ t*(Real.exp (s*t)*Real.exp (t/2)))*
            (Real.exp (s*x)*sourceFactorialRamp N x) := by ring
        _ = _ := by rw [hexp]
    simp_rw [hp]
    exact integral_const_mul _ _
  calc
    _ = ∫ t in Icc 0 (2*δ),
        (exponentialTentDensity δ t*Real.exp ((s+1/2)*t)) *
          (∫ x : ℝ, Real.exp (s*x)*sourceFactorialRamp N x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hi t ht
    _ = _ := integral_mul_const _ _

/-- Growing polar moment: `∫ e^(x/2) C_N = sourceFactorialCoefficient N · harmonicCorrection N / sqrt N`,
where `sourceFactorialCoefficient N = ((1 + e^(δ_N)) / 2)^3`. -/
theorem integral_exp_half_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    (∫ x : ℝ, Real.exp (x/2)*sourceFactorialCausal N x) =
      sourceFactorialCoefficient N*harmonicCorrection N/Real.sqrt N := by
  have h := integral_exp_sourceFactorialCausal hN (1/2)
  simp only [show (1/2 : ℝ)+1/2 = 1 by norm_num, one_mul,
    show ∀ x : ℝ, (1/2)*x = x/2 by intro x; ring] at h
  rw [show (fun t => exponentialTentDensity (sourceFactorialWidth N) t*Real.exp t) =
      (fun t => Real.exp t*exponentialTentDensity (sourceFactorialWidth N) t) by funext t; ring,
    integral_exp_exponentialTentDensity (sourceFactorialWidth_pos hN)] at h
  change _ = _ * (∫ x : ℝ, Real.exp (x/2)*rampBiNull (sourceFactorialCollar N) N x) at h
  rw [integral_exp_half_rampBiNull (sourceFactorialCollar_pos hN)] at h
  rw [h]
  unfold sourceFactorialCoefficient sourceFactorialCollar
  ring

/-- Decaying polar moment: `∫ e^(-x/2) C_N = -chebyshevBiNullProducer N / sqrt N`; the tent average has
total mass one, so the ramp moment passes through unchanged. -/
theorem integral_exp_neg_half_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    (∫ x : ℝ, Real.exp (-(x/2))*sourceFactorialCausal N x) =
      -chebyshevBiNullProducer N/Real.sqrt N := by
  have h := integral_exp_sourceFactorialCausal hN (-(1/2))
  simp only [neg_add_cancel, zero_mul, Real.exp_zero, mul_one,
    show ∀ x : ℝ, -(1/2)*x = -(x/2) by intro x; ring] at h
  rw [integral_Icc_exponentialTentDensity (sourceFactorialWidth_pos hN), one_mul] at h
  rw [h]
  exact integral_exp_neg_half_rampBiNull (sourceFactorialCollar_pos hN) hN

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
