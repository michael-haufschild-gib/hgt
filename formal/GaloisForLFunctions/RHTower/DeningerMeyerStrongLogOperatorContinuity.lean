import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogFrechet
import GaloisForLFunctions.RHTower.DeningerMeyerFiniteRankSourceSolvability

/-!
# Continuity of the actual Meyer generator and every finite Xi coupling

Fourier evaluation after exponential weighting and polynomial multiplication
realizes every Mellin jet as a continuous functional. The derivative gauges
also make the actual generator continuous. Both statements descend through
the literal Poisson quotient; the causal finite-packet operators therefore
act continuously in its natural Fréchet topology.
-/

open Complex Filter Topology MeasureTheory SchwartzMap FourierTransform

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology BoundedContinuousFunction

/-- All-order Mellin evaluation in the natural strong source topology. -/
def deningerMeyerStrongLogMellinJetCLM (k : ℕ) (s : ℂ) :
    DeningerMeyerStrongLogTarget →L[ℂ] ℂ :=
  (deningerSchwartzEval (-s.im / (2 * Real.pi))).comp
    ((FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).toContinuousLinearMap.comp
      ((SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => (t : ℂ) ^ k)).comp
        ((⟨deningerExpMulSchwartzLM s.re,
          deningerExpMulSchwartzLM_continuous s.re⟩ :
            DeningerMeyerSource →L[ℂ] 𝓢(ℝ, ℂ)).comp
          deningerMeyerStrongLogSourceContinuousEquiv.toContinuousLinearMap)))

theorem deningerMeyerStrongLogMellinJetCLM_apply (k : ℕ) (s : ℂ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogMellinJetCLM k s g =
      deningerMeyerStrongLogMellinJetLM k s g := by
  change (𝓕 (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => (t : ℂ) ^ k)
    (deningerExpMulSchwartzLM s.re (deningerMeyerStrongLogSourceEquiv g))))
      (-s.im / (2 * Real.pi)) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  change (∫ t : ℝ, _) = ∫ t : ℝ, deningerMeyerStrongLogMellinJet k s g t
  apply integral_congr_ae
  filter_upwards with t
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [deningerExpMulSchwartzLM_apply, deningerExpMul_apply,
    smul_eq_mul, deningerMeyerStrongLogMellinJet, Complex.ofReal_exp]
  change Complex.exp _ * ((t : ℂ) ^ k * (Complex.exp _ * g.val t)) =
    (t : ℂ) ^ k * Complex.exp (s * t) * g.val t
  have hphase :
      ((-2 * Real.pi * t * (-s.im / (2 * Real.pi)) : ℝ) : ℂ) * I +
        ((s.re * t : ℝ) : ℂ) = s * t := by
    push_cast
    conv_rhs => rw [← Complex.re_add_im s]
    field_simp [Real.pi_ne_zero]
    ring
  calc
    _ = (t : ℂ) ^ k *
        (Complex.exp (((-2 * Real.pi * t * (-s.im / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          Complex.exp ((s.re * t : ℝ) : ℂ)) * g.val t := by ring
    _ = _ := by rw [← Complex.exp_add, hphase]

theorem deningerMeyerStrongLogMellinJetLM_continuous (k : ℕ) (s : ℂ) :
    Continuous (deningerMeyerStrongLogMellinJetLM k s) := by
  convert (deningerMeyerStrongLogMellinJetCLM k s).continuous using 1
  ext g
  exact (deningerMeyerStrongLogMellinJetCLM_apply k s g).symm

theorem deningerMeyerXiSupportJetEvaluationLM_continuous
    (rho : XiDivisorSupport) (k : DeningerArithmeticJetIndex rho) :
    Continuous (deningerMeyerXiSupportJetEvaluationLM rho k) := by
  apply (LinearMap.range deningerMeyerStrongLogSumLM).isQuotientMap_mkQ.continuous_iff.mpr
  exact deningerMeyerStrongLogMellinJetLM_continuous k rho

theorem deningerMeyerFiniteXiJetPacketLM_continuous (S : Finset XiDivisorSupport) :
    Continuous (deningerMeyerFiniteXiJetPacketLM S) :=
  continuous_pi fun q => deningerMeyerXiSupportJetEvaluationLM_continuous q.1.1 q.2

theorem deningerMeyerStrongLogGauge_generator (n : ℕ) (k : ℤ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogGauge n k (deningerMeyerStrongLogGenerator g) =
      -deningerMeyerStrongLogGauge (n + 1) k g := by
  apply BoundedContinuousFunction.ext
  intro t
  simp only [deningerMeyerStrongLogGauge_apply, BoundedContinuousFunction.neg_apply]
  change (_ : ℂ) * iteratedDeriv n (-deriv (g : ℝ → ℂ)) t = _
  rw [iteratedDeriv_neg, ← iteratedDeriv_succ']
  simp

theorem deningerMeyerStrongLogGenerator_continuous :
    Continuous deningerMeyerStrongLogGenerator := by
  change @Continuous _ _ deningerMeyerStrongLogTopology
    (⨅ i : ℕ × ℤ, TopologicalSpace.induced
      (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) _
  rw [continuous_iInf_rng]
  intro i
  rw [continuous_induced_rng]
  convert (continuous_deningerMeyerStrongLogGaugeLinear (i.1 + 1) i.2).neg using 1
  funext g
  exact deningerMeyerStrongLogGauge_generator i.1 i.2 g

theorem deningerMeyerCohomologyGenerator_continuous :
    Continuous deningerMeyerCohomologyGenerator := by
  apply (LinearMap.range deningerMeyerStrongLogSumLM).isQuotientMap_mkQ.continuous_iff.mpr
  exact continuous_quot_mk.comp deningerMeyerStrongLogGenerator_continuous

theorem deningerMeyerGeneratorWord_continuous (L : List ℂ) :
    Continuous (deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L) := by
  induction L with
  | nil => exact continuous_id
  | cons rho L ih =>
    exact (deningerMeyerCohomologyGenerator_continuous.sub
      (continuous_id.const_smul rho)).comp ih

theorem deningerMeyerFiniteXiCausalSection_continuous (S : Finset XiDivisorSupport) :
    Continuous (deningerMeyerFiniteXiCausalSection S) :=
  (deningerMeyerFiniteXiCausalSection S).continuous_of_finiteDimensional

theorem deningerMeyerFiniteXiOperatorLift_continuous (S : Finset XiDivisorSupport)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S)) :
    Continuous (deningerMeyerFiniteXiOperatorLift S B) :=
  (deningerMeyerFiniteXiCausalSection_continuous S).comp
    (B.continuous_of_finiteDimensional.comp (deningerMeyerFiniteXiJetPacketLM_continuous S))

/-- Every finite coupling acts continuously on the original quotient. -/
theorem deningerMeyerCoupledSourceOperator_continuous (S : Finset XiDivisorSupport)
    (L : List ℂ) (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S)) :
    Continuous (deningerMeyerCoupledSourceOperator S L B) :=
  (deningerMeyerGeneratorWord_continuous L).add
    (deningerMeyerFiniteXiOperatorLift_continuous S B)

end
end RHTower
