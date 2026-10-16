import GaloisForLFunctions.RHTower.DeningerMeyerExponentialSolvability

/-! # Exponential gauges retain all arithmetic multiplicity slots

The actual source action has its full triangular derivative formula. This
proves finite spectral-support preservation without assuming simple zeros
or an arbitrary infinite packet synthesis theorem.
-/

open Complex
namespace RHTower
noncomputable section

theorem deningerMeyerXiSupportJetEvaluationLM_sourceGauge
    (g : DeningerMeyerStrongLogTarget) (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiSupportJetEvaluationLM rho k (deningerMeyerCohomologySourceGauge g u) =
      ∑ i ∈ Finset.range (k.val+1), (k.val.choose i : ℂ) *
        iteratedDeriv i (fun s => Complex.exp (deningerMeyerStrongLogMellin g s)) (rho : ℂ) *
        deningerMeyerXiSupportJetEvaluationLM rho
          ⟨k.val-i, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ u := by
  induction u using Submodule.Quotient.induction_on with
  | H h =>
    simp only [deningerMeyerCohomologySourceGauge_mk,
      deningerMeyerXiSupportJetEvaluationLM_mk,
      deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
    have he : deningerMeyerStrongLogMellin (deningerMeyerSourceGauge g h) =
        (fun s => Complex.exp (deningerMeyerStrongLogMellin g s)) *
          deningerMeyerStrongLogMellin h :=
      funext (deningerMeyerSourceGauge_mellin g h)
    rw [he]
    have hg : ContDiff ℂ (k.val : WithTop ℕ∞)
        (fun s => Complex.exp (deningerMeyerStrongLogMellin g s)) :=
      ((deningerMeyerStrongLogMellin_entireRegular g).differentiable.cexp).contDiff.of_le le_top
    have hh : ContDiff ℂ (k.val : WithTop ℕ∞) (deningerMeyerStrongLogMellin h) :=
      (deningerMeyerStrongLogMellin_entireRegular h).differentiable.contDiff.of_le le_top
    rw [iteratedDeriv_mul hg.contDiffAt hh.contDiffAt]

theorem deningerMeyerSourceGauge_preserves_zero_packet
    (g : DeningerMeyerStrongLogTarget) (rho : XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : ∀ j, deningerMeyerXiSupportJetEvaluationLM rho j u = 0) :
    ∀ j, deningerMeyerXiSupportJetEvaluationLM rho j
      (deningerMeyerCohomologySourceGauge g u) = 0 := by
  intro j
  rw [deningerMeyerXiSupportJetEvaluationLM_sourceGauge]
  simp only [hu, mul_zero, Finset.sum_const_zero]

/-- No full local packet is erased or created by the nonlinear source gauge. -/
theorem deningerMeyerSourceGauge_zero_packet_iff
    (g : DeningerMeyerStrongLogTarget) (rho : XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    (∀ j, deningerMeyerXiSupportJetEvaluationLM rho j
      (deningerMeyerCohomologySourceGauge g u) = 0) ↔
      ∀ j, deningerMeyerXiSupportJetEvaluationLM rho j u = 0 := by
  refine ⟨fun h => ?_, deningerMeyerSourceGauge_preserves_zero_packet g rho u⟩
  have h' := deningerMeyerSourceGauge_preserves_zero_packet (-g) rho _ h
  have he := (deningerMeyerCohomologySourceGaugeEquiv g).symm_apply_apply u
  change deningerMeyerCohomologySourceGauge (-g) (deningerMeyerCohomologySourceGauge g u) = u at he
  simpa only [he] using h'

end
end RHTower
