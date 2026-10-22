import GaloisForLFunctions.HTGeometry.TraceZeroNonrealDivisorMicroblock
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKreinRealDivisorRigidity

/-!
# Actual finite theta numerator divisor rigidity

The actual signed theta determinants already converge compact-open to normalized Xi.  Therefore
real divisors at every actual finite stage imply RH.  Unconditionally, either RH holds or one of
those actual stages has a nonreal zero.

The companion microblock theorem records why finite support, trace zero, and Hilbert--Schmidt
convergence cannot prove the missing real-divisor assertion: arbitrarily small traceless blocks
can carry nonreal zeros at radii escaping to infinity.
-/

open Complex Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Real divisor at every actual signed theta numerator stage. -/
def ThetaSourceSignedAllStagesRealDivisor : Prop :=
  ∀ k : ℕ, ThetaSourceSignedStageRealDivisor k

/-- The requested actual finite-stage real-divisor assertion already proves RH. -/
theorem riemannHypothesis_of_thetaSourceSignedAllStagesRealDivisor
    (hreal : ThetaSourceSignedAllStagesRealDivisor) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_thetaSourceKreinDouble_realDivisor
  intro k
  exact (thetaSourceKreinDoubleStageRealDivisor_iff_signed k).2 (hreal k)

/-- Sharp unconditional classification of the actual finite theta numerators. -/
theorem riemannHypothesis_or_thetaSourceSignedOrdinaryDet_nonrealStage :
    RiemannHypothesis ∨
      ∃ k : ℕ, ∃ z : ℂ,
        thetaSourceSignedOrdinaryDet k z = 0 ∧ z.im ≠ 0 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    have hnot : ¬ ThetaSourceSignedAllStagesRealDivisor := by
      intro hreal
      exact hRH (riemannHypothesis_of_thetaSourceSignedAllStagesRealDivisor hreal)
    simp only [ThetaSourceSignedAllStagesRealDivisor,
      ThetaSourceSignedStageRealDivisor, not_forall] at hnot
    rcases hnot with ⟨k, z, hzero, him⟩
    exact ⟨k, z, hzero, him⟩

/-- Closed boundary certificate: exact actual-stage dichotomy plus the local mechanism showing
why trace-zero Hilbert--Schmidt approximation alone cannot select its real-divisor branch. -/
theorem thetaSourceActualFiniteDivisorRigidity_certificate :
    (RiemannHypothesis ∨
      ∃ k : ℕ, ∃ z : ℂ,
        thetaSourceSignedOrdinaryDet k z = 0 ∧ z.im ≠ 0) ∧
    (ThetaSourceSignedAllStagesRealDivisor → RiemannHypothesis) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ),
        HilbertSchmidt.IsHS (fun p => M p.1 p.2) ∧
        HilbertSchmidt.hsTraceDiag (fun p => M p.1 p.2) = 0 ∧
        HilbertSchmidt.hsNorm (fun p => M p.1 p.2) < ε ∧
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z • M).det = 0 ∧
        z.im ≠ 0) := by
  exact ⟨riemannHypothesis_or_thetaSourceSignedOrdinaryDet_nonrealStage,
    riemannHypothesis_of_thetaSourceSignedAllStagesRealDivisor,
    exists_arbitrarilySmall_traceZero_nonrealDivisorMicroblock⟩

end
end RHTower.HedenmalmThetaSource
