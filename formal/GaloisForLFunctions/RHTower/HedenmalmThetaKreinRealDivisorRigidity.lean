import GaloisForLFunctions.RHTower.HedenmalmThetaKreinTracePolarization

/-!
# Real-divisor rigidity of the theta-source Krein double

The hyperbolic Krein double preserves every holomorphic source trace and carries an escaping
indefinite polarization, but its determinant is the source determinant times its Schwarz
reflection.  This file proves the exact stagewise consequence: the double has only real zeros if
and only if the original chiral source determinant has only real zeros.  Thus doubling cannot
hide a nonreal source divisor inside a conjugate pair.

Combined with compact-open convergence of the chiral determinant, real divisors at every doubled
stage imply RH.  The final closed alternative is unconditional: either RH holds, or some genuine
trace-preserving, coercively polarized Krein stage has a nonreal zero.
-/

open Complex Filter Matrix Metric Set Topology
open scoped Matrix

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Real-zero property of the original chiral source determinant at one finite stage. -/
def ThetaSourceSignedStageRealDivisor (k : ℕ) : Prop :=
  ∀ z : ℂ, thetaSourceSignedOrdinaryDet k z = 0 → z.im = 0

/-- Real-zero property of the full hyperbolic Krein determinant at one finite stage. -/
def ThetaSourceKreinDoubleStageRealDivisor (k : ℕ) : Prop :=
  ∀ z : ℂ, thetaSourceKreinDoubleDet k z = 0 → z.im = 0

/-- Schwarz doubling has a real divisor exactly when its chiral source factor does. -/
theorem thetaSourceKreinDoubleStageRealDivisor_iff_signed
    (k : ℕ) :
    ThetaSourceKreinDoubleStageRealDivisor k ↔
      ThetaSourceSignedStageRealDivisor k := by
  constructor
  · intro hdouble z hz
    apply hdouble z
    rw [thetaSourceKreinDoubleDet_eq_source_mul_reflected]
    exact mul_eq_zero.mpr (Or.inl hz)
  · intro hsigned z hz
    rw [thetaSourceKreinDoubleDet_eq_source_mul_reflected] at hz
    rcases mul_eq_zero.mp hz with hsource | hreflected
    · exact hsigned z hsource
    · have hconj :
        thetaSourceSignedOrdinaryDet k ((starRingEnd ℂ) z) = 0 := by
        apply (map_eq_zero (starRingEnd ℂ)).mp
        simpa [thetaSourceSignedReflectedOrdinaryDet] using hreflected
      have him := hsigned ((starRingEnd ℂ) z) hconj
      simpa using him

/-- Real divisors for all full Krein stages force RH.  Trace retention, Krein adjointness,
coercive escape, and compact-open convergence are already unconditional; this is the exact
remaining divisor implication. -/
theorem riemannHypothesis_of_thetaSourceKreinDouble_realDivisor
    (hreal : ∀ k, ThetaSourceKreinDoubleStageRealDivisor k) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_thetaSourceKreinChiralXiCandidate_realDivisor
  intro k z hz
  have hsource : thetaSourceSignedOrdinaryDet k z = 0 := by
    unfold thetaSourceKreinChiralXiCandidate at hz
    exact (mul_eq_zero.mp hz).resolve_left XiC_zero_ne
  exact (thetaSourceKreinDoubleStageRealDivisor_iff_signed k).mp
    (hreal k) z hsource

/-- Closed real-divisor lock for the actual trace-preserving Krein construction. -/
theorem riemannHypothesis_or_thetaSourceKreinDouble_nonrealStage :
    RiemannHypothesis ∨
      ∃ k : ℕ, ∃ z : ℂ,
        thetaSourceKreinDoubleDet k z = 0 ∧ z.im ≠ 0 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    by_contra hnone
    push Not at hnone
    apply hRH
    apply riemannHypothesis_of_thetaSourceKreinDouble_realDivisor
    intro k z hz
    exact hnone k z hz

/-- The complete unconditional Krein data and its sharp divisor alternative. -/
theorem thetaSourceKreinRealDivisorRigidity_certificate :
    (∀ k, thetaSourceEscapingKreinPolarization k * thetaSourceKreinDouble k =
      (thetaSourceKreinDouble k)ᴴ * thetaSourceEscapingKreinPolarization k) ∧
    (∀ k m, (thetaSourceKreinChiralWeight k *
        (thetaSourceKreinDouble k) ^ m).trace =
      ((thetaSourceKreinFiniteMatrix k) ^ m).trace) ∧
    TendstoLocallyUniformly thetaSourceKreinDoubleDet
      (fun z => (XiC z / XiC 0) ^ (2 : ℕ)) atTop ∧
    (∀ k,
      ThetaSourceKreinDoubleStageRealDivisor k ↔
        ThetaSourceSignedStageRealDivisor k) ∧
    (RiemannHypothesis ∨
      ∃ k : ℕ, ∃ z : ℂ,
        thetaSourceKreinDoubleDet k z = 0 ∧ z.im ≠ 0) := by
  exact ⟨thetaSourceKreinDouble_metricAdjoint,
    thetaSourceKreinChiralWeight_trace_pow,
    thetaSourceKreinDoubleDet_tendstoLocallyUniformly_XiC_sq,
    thetaSourceKreinDoubleStageRealDivisor_iff_signed,
    riemannHypothesis_or_thetaSourceKreinDouble_nonrealStage⟩

end

end RHTower.HedenmalmThetaSource
