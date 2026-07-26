import GaloisForLFunctions.HTGeometry.HankelGuardrailConsequences
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.ThetaFirstGibbsSupportHavilandUniversalityLaw

/-!
# Theta first-Gibbs finite-observation Haviland horizon

The complete first theta-Gibbs sequence satisfies exact support-Haviland positivity, but every
finite prefix admits an arbitrarily delayed continuation with a negative square test and no
positive representing measure.
-/

open MeasureTheory Polynomial

namespace RHTower

noncomputable section

/-- The first theta-Gibbs moment sequence has strictly positive total mass. -/
theorem thetaCuspFirstAtomLiouvilleGibbsMoment_zero_pos :
    0 < thetaCuspLiouvilleGibbsMoment 0 1 := by
  have horientation :=
    exp_neg_pi_lt_two_pi_mul_firstLiouvilleGibbsMoment_zero
  have hexp : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  nlinarith

/-- Complete positivity together with failure of every finite prefix to certify it. -/
structure ThetaFirstGibbsFiniteObservationHavilandHorizonCertificate : Prop where
  fullSupportHaviland : ThetaFirstGibbsSupportHavilandCertificate
  finiteObservationHorizon :
    ∀ (N n : ℕ), N < n →
      ∃ b : ℕ → ℝ,
        (∀ k (_hk : k ≤ N),
          b k = thetaCuspLiouvilleGibbsMoment k 1) ∧
        HTGeometry.momentFunctional b
            (((1 : Polynomial ℝ) - (2 : ℝ) • X ^ n) ^ 2) < 0 ∧
        ¬ ∃ μ : Measure ℝ,
          (∀ k, b k = ∫ x, x ^ k ∂μ) ∧
          (∀ k, Integrable (fun x : ℝ => x ^ k) μ)

/-- **Theta first-Gibbs finite-observation Haviland-horizon universality.**

The true full sequence is support-Haviland positive, but no finite prefix can distinguish it from
an arbitrarily delayed continuation that fails a polynomial-square test. -/
theorem thetaFirstGibbs_finiteObservationHavilandHorizonUniversality :
    ThetaFirstGibbsFiniteObservationHavilandHorizonCertificate := by
  refine
    { fullSupportHaviland := thetaFirstGibbs_supportHavilandUniversality
      finiteObservationHorizon := ?_ }
  intro N n hn
  let a : Fin (N + 1) → ℝ :=
    fun k => thetaCuspLiouvilleGibbsMoment k 1
  let b : ℕ → ℝ := HTGeometry.badMomentContinuation N n a
  refine ⟨b, ?_, ?_, ?_⟩
  · intro k hk
    exact HTGeometry.badMomentContinuation_prefix N n a k hk
  · rw [HTGeometry.momentFunctional_one_sub_two_X_pow_square,
      HTGeometry.badMomentContinuation_delayedSquareTest N n a hn]
    dsimp only [a]
    nlinarith [thetaCuspFirstAtomLiouvilleGibbsMoment_zero_pos]
  · exact HTGeometry.badMomentContinuation_not_momentSequence N n a
      thetaCuspFirstAtomLiouvilleGibbsMoment_zero_pos hn

end

end RHTower
