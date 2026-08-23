import GaloisForLFunctions.RHTower.PrimeArchXiCompactThorinRH
import GaloisForLFunctions.RHTower.SeamJetFunctionComplete
import GaloisForLFunctions.RHTower.XiTraceHankelCriterion
import GaloisForLFunctions.HTGeometry.AffineFluxTaylorCoeff

open Complex Filter MeasureTheory Polynomial Set Topology
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Entire square quotient in the card's unrotated coordinate `w = s - 1/2`. -/
def canonicalXiSeamQuotient (z : ℂ) : ℂ :=
  xiSquaredSeamEntireQuotient (-z)

/-- The unrotated quotient recovers `xi (1/2 + w)` after the square substitution. -/
theorem canonicalXiSeamQuotient_sq (w : ℂ) :
    canonicalXiSeamQuotient (w ^ 2) = xi (1 / 2 + w) := by
  calc
    canonicalXiSeamQuotient (w ^ 2) =
        xiSquaredSeamEntireQuotient ((-I * w) ^ 2) := by
          unfold canonicalXiSeamQuotient
          congr 1
          rw [mul_pow]
          simp [I_sq]
    _ = XiC (-I * w) := xiSquaredSeamEntireQuotient_sq (-I * w)
    _ = xi (1 / 2 + w) := by
      rw [XiC]
      congr 1
      calc
        1 / 2 + -I * w * I = 1 / 2 + -(I * I) * w := by ring
        _ = 1 / 2 + w := by rw [I_mul_I]; ring

/-- Uniqueness of the entire quotient is already forced pointwise by the square map. -/
theorem canonicalXiSeamQuotient_unique
    {F : ℂ → ℂ} (hF : ∀ w : ℂ, F (w ^ 2) = xi (1 / 2 + w)) :
    F = canonicalXiSeamQuotient := by
  funext z
  let w : ℂ := Complex.sqrt z
  have hw : w ^ 2 = z :=
    GaloisForLFunctions.HTGeometry.complex_sqrt_sq z
  calc
    F z = F (w ^ 2) := by rw [hw]
    _ = xi (1 / 2 + w) := hF w
    _ = canonicalXiSeamQuotient (w ^ 2) :=
      (canonicalXiSeamQuotient_sq w).symm
    _ = canonicalXiSeamQuotient z := by rw [hw]

theorem differentiable_canonicalXiSeamQuotient :
    Differentiable ℂ canonicalXiSeamQuotient := by
  exact differentiable_xiSquaredSeamEntireQuotient.comp (by fun_prop)

theorem canonicalXiSeamQuotient_zero_ne :
    canonicalXiSeamQuotient 0 ≠ 0 := by
  have h := canonicalXiSeamQuotient_sq 0
  norm_num at h
  rw [h]
  simpa [XiC] using XiC_zero_ne

/-- Canonical seam logarithm in the unrotated square coordinate of the completed xi function. -/
def canonicalXiSeamLog (z : ℂ) : ℂ :=
  Complex.log
    (canonicalXiSeamQuotient z / canonicalXiSeamQuotient 0)

theorem analyticAt_canonicalXiSeamLog :
    AnalyticAt ℂ canonicalXiSeamLog 0 := by
  have hratio : AnalyticAt ℂ (fun z : ℂ =>
      canonicalXiSeamQuotient z / canonicalXiSeamQuotient 0) 0 :=
    (differentiable_canonicalXiSeamQuotient.analyticAt 0).div_const
  have hvalue : canonicalXiSeamQuotient 0 / canonicalXiSeamQuotient 0 = 1 :=
    div_self canonicalXiSeamQuotient_zero_ne
  exact hratio.clog (by rw [hvalue]; exact Complex.one_mem_slitPlane)

@[simp] theorem canonicalXiSeamLog_zero : canonicalXiSeamLog 0 = 0 := by
  rw [canonicalXiSeamLog, div_self canonicalXiSeamQuotient_zero_ne,
    Complex.log_one]

theorem completedSeamSourceLogExponent_neg (z : ℂ) :
    completedSeamSourceLogExponent (-z) = -2 * canonicalXiSeamLog z := by
  simp only [completedSeamSourceLogExponent, canonicalXiSeamLog,
    canonicalXiSeamQuotient, xiSquaredSeamCassiniSource]
  apply congrArg (fun u : ℂ => -2 * Complex.log u)
  congr 1
  all_goals ring_nf

/-- The card's literal generating function `2 L'(-z)`. -/
def canonicalXiSeamLogGeneratingFunction (z : ℂ) : ℂ :=
  2 * deriv canonicalXiSeamLog (-z)

theorem completedSeamMomentGerm_eventuallyEq_canonicalXiSeamLogGeneratingFunction :
    completedSeamMomentGerm =ᶠ[𝓝 0]
      canonicalXiSeamLogGeneratingFunction := by
  have hsource := deriv_completedSeamSourceLogExponent_eventuallyEq_momentGerm
  filter_upwards [hsource] with z hz
  rw [← hz, canonicalXiSeamLogGeneratingFunction]
  have hfun : completedSeamSourceLogExponent =
      fun w : ℂ => -2 * canonicalXiSeamLog (-w) := by
    funext w
    simpa using completedSeamSourceLogExponent_neg (-w)
  rw [hfun]
  have hconst := congrFun
    (GaloisForLFunctions.iteratedDeriv_const_mul_field
      (-2 : ℂ) (fun w : ℂ => canonicalXiSeamLog (-w)) 1) z
  simp only [iteratedDeriv_one] at hconst
  rw [hconst]
  have hneg := GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
    canonicalXiSeamLog 1 (by norm_num : (-1 : ℂ) ≠ 0) z
  simp only [iteratedDeriv_one, one_mul, neg_mul] at hneg
  rw [hneg]
  ring

/-- Positive-degree Taylor coefficients of the canonical seam logarithm. -/
def canonicalXiSeamLogCoeff (k : ℕ) : ℂ :=
  seamLogCoeff canonicalXiSeamLog k

/-- Card normalization `Tₖ = -2 k (-1)ᵏ ellₖ`. -/
def canonicalXiSeamLogMoment (k : ℕ) : ℂ :=
  -2 * (k : ℂ) * (-1 : ℂ) ^ k * canonicalXiSeamLogCoeff k

theorem canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment (n : ℕ) :
    canonicalXiSeamLogMoment (n + 1) =
      (normalizedPrimeArchMoment n : ℂ) := by
  have hjet :=
    deriv_completedSeamSourceLogExponent_eventuallyEq_momentGerm.iteratedDeriv_eq n
  rw [← iteratedDeriv_succ'] at hjet
  rw [iteratedDeriv_completedSeamMomentGerm] at hjet
  have hfun : completedSeamSourceLogExponent =
      fun w : ℂ => -2 * canonicalXiSeamLog (-w) := by
    funext w
    simpa using completedSeamSourceLogExponent_neg (-w)
  rw [hfun] at hjet
  rw [congrFun
    (GaloisForLFunctions.iteratedDeriv_const_mul_field
      (-2 : ℂ) (fun w : ℂ => canonicalXiSeamLog (-w)) (n + 1)) 0] at hjet
  have hnegfun : (fun w : ℂ => canonicalXiSeamLog (-w)) =
      fun w : ℂ => canonicalXiSeamLog ((-1 : ℂ) * w) := by
    funext w
    congr 1
    ring
  rw [hnegfun] at hjet
  rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
    canonicalXiSeamLog (n + 1) (by norm_num : (-1 : ℂ) ≠ 0) 0] at hjet
  simp only [neg_mul, mul_zero] at hjet
  unfold canonicalXiSeamLogMoment canonicalXiSeamLogCoeff seamLogCoeff
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  calc
    -2 * (↑(n + 1) : ℂ) * (-1) ^ (n + 1) *
          ((↑(n + 1).factorial : ℂ)⁻¹ *
            iteratedDeriv (n + 1) canonicalXiSeamLog 0) =
        (-2 * (-1) ^ (n + 1) *
          iteratedDeriv (n + 1) canonicalXiSeamLog 0) /
            (↑n.factorial : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp [hfac, hn]
    _ = (normalizedPrimeArchMoment n : ℂ) := by
      rw [show -2 * (-1 : ℂ) ^ (n + 1) *
          iteratedDeriv (n + 1) canonicalXiSeamLog 0 =
            (↑n.factorial : ℂ) * (normalizedPrimeArchMoment n : ℂ) by
        simpa only [neg_mul, mul_assoc] using hjet]
      field_simp [hfac]

/-- Every Taylor jet of `G_src = 2 L'(-z)` is the corresponding shifted source moment. -/
theorem iteratedDeriv_canonicalXiSeamLogGeneratingFunction (n : ℕ) :
    iteratedDeriv n canonicalXiSeamLogGeneratingFunction 0 =
      ((Nat.factorial n : ℕ) : ℂ) * canonicalXiSeamLogMoment (n + 1) := by
  have hjet :=
    completedSeamMomentGerm_eventuallyEq_canonicalXiSeamLogGeneratingFunction.iteratedDeriv_eq n
  calc
    iteratedDeriv n canonicalXiSeamLogGeneratingFunction 0 =
        iteratedDeriv n completedSeamMomentGerm 0 := hjet.symm
    _ = ((Nat.factorial n : ℕ) : ℂ) * normalizedPrimeArchMoment n :=
      iteratedDeriv_completedSeamMomentGerm n
    _ = ((Nat.factorial n : ℕ) : ℂ) * canonicalXiSeamLogMoment (n + 1) := by
      rw [canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment]

theorem normalizedPrimeArchMoment_coe_eq_xiCentralReciprocalMoment (n : ℕ) :
    (normalizedPrimeArchMoment n : ℂ) = xiCentralReciprocalMoment n := by
  simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
    primeArchSourceMoment_eq_xiCentralReciprocalMoment n

/-- Literal finite Hankel pairing formed from the canonical seam-log tower. -/
def canonicalXiSeamLogTraceHankel (p : Polynomial ℝ) : ℂ :=
  ∑ k ∈ Finset.range (((p.map (algebraMap ℝ ℂ)) ^ 2).natDegree + 1),
    ((p.map (algebraMap ℝ ℂ)) ^ 2).coeff k *
      canonicalXiSeamLogMoment (k + 1)

theorem canonicalXiSeamLogTraceHankel_eq_xiCentralTraceHankel
    (p : Polynomial ℝ) :
    canonicalXiSeamLogTraceHankel p = xiCentralTraceHankel p := by
  rw [canonicalXiSeamLogTraceHankel, xiCentralTraceHankel_eq_moment_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment,
    normalizedPrimeArchMoment_coe_eq_xiCentralReciprocalMoment]

/-- Full real-polynomial Hankel positivity of the literal seam-log coefficients. -/
def CanonicalXiSeamLogTraceHankelNonnegative : Prop :=
  ∀ p : Polynomial ℝ, 0 ≤ (canonicalXiSeamLogTraceHankel p).re

/-- Canonical seam-log Hankel positivity is exactly RH. -/
theorem canonicalXiSeamLogTraceHankelNonnegative_iff_riemannHypothesis :
    CanonicalXiSeamLogTraceHankelNonnegative ↔ RiemannHypothesis := by
  rw [← xiCentralTraceHankelNonnegative_iff_riemannHypothesis]
  constructor
  · intro h p
    rw [← canonicalXiSeamLogTraceHankel_eq_xiCentralTraceHankel]
    exact h p
  · intro h p
    rw [canonicalXiSeamLogTraceHankel_eq_xiCentralTraceHankel]
    exact h p

/-- Compact positive Markov representation of the card's literal seam-log generating function. -/
def CanonicalXiSeamLogCompactMarkovRepresentation : Prop :=
  ∃ (μ : Measure ℝ) (B : ℝ),
    IsFiniteMeasure μ ∧
    0 < B ∧
    (∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ B) ∧
    canonicalXiSeamLogGeneratingFunction =ᶠ[𝓝 0] compactMarkovTransform μ

theorem canonicalXiSeamLogCompactMarkovRepresentation_iff_primeArch :
    CanonicalXiSeamLogCompactMarkovRepresentation ↔
      PrimeArchCompactMarkovGermRepresentation := by
  constructor
  · rintro ⟨μ, B, hfinite, hB, hsupport, hgerm⟩
    exact ⟨μ, B, hfinite, hB, hsupport,
      completedSeamMomentGerm_eventuallyEq_canonicalXiSeamLogGeneratingFunction.trans hgerm⟩
  · rintro ⟨μ, B, hfinite, hB, hsupport, hgerm⟩
    exact ⟨μ, B, hfinite, hB, hsupport,
      completedSeamMomentGerm_eventuallyEq_canonicalXiSeamLogGeneratingFunction.symm.trans hgerm⟩

/-- Literal seam-log compact Markov representation is exactly RH. -/
theorem canonicalXiSeamLogCompactMarkovRepresentation_iff_riemannHypothesis :
    CanonicalXiSeamLogCompactMarkovRepresentation ↔ RiemannHypothesis := by
  rw [canonicalXiSeamLogCompactMarkovRepresentation_iff_primeArch,
    primeArchCompactMarkovGermRepresentation_iff_riemannHypothesis]

/-- Under RH, the representing measure is the canonical weighted reciprocal-divisor measure. -/
theorem canonicalXiSeamLogGeneratingFunction_eventuallyEq_canonicalMarkov_of_rh
    (hRH : RiemannHypothesis) :
    canonicalXiSeamLogGeneratingFunction =ᶠ[𝓝 0]
      compactMarkovTransform primeArchXiCompactMomentMeasure :=
  completedSeamMomentGerm_eventuallyEq_canonicalXiSeamLogGeneratingFunction.symm.trans
    (completedSeamMomentGerm_eventuallyEq_primeArchXiCompactMarkovTransform_of_rh hRH)

/-- Markov and Hankel formulations of the canonical seam-log wall are equivalent. -/
theorem canonicalXiSeamLogCompactMarkovRepresentation_iff_hankelNonnegative :
    CanonicalXiSeamLogCompactMarkovRepresentation ↔
      CanonicalXiSeamLogTraceHankelNonnegative := by
  rw [canonicalXiSeamLogCompactMarkovRepresentation_iff_riemannHypothesis,
    canonicalXiSeamLogTraceHankelNonnegative_iff_riemannHypothesis]

end

end RHTower
