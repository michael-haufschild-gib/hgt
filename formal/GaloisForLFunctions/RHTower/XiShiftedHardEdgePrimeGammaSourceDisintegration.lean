import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCofinalLinearFiniteHankelDimension
import GaloisForLFunctions.RHTower.XiPolynomialGaussianExplicitFormula

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory Polynomial Set

noncomputable section

namespace RHTower

/-- Literal Gamma--polar--von-Mangoldt balance of a shifted-reversal heat packet. -/
def routeUShiftedCompletedPrimeGammaBalance
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ)
    (t : {τ : ℝ // 0 < τ}) : ℝ :=
  let Q := xiShiftedReversedPolynomial y d c
  (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x) +
    2 * Real.pi * (Q.eval (-(1 / 4 : ℝ))) ^ (2 : ℕ) * Real.exp (t.1 / 4) -
      (routeUPolynomialGaussianPrimeSource Q t).re

/-- The literal completed balance is exactly pi times the polynomial Xi heat trace. -/
theorem routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ)
    (t : {τ : ℝ // 0 < τ}) :
    routeUShiftedCompletedPrimeGammaBalance y d c t =
      Real.pi * xiPolynomialGaussianHeatTraceReal
        (xiShiftedReversedPolynomial y d c) t.1 := by
  exact (pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma
    (xiShiftedReversedPolynomial y d c) t).symm

/-- Positive-time Laplace disintegration of the literal completed source. -/
def routeUShiftedFilteredCompletedSourceKernel
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) (t : ℝ) : ℝ :=
  if ht : 0 < t then
    t ^ (2 * d) * Real.exp (-(y * t)) *
      routeUShiftedCompletedPrimeGammaBalance y d c ⟨t, ht⟩
  else 0

theorem routeUShiftedFilteredCompletedSourceKernel_eq
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ)
    {t : ℝ} (ht : 0 < t) :
    routeUShiftedFilteredCompletedSourceKernel y d c t =
      Real.pi * xiShiftedFilteredGammaKernelReal y 0 d c t := by
  rw [routeUShiftedFilteredCompletedSourceKernel, dif_pos ht,
    routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace,
    xiShiftedFilteredGammaKernelReal]
  ring

/-- Complete pre-divisor source capital of a shifted reciprocal Hankel packet. -/
def routeUShiftedFilteredCompletedSourceCapital
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), routeUShiftedFilteredCompletedSourceKernel y d c t

theorem integrableOn_routeUShiftedFilteredCompletedSourceKernel
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c : Fin (d + 1) → ℝ) :
    IntegrableOn (routeUShiftedFilteredCompletedSourceKernel y d c) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_xiShiftedFilteredGammaKernelReal hy 0 d c).const_mul Real.pi
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (routeUShiftedFilteredCompletedSourceKernel_eq y d c ht).symm

/-- Exact positive source disintegration of every shifted reciprocal Hankel quadratic. -/
theorem routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c : Fin (d + 1) → ℝ) :
    routeUShiftedFilteredCompletedSourceCapital y d c =
      Real.pi * ((2 * d).factorial : ℝ) *
        xiShiftedReciprocalHankelQuadratic y c := by
  calc
    routeUShiftedFilteredCompletedSourceCapital y d c =
        ∫ t in Ioi (0 : ℝ),
          Real.pi * xiShiftedFilteredGammaKernelReal y 0 d c t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact routeUShiftedFilteredCompletedSourceKernel_eq y d c ht
    _ = Real.pi * ∫ t in Ioi (0 : ℝ),
          xiShiftedFilteredGammaKernelReal y 0 d c t := by
      rw [integral_const_mul]
    _ = Real.pi * ((2 * d).factorial : ℝ) *
          xiShiftedReciprocalHankelQuadratic y c := by
      rw [integral_xiShiftedFilteredGammaKernelReal_eq_hankelQuadratic hy]
      ring

/-- Negative filtered capital contains an actual positive-time completed-source inversion. -/
theorem exists_routeUShiftedCompletedPrimeGammaBalance_neg_of_capital_neg
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ)
    (hcap : routeUShiftedFilteredCompletedSourceCapital y d c < 0) :
    ∃ t : {τ : ℝ // 0 < τ},
      routeUShiftedCompletedPrimeGammaBalance y d c t < 0 := by
  by_contra h
  push Not at h
  have hkernel : 0 ≤ routeUShiftedFilteredCompletedSourceCapital y d c := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    change (0 : ℝ) ≤ routeUShiftedFilteredCompletedSourceKernel y d c t
    rw [routeUShiftedFilteredCompletedSourceKernel, dif_pos ht]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg ht.le _) (Real.exp_nonneg _)) (h ⟨t, ht⟩)
  exact (not_lt_of_ge hkernel) hcap

/-- Every negative source capital has a pointwise inversion beyond the completed aperture. -/
theorem exists_routeUShiftedCompletedPrimeGammaBalance_neg_beyond_aperture
    {y : ℝ} (hy : 0 < y) (d : ℕ) (c : Fin (d + 1) → ℝ)
    (hcap : routeUShiftedFilteredCompletedSourceCapital y d c < 0) :
    ∃ t : {τ : ℝ // 0 < τ},
      routeUShiftedCompletedPrimeGammaBalance y d c t < 0 ∧
      routeUCompletedPrimeGammaAperture <
        t.1 * ((xiShiftedReversedPolynomial y d c).natDegree + 1) := by
  obtain ⟨t, hbalance⟩ :=
    exists_routeUShiftedCompletedPrimeGammaBalance_neg_of_capital_neg y d c hcap
  have hquad : xiShiftedReciprocalHankelQuadratic y c < 0 := by
    rw [routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic hy d c] at hcap
    have hfactor : 0 < Real.pi * ((2 * d).factorial : ℝ) := by positivity
    nlinarith
  have hc : c ≠ 0 := by
    intro hc
    rw [hc] at hquad
    simp [xiShiftedReciprocalHankelQuadratic] at hquad
  have hQ : xiShiftedReversedPolynomial y d c ≠ 0 :=
    xiShiftedReversedPolynomial_ne_zero y d c hc
  have htrace : xiPolynomialGaussianHeatTraceReal
      (xiShiftedReversedPolynomial y d c) t.1 < 0 := by
    rw [routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace] at hbalance
    nlinarith [Real.pi_pos]
  exact ⟨t, hbalance,
    xiPolynomialGaussianHeatTraceReal_negative_outside_completedAperture
      ⟨xiShiftedReversedPolynomial y d c, hQ⟩ t htrace⟩

/-- Reciprocal hard-edge lift after the shifted-reversal heat filter. -/
def routeUHardEdgeFilteredPolynomial (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedReversedPolynomial (a ^ (2 : ℕ))
    (xiHardEdgeReciprocalPolynomial a P).natDegree
    (xiHardEdgeLiftCoefficients a P)

/-- Degree-free Cauchy hard-edge density. -/
def routeUHardEdgeCauchyDensity (a : ℝ) (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  a ^ (2 : ℕ) / (a ^ (2 : ℕ) + x ^ (2 : ℕ)) *
    (P.eval ((a ^ (2 : ℕ) - x ^ (2 : ℕ)) / (a ^ (2 : ℕ) + x ^ (2 : ℕ)))) ^ (2 : ℕ)

/-- Exact cancellation of every admission-degree power in the hard-edge source density. -/
theorem routeUHardEdgeFilteredPolynomial_degree_cancellation
    {a : ℝ} (ha : 0 < a) (P : Polynomial ℝ) (x : ℝ) :
    a ^ (2 : ℕ) * (routeUHardEdgeFilteredPolynomial a P).eval (x ^ (2 : ℕ)) ^ (2 : ℕ) /
        (a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^
          (2 * (xiHardEdgeReciprocalPolynomial a P).natDegree + 1) =
      routeUHardEdgeCauchyDensity a P x := by
  let d := (xiHardEdgeReciprocalPolynomial a P).natDegree
  let c : Fin (d + 1) → ℝ := xiHardEdgeLiftCoefficients a P
  have hden : 0 < a ^ (2 : ℕ) + x ^ (2 : ℕ) := by positivity
  have hdenC : ((a ^ (2 : ℕ) : ℝ) : ℂ) + (x ^ (2 : ℕ) : ℝ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [pow_two, Complex.mul_re] at hre
    nlinarith
  have hsumC : ((a ^ (2 : ℕ) : ℝ) : ℂ) + (x ^ (2 : ℕ) : ℝ) =
      ((a ^ (2 : ℕ) + x ^ (2 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  have hQ := eval_xiShiftedReversedPolynomial_eq
    (a ^ (2 : ℕ)) d c ((x ^ (2 : ℕ) : ℝ) : ℂ) hdenC
  rw [show Polynomial.ofFn (d + 1) c = xiHardEdgeReciprocalPolynomial a P by
    exact ofFn_xiHardEdgeLiftCoefficients a P] at hQ
  rw [evalRealPolynomial_xiHardEdgeReciprocalPolynomial] at hQ
  have harg : (((2 * a ^ (2 : ℕ) : ℝ) : ℂ) *
        ((((a ^ (2 : ℕ) : ℝ) : ℂ) + (x ^ (2 : ℕ) : ℝ))⁻¹) - 1) =
      (((a ^ (2 : ℕ) - x ^ (2 : ℕ)) / (a ^ (2 : ℕ) + x ^ (2 : ℕ)) : ℝ) : ℂ) := by
    rw [hsumC]
    norm_cast
    field_simp [hden.ne']
    ring
  rw [harg, evalRealPolynomial_ofReal] at hQ
  rw [hsumC] at hQ
  simp only [evalRealPolynomial_ofReal] at hQ
  norm_cast at hQ
  have hQreal : (routeUHardEdgeFilteredPolynomial a P).eval (x ^ (2 : ℕ)) =
      (a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ d *
        P.eval ((a ^ (2 : ℕ) - x ^ (2 : ℕ)) / (a ^ (2 : ℕ) + x ^ (2 : ℕ))) := by
    simpa [routeUHardEdgeFilteredPolynomial, d, c] using hQ
  rw [hQreal]
  simp only [routeUHardEdgeCauchyDensity]
  field_simp [hden.ne']
  ring

/-- Explicit degree of the cofinal source packet. -/
def routeUExplicitFinitePrimeGammaDegree
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) : ℕ :=
  (xiHardEdgeReciprocalPolynomial (routeUHardEdgeMass (k : ℝ))
    (routeUExplicitFiniteChebyshevPacket n k
      (routeUXiHeatPhysicalReal P t))).natDegree

/-- Exact coefficient vector of the cofinal source packet. -/
def routeUExplicitFinitePrimeGammaCoefficients
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) :
    Fin (routeUExplicitFinitePrimeGammaDegree P t n k + 1) → ℝ :=
  xiHardEdgeLiftCoefficients (routeUHardEdgeMass (k : ℝ))
    (routeUExplicitFiniteChebyshevPacket n k (routeUXiHeatPhysicalReal P t))

/-- Literal completed balance at one heat time for the explicit cofinal packet. -/
def routeUExplicitFinitePrimeGammaBalance
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ)
    (s : {σ : ℝ // 0 < σ}) : ℝ :=
  routeUShiftedCompletedPrimeGammaBalance
    (routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ))
    (routeUExplicitFinitePrimeGammaDegree P t n k)
    (routeUExplicitFinitePrimeGammaCoefficients P t n k) s

/-- Complete source capital of the explicit cofinal packet. -/
def routeUExplicitFinitePrimeGammaCapital
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) : ℝ :=
  routeUShiftedFilteredCompletedSourceCapital
    (routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ))
    (routeUExplicitFinitePrimeGammaDegree P t n k)
    (routeUExplicitFinitePrimeGammaCoefficients P t n k)

theorem routeUExplicitFinitePrimeGammaCapital_eq_hankelQuadratic
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) :
    routeUExplicitFinitePrimeGammaCapital P t n k =
      Real.pi *
        ((2 * routeUExplicitFinitePrimeGammaDegree P t n k).factorial : ℝ) *
          routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k := by
  rw [routeUExplicitFinitePrimeGammaCapital,
    routeUShiftedFilteredCompletedSourceCapital_eq_hankelQuadratic
      (sq_pos_of_pos (routeUHardEdgeMass_pos (k : ℝ)))]
  rfl

/-- Closed false-RH phase retaining an actual source inversion at every cofinal mass. -/
def XiShiftedHardEdgeCofinalPrimeGammaInversionPhase : Prop :=
  ∃ (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n K : ℕ),
    ∀ k : ℕ, K ≤ k →
      routeUExplicitFinitePrimeGammaCapital P t n k < 0 ∧
      (∃ s : {σ : ℝ // 0 < σ},
        routeUExplicitFinitePrimeGammaBalance P t n k s < 0 ∧
        routeUCompletedPrimeGammaAperture <
          s.1 * ((xiShiftedReversedPolynomial
            (routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ))
            (routeUExplicitFinitePrimeGammaDegree P t n k)
            (routeUExplicitFinitePrimeGammaCoefficients P t n k)).natDegree + 1)) ∧
      routeUHardEdgeMass (k : ℝ) ^ (2 : ℕ) <
        routeUParabolicDegreeHorizon *
          (routeUExplicitFiniteHankelSize n k (routeUXiHeatPhysicalReal P t) : ℝ) ^ (2 : ℕ) ∧
      routeUExplicitFiniteHankelSize n k (routeUXiHeatPhysicalReal P t) ≤
        (n + 1) * (k + 1) + 2

/-- False RH is exactly a cofinal fixed-carrier family of literal prime--Gamma inversions. -/
theorem not_rh_iff_xiShiftedHardEdgeCofinalPrimeGammaInversionPhase :
    ¬ RiemannHypothesis ↔ XiShiftedHardEdgeCofinalPrimeGammaInversionPhase := by
  rw [not_rh_iff_xiShiftedHardEdgeCofinalLinearNegativePhase]
  constructor
  · rintro ⟨P, t, n, K, hphase⟩
    refine ⟨P, t, n, K, fun k hk => ?_⟩
    obtain ⟨hquad, hlower, hupper⟩ := hphase k hk
    have hcapital : routeUExplicitFinitePrimeGammaCapital P t n k < 0 := by
      rw [routeUExplicitFinitePrimeGammaCapital_eq_hankelQuadratic]
      have hfactor : 0 < Real.pi *
          ((2 * routeUExplicitFinitePrimeGammaDegree P t n k).factorial : ℝ) := by
        positivity
      nlinarith
    have hinversion :=
      exists_routeUShiftedCompletedPrimeGammaBalance_neg_beyond_aperture
        (sq_pos_of_pos (routeUHardEdgeMass_pos (k : ℝ)))
        (routeUExplicitFinitePrimeGammaDegree P t n k)
        (routeUExplicitFinitePrimeGammaCoefficients P t n k) hcapital
    exact ⟨hcapital, hinversion, hlower, hupper⟩
  · rintro ⟨P, t, n, K, hphase⟩
    refine ⟨P, t, n, K, fun k hk => ?_⟩
    obtain ⟨hcapital, _hinversion, hlower, hupper⟩ := hphase k hk
    have hquad :
        routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k < 0 := by
      rw [routeUExplicitFinitePrimeGammaCapital_eq_hankelQuadratic] at hcapital
      have hfactor : 0 < Real.pi *
          ((2 * routeUExplicitFinitePrimeGammaDegree P t n k).factorial : ℝ) := by
        positivity
      nlinarith
    exact ⟨hquad, hlower, hupper⟩

/-- Premise-free source-side hard-edge phase dichotomy. -/
theorem riemannHypothesis_or_xiShiftedHardEdgeCofinalPrimeGammaInversionPhase :
    RiemannHypothesis ∨ XiShiftedHardEdgeCofinalPrimeGammaInversionPhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (not_rh_iff_xiShiftedHardEdgeCofinalPrimeGammaInversionPhase.mp hRH)

end RHTower
