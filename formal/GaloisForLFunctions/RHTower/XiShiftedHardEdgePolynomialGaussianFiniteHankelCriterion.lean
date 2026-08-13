import GaloisForLFunctions.RHTower.XiShiftedHardEdgePolynomialGaussianCompactTransfer
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeFiniteHankelWitness

/-!
# Finite-Hankel criterion from the Route-U polynomial--Gaussian carrier

The complex compact-transfer theorem and exact hard-edge finite lift compose without loss:
every negative polynomial--Gaussian Xi heat trace produces a negative explicit finite shifted
reciprocal Hankel quadratic. Conversely any such negative quadratic contradicts RH. Consequently
RH is equivalent to nonnegativity of the complete explicit Route-U polynomial--Gaussian finite
Hankel family.
-/

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter

noncomputable section

namespace RHTower


/-- Exact finite Hankel scalar produced by the polynomial--Gaussian Route-U compact packet. -/
def routeUPolynomialGaussianFiniteHankelQuadratic
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k N : ℕ) : ℝ :=
  xiShiftedReciprocalHankelQuadratic
    (routeUHardEdgeMass (k : ℝ) ^ 2)
    (xiHardEdgeLiftCoefficients (routeUHardEdgeMass (k : ℝ))
      (routeUFiniteChebyshevPacketPolynomial n
        (routeUXiHeatPhysicalReal P t) (k : ℝ) N))

theorem exists_negative_routeUPolynomialGaussianFiniteHankelQuadratic_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ})
      (n k N : ℕ),
      routeUPolynomialGaussianFiniteHankelQuadratic P t n k N < 0 := by
  have hnot : ¬ ∀ (P : Polynomial ℝ) (t : ℝ), 0 < t →
      0 ≤ xiPolynomialGaussianHeatTraceReal P t := by
    intro hall
    exact hRH
      (riemannHypothesis_iff_forall_xiPolynomialGaussianHeatTraceReal_nonneg.mpr hall)
  push Not at hnot
  obtain ⟨P, τ, hτ, htraceNeg⟩ := hnot
  let t : {τ : ℝ // 0 < τ} := ⟨τ, hτ⟩
  have hcutLim := tendsto_routeUXiPolynomialGaussianCutoffDivisorTrace P t
  have hcutRe : Tendsto (fun n : ℕ =>
      (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re)
      atTop (nhds (xiPolynomialGaussianHeatTraceReal P τ)) := by
    have h := (Complex.reCLM.continuous.tendsto
      (xiPolynomialGaussianHeatTrace P τ)).comp hcutLim
    have hfun :
        ((Complex.reCLM : ℂ → ℝ) ∘ fun n : ℕ =>
          ∑' q : XiZeroCopy,
            routeUComplexPositiveFourierExtension n
              (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2) =
        fun n : ℕ =>
          (∑' q : XiZeroCopy,
            routeUComplexPositiveFourierExtension n
              (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re := by
      funext n
      exact Complex.reCLM_apply _
    rw [hfun] at h
    have hreval : (Complex.reCLM : ℂ → ℝ)
        (xiPolynomialGaussianHeatTrace P τ) =
          (xiPolynomialGaussianHeatTrace P τ).re := Complex.reCLM_apply _
    rw [hreval] at h
    simpa only [xiPolynomialGaussianHeatTraceReal] using h
  have hcutEventually : ∀ᶠ n : ℕ in atTop,
      (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re < 0 :=
    hcutRe.eventually (Iio_mem_nhds htraceNeg)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hcutEventually
  have hcutNeg := hn n le_rfl
  let g : SchwartzMap ℝ ℝ := routeUXiHeatPhysicalReal P t
  have hhardLim :=
    tendsto_tsum_routeUXiComplexHardEdgeSampleDivisorTerm_natCast n
      (routeURealEvenAmplitude g)
  have htarget :
      (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n (routeURealEvenAmplitude g)
          (xiSpectralPoint q) ^ 2) =
      ∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2 := by
    rw [show routeURealEvenAmplitude g = routeUXiHeatPhysicalComplex P t by
      exact routeURealEvenAmplitude_heatPhysical_eq P t]
  have hhardRe : Tendsto (fun k : ℕ =>
      (∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeSampleDivisorTerm n
          (routeURealEvenAmplitude g) (k : ℝ) q).re)
      atTop
      (nhds ((∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re)) := by
    rw [← htarget]
    have h := (Complex.reCLM.continuous.tendsto _).comp hhardLim
    have hfun :
        ((Complex.reCLM : ℂ → ℝ) ∘ fun k : ℕ =>
          ∑' q : XiZeroCopy,
            routeUXiComplexHardEdgeSampleDivisorTerm n
              (routeURealEvenAmplitude g) (k : ℝ) q) =
        fun k : ℕ =>
          (∑' q : XiZeroCopy,
            routeUXiComplexHardEdgeSampleDivisorTerm n
              (routeURealEvenAmplitude g) (k : ℝ) q).re := by
      funext k
      exact Complex.reCLM_apply _
    rw [hfun] at h
    exact h
  have hhardEventually : ∀ᶠ k : ℕ in atTop,
      (∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeSampleDivisorTerm n
          (routeURealEvenAmplitude g) (k : ℝ) q).re < 0 :=
    hhardRe.eventually (Iio_mem_nhds hcutNeg)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hhardEventually
  have hsampleNeg := hk k le_rfl
  obtain ⟨N, hpoint, hquadEq⟩ :=
    exists_routeUExactFiniteHankelWitness n g (k : ℝ)
  refine ⟨P, t, n, k, N, ?_⟩
  have hmass : 0 < routeUHardEdgeMass (k : ℝ) ^ 2 :=
    sq_pos_of_pos (routeUHardEdgeMass_pos (k : ℝ))
  dsimp only [g] at hquadEq
  change xiShiftedReciprocalHankelQuadratic
    (routeUHardEdgeMass (k : ℝ) ^ 2)
    (xiHardEdgeLiftCoefficients (routeUHardEdgeMass (k : ℝ))
      (routeUFiniteChebyshevPacketPolynomial n
        (routeUXiHeatPhysicalReal P t) (k : ℝ) N)) < 0
  nlinarith

theorem not_rh_iff_exists_negative_routeUPolynomialGaussianFiniteHankelQuadratic :
    ¬ RiemannHypothesis ↔
      ∃ (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ})
        (n k N : ℕ), routeUPolynomialGaussianFiniteHankelQuadratic P t n k N < 0 := by
  constructor
  · exact exists_negative_routeUPolynomialGaussianFiniteHankelQuadratic_of_not_rh
  · rintro ⟨P, t, n, k, N, hneg⟩
    exact not_riemannHypothesis_of_xiShiftedReciprocalHankelQuadratic_neg
      (sq_nonneg (routeUHardEdgeMass (k : ℝ))) hneg

theorem rh_iff_all_routeUPolynomialGaussianFiniteHankelQuadratics_nonneg :
    RiemannHypothesis ↔
      ∀ (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ})
        (n k N : ℕ), 0 ≤ routeUPolynomialGaussianFiniteHankelQuadratic P t n k N := by
  constructor
  · intro hRH P t n k N
    exact xiShiftedReciprocalHankelQuadratic_nonneg_of_riemannHypothesis
      hRH (sq_nonneg (routeUHardEdgeMass (k : ℝ))) _
  · intro hall
    by_contra hnot
    obtain ⟨P, t, n, k, N, hneg⟩ :=
      exists_negative_routeUPolynomialGaussianFiniteHankelQuadratic_of_not_rh hnot
    exact (not_lt_of_ge (hall P t n k N)) hneg

end RHTower

