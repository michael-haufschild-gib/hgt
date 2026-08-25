import GaloisForLFunctions.HTGeometry.NonlocalSourceChiralPolarization
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSignedOrdinaryDeterminantCompletion
import GaloisForLFunctions.RHTower.RoutePPrimeGammaCubicCarrierIdentification
import GaloisForLFunctions.RHTower.XiCRealZeroApproximationErrorFloor

/-!
# Escaping nonlocal chiral polarizations of finite RH source operators

This module specializes the universal source-Gram chiral construction twice.

* On every finite Route-P prime--Gamma packet, the upper-right chiral block is literally the
  coefficient-faithful prime--Gamma matrix.  Positive similarity changes neither its entries before
  dilation nor the resulting real divisor.
* On the actual signed theta finite-rank completion, the construction gives explicit positive,
  globally coupled, escaping metrics and real finite-stage divisors.

The final compact-open audit is sharp.  If these new real divisors converged to centered `XiC`, RH
would follow.  If RH is false, one fixed nonreal Xi contour carries a positive approximation-error
floor for every stage.  Thus escaping nonlocal positivity is constructible; coefficient-faithful
Xi divisor convergence remains the exact RH-bearing weld and is not smuggled into the metric.
-/

open Complex Filter Matrix Metric Set
open scoped ComplexOrder Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Literal finite prime--Gamma provenance -/

/-- Escaped chiral operator of an arbitrary finite Route-P prime--Gamma packet. -/
def routePPrimeGammaEscapingChiralOperator {N : ℕ}
    (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  sourceEscapingChiralOperator k (routePPrimeGammaCubicKernelMatrix R n kappa)

/-- Its positive nonlocal metric. -/
def routePPrimeGammaEscapingNonlocalMetric {N : ℕ}
    (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  sourceEscapingNonlocalMetric k (routePPrimeGammaCubicKernelMatrix R n kappa)

/-- Coefficient fidelity is entrywise and precedes positivity: the complete prime--Gamma matrix is
the positive-to-negative chiral block. -/
@[simp] theorem routePPrimeGammaHermitianDilation_sourceBlock {N : ℕ}
    (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) (i j : Fin N) :
    sourceHermitianDilation (routePPrimeGammaCubicKernelMatrix R n kappa)
      (Sum.inl i) (Sum.inr j) =
        routePPrimeGammaCubicKernelMatrix R n kappa i j := rfl

theorem routePPrimeGammaEscapingNonlocalMetric_posDef {N : ℕ}
    (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) :
    (routePPrimeGammaEscapingNonlocalMetric k R n kappa).PosDef :=
  sourceEscapingNonlocalMetric_posDef k (routePPrimeGammaCubicKernelMatrix R n kappa)

theorem routePPrimeGammaEscapingChiralOperator_metricAdjoint {N : ℕ}
    (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) :
    routePPrimeGammaEscapingNonlocalMetric k R n kappa *
        routePPrimeGammaEscapingChiralOperator k R n kappa =
      (routePPrimeGammaEscapingChiralOperator k R n kappa)ᴴ *
        routePPrimeGammaEscapingNonlocalMetric k R n kappa :=
  sourceEscapingChiralOperator_metricAdjoint k
    (routePPrimeGammaCubicKernelMatrix R n kappa)

theorem routePPrimeGammaEscapingChiralOperator_divisor_zero_im_eq_zero {N : ℕ}
    (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) {z : ℂ}
    (hz : ((1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) -
      z • routePPrimeGammaEscapingChiralOperator k R n kappa).det = 0) :
    z.im = 0 :=
  sourceEscapingChiralOperator_divisor_zero_im_eq_zero k
    (routePPrimeGammaCubicKernelMatrix R n kappa) hz

/-! ## Actual signed theta/Xi completion -/

namespace HedenmalmThetaSource

open HilbertSchmidt

/-- Actual finite signed theta source matrix before chiral dilation. -/
def thetaSourceSignedFiniteMatrix (k : ℕ) :
    Matrix ↥(thetaSourceSignedCutoff k) ↥(thetaSourceSignedCutoff k) ℂ :=
  blockMatrix (thetaSourceSignedKernel k) (thetaSourceSignedCutoff k)

/-- Escaped source operator.  Its metric is nonlocal, but its divisor is that of the Hermitian
chiral dilation. -/
def thetaSourceEscapingChiralOperator (k : ℕ) :
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ :=
  sourceEscapingChiralOperator k (thetaSourceSignedFiniteMatrix k)

/-- Positive escaping source-Gram metric. -/
def thetaSourceEscapingNonlocalPolarization (k : ℕ) :
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ :=
  sourceEscapingNonlocalMetric k (thetaSourceSignedFiniteMatrix k)

/-- Positive root exposing chiral floor and global source Gram separately. -/
def thetaSourceEscapingPolarizationRoot (k : ℕ) :
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ :=
  sourceEscapingNonlocalRoot k (thetaSourceSignedFiniteMatrix k)

/-- Real finite-stage ordinary divisor. -/
def thetaSourceChiralDet (k : ℕ) (z : ℂ) : ℂ :=
  ((1 : Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ) -
    z • thetaSourceEscapingChiralOperator k).det

/-- Central normalization needed to compare the unit-pointed divisor with `XiC`. -/
def thetaSourceChiralXiCandidate (k : ℕ) (z : ℂ) : ℂ :=
  XiC 0 * thetaSourceChiralDet k z

/-- Exact signed-source provenance survives in one chiral block. -/
@[simp] theorem thetaSourceHermitianDilation_sourceBlock
    (k : ℕ) (i j : ↥(thetaSourceSignedCutoff k)) :
    sourceHermitianDilation (thetaSourceSignedFiniteMatrix k)
      (Sum.inl i) (Sum.inr j) =
        thetaSourceSignedKernel k ((i : thetaIndex), (j : thetaIndex)) := rfl

/-- Root contains both global coefficient-interference Grams exactly. -/
theorem thetaSourceEscapingPolarizationRoot_sourceGramBlocks (k : ℕ) :
    thetaSourceEscapingPolarizationRoot k =
      sourceChiralFloor k +
        Matrix.fromBlocks
          (thetaSourceSignedFiniteMatrix k * (thetaSourceSignedFiniteMatrix k)ᴴ) 0 0
          ((thetaSourceSignedFiniteMatrix k)ᴴ * thetaSourceSignedFiniteMatrix k) := by
  exact sourceEscapingNonlocalRoot_eq_sourceGramBlocks k (thetaSourceSignedFiniteMatrix k)

/-- Exact coercive floor: nonlocal source Gram is a positive-semidefinite excess above the
asymmetric floor whose positive-chirality coefficient is `k+1`. -/
theorem thetaSourceEscapingPolarizationRoot_floor (k : ℕ) :
    (thetaSourceEscapingPolarizationRoot k - sourceChiralFloor k).PosSemidef := by
  exact sourceEscapingNonlocalRoot_sub_chiralFloor_posSemidef k
    (thetaSourceSignedFiniteMatrix k)

theorem thetaSourceEscapingNonlocalPolarization_posDef (k : ℕ) :
    (thetaSourceEscapingNonlocalPolarization k).PosDef :=
  sourceEscapingNonlocalMetric_posDef k (thetaSourceSignedFiniteMatrix k)

theorem thetaSourceEscapingChiralOperator_metricAdjoint (k : ℕ) :
    thetaSourceEscapingNonlocalPolarization k * thetaSourceEscapingChiralOperator k =
      (thetaSourceEscapingChiralOperator k)ᴴ *
        thetaSourceEscapingNonlocalPolarization k :=
  sourceEscapingChiralOperator_metricAdjoint k (thetaSourceSignedFiniteMatrix k)

/-- Similarity changes no finite divisor. -/
theorem thetaSourceChiralDet_eq_sourceDilationDivisor (k : ℕ) :
    thetaSourceChiralDet k = sourceHermitianDilationDivisor (thetaSourceSignedFiniteMatrix k) := by
  funext z
  exact sourceEscapingChiralOperator_divisor_eq k (thetaSourceSignedFiniteMatrix k) z

theorem differentiable_thetaSourceChiralDet (k : ℕ) :
    Differentiable ℂ (thetaSourceChiralDet k) := by
  rw [thetaSourceChiralDet_eq_sourceDilationDivisor]
  exact differentiable_sourceHermitianDilationDivisor _

theorem differentiable_thetaSourceChiralXiCandidate (k : ℕ) :
    Differentiable ℂ (thetaSourceChiralXiCandidate k) := by
  exact (differentiable_const (c := XiC 0)).mul (differentiable_thetaSourceChiralDet k)

/-- Every new finite divisor is real. -/
theorem thetaSourceChiralDet_zero_im_eq_zero (k : ℕ) {z : ℂ}
    (hz : thetaSourceChiralDet k z = 0) : z.im = 0 := by
  rw [thetaSourceChiralDet_eq_sourceDilationDivisor] at hz
  exact sourceHermitianDilationDivisor_zero_im_eq_zero _ hz

theorem thetaSourceChiralXiCandidate_zero_im_eq_zero (k : ℕ) {z : ℂ}
    (hz : thetaSourceChiralXiCandidate k z = 0) : z.im = 0 := by
  apply thetaSourceChiralDet_zero_im_eq_zero k
  exact (mul_eq_zero.mp hz).resolve_left XiC_zero_ne

/-- Compact-open Xi fidelity of this real-divisor family would prove RH. -/
theorem riemannHypothesis_of_thetaSourceChiralXiCandidate_tendstoLocallyUniformly
    (hconv : TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
  · exact Filter.Eventually.of_forall differentiable_thetaSourceChiralXiCandidate
  · exact Filter.Eventually.of_forall thetaSourceChiralXiCandidate_zero_im_eq_zero

/-- Closed qualitative fidelity wall. -/
theorem riemannHypothesis_or_not_thetaSourceChiralXiCandidate_tendstoLocallyUniformly :
    RiemannHypothesis ∨
      ¬ TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr fun hconv =>
      hRH (riemannHypothesis_of_thetaSourceChiralXiCandidate_tendstoLocallyUniformly hconv)

/-- Closed quantitative fidelity wall.  Off RH, one fixed contour and one positive error work for
every finite escaped polarization. -/
theorem thetaSourceEscapingChiralXi_errorFloor_dichotomy :
    RiemannHypothesis ∨
      ∃ z : ℂ, ∃ r epsilon : ℝ,
        0 < r ∧ r < |z.im| ∧ XiC z = 0 ∧ 0 < epsilon ∧
          ∀ k : ℕ, ∃ w ∈ sphere z r,
            epsilon ≤ dist (XiC w) (thetaSourceChiralXiCandidate k w) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    obtain ⟨z, r, epsilon, hr, hrim, hz, hepsilon, hfloor⟩ :=
      exists_XiC_realZero_approximation_error_floor_of_not_riemannHypothesis hRH
    refine ⟨z, r, epsilon, hr, hrim, hz, hepsilon, ?_⟩
    intro k
    exact hfloor (thetaSourceChiralXiCandidate k)
      (differentiable_thetaSourceChiralXiCandidate k)
      (fun _ hzG => thetaSourceChiralXiCandidate_zero_im_eq_zero k hzG)

/-- Closed construction certificate: explicit positive/coercive nonlocal metrics, exact
metric-adjointness, real finite divisors, and sharp compact-open Xi-fidelity dichotomy. -/
theorem thetaSourceEscapingNonlocalPolarization_certificate :
    (∀ k, (thetaSourceEscapingNonlocalPolarization k).PosDef) ∧
    (∀ k, thetaSourceEscapingNonlocalPolarization k * thetaSourceEscapingChiralOperator k =
      (thetaSourceEscapingChiralOperator k)ᴴ *
        thetaSourceEscapingNonlocalPolarization k) ∧
    (∀ k z, thetaSourceChiralDet k z = 0 → z.im = 0) ∧
    (RiemannHypothesis ∨
      ¬ TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop) := by
  exact ⟨thetaSourceEscapingNonlocalPolarization_posDef,
    thetaSourceEscapingChiralOperator_metricAdjoint,
    thetaSourceChiralDet_zero_im_eq_zero,
    riemannHypothesis_or_not_thetaSourceChiralXiCandidate_tendstoLocallyUniformly⟩

end HedenmalmThetaSource

end

end RHTower
