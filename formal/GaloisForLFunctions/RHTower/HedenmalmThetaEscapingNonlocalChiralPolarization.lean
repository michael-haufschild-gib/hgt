import GaloisForLFunctions.HTGeometry.NonlocalSourceChiralPolarization
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
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

/-- Exact divisor cost of positive chiralization: the prime--Gamma eigenvalue divisor is replaced
by its squared singular-value divisor, with all coefficient interference retained in `Cᴴ C`. -/
theorem routePPrimeGammaEscapingChiralOperator_divisor_eq_gramDet {N : ℕ}
    (k : ℕ) (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) (z : ℂ) :
    ((1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) -
      z • routePPrimeGammaEscapingChiralOperator k R n kappa).det =
      ((1 : Matrix (Fin N) (Fin N) ℂ) - (z * z) •
        ((routePPrimeGammaCubicKernelMatrix R n kappa)ᴴ *
          routePPrimeGammaCubicKernelMatrix R n kappa)).det := by
  unfold routePPrimeGammaEscapingChiralOperator
  rw [sourceEscapingChiralOperator_divisor_eq,
    sourceHermitianDilationDivisor_eq_gramDet]

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

/-- Full-index Hermitian dilation of the corrected signed source kernel. -/
def thetaSourceSignedChiralKernel (k : ℕ) :
    (thetaIndex ⊕ thetaIndex) × (thetaIndex ⊕ thetaIndex) → ℂ :=
  sourceHermitianDilationKernel (thetaSourceSignedKernel k)

/-- Forced infinite source target of positive chiralization. -/
def thetaSourceChiralLimitKernel :
    (thetaIndex ⊕ thetaIndex) × (thetaIndex ⊕ thetaIndex) → ℂ :=
  sourceHermitianDilationKernel (-thetaKernelMatrix)

/-- Forced compact-open limit of the normalized finite chiral divisors. -/
def thetaSourceChiralEntireLimit (z : ℂ) : ℂ :=
  XiC 0 * entireDet2 thetaSourceChiralLimitKernel z

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

/-- Exact finite divisor change.  Positivity retains the complete signed source matrix inside
`Cᴴ C`, but replaces its ordinary divisor by the squared singular-value divisor. -/
theorem thetaSourceChiralDet_eq_sourceGramDet (k : ℕ) (z : ℂ) :
    thetaSourceChiralDet k z =
      ((1 : Matrix ↥(thetaSourceSignedCutoff k) ↥(thetaSourceSignedCutoff k) ℂ) -
        (z * z) • ((thetaSourceSignedFiniteMatrix k)ᴴ *
          thetaSourceSignedFiniteMatrix k)).det := by
  rw [thetaSourceChiralDet_eq_sourceDilationDivisor,
    sourceHermitianDilationDivisor_eq_gramDet]

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

/-- Infinite finite-support determinant is exactly the escaped finite matrix divisor. -/
theorem thetaSourceChiralDet_eq_entireDet2_signedChiralKernel (k : ℕ) :
    thetaSourceChiralDet k = entireDet2 (thetaSourceSignedChiralKernel k) := by
  rw [thetaSourceChiralDet_eq_sourceDilationDivisor]
  exact (entireDet2_sourceHermitianDilationKernel_eq_sourceHermitianDilationDivisor
    (isHS_thetaSourceSignedKernel k) (thetaSourceSignedKernel_support k)).symm

theorem thetaSourceChiralXiCandidate_eq_entireDet2_signedChiralKernel
    (k : ℕ) (z : ℂ) :
    thetaSourceChiralXiCandidate k z =
      XiC 0 * entireDet2 (thetaSourceSignedChiralKernel k) z := by
  rw [thetaSourceChiralXiCandidate,
    thetaSourceChiralDet_eq_entireDet2_signedChiralKernel]

theorem isHS_thetaSourceSignedChiralKernel (k : ℕ) :
    IsHS (thetaSourceSignedChiralKernel k) :=
  isHS_sourceHermitianDilationKernel (isHS_thetaSourceSignedKernel k)

theorem isHS_thetaSourceChiralLimitKernel : IsHS thetaSourceChiralLimitKernel :=
  isHS_sourceHermitianDilationKernel isHS_neg_thetaKernelMatrix

/-- Escaping chiral kernels retain exact Hilbert--Schmidt convergence; norm cost is `sqrt 2`. -/
theorem thetaSourceSignedChiralKernel_tendsto_limit :
    Tendsto (fun k => hsNorm (thetaSourceSignedChiralKernel k -
      thetaSourceChiralLimitKernel)) atTop (nhds 0) := by
  have hfun :
      (fun k => hsNorm (thetaSourceSignedChiralKernel k -
        thetaSourceChiralLimitKernel)) =
      (fun k => Real.sqrt 2 *
        hsNorm (thetaSourceSignedKernel k - (-thetaKernelMatrix))) := by
    funext k
    rw [thetaSourceSignedChiralKernel, thetaSourceChiralLimitKernel,
      ← sourceHermitianDilationKernel_sub,
      hsNorm_sourceHermitianDilationKernel]
    exact isHS_sub (isHS_thetaSourceSignedKernel k) isHS_neg_thetaKernelMatrix
  rw [hfun]
  simpa using thetaSourceSignedKernel_tendsto_source.const_mul (Real.sqrt 2)

/-- Unconditional compact-open limit after chiral positivity: singular-value source target. -/
theorem thetaSourceChiralXiCandidate_tendstoLocallyUniformly_forcedLimit :
    TendstoLocallyUniformly thetaSourceChiralXiCandidate
      thetaSourceChiralEntireLimit atTop := by
  have hdet := tendstoLocallyUniformly_entireDet2_of_hsNorm_sub_tendsto_zero
    thetaSourceSignedChiralKernel thetaSourceChiralLimitKernel
    isHS_thetaSourceSignedChiralKernel isHS_thetaSourceChiralLimitKernel
    thetaSourceSignedChiralKernel_tendsto_limit
  have hconst : TendstoLocallyUniformly
      (fun _ : ℕ => fun _ : ℂ => XiC 0) (fun _ : ℂ => XiC 0) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall (fun k z hz => by simpa using hepsilon)
  have hmul := tendstoLocallyUniformly_mul hconst hdet
    continuous_const (differentiable_entireDet2 isHS_thetaSourceChiralLimitKernel).continuous
  rw [show thetaSourceChiralXiCandidate =
      (fun k z => XiC 0 * entireDet2 (thetaSourceSignedChiralKernel k) z) by
    funext k z
    exact thetaSourceChiralXiCandidate_eq_entireDet2_signedChiralKernel k z]
  exact hmul

/-- Exact fidelity classification: Xi convergence occurs precisely when forced chiral source
limit equals Xi. -/
theorem thetaSourceChiralXiCandidate_tendstoLocallyUniformly_XiC_iff_limit_eq :
    TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop ↔
      thetaSourceChiralEntireLimit = XiC := by
  constructor
  · intro hXi
    funext z
    have hforcedPoint :=
      ((tendstoLocallyUniformly_iff_forall_isCompact.mp
        thetaSourceChiralXiCandidate_tendstoLocallyUniformly_forcedLimit)
        {z} isCompact_singleton).tendsto_at (Set.mem_singleton z)
    have hXiPoint :=
      ((tendstoLocallyUniformly_iff_forall_isCompact.mp hXi)
        {z} isCompact_singleton).tendsto_at (Set.mem_singleton z)
    exact tendsto_nhds_unique hforcedPoint hXiPoint
  · intro hlimit
    simpa only [hlimit] using
      thetaSourceChiralXiCandidate_tendstoLocallyUniformly_forcedLimit

/-- Compact-open Xi fidelity of this real-divisor family would prove RH. -/
theorem riemannHypothesis_of_thetaSourceChiralXiCandidate_tendstoLocallyUniformly
    (hconv : TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
  · exact Filter.Eventually.of_forall differentiable_thetaSourceChiralXiCandidate
  · exact Filter.Eventually.of_forall thetaSourceChiralXiCandidate_zero_im_eq_zero

/-- Identification of the forced singular-value limit with Xi is already sufficient for RH. -/
theorem riemannHypothesis_of_thetaSourceChiralEntireLimit_eq_XiC
    (hlimit : thetaSourceChiralEntireLimit = XiC) : RiemannHypothesis := by
  apply riemannHypothesis_of_thetaSourceChiralXiCandidate_tendstoLocallyUniformly
  exact thetaSourceChiralXiCandidate_tendstoLocallyUniformly_XiC_iff_limit_eq.mpr hlimit

/-- Closed target classification: either chiral completion misses Xi or RH holds. -/
theorem thetaSourceChiralEntireLimit_ne_XiC_or_riemannHypothesis :
    thetaSourceChiralEntireLimit ≠ XiC ∨ RiemannHypothesis := by
  by_cases hlimit : thetaSourceChiralEntireLimit = XiC
  · exact Or.inr (riemannHypothesis_of_thetaSourceChiralEntireLimit_eq_XiC hlimit)
  · exact Or.inl hlimit

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
    (∀ k z, thetaSourceChiralDet k z =
      ((1 : Matrix ↥(thetaSourceSignedCutoff k) ↥(thetaSourceSignedCutoff k) ℂ) -
        (z * z) • ((thetaSourceSignedFiniteMatrix k)ᴴ *
          thetaSourceSignedFiniteMatrix k)).det) ∧
    (∀ k z, thetaSourceChiralDet k z = 0 → z.im = 0) ∧
    TendstoLocallyUniformly thetaSourceChiralXiCandidate
      thetaSourceChiralEntireLimit atTop ∧
    (TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop ↔
      thetaSourceChiralEntireLimit = XiC) ∧
    (RiemannHypothesis ∨
      ¬ TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop) := by
  exact ⟨thetaSourceEscapingNonlocalPolarization_posDef,
    thetaSourceEscapingChiralOperator_metricAdjoint,
    thetaSourceChiralDet_eq_sourceGramDet,
    thetaSourceChiralDet_zero_im_eq_zero,
    thetaSourceChiralXiCandidate_tendstoLocallyUniformly_forcedLimit,
    thetaSourceChiralXiCandidate_tendstoLocallyUniformly_XiC_iff_limit_eq,
    riemannHypothesis_or_not_thetaSourceChiralXiCandidate_tendstoLocallyUniformly⟩

end HedenmalmThetaSource

end

end RHTower
