import GaloisForLFunctions.HTGeometry.SourceKreinTracePolarization
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSignedOrdinaryDeterminantCompletion
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Theta-source Krein trace polarization and divisor lock

The hyperbolic double of every corrected finite theta source is genuinely Krein self-adjoint.
Its positive-chirality weight preserves every source power trace exactly, and its rescaled Krein
metric escapes with absolute square `(k+1)² I`.  Selecting positive chirality gives the existing
honest source determinant, hence compact-open convergence to normalized Xi.  The full Krein
determinant is its Schwarz square and converges compact-open to normalized Xi squared.

This closes the representation question sharply.  Krein doubling preserves signed traces without
the Gram replacement forced by positive Hermitian dilation.  It does not move the source divisor:
the full divisor only adds conjugate partners, while chiral selection restores the original zeros.
Consequently real-axis support of every selected finite divisor, together with already-proved
compact-open convergence, would prove RH.  The final theorem records the unconditional alternative:
RH holds, or one selected finite Krein stage has a nonreal zero.
-/

open Complex Filter Matrix Metric Set Topology
open scoped Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HilbertSchmidt

noncomputable section

/-- Actual finite signed theta source block. -/
def thetaSourceKreinFiniteMatrix (k : ℕ) :
    Matrix ↥(thetaSourceSignedCutoff k) ↥(thetaSourceSignedCutoff k) ℂ :=
  blockMatrix (thetaSourceSignedKernel k) (thetaSourceSignedCutoff k)

/-- Genuine hyperbolic Krein double of the source block. -/
def thetaSourceKreinDouble (k : ℕ) :
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ :=
  sourceKreinDouble (thetaSourceKreinFiniteMatrix k)

/-- Escaping indefinite source polarization. -/
def thetaSourceEscapingKreinPolarization (k : ℕ) :
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ :=
  sourceEscapingKreinMetric (ι := ↥(thetaSourceSignedCutoff k)) k

/-- Positive-chirality source-trace weight. -/
def thetaSourceKreinChiralWeight (k : ℕ) :
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ :=
  sourceKreinChiralWeight (ι := ↥(thetaSourceSignedCutoff k))

/-- Full ordinary determinant of the Krein double. -/
def thetaSourceKreinDoubleDet (k : ℕ) (z : ℂ) : ℂ :=
  ((1 : Matrix (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k))
      (↥(thetaSourceSignedCutoff k) ⊕ ↥(thetaSourceSignedCutoff k)) ℂ) -
    z • thetaSourceKreinDouble k).det

/-- Schwarz-reflected finite source determinant. -/
def thetaSourceSignedReflectedOrdinaryDet (k : ℕ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (thetaSourceSignedOrdinaryDet k ((starRingEnd ℂ) z))

/-- Chiral Krein selection, centrally normalized to converge to `XiC`. -/
def thetaSourceKreinChiralXiCandidate (k : ℕ) (z : ℂ) : ℂ :=
  XiC 0 * thetaSourceSignedOrdinaryDet k z

/-- Pointwise Schwarz reflection. -/
def sourceSchwarzReflect (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (f ((starRingEnd ℂ) z))

/-- Exact Krein self-adjointness of every finite signed theta source. -/
theorem thetaSourceKreinDouble_metricAdjoint (k : ℕ) :
    thetaSourceEscapingKreinPolarization k * thetaSourceKreinDouble k =
      (thetaSourceKreinDouble k)ᴴ * thetaSourceEscapingKreinPolarization k :=
  sourceEscapingKreinMetric_metricAdjoint k (thetaSourceKreinFiniteMatrix k)

/-- Exact absolute coercive escape. -/
theorem thetaSourceEscapingKreinPolarization_absSq (k : ℕ) :
    (thetaSourceEscapingKreinPolarization k)ᴴ *
        thetaSourceEscapingKreinPolarization k =
      ((((k : ℝ) + 1) ^ (2 : ℕ) : ℝ) : ℂ) • 1 :=
  sourceEscapingKreinMetric_absSq k

/-- All signed holomorphic source traces survive, at every degree. -/
theorem thetaSourceKreinChiralWeight_trace_pow (k m : ℕ) :
    (thetaSourceKreinChiralWeight k * (thetaSourceKreinDouble k) ^ m).trace =
      ((thetaSourceKreinFiniteMatrix k) ^ m).trace :=
  sourceKreinChiralWeight_trace_pow (thetaSourceKreinFiniteMatrix k) m

/-- Full Krein determinant is exactly the source determinant times its Schwarz reflection. -/
theorem thetaSourceKreinDoubleDet_eq_source_mul_reflected (k : ℕ) (z : ℂ) :
    thetaSourceKreinDoubleDet k z =
      thetaSourceSignedOrdinaryDet k z * thetaSourceSignedReflectedOrdinaryDet k z := by
  unfold thetaSourceKreinDoubleDet thetaSourceKreinDouble thetaSourceKreinFiniteMatrix
    thetaSourceSignedReflectedOrdinaryDet
  rw [sourceKreinDouble_det_eq_source_mul_reflected]
  rfl

/-- The full finite divisor is Schwarz-stable.  Krein doubling adds reflected partners; it does
not force either partner onto the real axis. -/
theorem thetaSourceKreinDoubleDet_conj_zero (k : ℕ) {z : ℂ}
    (hz : thetaSourceKreinDoubleDet k z = 0) :
    thetaSourceKreinDoubleDet k ((starRingEnd ℂ) z) = 0 := by
  rw [thetaSourceKreinDoubleDet_eq_source_mul_reflected] at hz ⊢
  rcases mul_eq_zero.mp hz with hdirect | hreflected
  · apply mul_eq_zero.mpr
    right
    simp [thetaSourceSignedReflectedOrdinaryDet, hdirect]
  · have hdirect : thetaSourceSignedOrdinaryDet k ((starRingEnd ℂ) z) = 0 := by
      apply (map_eq_zero (starRingEnd ℂ)).mp
      simpa [thetaSourceSignedReflectedOrdinaryDet] using hreflected
    exact mul_eq_zero.mpr (Or.inl hdirect)

/-- Compact-open convergence is preserved by Schwarz reflection. -/
theorem tendstoLocallyUniformly_sourceSchwarzReflect
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f atTop) :
    TendstoLocallyUniformly (fun k => sourceSchwarzReflect (F k))
      (sourceSchwarzReflect f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at h ⊢
  intro K hK
  let K' : Set ℂ := (starRingEnd ℂ) '' K
  have hK' : IsCompact K' := hK.image Complex.continuous_conj
  have hU := h K' hK'
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro epsilon hepsilon
  filter_upwards [hU epsilon hepsilon] with k hk z hz
  have hz' : (starRingEnd ℂ) z ∈ K' := ⟨z, hz, rfl⟩
  have hdist := hk ((starRingEnd ℂ) z) hz'
  rw [dist_eq_norm] at hdist ⊢
  simpa [sourceSchwarzReflect, ← map_sub] using hdist

/-- Reflected chiral determinants converge to same normalized Xi source. -/
theorem thetaSourceSignedReflectedOrdinaryDet_tendstoLocallyUniformly_XiC :
    TendstoLocallyUniformly thetaSourceSignedReflectedOrdinaryDet
      (fun z => XiC z / XiC 0) atTop := by
  have h := tendstoLocallyUniformly_sourceSchwarzReflect
    thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC
  have hlimit : sourceSchwarzReflect (fun z => XiC z / XiC 0) =
      (fun z => XiC z / XiC 0) := by
    have hzero : (starRingEnd ℂ) (XiC 0) = XiC 0 := by
      simpa using (XiC_conj 0).symm
    funext z
    simp [sourceSchwarzReflect, XiC_conj, hzero]
  change TendstoLocallyUniformly
    (fun k => sourceSchwarzReflect (thetaSourceSignedOrdinaryDet k))
      (fun z => XiC z / XiC 0) atTop
  simpa only [hlimit] using h

/-- Full Krein determinants converge compact-open to the Schwarz square of normalized Xi. -/
theorem thetaSourceKreinDoubleDet_tendstoLocallyUniformly_XiC_sq :
    TendstoLocallyUniformly thetaSourceKreinDoubleDet
      (fun z => (XiC z / XiC 0) ^ (2 : ℕ)) atTop := by
  have hmul := tendstoLocallyUniformly_mul
    thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC
    thetaSourceSignedReflectedOrdinaryDet_tendstoLocallyUniformly_XiC
    (XiC_differentiable.div_const (XiC 0)).continuous
    (XiC_differentiable.div_const (XiC 0)).continuous
  rw [show thetaSourceKreinDoubleDet = fun k z =>
      thetaSourceSignedOrdinaryDet k z * thetaSourceSignedReflectedOrdinaryDet k z by
    funext k z
    exact thetaSourceKreinDoubleDet_eq_source_mul_reflected k z]
  simpa [pow_two] using hmul

/-- Chiral selection preserves source determinant and converges compact-open to `XiC`. -/
theorem thetaSourceKreinChiralXiCandidate_tendstoLocallyUniformly_XiC :
    TendstoLocallyUniformly thetaSourceKreinChiralXiCandidate XiC atTop := by
  have hconst : TendstoLocallyUniformly (fun _ : ℕ => fun _ : ℂ => XiC 0)
      (fun _ : ℂ => XiC 0) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall fun k z hz => by simpa using hepsilon
  have hmul := tendstoLocallyUniformly_mul hconst
    thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC
    continuous_const (XiC_differentiable.div_const (XiC 0)).continuous
  change TendstoLocallyUniformly
    (fun k z => XiC 0 * thetaSourceSignedOrdinaryDet k z) XiC atTop
  convert hmul using 1
  funext z
  symm
  calc
    XiC 0 * (XiC z / XiC 0) = (XiC z / XiC 0) * XiC 0 := mul_comm _ _
    _ = XiC z := div_mul_cancel₀ _ XiC_zero_ne

theorem differentiable_thetaSourceKreinChiralXiCandidate (k : ℕ) :
    Differentiable ℂ (thetaSourceKreinChiralXiCandidate k) :=
  (differentiable_const (c := XiC 0)).mul
    (differentiable_thetaSourceSignedOrdinaryDet k)

/-- If all chiral selected stages had real divisor, already-proved compact-open convergence would
close RH. -/
theorem riemannHypothesis_of_thetaSourceKreinChiralXiCandidate_realDivisor
    (hreal : ∀ k z, thetaSourceKreinChiralXiCandidate k z = 0 → z.im = 0) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants
    thetaSourceKreinChiralXiCandidate_tendstoLocallyUniformly_XiC
    (Filter.Eventually.of_forall differentiable_thetaSourceKreinChiralXiCandidate)
    (Filter.Eventually.of_forall hreal)

/-- Closed divisor lock: either RH is true, or exact trace-preserving chiral Krein selection has a
nonreal finite-stage divisor.  Grading cannot supply real stages without supplying RH itself. -/
theorem thetaSourceKreinChiralXiCandidate_nonrealStage_or_riemannHypothesis :
    RiemannHypothesis ∨
      ∃ k : ℕ, ∃ z : ℂ,
        thetaSourceKreinChiralXiCandidate k z = 0 ∧ z.im ≠ 0 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    by_contra hnone
    push Not at hnone
    apply hRH
    exact riemannHypothesis_of_thetaSourceKreinChiralXiCandidate_realDivisor
      fun k z hz => hnone k z hz

/-- Closed construction certificate.  Exact all-degree trace retention, Krein self-adjointness,
coercive escape, normalized-Xi convergence, and Schwarz-square full completion are unconditional.
The requested real-axis finite divisor is isolated by the final RH/nonreal-stage alternative. -/
theorem thetaSourceKreinTracePolarization_certificate :
    (∀ k, thetaSourceEscapingKreinPolarization k * thetaSourceKreinDouble k =
      (thetaSourceKreinDouble k)ᴴ * thetaSourceEscapingKreinPolarization k) ∧
    (∀ k, (thetaSourceEscapingKreinPolarization k)ᴴ *
        thetaSourceEscapingKreinPolarization k =
      ((((k : ℝ) + 1) ^ (2 : ℕ) : ℝ) : ℂ) • 1) ∧
    (∀ k m, (thetaSourceKreinChiralWeight k *
        (thetaSourceKreinDouble k) ^ m).trace =
      ((thetaSourceKreinFiniteMatrix k) ^ m).trace) ∧
    (∀ k z, thetaSourceKreinDoubleDet k z =
      thetaSourceSignedOrdinaryDet k z * thetaSourceSignedReflectedOrdinaryDet k z) ∧
    TendstoLocallyUniformly thetaSourceKreinDoubleDet
      (fun z => (XiC z / XiC 0) ^ (2 : ℕ)) atTop ∧
    TendstoLocallyUniformly thetaSourceKreinChiralXiCandidate XiC atTop ∧
    (RiemannHypothesis ∨
      ∃ k : ℕ, ∃ z : ℂ,
        thetaSourceKreinChiralXiCandidate k z = 0 ∧ z.im ≠ 0) := by
  exact ⟨thetaSourceKreinDouble_metricAdjoint,
    thetaSourceEscapingKreinPolarization_absSq,
    thetaSourceKreinChiralWeight_trace_pow,
    thetaSourceKreinDoubleDet_eq_source_mul_reflected,
    thetaSourceKreinDoubleDet_tendstoLocallyUniformly_XiC_sq,
    thetaSourceKreinChiralXiCandidate_tendstoLocallyUniformly_XiC,
    thetaSourceKreinChiralXiCandidate_nonrealStage_or_riemannHypothesis⟩

end

end RHTower.HedenmalmThetaSource
