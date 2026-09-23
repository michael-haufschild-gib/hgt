import GaloisForLFunctions.HTGeometry.FiniteReporterDataProcessing

/-!
# Bounded recovery of finite derivative-clock reporters

Suppose a bounded downstream reporter map `decode` has a bounded left recovery `recover` on the
image of a source reporter.  Data processing applied forward bounds the postprocessed conditional
information by `‖decode‖²` times the source value.  Applying the same theorem to `recover` and
using exact recovery gives the missing reverse inequality:

```text
I(decode o report) <= ‖decode‖² I(report),
I(report) <= ‖recover‖² I(decode o report).
```

Thus the condition of a recoverable observation channel quantitatively controls every sequential
clock-innovation value.  A recovery norm bound `C` gives
`I(report) / C² <= I(decode o report)`.  If both maps are contractions, exact recovery forces
equality of conditional information even when the encoding was not supplied as a linear
isometry.

These are static observation/reconstruction laws.  They assume neither a temporal channel nor a
Hamiltonian flow.  They generalize the exact isometric-adjoint result in
`FiniteReporterIsometricRecovery` and provide a reusable norm-conditioned interface for quantum
error correction, holographic reconstruction, learned encoders, genomic reporters, and inverse
measurement systems.

Quantum-information provenance: recoverability is the equality side of data processing; see
Gao--Li--Marvian--Rouze, arXiv:2302.02341, and Beny--Oreshkov, arXiv:0907.5391.  The formal result
below is the Hilbert-valued operator-norm consequence of an explicitly supplied left recovery.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

/-- A bounded left recovery supplies the reverse conditional-information data-processing bound. -/
theorem finiteDerivativeReporterConditionalInformation_le_recovery_norm_sq_mul
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report) :
    finiteDerivativeReporterConditionalInformation N f report ≤
      ‖recover‖ ^ (2 : ℕ) *
        finiteDerivativeReporterConditionalInformation N f
          (decode.toLinearMap.comp report) := by
  have h := finiteDerivativeReporterConditionalInformation_postcomp_le
    N f (decode.toLinearMap.comp report) recover
  rw [hrecover] at h
  exact h

/-- **Bounded-recovery information sandwich.**  Decoder and recovery norms control both
directions of every sequential reporter-information value. -/
theorem finiteDerivativeReporterConditionalInformation_boundedRecovery_sandwich
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report) :
    finiteDerivativeReporterConditionalInformation N f
        (decode.toLinearMap.comp report) ≤
        ‖decode‖ ^ (2 : ℕ) * finiteDerivativeReporterConditionalInformation N f report ∧
      finiteDerivativeReporterConditionalInformation N f report ≤
        ‖recover‖ ^ (2 : ℕ) *
          finiteDerivativeReporterConditionalInformation N f
            (decode.toLinearMap.comp report) :=
  ⟨finiteDerivativeReporterConditionalInformation_postcomp_le N f report decode,
    finiteDerivativeReporterConditionalInformation_le_recovery_norm_sq_mul
      N f report decode recover hrecover⟩

/-- **Recoverable algebraic-metric reporter profile.**  Exact left recovery preserves visible
coefficient rank and the entire blind coefficient subspace, even when the recoding is not
isometric.  Decoder and recovery norms separately control the possible metric distortion of the
same reporter's conditional information. -/
theorem finiteDerivativeReporter_recoverableCapacityAndInformationProfile
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report) :
    Module.finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap N f (decode.toLinearMap.comp report))) =
        Module.finrank ℂ
          (LinearMap.range (finiteDerivativeReporterMap N f report)) ∧
      LinearMap.ker
          (finiteDerivativeReporterMap N f (decode.toLinearMap.comp report)) =
        LinearMap.ker (finiteDerivativeReporterMap N f report) ∧
      finiteDerivativeReporterConditionalInformation N f
          (decode.toLinearMap.comp report) ≤
        ‖decode‖ ^ (2 : ℕ) * finiteDerivativeReporterConditionalInformation N f report ∧
      finiteDerivativeReporterConditionalInformation N f report ≤
        ‖recover‖ ^ (2 : ℕ) *
          finiteDerivativeReporterConditionalInformation N f
            (decode.toLinearMap.comp report) := by
  have hcapacity := finiteDerivativeReporterMap_postcomp_capacity_eq_of_recovery
    N f report decode.toLinearMap recover.toLinearMap hrecover
  have hinformation :=
    finiteDerivativeReporterConditionalInformation_boundedRecovery_sandwich
      N f report decode recover hrecover
  exact ⟨hcapacity.1, hcapacity.2, hinformation.1, hinformation.2⟩

/-- A positive uniform recovery-norm bound gives an explicit lower bound on every surviving
postprocessed innovation value. -/
theorem finiteDerivativeReporterConditionalInformation_div_recovery_bound_le
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report)
    {C : ℝ} (hC : 0 < C) (hrecoverNorm : ‖recover‖ ≤ C) :
    finiteDerivativeReporterConditionalInformation N f report / C ^ (2 : ℕ) ≤
      finiteDerivativeReporterConditionalInformation N f
        (decode.toLinearMap.comp report) := by
  rw [div_le_iff₀ (sq_pos_of_pos hC)]
  have hbound :=
    finiteDerivativeReporterConditionalInformation_le_recovery_norm_sq_mul
      N f report decode recover hrecover
  have hpost := finiteDerivativeReporterConditionalInformation_nonneg N f
    (decode.toLinearMap.comp report)
  have hnorm : ‖recover‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by
    nlinarith [norm_nonneg recover]
  exact hbound.trans (by
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hnorm hpost)

/-- Exact recovery by two contractions is an equality case of conditional-information data
processing, without requiring a separately packaged isometry. -/
theorem finiteDerivativeReporterConditionalInformation_eq_of_contractive_recovery
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report)
    (hdecode : ‖decode‖ ≤ 1) (hrecoverNorm : ‖recover‖ ≤ 1) :
    finiteDerivativeReporterConditionalInformation N f
        (decode.toLinearMap.comp report) =
      finiteDerivativeReporterConditionalInformation N f report := by
  apply le_antisymm
  · exact finiteDerivativeReporterConditionalInformation_postcomp_le_of_norm_le_one
      N f report decode hdecode
  · have hbound :=
      finiteDerivativeReporterConditionalInformation_le_recovery_norm_sq_mul
        N f report decode recover hrecover
    have hpost := finiteDerivativeReporterConditionalInformation_nonneg N f
      (decode.toLinearMap.comp report)
    have hnorm : ‖recover‖ ^ (2 : ℕ) ≤ 1 := by
      nlinarith [norm_nonneg recover]
    exact hbound.trans (by
      simpa using mul_le_mul_of_nonneg_right hnorm hpost)

end

end HTGeometry
