import GaloisForLFunctions.RHTower.SoninLudersPinching
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# Hilbert--Schmidt closure of the Sonin Lüders--Calkin law

The concrete Sonin time--band ideal was already proved Hilbert--Schmidt, while the Lüders
decomposition reduced its Calkin identity to compactness of one cutoff commutator.  Combining
those results shows that every member of the whole time--band ideal satisfies the identity.
The exterior compression then gives an unconditional source-specific instance.
-/

namespace RHTower

noncomputable section

/-- Every member of the concrete Sonin time--band ideal satisfies the central Lüders--Calkin
formula.  No additional compactness or cutoff-commutation premise is required. -/
theorem isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_mem_timeBandIdeal
    (a : ℝ) (ha : 0 < a)
    (X : SoninL2 →L[ℂ] SoninL2)
    (hX : IsSoninTimeBandIdeal X) :
    let hT := norm_centralSoninAlternatingBlock_lt_one a ha
    let X₀ := ludersPinching (centralPhysicalForbidden a).starProjection X
    let E := (centralPhysicalForbidden a).orthogonal.starProjection
    let V := soninProjectionResolvent
      (centralPhysicalForbidden a) (centralFourierForbidden a) hT
    IsCompactOperator
      (ccmCommutator X (centralSoninProjection a) -
        (-E * V *
          (ccmCommutator X₀ (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                ccmCommutator X₀ (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            ccmCommutator X₀ (centralFourierForbidden a).starProjection) * E) :
        SoninL2 →L[ℂ] SoninL2) := by
  apply isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_cutoffCommutator a ha X
  exact isCompactOperator_ccmCommutator_of_leftCompact
    X (centralPhysicalForbidden a).starProjection hX.isHilbertSchmidt.isCompactOperator

/-- The exterior positive compression satisfies the central Lüders--Calkin formula from source
data alone.  Its Hilbert--Schmidt realization discharges the final operator premise. -/
theorem isCompactOperator_centralSoninExteriorCompression_commutator_sub_ludersDressed
    (a : ℝ) (ha : 0 < a) :
    let hT := norm_centralSoninAlternatingBlock_lt_one a ha
    let X := centralSoninExteriorCompression a
    let X₀ := ludersPinching (centralPhysicalForbidden a).starProjection X
    let E := (centralPhysicalForbidden a).orthogonal.starProjection
    let V := soninProjectionResolvent
      (centralPhysicalForbidden a) (centralFourierForbidden a) hT
    IsCompactOperator
      (ccmCommutator X (centralSoninProjection a) -
        (-E * V *
          (ccmCommutator X₀ (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                ccmCommutator X₀ (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            ccmCommutator X₀ (centralFourierForbidden a).starProjection) * E) :
        SoninL2 →L[ℂ] SoninL2) := by
  apply isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_cutoffCommutator
    a ha (centralSoninExteriorCompression a)
  exact isCompactOperator_ccmCommutator_of_leftCompact
    (centralSoninExteriorCompression a) (centralPhysicalForbidden a).starProjection
      (centralSoninExteriorCompression_isHilbertSchmidt a ha).isCompactOperator

end

end RHTower
