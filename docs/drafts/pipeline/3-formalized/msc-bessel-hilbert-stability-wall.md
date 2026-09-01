# MSC Bessel-Hilbert stability wall

- **ID:** MSC-BHSW
- **Stage:** 3-formalized
- **Type:** THEOREM `[LEAN-PROVED]`
- **Route:** MSC singular-order transport
- **Statement:** A coefficient-faithful positive Hilbert realization of exact physical MSC source and overlap columns has a finite Bessel bound iff `1 < Re ρ`; at `Re ρ≤1`, every realization has arbitrarily large finite-packet analysis amplification.

## Proof chain

Bessel puts both analysis columns in `ℓ²`; `ℓ²·ℓ²⊂ℓ¹`; mode norms cancel; exact corpus product becomes squarefree-Möbius mass at `Re ρ`, summable iff `1<Re ρ`. Conversely, balanced weight `wₙ=exp((Re ρ-σ)log n)` constructs an exact canonical `ℓ²` realization with orthonormal normalized modes.

## RH consequence

Every hypothetical strict-right Xi zero has `1/2<Re ρ<1`, so no frame, Riesz basis, bounded-synthesis family, or Gram-Schur-stable non-diagonal completion can retain both exact MSC columns. Gauge-breaking alone is insufficient; surviving geometry must be non-Bessel singular/distributional.

## Evidence

- **Lean:** `HedenmalmGammaSewnSquarefreeFisherBesselHilbertStabilityWall.lean`.
- **Capstones:** `exists_mscPhysicalOverlapBesselHilbertRealization_iff`, `exists_besselViolation_of_re_le_one`, `strictRightXiZero_mscBesselHilbertStabilityWall`.
- **Audit:** Targeted build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`.
- **Novelty:** Bessel bounded-analysis theorem is classical; exact MSC arithmetic stability wall and compulsory non-Bessel survivor had no corpus/literature collision through 2026-08.
