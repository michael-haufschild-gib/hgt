# Weak-interaction singular time expansion — promoted to stage 3 (2026-08-10)

Card `weak-interaction-singular-quantum-time-expansion.md` moved to `3-formalized` with companion
`-formalized.md`.  All five Lean gates closed; the two open gates (specialist proof audit, hostile
editorial pass) are not formalization gates.

## Four new modules

1. `HTGeometry/FiniteHorizonReporterHausdorff.lean` — equation `(7)`: weighted reporter family in
   `PiLp 2` over a unital C*-algebra, `norm_reporterFamily` = the card's `B_O`, family-wide
   stability, and `hausdorffDist_coupledReporterOrbit_le : d_H ≤ 2T|g|‖V‖B_O`.
2. `HTGeometry/ComplexAffineLinePolynomialAvoidance.lean` — real affine-line avoidance lifted to
   complex-coefficient obstructions at real parameters via a coefficientwise real/imaginary split
   (`mvPolynomialRealShadow`).
3. `HTGeometry/OneKnobSpectralActivationLaw.lean` — the one-knob law with the ACTUAL spectral
   relation polynomials: `countable_exceptional_coupling_of_maximallyProjective_witness`.
4. `HTGeometry/OneKnobLocalChainActivationLaw.lean` — the local qudit chain instance
   `exists_uniformQuditPath_countable_exceptional_coupling`.

## The decisive structural fact

The card's "tensor-local spectral witness", flagged for two sessions as research-level, was
**already formalized upstream**: the parent card
`3-formalized/nearest-neighbor-qudit-projective-spectral-maximality` proves a physical uniform
qudit-path Hamiltonian with maximally projective spectrum for all `n,q ≥ 2`
(`exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`).
Everything reduced to plumbing once the obstruction polynomials were connected across the ℝ/ℂ
coefficient boundary.  **Read the whole parent chain before declaring a witness missing.**

## Reusable interfaces discovered

- `complexSpectralCoefficientObstructionPullback coefficient k` — the balanced-character
  obstruction as an `MvPolynomial` in the real parameters (the symmetric-function step is already
  done: `matrixCharacteristicElementaryPolynomial`, `eval₂_spectralRelationCoefficientPolynomial_complex_esymm`).
- `complexSpectralCoefficientObstructionPullback_has_real_witness` — maximal projectivity ⇒
  obstruction ≠ 0 at that parameter (the direction needed to make each polynomial nonzero).
- `maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet` — the converse.
- `realHermitianSubmoduleMaximalSet L hL` unfolds definitionally to
  `polynomialHermitianMatrixMaximalSet (realAffineMatrixPolynomial 0 (realMatrixSubmoduleGenerator L))`,
  so the parent's Dense set feeds `countable_exceptional_coupling_...` directly via `Dense.nonempty`.

## Lean note

`simp [h]` on a cast identity `∏ (↑x)^k = ↑(∏ x^k)` loops (max recursion); use explicit
`rw [h, Complex.ofReal_re]` / `Complex.ofReal_im`.
