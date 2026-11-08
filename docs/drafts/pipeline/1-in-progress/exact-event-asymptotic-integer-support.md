# Asymptotic integer support and integrable FE defects

- **ID:** exact-event-asymptotic-integer-support
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** exact-event-integer-support-fe-rigidity; obstacles-summary §2.5, B84
- **Statement:** A positive ordered spectrum with first frequency and mass one, masses at least one, and cos(2πλₙ) → 1 is exactly the positive-integer unit spectrum whenever its uncompleted Riemann FE defect is integrable in the Hamburger class.

## Argument to formalize

Write C_y(ε) for the Abel cosine means. Their limits are C₀ → β/π and
C₁ → 1/(2π); integrable defects contribute no radial residue. For every δ > 0,
choose M with 1−cos(2πλₙ) ≤ δ for n ≥ M. Positivity gives

    0 ≤ C₀(ε)−C₁(ε) ≤ 2ε Σ_{n<M} aₙ + δ C₀(ε).

Taking ε ↓ 0 and then δ ↓ 0 forces β = 1/2. Existing unit-density rigidity
gives λₙ = n+1 and aₙ = 1. This would rule out decaying displacement from the
integer lattice as a way to obtain finite uncompleted FE defect, not merely exact
integer support. No assertion about near-integer prime atoms alone follows: products
of such atoms need not approach the integer lattice.

## Gates

- [x] Paper mechanism identified, using existing Abel residue theorems.
- [x] Corpus audit found the unit-density and small-defect theorems, not this asymptotic-support statement.
- [x] Related literature: Favorov, [Uniqueness Theorems for Fourier Quasicrystals and Temperate Distributions with Discrete Support](https://arxiv.org/abs/2006.07610), studies rigidity when supports and masses approach each other. The present target uses an integrable FE defect and does not assume masses approach unit masses. No literature-priority claim.
- [ ] Lean proof and axiom audit.

No new result from this card is yet asserted in the programme README.
