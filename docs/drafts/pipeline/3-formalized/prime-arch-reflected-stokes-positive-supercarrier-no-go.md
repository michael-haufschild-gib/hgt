# Reflected Stokes positive-supercarrier no-go

- **ID:** C1-REFLECTED-STOKES-SUPERCARRIER-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED / CLASSIFICATION
- **Source:** C1 reflected prime--Gamma Stokes lane
- **Statement:** No finite positive measure dominating the raw critical reflected Stokes squared
  carrier can have compact Markov germ equal to the completed seam moment germ.

## Gates

- [x] Stage 1: exact claim and hostile audit
- [x] Stage 2: dependency-closed paper proof
- [x] Stage 3: exact Lean theorem and axiom audit

## Paper proof

Write `μ₀` for the raw critical squared Stokes carrier and `m₀` for completed zeroth moment.
Existing Lean proves `m₀ < ∫ 1 dμ₀`. Hence `m₀ < μ₀.real univ`. If `μ₀ ≤ μ` and `μ` is finite,
monotonicity gives `μ₀.real univ ≤ μ.real univ`. Germ equality at zero forces
`m₀ = μ.real univ`, contradiction.

## No-go closure

- **Killing mechanism:** finite positive supercarrier cannot subtract excess Stokes mass.
- **Positive survivor:** every exact repair must fail domination; it must delete/reweight raw atoms
  or introduce signed negative correction. Existing first-moment excess proves a constant
  counterterm cannot repair all degrees.
- **Representation lesson:** reflection repairs parity but not normalization. Positivity plus retention
  of raw physical atoms is incompatible with completed source germ.
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`. Generic domination theorem, exact survivor
  constraint, and closed no-supercarrier capstone pass targeted build. Axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
