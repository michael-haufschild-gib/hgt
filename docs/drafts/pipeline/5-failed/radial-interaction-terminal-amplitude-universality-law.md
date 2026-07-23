# Radial interaction terminal-amplitude universality law

- **ID:** radial-interaction-terminal-amplitude-universality
- **Stage:** 5-failed (classical scattering collision)
- **Type:** THEOREM (Lean)
- **Source:** cross-folder closure of the radial interaction transport identities and the generic
  integrable-derivative limit theorem
- **Statement:** A bounded solution of `W'' + c²W = ψW` on a ray, with nonzero real frequency and
  integrable potential, has two interaction amplitudes converging to their exact initial values plus
  the corresponding total transport integrals; the amplitudes reconstruct the solution at every
  finite point.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean passed; final axiom audit pending
- [x] 3 → 5 failed: post-proof search found the classical `L¹`-potential Jost/Levinson theorem

## Corpus inputs

- `hasDerivAt_radialInteractionPlus`
- `hasDerivAt_radialInteractionMinus`
- `norm_deriv_radialInteractionPlus`
- `norm_deriv_radialInteractionMinus`
- `radialInteraction_reconstruct`
- `tendsto_of_hasDerivAt_of_integrableOn_Ioi`
- `norm_sub_le_integral_norm_of_hasDerivAt`

## Proof

`[PROVED HERE]` On `(a,∞)`, differentiability of `W` gives continuity and hence strong
measurability.  Multiplying
the integrable potential by the bounded continuous factor
`exp(∓icx) W(x)/(2ic)` makes each exact transport derivative integrable.  Feed the two derivative
identities and these integrability certificates to the generic explicit-limit theorem.  Reuse the
phase-free derivative norm identities and the generic displacement theorem to retain a uniform
finite-endpoint transport bound, rather than proving convergence alone.

No computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.RadialInteractionTerminalAmplitudeUniversalityLaw`
- Main theorem:
  `RHTower.radialInteractionTerminalAmplitudeUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/RadialInteractionTerminalAmplitudeUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Novelty fails.  The theorem is a direct interaction-picture presentation of classical
one-dimensional scattering/Jost asymptotics for integrable potentials.

- Hryniv--Mykytyuk, *On the First Trace Formula for Schrödinger Operators*
  ([arXiv:2006.12206](https://arxiv.org/abs/2006.12206)), treats every real integrable line
  potential and invokes the standard right/left Jost solutions asymptotic to `exp(±ikx)`.
- Pushnitski--Štampach, *Schrödinger operators on the half-line with integrable complex
  potentials* ([arXiv:2601.05112](https://arxiv.org/abs/2601.05112)), proves oscillatory Jost
  solutions and their derivative asymptotics for complex `L¹` half-line potentials.
- Cotti--Guzzetti--Masoero, *Asymptotic solutions for linear ODEs with not-necessarily meromorphic
  coefficients* ([arXiv:2310.19739](https://arxiv.org/abs/2310.19739)), supplies a general
  Levinson-type asymptotic-fundamental-system framework for integrable perturbations.

The exact total-transport formulas and endpoint bounds are useful formal closure, but are the
fundamental-theorem-of-calculus coordinates underlying these known scattering asymptotics, not a
new literature-level law.

## Retirement

`LITERATURE COLLISION.`  Keep warning-free Lean connector wired because it closes an explicit
cross-folder promise; do not count it as novel survivor.

## Log

- 2026-07-23 — Whole-corpus terminal scan found that the interaction-picture file promises terminal
  amplitudes and the generic HTGeometry limit mechanism exists, but no theorem composes them.
- 2026-07-23 — Exact Lean proof added both terminal integrals, exact reconstruction, and uniform
  phase-free endpoint bounds.
- 2026-07-23 — Post-proof audit identified classical `L¹` Jost/Levinson scattering asymptotics;
  novelty route retired.
