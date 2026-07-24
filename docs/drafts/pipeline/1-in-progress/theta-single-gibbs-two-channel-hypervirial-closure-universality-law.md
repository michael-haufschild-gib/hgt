# Theta single-Gibbs two-channel hypervirial closure universality law

- **ID:** theta-single-gibbs-two-channel-hypervirial-closure-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the rational Gibbs enclosure, Morse envelope,
  quadratic-to-two-channel embedding, Rayleigh--Ritz elimination, and polarized hypervirial
  replacement
- **Statement:** One finite rational enclosure of the first theta-cusp Gibbs moments forces the
  optimized two-channel hypervirial Rayleigh--Ritz certificate, the relaxed low-degree channel,
  and every linear prime--archimedean Hankel inequality; with the existing degree-two tail it
  forces the complete integer cone and RH.

## Goal

Connect the rational-enclosure terminal theorem to the later two-channel hypervirial endpoint
through every exact intermediate theorem, rather than treating their shared trace-Hankel consumer
as an accidental collision.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: completed; negative priority result

## Corpus inputs

- `thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_rationalMomentEnclosure`
- `thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_iff`
- `thetaCusp_quadraticVirialEnergyCertificate_of_morseQuadraticEnvelope`
- `quadraticSteinEnergyCertificate_iff_virialEnergyCertificate`
- `twoChannelSteinEnergyCertificate_of_quadraticSteinEnergyCertificate`
- `thetaCuspFirstRadialTwoChannelRayleighRitzCertificate_iff`
- `thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelVirialRayleighRitz`
- `primeArchSourceTraceHankelIntNonnegative_of_twoChannelSteinEnergy_of_degreeTwoTail`
- `riemannHypothesis_of_twoChannelVirialRayleighRitz_of_primeArchDegreeTwoTail`

## Proof

**[PROVED HERE]** Assume the finite rational enclosure. Its gate theorem produces the joint
single-Gibbs low-degree certificate. The exact reduction of that certificate supplies both the
Morse quadratic-envelope certificate and the relaxed fourth-moment inequality.

The Morse envelope implies the quadratic virial-energy certificate. Exact quadratic
Stein/virial equivalence converts this to the quadratic Stein-energy certificate. The quadratic
field is the coefficient pair `(1,-1/2)` in the two-channel span, so the existing embedding
produces the variational two-channel Stein certificate. Exact Rayleigh--Ritz elimination converts
that existential witness to the explicit two-by-two determinant certificate, and the polarized
hypervirial equivalence replaces every score product without changing the proposition.

The hypervirial consumer and the retained relaxed inequality prove every real linear
prime--archimedean trace-Hankel inequality. If the unchanged degree-two tail is also supplied, the
two-channel integer-cone theorem combines it with this complete constant/linear block to prove
`PrimeArchSourceTraceHankelIntNonnegative`; the RH consumer then proves RH. No numerical
approximation is executed: the rational enclosure remains an explicit analytic premise. ∎

## Strict gain over corpus endpoints

The enclosure theorem terminates at a scalar low-degree certificate and linear Hankel
nonnegativity. The hypervirial theorem starts from an independent two-channel certificate and
does not show how to obtain it. Their exact closure proves that the same finite rational boxes
already certify the optimized two-channel curvature geometry and expose the precise remaining
degree-two-tail gate to the complete integer cone and RH.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaSingleGibbsTwoChannelHypervirialClosureUniversalityLaw`
- Main theorem:
  `thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_rationalEnclosure`
- RH theorem:
  `riemannHypothesis_of_singleGibbsRationalEnclosure_of_primeArchDegreeTwoTail`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/ThetaSingleGibbsTwoChannelHypervirialClosureUniversalityLaw.lean`
- Result: passed warning-free.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Performed only after the dependency-closed Lean proof passed. Searches combining theta-cusp
Gibbs moments, Morse/Fisher bounds, two-channel Rayleigh--Ritz reduction, hypervirial identities,
and prime--archimedean Hankel positivity found only separate classical literatures on
Rayleigh--Ritz approximation, Gibbs variational inequalities, and Hankel determinants. No source
located states the exact finite-enclosure-to-hypervirial-to-RH closure. This is a negative search
result, not a priority claim.

## Log

- 2026-07-23 — terminal-pair scan exposed the shared `primeArchSourceTraceHankel` consumer.
- 2026-07-23 — full theorem-chain read revealed the exact quadratic `(1,-1/2)` embedding into
  the optimized two-channel span.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — Lean source passed the required exact-file check warning-free and was wired into
  `GaloisForLFunctions/RHTower.lean`.
- 2026-07-23 — post-proof literature audit found separate Gibbs, Rayleigh--Ritz, and Hankel
  frameworks, but not the exact theta-cusp closure chain.
