# Von Mangoldt--Gamma boundary/Beta-reflection fracture universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Lean-derived statement

For every sufficiently large source displacement, the raw von Mangoldt--Gamma source
simultaneously has:

- square-summable canonical prime-boundary coordinates;
- all-depth raw moments and exact Euler identification;
- entrywise finite-to-cofinal convergence;
- positive-semidefinite arbitrary depth packets;
- positive-definite injectively labelled depth packets;
- convergence of every admissible Bianchi anomaly packet.

Yet the canonical factorial/Beta reflection of the first separated even-order packet `[0,2]` is
not positive semidefinite. Consequently factorial/Beta reflection does not preserve positivity on
the complete positive-displacement boundary phase.

## Corpus inputs

- `positiveDisplacement_iff_vonMangoldtGammaBoundaryUniversalCertificate`
- `vonMangoldtGamma_betaReflectionPositivityGapUniversality`

No numerical computation or external premise is used.

## Paper proof

The displacement theorem identifies `0 < x` exactly with the complete raw boundary certificate.
Positivity `0 < x` holds eventually as `x -> +infinity`. The Beta-reflection theorem also holds
eventually and states that the raw `[0,2]` Gram is positive definite with positive determinant,
while its factorial/Beta reflection is not positive semidefinite. Intersect the two eventual sets.
Any hypothetical positivity-preservation theorem on every boundary-certified source contradicts
one point in this nonempty eventual intersection.

## Hostile subsumption audit

- The boundary-displacement parent has no factorial/Beta reflection and no positivity failure.
- The Beta-reflection parent retains only one raw positive packet; it does not place the witness
  inside the full finite-energy, all-moment, all-packet-positive boundary phase.
- The older factorial-normalization no-go similarly compares one raw block with its normalization,
  not the complete boundary certificate.
- The new theorem proves a preservation no-go, not a detached conjunction: the reflected failure
  occurs on a source satisfying the strongest existing raw positivity certificate.
- Whole-corpus search found no theorem relating
  `VonMangoldtGammaBoundaryDisplacementUniversalCertificate` to the factorial/Beta trace Gram.

## Lean verification

Formal module:

```text
formal/GaloisForLFunctions/RHTower/VonMangoldtGammaBoundaryBetaReflectionFractureUniversalityLaw.lean
```

Required exact check passed:

```text
lake env lean GaloisForLFunctions/RHTower/VonMangoldtGammaBoundaryBetaReflectionFractureUniversalityLaw.lean
```

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Post-proof literature boundary

Searches were run only after the Lean theorem passed. Closest located sources were:

- Belton, Guillot, Khare, and Putinar, *Moment-sequence transforms*, arXiv:1610.05740 / JEMS 24
  (2022), which classifies entrywise maps preserving moment sequences and positive Hankel
  matrices;
- Choi and Jafari, *Positive definite Hankel matrix completions and Hamburger moment
  completions*, arXiv:1509.06296, which studies positivity-preserving completion of partial moment
  sequences;
- general Hamburger/Stieltjes moment literature relating positive Hankel matrices to positive
  measures.

No located source states the source-specific fracture proved here: the complete
positive-displacement von Mangoldt--Gamma boundary certificate holds, while its canonical
factorial/Beta reflection fails positive semidefiniteness already on `[0,2]`, thereby refuting
positivity preservation on that entire universal phase. Negative search is not proof of priority;
specialist review remains required.

## Gates

- [x] whole-corpus source search
- [x] exact conjecture stated from theorem interfaces
- [x] dependency-closed paper proof
- [x] hostile corpus-subsumption audit
- [x] Lean exact check
- [x] umbrella wiring
- [x] post-proof literature audit
- [ ] final axiom/lint/build audit
