# Prime barycentric-sampling joint escape universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/PrimeBarycentricProjectiveEscape.lean`
  - `tendsto_primeBarycentricProjectiveRatio_atTop`
- `RHTower/PrimeLogSamplingWeightObstruction.lean`
  - `tendsto_primeShiftedSincProfileSum_atTop`
- both mechanisms are forced by `primeReciprocalLogSqTailSum`

## Universal law

For every ordered pair of distinct prime labels, the pointwise minimum of the canonical
barycentric projective coefficient ratio and the critical shifted-sinc prime sampling profile tends
to infinity. Hence neither prime-tail observable can stay bounded on a common cofinal scale, even
after retaining only the weaker channel.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/PrimeBarycentricSamplingJointEscapeUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/RHTower/PrimeBarycentricSamplingJointEscapeUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
