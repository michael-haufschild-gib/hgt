# Sonin semilocal probe-universal source-separation law

## Status

Fully proven on paper; Lean 4 source written. Exact check deferred because both terminal source
modules lack `.olean`; dependency builds are reserved for final audit by user rule.

## Theorem-first source

- `exists_finiteSoninSemilocalRelativeTrace_ne_allWeylSourceGenerators`: one finite prime-power
  test separates canonical projection-correction relative trace from exact Weyl tangent source and
  every Wigner--Smith source generator.
- `opTrace_normalizedHilbertSchmidtCentralTangentCarrier`: any cyclic carrier normalized by a
  nonzero Hilbert--Schmidt probe has trace exactly equal to its scalar tangent coefficient.
- `I_mul_deriv_soninSemilocalWeylFluxOrbit_zero`: Weyl tangent coefficient is actual semilocal
  prime-flux/von Mangoldt coefficient.
- `summable_traceNorm_normalizedHilbertSchmidtCentralTangentCarrier_iff`: changing fixed nonzero
  probe cannot change scalar source summability phase.

Corpus research found only canonical-probe specialization; no theorem made source-separation
uniform over all complex Hilbert spaces and all nonzero Hilbert--Schmidt cyclic probes.

## Universal law

There exists one finite prime-power test such that, on every complex Hilbert space and for every
nonzero Hilbert--Schmidt probe, failed projection-correction relative trace differs from sum of
normalized cyclic tangent traces. Thus no probe geometry, rank, or scale can repair failed
geometric scalarization; obstruction lies in source itself.

## Paper proof

Take separating test from source-replacement theorem. For arbitrary nonzero Hilbert--Schmidt
probe, self Hilbert--Schmidt inner product is nonzero. Universal normalized-carrier trace theorem
therefore reduces every cyclic trace to prime-flux coefficient. Weyl tangent theorem identifies
same coefficient with exact Weyl source generator. Equality with cyclic sum would contradict
chosen test's source-separation property. No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.SoninSemilocalProbeUniversalSourceSeparationLaw`.

Full exact command is deferred to final dependency audit.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
