# Sonin exterior Shannon-variance partition universality law

- **ID:** `sonin-exterior-shannon-variance-partition-universality-law`
- **Law:** LAW507
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SoninExteriorShannonVariancePartitionUniversalityLaw.lean`

## Theorem

For every positive Sonin aperture `a`, the zero-mode-subtracted exterior compressed Hamiltonian
`E_a` has exact Shannon trace and a lossless retained/fluctuation partition:

```text
Re tr(E_a) = 4 a^2,
||E_a||_HS^2 + Re tr(E_a - E_a^2) = Re tr(E_a) = 4 a^2.
```

Thus the exterior supersymmetric factor alone carries the full finite-aperture occupation budget:
retained Hilbert--Schmidt energy plus exterior free-fermion number variance.

## Theorem-generated derivation

Whole-corpus theorem-leaf pairing and subsequent source reading exposed:

- `hsNormSq_centralSoninExteriorCompression_eq_prolateBlock`;
- `re_opTrace_centralExteriorCompressionImpurity_eq_transition_hsNormSq`;
- `hsNormSq_centralProlateBlock_add_transition_eq_four_mul_sq`;
- `opTrace_centralSoninAlternatingBlock_eq_exteriorCompression`;
- `re_opTrace_centralProlateBlock_eq_four_mul_sq`.

The corpus separately proves supersymmetric equality of retained factors, equality of impurity
channels, the interior occupation budget, and full-counting trace reflection.  It does not state
the induced exterior occupation law.

## Dependency-closed paper proof

Trace reflection identifies the complex traces of interior and exterior compressed Hamiltonians.
Taking real parts and applying the central Shannon-number theorem gives
`Re tr(E_a) = 4a^2`.

Supersymmetric factor equality replaces `||E_a||_HS^2` by the prolate-block Hilbert--Schmidt
energy.  Exterior impurity/transition equality replaces `Re tr(E_a-E_a^2)` by transition energy.
The existing interior occupation budget says the sum of those two substituted terms is exactly
`4a^2`.  Combining with the trace value yields the full chained equality.  No numerical
computation is used.

## Strict corpus delta

Existing full-counting reflection compares the two factors, while existing free-fermion budget is
written only in the interior/prolate chart.  New law transfers the entire occupation partition to
the zero-mode-subtracted exterior chart and identifies its total directly with its own trace.

## Lean result

`formal/GaloisForLFunctions/RHTower/SoninExteriorShannonVariancePartitionUniversalityLaw.lean`
proves:

- `re_opTrace_centralSoninExteriorCompression_eq_four_mul_sq`;
- `hsNormSq_centralSoninExteriorCompression_add_impurity_eq_trace_eq_four_mul_sq`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/SoninExteriorShannonVariancePartitionUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.

- Classical prolate literature studies time-band limiting, Shannon-number eigenvalue counts, and
  clustering near zero and one.
- Trace-ideal literature supplies generic identities for trace-class and Hilbert--Schmidt
  operators.
- Targeted searches found no zero-mode-subtracted exterior Sonin factor, no supersymmetric
  exterior/interior reflection with this construction, and no exact exterior retained-energy plus
  impurity partition at `4a^2`.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the concrete
exterior Sonin factor and exact transferred partition, not for the scalar identity
`lambda^2 + lambda(1-lambda) = lambda`.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
