# BV/co-Poisson critical-provider terminal closure

- **ID:** `bv-copoisson-critical-provider-terminal-closure`
- **Stage:** 3 — formalized
- **Type:** DEPENDENCY-CLOSED SOURCE NO-GO + EXACT POSITIVE SURVIVOR
- **Scientific status:** `[FORMALIZED] [CANDIDATE NEW NO-GO]`
  `[ROUTE G PROVIDER TERMINALIZED] [ROUTE G OPEN] [NOT RH]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki/bv-copoisson-sharp-critical-half-weight-log-flux.md`
- **RH used:** no
- **Computation used:** no

## Closed mechanism

For the canonical sharp compact BV seed, the ordinary co-Poisson vector is in `L2`, its physical
critical half-weight is not, and its exact arbitrary-real-cutoff weighted energy obeys

```text
integral_0^T t |P(t)|^2 dt / log T -> 1/4.
```

The ordinary logarithmic boundary quotient cannot retain the missing normal class: ideal vectors
`e_0+e_j` have dense span. The sharper extended-property-S topology cannot accept the critical eta
Mellin seed: both parity choices expose an infinite nonzero reflected pole lattice, and no nonzero
polynomial clears either lattice. Multiplicative convolution by any integrable seed supported in
one positive compact interval cannot repair this resonance; the required even or odd moment
vanishing forces that seed to vanish almost everywhere.

These failures are not evidence that no completion exists. The separately paper-proved universal
Gamma--Gaussian property-S envelope supplies a noncompact completion for every moderate Mellin
datum, including off-line models. Completion existence is therefore nonselective. This
BV/co-Poisson completion/provider program is closed. Route G itself remains open because Suzuki's
actual source-coefficient, chord-mass, and global Pick/Ward mechanism has neither been constructed
nor class-completely refuted.

## Formal theorem map

| Paper content | Lean module | Exported theorem |
|---|---|---|
| sharp harmonic bounds | `BVCoPoissonSharpCriticalFluxCore` | `sharpHarmonicError_bounds` |
| exact cutoff flux | `BVCoPoissonSharpCriticalFluxCore` | `tendsto_integral_sharpCriticalFlux_cutoff_div_log` |
| arbitrary-real `1/4` flux | `BVCoPoissonSharpCriticalFlux` | `tendsto_sharpCriticalFluxFromZero_div_log` |
| ordinary `L2` survival | `BVCoPoissonSharpCriticalFlux` | `integrableOn_sharpCoPoissonP_sq_Ioi_zero` |
| critical non-integrability | `BVCoPoissonSharpCriticalFlux` | `not_integrableOn_sharpCriticalDensity_Ioi_zero` |
| dense ideal span | `BVCoPoissonLogBoundaryQuotient` | `logIdealSpan_topologicalClosure_eq_top` |
| even eta resonance | `BVCoPoissonHalfWeightResonance` | `polynomial_eq_zero_of_cancels_criticalEta_even_poles` |
| odd eta resonance | `BVCoPoissonHalfWeightResonance` | `polynomial_eq_zero_of_cancels_criticalEta_odd_poles` |
| compact even-moment rigidity | `BVCoPoissonCompactSeedRigidity` | `ae_eq_zero_of_even_moments_of_positive_compact_support` |
| compact odd-moment rigidity | `BVCoPoissonCompactSeedRigidity` | `ae_eq_zero_of_odd_moments_of_positive_compact_support` |

All modules are imported by `GaloisForLFunctions.RHTower`. All statements are unconditional.
Targeted module builds pass. `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound` for terminal exports.

## Exact scope boundary

The paper's Rademacher Gram/Stein supplement is not part of this formal card. It is not used to
prove any no-go above, and its candidate graph has an unbounded conormal, so it cannot reopen the
provider. No abstract `ell2` replacement is counted as formalization of that analytic limit.

This card proves neither Hermite--Biehler positivity nor a no-go for Suzuki itself. It prevents
following research theatre: renaming open source sign as a graph norm, assuming a divisor-selected metric,
claiming that generic property-S existence selects the critical line, or presenting a compact
archimedean correction after all-moments rigidity has forced it to zero.
