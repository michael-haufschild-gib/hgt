# Source-selected Gamma Ward shared-ghost descent

- **ID:** RH-GAMMA-WARD-SHARED-GHOST
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** cross-corpus Frankenstein: Route-R Gamma Bockstein determinant + Route-L Big-Witt prime-clock Ward wall + CCM source dagger
- **Statement:** For `D_p(t) = -p^t`, a positive inverse-oriented ghost `c` satisfies `c D_p(t) = c⁻¹ D_p(-t)` exactly when `c = p⁻ᵗ`; hence one prime-independent ghost repairs both labels `2` and `3` exactly when `t = 0`.

## Goal

Classify the requested unconditional, source-selected, coefficient-faithful Gamma Ward descent rather than hiding its anomaly in a fitted contractible pair.  At an Xi divisor set `t = 2 Re rho - 1`.  A single Gamma/archimedean ghost must be independent of the retained ordinary-prime label, while reflection reverses its orientation.  Simultaneous Ward descent at labels `2` and `3` would force `t = 0`, then compose with the existing Big-Witt selected-Ward endpoint.

## Gates

- [x] 0 → 1 in-progress: exact claim, source/physical roles separated, two-prime attack fixed
- [x] 1 → 2 fully-proven: complete paper proof and hostile no-go audit
- [x] 2 → 3 formalized: targeted Lean module, scratch check, leaf build, axiom/lint audit
- [ ] 3 → 4 publication-ready: not claimed

## Conjecture / fail / pivot log

1. **Conjecture A:** fixed Cartier polarization makes resolved BV--Wold flatness descend to the physical Gamma scalar. **FAIL.** Existing `primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis` and Rees-corona comparison classify that descent as RH itself.
2. **Conjecture B:** coherent Big-Witt all-fibre cancellation lets a cyclic/BRST reporter erase the diagonal ghost while retaining the off-diagonal physical seam. **FAIL.** Strict Gamma/BV descent transports diagonal and off-diagonal with opposite full coefficients; the canonical cyclic correction retains the entire physical residue.
3. **Conjecture C:** allow an orientation-sensitive Faddeev--Popov correction, but require one source-selected Gamma ghost for every retained prime label. **ACTIVE.** Local correction exists, but its value is forced.  Two labels test whether it is genuinely source/Gamma-derived or merely fitted prime by prime.

## Paper attack

For a prime `p`, positivity gives `p^t > 0`.  The inverse-oriented Ward equation is

`-c p^t = -c⁻¹ p⁻ᵗ`.

For `c > 0`, multiply by `c` and use positivity:

`c² = p⁻²ᵗ`, hence `c = p⁻ᵗ`.

If the same `c` works for `p = 2` and `p = 3`, then `2⁻ᵗ = 3⁻ᵗ`.  Strict monotonicity of real exponentiation (or injectivity after logarithms) gives `t = 0`.  Conversely `t = 0`, `c = 1` works.  With `t = 2 Re rho - 1`, this is `Re rho = 1/2`.

The pointwise result will be connected in Lean to:

- `primeGammaPhysicalRotationDeterminant`,
- `deningerHalfDensityMateGain_two_eq_three_iff`,
- `FrankensteinPrimeClockParacyclicSelectedWardDescendsAt`.

## Hostile audit

- A prime-dependent family `c_p := p⁻ᵗ` repairs every label for every `t`; therefore local ghost existence alone is vacuous and must not be advertised as producer.
- A common same-orientation scalar correction is already blocked by `primeGammaCommonCorrectedRotationDeterminant_eq_reflection_iff`; inverse orientation is the only new case.
- Contractible fitted ghosts do not alter physical cohomology.  New target requires one label-independent Gamma ghost and keeps labels `2` and `3` visible.
- Result is a producer classification, not an unconditional RH proof.  Remaining arithmetic theorem is existence of the shared ghost from genuine source/Gamma Ward naturality.

## Novelty status

- Internal semantic search found common same-orientation correction no-go and primewise countercharacters, but no inverse-oriented shared-ghost classification or bridge to the Big-Witt selected Ward endpoint.
- Elementary algebra is not claimed as external mathematical novelty.  New knowledge is exact cross-corpus identification of what coefficient-faithful Faddeev--Popov descent must produce and why prime-local fitting is insufficient.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.SourceSelectedGammaWardSharedGhostDescent`
- Main local classification: `primeGammaInverseOrientedGhostWardEquation_iff`
- Unconditional fitted survivor: `primeGammaLocalInverseOrientedGhost_ward` and uniqueness
- Shared-label rigidity: `primeGammaTwoThreeSharedInverseOrientedGhostWard_iff`
- Frankenstein bridge: `frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff_primeClockWard`
- Global endpoint classification: `everyFrankensteinSourceSelectedGammaWardSharedGhostDescends_iff_riemannHypothesis`
- Exact leaf build: PASS
- Formal lint: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

## Log

- 2026-08-16 — Stage-1 claim frozen after two failed conjectures.
- 2026-08-16 — Paper proof and hostile audit closed; formalized and wired into `RHTower.lean`.
