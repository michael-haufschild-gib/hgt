# PTR bare helical harmonic conormal law

- **ID:** ptr-bare-helical-harmonic-conormal-law
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** literal `photonicPrimeConstitutiveHarmonic` and the canonical prime complex-PTC conormal family
- **Statement:** A spectral-label-blind boundary law depending only on one instantaneous bare prime helical coefficient can produce the full PTR conormal amplitude family.

## No-go closure

- **Exact killing theorem:** one fixed output cannot equal both the target at `Re s=1/2`, which is bilaterally moderate, and at `s=0`, which is not. The target’s exact moderation criterion gives the contradiction.
- **Strongest positive survivor:** a valid boundary law must retain spectral/temporal matching data (or an equivalent nonlocal datum) in addition to the instantaneous helical coefficient.
- **Route consequence:** the finite material harmonic is a nonzero coupling source, not the conormal amplitude law. The remaining PTR task is a literal infinite-carrier temporal-boundary map with this necessary spectral dependence, then defect confinement.
- **Lean status:** dependency-closed `PhotonicBareHarmonicConormalNoGo.lean`; direct audit and leaf OLean passed. The no-go uses only `propext`, `Classical.choice`, `Quot.sound`. Umbrella build intentionally not run.
