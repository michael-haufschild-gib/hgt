# Theta-cusp center-mixed three-point localization law

- **ID:** theta-cusp-center-mixed-three-point-localization-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized; hostile literature audit passed)
- **Source:** Bottom-up closure of the terminal uniform-coalescence and large-gap three-point laws
- **Statement:** For every critical aperture, every possible failure of positive semidefiniteness
  of the center-mixed theta three-point matrix is confined to a bounded two-gap shell separated
  from the coalesced corner. Global PSD is equivalent to PSD on this shell.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and consumers read
- [x] Internal noncollision audit
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Exact repository research queries for `theta cusp center mixed three point nonpositive compact
annulus localization`, `uniform coalesced square large gap positive semidefinite`, and `center
mixed three point failure localization` found no existing theorem. The existing compact-core
theorem removes only the large-gap exterior; it does not remove the positive-definite coalescence
corner or localize every failure to the remaining shell.

## Paper proof

Fix aperture `0 < a < 1/2`. The uniform-coalescence theorem supplies `delta > 0` such that the
matrix is positive definite whenever both gaps lie in `(0, delta)`. The large-gap theorem supplies
`Y₀` such that the matrix is positive semidefinite whenever either gap is at least `Y₀`. Set
`Y = max Y₀ delta`.

Then `delta ≤ Y`, and the large-gap conclusion remains valid at cutoff `Y`. If a positive-gap
packet is not positive semidefinite, it cannot have both gaps below `delta`, because positive
definiteness implies positive semidefiniteness. It also cannot have either gap at least `Y`.
Therefore it lies in the shell

`(delta ≤ x or delta ≤ y) and x < Y and y < Y`.

The same dichotomy proves the exact reduction: global positive semidefiniteness trivially implies
shell positive semidefiniteness; conversely, any failure of global positive semidefiniteness lies
in the shell and contradicts shell positive semidefiniteness. `[PROVED HERE]`

## Lean formalization

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedThreePointLocalizationLaw.lean`
- Certificate: `ThetaCuspCenterMixedThreePointLocalizationCertificate`
- Capstone: `thetaCuspCenterMixedThreePoint_localizationLaw`

Exact direct check passed:

```text
lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedThreePointLocalizationLaw.lean
```

## Hostile literature noncollision audit

Post-proof searches covered Hedenmalm/Jacobi-theta spectral models, theta-kernel positivity,
three-point correlation matrices, coalescence, large-gap behavior, compact-core reductions, and
obstruction localization. Nearest sources were Hedenmalm's
[theta-based spectral eigenproblem](https://arxiv.org/abs/2606.17494), a distinct
[theta-kernel critical-strip localization](https://www.preprints.org/manuscript/202606.0062), and
a [finite-core Weyl/Volterra reduction](https://arxiv.org/abs/2606.29555). None defines the actual
center-mixed density matrix or proves its bounded two-gap failure shell and exact global-PSD iff
shell-PSD law. Verdict: `NO COLLISION FOUND`; no priority claim.

## Log

- 2026-07-21 — Found during post-Law-36 cross-folder HilbertMetric/RHTower consumer audit.
  Internal duplicate search and dependency-closed paper proof pass; Lean implementation written.
- 2026-07-21 — Exact direct Lean check passes. Hostile literature audit found no matching
  center-mixed three-point annular localization law. Exhaustion restarted.
