# Suzuki ground-edge Herglotz obstruction law

- **ID:** suzuki-ground-edge-herglotz-obstruction-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-35 theorem-first scan of `SuzukiCarlemanCentralFlux.lean` and
  `SuzukiGroundEdgeApertureObstruction.lean`
- **Statement:** Any positive-mass ground-edge source whose moment is at least half the negative
  Xi-curvature level cannot supply a Herglotz affine-sewn exterior when its weighted average is
  the central source flux. By Robin compression, the same no-go holds for every nonzero even
  eigenmode satisfying the exact boundary-flux equation.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Three exact `scripts/formal_tools.py research` searches found the separate central Herglotz
threshold, ground-edge average lower bound, and Robin compression, but no theorem consuming them
together to rule out a Herglotz exterior.

## Paper proof

Herglotz positivity forces central source flux at most `XiC''(0)/XiC(0)`. Positive mass and the
half-curvature moment lower bound force the ground-edge average strictly above that same curvature.
Identifying flux with average contradicts these strict inequalities. The even eigenmode corollary
uses `-2 U'(a)=lambda*mass` to identify the Robin boundary ratio with the same weighted average.

## Lean formalization

`RHTower/SuzukiGroundEdgeHerglotzObstructionLaw.lean` proves both weighted-average and
Robin-compressed no-go forms. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/SuzukiGroundEdgeHerglotzObstructionLaw.lean
```

passes.

## Hostile literature noncollision audit

Searches covered Suzuki screw functions and screw lines, Xi canonical systems, Herglotz/Weyl
positivity, finite-aperture ground modes, and Robin boundary ratios. The relevant primary Suzuki
sources are [arXiv:2206.03682](https://arxiv.org/abs/2206.03682),
[arXiv:2209.04658](https://arxiv.org/abs/2209.04658), and the Xi canonical-system construction
[arXiv:1204.1827](https://arxiv.org/abs/1204.1827). None states this positive-ground-moment
incompatibility with the affine-sewn central Herglotz residue threshold, nor its Robin-compressed
form. No exact collision was found; this is not a priority claim.

## Log

- 2026-07-21 — Found from exact central-flux and ground-edge/Robin terminal theorems after Law 35.
  Internal duplicate search and paper proof pass; Lean implementation started.
- 2026-07-21 — Weighted-average and Robin no-go forms passed exact direct Lean check. Hostile
  literature search found no matching ground-edge/Herglotz threshold law. Exhaustion restarted.
