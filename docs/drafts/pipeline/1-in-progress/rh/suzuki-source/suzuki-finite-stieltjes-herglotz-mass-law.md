# Suzuki finite-Stieltjes Herglotz mass law

- **ID:** suzuki-finite-stieltjes-herglotz-mass-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-34 theorem-first scan of `SuzukiCarlemanCentralFlux.lean` and
  `SuzukiCarlemanStieltjesFlux.lean`
- **Statement:** For every finite negative-Stieltjes realization of the two normalized Suzuki
  source jets, upper-half-plane Herglotz positivity of the affine-sewn exterior Weyl quotient
  forces its chord-weighted spectral mass to fill the exact gap between the asymptotic edge and
  Xi central curvature. Simultaneously, the central residue has the corresponding exact split,
  the source flux meets the Xi-curvature threshold, and that flux is strictly negative.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Three exact `scripts/formal_tools.py research` searches found no consumer combining Suzuki's
Herglotz residue bound with the finite negative-Stieltjes chord-mass equivalence. The source file
states both ingredients separately and explicitly leaves source selection as the live interface.

## Paper proof

The finite negative-Stieltjes affine-intercept formula evaluates central source flux as the real
number `edge - sum(weight_i * chordKernel_i)`. The central residue theorem adds this flux to the
fixed term `-XiC''(0)/XiC(0)`. Herglotz positivity forces flux at most `XiC''(0)/XiC(0)`; rearranging
is exactly the spectral-mass lower bound
`edge - XiCurvature <= sum(weight_i * chordKernel_i)`. Since Xi central logarithmic curvature is
strictly negative, the same threshold makes source flux strictly negative.

## Lean formalization

`RHTower/Suzuki/SuzukiFiniteStieltjesHerglotzMassLaw.lean` proves the residue, source-flux, curvature,
spectral-gap, and strict-sign conclusions in one theorem. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteStieltjesHerglotzMassLaw.lean
```

passes.

## Hostile literature noncollision audit

Searches covered Suzuki screw functions, canonical systems, Weyl/Herglotz functions, and finite
Stieltjes realizations. Suzuki's original screw-function paper develops RH criteria from the Xi
screw profile ([arXiv:2206.03682](https://arxiv.org/abs/2206.03682)); the screw-line paper gives
norm/positivity formulations ([arXiv:2209.04658](https://arxiv.org/abs/2209.04658)); the canonical
system paper studies Xi-derived meromorphic inner functions
([arXiv:1204.1827](https://arxiv.org/abs/1204.1827)); and the 2026 synthesis treats Weil quadratic
forms through continuous screw kernels ([arXiv:2606.09096](https://arxiv.org/abs/2606.09096)).
None states this affine-sewn central-residue/chord-mass threshold for a finite negative-Stieltjes
source jet. No exact collision was found; this is not a priority claim.

## Log

- 2026-07-21 — New connector found only after reading newly present Suzuki Lean modules. Internal
  duplicate search and paper proof complete; Lean implementation started.
- 2026-07-21 — Five-coordinate mass law passed exact direct Lean check. Hostile Suzuki/canonical-
  system/Stieltjes search found no matching residue-to-chord-budget theorem. Exhaustion restarted.
