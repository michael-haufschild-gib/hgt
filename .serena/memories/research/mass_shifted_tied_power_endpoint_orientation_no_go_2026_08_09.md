# Mass-shifted tied-power endpoint orientation no-go (2026-08-09)

Task: attack `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 using `docs/notes.md` source-conditioned joint realizability idea.

## Exact finding
The local source-like strengthening is still insufficient. Define tied-power moments
`s_k(Z)=Re Σ_{z∈Z} z^(k+1)` and atomic transport `z(h)=z/(1+h z)`. Two conjugation-stable clouds
`Z+={11,9,10+i,10-i}` and `Z-={11+i,9+i,9-i,11-i}` have identical moments `(40,400,4000)`, the same positive singular size-2 Hankel face and kernel `(-10,1)`, but fourth moments `40004` and `39984`, hence opposite first-unseen remainders `+4` and `-16`. Every atom obeys the strict Xi sector `84^2|z|^2 < 85^2(Re z)^2`.

Rescaling by `1/256` additionally gives the exact centered-Xi radius bound `41^2|z|^2<4` (i.e. `|z|<2/41`). The common visible moments are `5/32,25/4096,125/524288`; common kernel is `(-5/128,1)`; remainders are `2^-30>0` and `-2^-28<0`. Transport is exact at every order:
`d/dh (z/(1+h z))^(k+1)|_0 = -(k+1)z^(k+2)`.

Therefore finite tied-power form + conjugation + exact Xi sector/radius + current-face positivity + mass-shift transport cannot orient the affine extension class. A successful source theorem must use a genuinely global property of one normalized completed Xi function (coupled Euler–Gamma incidence), not separate local marginals. This is the precise useful survivor from `docs/notes.md`.

## Lean
- `formal/GaloisForLFunctions/HTGeometry/TiedPowerSectorOrientationNoGo.lean`
- `formal/GaloisForLFunctions/HTGeometry/TiedPowerEndpointOrientationNoGo.lean`
- capstones `HTGeometry.tiedPowerNarrowSectorOrientationNoGo`, `HTGeometry.tiedPowerEndpointOrientationNoGo`
- both targeted `lake build` commands pass
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- both wired into `formal/GaloisForLFunctions/HTGeometry.lean`

## Documentation
- `docs/drafts/pipeline/3-formalized/mass-shifted-tied-power-sector-orientation-no-go.md`
- `docs/drafts/pipeline/3-formalized/mass-shifted-hankel-flat-quadrature-extension-class.md`
- §9.3 report equations (9.3.237)–(9.3.243)

Novelty remains unverified. Corpus already contains the stronger finite-entire-jet nonselection route, so do not re-prove mere even-entire/functional-equation finite-jet insufficiency. Next useful avenue should be global completed-source port dominance, likely through a polynomial-filtered heat/Euler–Gamma bridge.