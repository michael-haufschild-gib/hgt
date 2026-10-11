# Two-ended rank of the actual Weil pole source

- **ID:** weil-polar-source-endpoint-rank
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` RW
- **Statement:** For every positive aperture and nonzero real even/odd coefficient pair, the actual prime–Gamma source combination diverges with one sign at one endpoint. In particular it cannot be bounded on the aperture.

## Goal

Classify the logarithmic boundary singularities of the physical prime–Gamma source. A bounded arithmetic or lower-order correction cannot erase both endpoint channels. This is source-side structure; it does not sign the selected constrained ground or imply RH.

## Gates

- [x] 0 → 1: source-pure, exact profile, two-ended attack
- [x] 1 → 2: complete paper proof below
- [x] 2 → 3: `ccmPolarSourceParityCombination_endpoint_rank`, direct Lean check, named build, axiom audit

## Approach

Let `K(x)=e^(x/2)(B(a−x,a+x)−A(x))`, with bounded arithmetic error `A` and bounded reflection asymmetry of `B`. Put `P₊=K(x)+K(−x)` and `P₋=K(x)−K(−x)`. For `f=cP₊+dP₋`, the coefficient of the divergent `B(a−x,a+x)` at the right endpoint is `k_R=c(E+F)+d(E−F)`, where `E=e^(a/2)>F=e^(−a/2)>0`. Reflection gives the left coefficient `k_L=c(E+F)−d(E−F)`. The arithmetic remainder is bounded uniformly on the aperture. If `k_R≠0`, `f` or `−f` tends to `+∞` on the right. If `k_L≠0`, the same holds on the left. If both vanished, their sum gives `c(E+F)=0` and difference gives `d(E−F)=0`, hence `c=d=0`. This proves the dichotomy. Every endpoint collar has positive measure, so the combination is also essentially unbounded.

## Conjecture loop

- Direct conjecture: endpoint divergence excludes a zero constrained ground. **Fails as an argument:** divergence is in the fixed pole-source vector; the ground pairing can vanish or have either sign. Existing source surjectivity and Hermitian swap countermodel do not restrict a selected ground.
- **Positive survivor:** the two physical parity source channels have independent logarithmic endpoint coefficients. No nonzero real source direction has a bounded repair by lower-order arithmetic terms. This strengthens separate source nonvanishing and identifies the exact two-ended obstruction to a bounded-source comparison. It remains a source-geometry result, not a sign inequality or RH producer.

## Lean certificate and audit

- Module: `formal/GaloisForLFunctions/RHTower/CCMPolarSourceEndpointRank.lean`; wired into `RHTower.lean`.
- `lake env lean GaloisForLFunctions/RHTower/CCMPolarSourceEndpointRank.lean`: pass.
- `lake build --old GaloisForLFunctions.RHTower.CCMPolarSourceEndpointRank`: pass, 12783 jobs (dependency replay).
- `#print axioms` from `/tmp` for reflection and endpoint-rank theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: fails on unrelated concurrent unwired modules and `LiUpperQuadraticCriterion.lean:203` `sorry`; no issue reported for this module.

## Log

- 2026-10-10 — Created after RW and PBAP corpus search; no web or literature novelty test per user instruction.
- 2026-10-10 — Paper proof closed; Lean theorem built, axiom audited, umbrella import added. RH and selected-ground source sign remain open.
