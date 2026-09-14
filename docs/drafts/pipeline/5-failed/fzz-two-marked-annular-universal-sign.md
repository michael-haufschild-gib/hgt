# FZZ depth-one annular universal-sign producer

- **ID:** fzz-two-marked-annular-universal-sign
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `FZZCigarParityTwoMarkedSourceContact`
- **Statement:** Depth-one compact opposite-winding response cannot have geometry-independent sign.

## Goal

Test subroute
`depth-one compact sign → Ward orientation → balanced-Gamma saturation → passivity → RH`.

## No-go closure

- **Exact killing theorem/mechanism:** `fzzTwoMarkedAnnularUniversalSignRouteKilled`; at every
  physical level the full response realizes both signs as annulus geometry varies.
- **Strongest positive survivor:** exact contact--variance decomposition and unique neutral geometry,
  `existsUnique_fzzTwoMarkedAnnularFullMixedResponse_eq_zero`.
- **New insight:** position integration adds connected radial fluctuation but does not fix orientation;
  all-depth neutral completion must select geometry/phase and correlate screening depths.
- **Status:** Lean theorem dependency-closed; targeted leaf build and standard-axiom audit pass.

## Scope

Kills depth-one annular universal-sign producer, not FZZ-P. Full neutral screening sum remains live.
