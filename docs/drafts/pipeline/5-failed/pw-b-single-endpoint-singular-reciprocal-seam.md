# PW-B single-endpoint singular reciprocal seam

- **ID:** pw-b-single-endpoint-singular-reciprocal-seam
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B
- **Statement:** One literal Parikh--Wilczek endpoint event cannot simultaneously realize reciprocal energy and the source-native singular reflected-Gamma contact.

## Goal

Test the most literal possible source seam: identify one physical endpoint event with both the reciprocal-energy reverse and the singular first-winding contact. This isolates whether an actual multi-event/nonlocal calibration is mathematically necessary.

## Gates

- [x] 0 → 1 in-progress: literal endpoint energy and first-winding contact expressed at common backreaction scale.
- [x] 1 → 2 fully-proven: exact scale classification and incompatibility proof, dependency-closed.
- [x] 2 → 3 formalized: `RHTower.not_PWLiteralSingleEndpointSingularReciprocalSeam`; direct check, leaf build, and axiom audit green.
- [ ] 3 → 4 publication-ready: not applicable to retired subroute.

## Approach

For a positive source coordinate `x`, reciprocal endpoint energy `E(ε)=x⁻¹` forces `ε=x/2`. The literal first-endpoint singular contact `W₀(ε,E(ε))=exp(-x⁻¹)` forces `ε=x/4`. The two forced scales disagree; specializing to `x=1` disproves the universal one-event seam.

## No-go closure

- **Exact killing theorem/mechanism:** `not_PWLiteralSingleEndpointSingularReciprocalSeam` proves the direct one-event identification impossible. The endpoint-energy and source-contact scales are separately rigid in `schwarzschildParikhWilczek_endpointScale_eq_half_of_reciprocal` and `schwarzschildParikhWilczek_endpointScale_eq_quarter_of_singularContact`.
- **Strongest positive survivor:** Exact scale-split classification: a reciprocal-energy leg has `ε=x/2`, while the singular reflected-Gamma contact leg has `ε=x/4`. Any viable PW-B source seam must therefore supply a multi-event/nonlocal calibration that combines distinct scales while retaining the contact.
- **New insight:** The already-proved singular/transseries carrier cannot be promoted to a literal seam by identifying it with one physical endpoint. The remaining seam burden is not an unspecified normalization: it is a concrete two-scale causal composition problem.
- **Status:** Paper proof is the two endpoint identities plus injectivity of `Real.exp`. Lean module `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekSingleEndpointSeamNoGo.lean`; direct `lake env lean` and leaf `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingleEndpointSeamNoGo` passed. `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-09-21 — direct single-endpoint PW-B source seam retired; two-scale survivor retained.
