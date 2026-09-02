# HB first-live copy-diagonal causal phase no-go

- **ID:** HB-FIRST-LIVE-DIAGONAL-PHASE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** No copy-diagonal channel-Schwarz-odd Peierls weight realizes exact unit HB incidence through the actual multiplicity-matched completed balanced spin-two first-live jet on every Xi copy.

## RH proof chain

`first-live angular jet × radial/left-QNM Green weight` → exact same-pole AIME cancellation → HB unit boundary incidence → existing HB endpoint → RH.

This card attacks radial/left-QNM Green-weight realization. On a Hardy critical Xi copy, corpus factorization makes first-live angular jet nonzero and Schwarz-real; exact incidence forces its product with weight to equal negative unit AIME numerator, whose imaginary part is corpus-proved nonzero. Causal channel-Schwarz oddness forces every copy-diagonal weight Schwarz-real. Contradiction.

## Gates

- [x] Corpus novelty audit: no first-live-jet/causal-diagonal compatibility theorem found
- [x] Hostile tests: arbitrary copywise weights; exact multiplicity; unconditional Hardy critical witness
- [x] Closed Lean route kill: `d4HBActualMultiplicityMatchedCompletedBalancedSpinTwoCopyDiagonalCausalRouteKilled`
- [x] Direct Lean, targeted build, standard-axiom audit, umbrella wiring
- [ ] Publication-ready paper

## Positive survivor

Any surviving physical HB producer must be genuinely non-diagonal across Xi fibres/channels; no scalar copy-diagonal radial/left-QNM Green jump can close first-live incidence while obeying causal Schwarz reciprocity.

## Certificate

`ThetaCuspHawkingBMCompletedBalancedSpinTwoFirstLiveCausalDiagonalNoGo.lean`; targeted build PASS. Global lint remains blocked only by unrelated pre-existing unreachable modules.

## Literature audit (through 2026-08)

Birmingham--Mokhtari gives exact linear topological-AdS QNMs; Sberna et al. gives third-order AIME; Lestingi--Sberna--Green gives higher-order QNM perturbation with explicit continuum incompleteness. None states the completed-Xi multiplicity-jet/causal-diagonal phase obstruction proved here.
