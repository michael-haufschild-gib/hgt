# Xi bidescent anchor capacity

## Claim `XI-BIDESCENT-CAPACITY`

For finite off-line Xi packet `S`, let `V_S` be source-invisible fibre of closed full-jet
half-density relation and let `A : V_S → E` be restriction of any proposed horizontal anchor.

`rank(A) + dim ker(A) = Σ_{rho in S} ord_rho(Xi)`.

Hence `dim E < Σ ord_rho(Xi)` forces a vertically exact two-level field with distinct horizontal
endpoints collapsed by both source projection and anchor.

## Meaning

- Vertical completion transports horizontal defect; it cannot pay horizontal information debt.
- Xi multiplicity is conserved horizontal capacity: detected rank plus unresolved rank.
- Any RH route claiming vertical exactness alone forces horizontal descent is falsified by explicit
  under-capacity witness.

## Paper proof

1. Closed source kernel is linearly equivalent to full finite Xi-jet vertical fibre.
2. Off line, fibre dimension is total analytic Xi multiplicity.
3. Restrict anchor to that fibre and apply rank-nullity.
4. A sub-multiplicity codomain leaves nonzero kernel vector; hold it constant in vertical
   coordinate to obtain claimed bidescent witness.

## Novelty boundary

Meyer supplies spectral multiplicity; generic rank-nullity is classical. Corpus separately
supplies Xi vertical-fibre multiplicity and bidescent conservation. Search found no exact theorem
joining them into this quantitative horizontal-capacity law. Preliminary novelty only.

## Falsifiers

- Rank sum differs from analytic multiplicity.
- Sub-multiplicity anchor resolves every horizontal pair.
- “Vertical” field is not exactly glued at every horizontal endpoint.

## Status

Formalized in
`DeningerMeyerHalfDensityFiniteXiJetHorizontalAnchorCapacity.lean`:

- `deningerMeyerFiniteXiJet_horizontalAnchor_rank_add_unresolvedRank`
- `deningerMeyerFiniteXiJet_horizontalAnchor_unresolvedRank_lower_bound`
- `deningerMeyerFiniteXiJet_exists_verticallyExact_unresolvedHorizontalPair`

Direct Lean and targeted module build pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
Global lint reaches this module but retains unrelated pre-existing HTGeometry umbrella error.
