# 110 — The three supply problems: (S) discharged, (D) reduced to the named interfaces, parity in boundary form

[PROVED HERE, Lean: `CarrierSplit.lean`, `ZetaDominationTransfer.lean`] — the three named
problems of doc 109, attacked in one pass. Survey verdict first: the tree already held
more than expected, and the build reuses it.

## What the tree already offered (survey)

- `ZetaCarrier` §7 had the ENTIRE (D)-transfer at the pointwise level:
  `xi_eq_archFactor_mul_zeta`, `xi_sub_completedGN`, `completed_domination_iff`
  (completed domination ⟺ raw `‖ζ−gN‖ < ‖gN‖`), and the two NAMED interfaces of the
  anneal reduction — `AFEAccurateOn` (ζ-accuracy ε) and `CarrierFloorOn` (carrier floor ε)
  — with `completed_domination_of_interfaces` assembling them on any strip subset.
- `LedgerTelescope` had `ledgerChainE_trans` (chain concatenation).
- `AnchorSupply` has `exists_norm_floor_in_window_of_secondMoment` — a (LOW)-type floor
  from second-moment data on line windows — and the mollified-carrier anchor machinery;
  `CarrierLineSup` has the line-sup budgets. These are the designated suppliers of the
  interfaces on vertical segments.
- `exists_peel` (Peeling) preserves orders away from the peeled point — the exact clause
  that drives the multi-peel recursion.

## (S-supply) — DISCHARGED as a theorem (`CarrierSplit.lean`)

- `charts_union_eq_annulus` — the two slit charts cover the full annulus (each point off
  the centre avoids one slit).
- `finite_closedBall_zeros` — an analytic member with a nonvanishing point has finitely
  many zeros in the closed hole: an infinite zero set accumulates in the compact hole,
  and the isolated-zeros alternative at the accumulation point forces the member to
  vanish identically on the ball.
- `exists_split_of_finite_zeros` — complete peeling by descent on the zero-set
  cardinality: the cofactor after one peel has the original zero set minus the peeled
  point (order preservation), so a finite hole-confined zero set peels off entirely.
- `exists_split_of_domination` — **the (S) clause of the weld is a theorem**: domination
  on the charts ⟹ nonvanishing on the whole annulus (cover) ⟹ zeros confined to the
  hole and finite ⟹ split.

## The weld upgraded: milestone M with (S) gone

- `anchoredEventLedger_of_domination` — domination + "every split has even count" ⟹
  the anchored event ledger. Two clauses, not three.
- `rhLadder_one_of_domination_parity` — the base rung from domination + parity on one
  isolating annulus per off-line zero.

## (parity certificate) — boundary form (`split_deckClass_one_iff_even`)

Any analytic square roots of a split member on the two slit charts have deck class
`exp(2πi·count/2)`: **the class is trivial iff the count is even**. The parity the weld
consumes is the triviality of the member's own mod-2 deck cocycle — a carrier-side
boundary datum with no reference to ξ. This is the object the anchored tilt and
defect-steering instruments (doc 108 addendum) are built to certify: the carrier's
boundary phase data decides its own cocycle.

## (D-supply) — reduced to the named interfaces (`ZetaDominationTransfer.lean`)

- `rhLadder_one_of_zeta_carrier_close` — the base rung from RAW ζ-carrier closeness:
  `‖ζ − gN‖ < ‖gN‖` pointwise on the slit charts of one isolating annulus per off-line
  zero, plus the parity. The completed domination is recovered through the banked
  `completed_domination_iff` (the arch factor divides out).
- `rhLadder_one_of_interfaces_parity` — **the capstone**: the base rung from
  `AFEAccurateOn` + `CarrierFloorOn` on the charts, plus the parity. The rung's analytic
  burden now IS the anneal reduction's own two named residues, localized to one isolating
  annulus per hypothetical off-line zero, plus one mod-2 cocycle.

## Route state after this pass

```
RHLadder 1  ⟸  per off-line zero ρ, ONE isolating annulus with:
   (AFE)  ‖ζ − gN‖ ≤ ε   on the two slit charts     [named interface, doc 22/32/72]
   (LOW)  ε < ‖gN‖        on the two slit charts     [named interface]
   (PAR)  the completed member's mod-2 deck cocycle trivial
```

Everything else — split, chain, jumps, domination transfer, Rouché counting, pairing,
deck reading, isolation — is machine-checked with no residue. Status of the three inputs:

- (AFE) is the known hard core (mathlib lacks the exponential-sum foundation; the R7
  reduction isolated it) — but it is only needed ON THE CHARTS OF ONE ANNULUS per
  hypothetical zero, a much weaker demand than uniform strip accuracy.
- (LOW) on segments is exactly what `AnchorSupply.exists_norm_floor_in_window_of_secondMoment`
  already extracts from the banked second-moment budgets; the residual work is
  segment→chart geometry (two slit arcs instead of one vertical window).
- (PAR) is where the D–H filter says the arithmetic must sit, and where the tilt/defect
  instruments engage.

Next object: the segment→chart carry for (LOW) — expressing the two slit-chart arcs as a
finite union of vertical segments plus two horizontal caps, so the banked window floors
apply verbatim; it is pure annulus geometry over existing budgets, and it would leave
(AFE)+(PAR) as the only analytic content of the base rung.
