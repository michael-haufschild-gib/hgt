# 126 — The carrier's hole-zero disposition: count pinned, positions free

Formal home: `formal/GaloisForLFunctions/RHTower/CarrierCountConstraint.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`).
Discharges both halves of the doc-125 forward goal; the constraint system on
one pinned annulus is settled.

## 1. The count identity, carried [PROVED HERE]

- `configList` bridge: indexed configurations with multiplicities ARE list
  splits (`configList_length`, `configList_map_prod`, `configList_mem`).
- `enclosed_configuration_count_of_domination`: the total multiplicity of ANY
  enclosed configuration of ANY member dominating ξ on the charts of an
  isolating annulus equals the central ξ-order — the banked list-split count
  identity (`enclosed_count_eq_of_split_domination`, ledger machinery) carried
  to multiplicity-indexed configurations.
- `configuration_parity_of_circle_domination`: the parity from ONE circle —
  domination on a single interior circle already pins the count parity, via
  the holonomy transfer (`holonomy_eq_of_circle_domination`) against the two
  trace-count formulas. Strictly weaker input than the chart-domination count
  identity; boundary data on one circle suffices for the bit RH₂ cares about.

## 2. The negation surface [PROVED HERE]

`emSplit_odd_count_at_odd_xi_order`: at a strip point of odd ξ-order,
dominating splits of the completed EM member exist unconditionally
(`emSplitData_exists`) and EVERY one of them has an odd hole count. The finite
carrier's hole-zero disposition is, literally and machine-checked, the surface
on which the base rung is decided.

## 3. The constraint system, settled [PROVED HERE]

Which placements `zs` (hole-confined zero lists) are compatible with SOME
member dominating ξ on the charts of the pinned annulus?

**Necessary:**
- count: `zs.length = m` (the central ξ-order) — §1;
- open-hole confinement (`dominating_split_zeros_lt_hole`): every zero of a
  dominating split lies STRICTLY inside the hole. A placement touching the
  hole boundary is incompatible whatever the cofactor: approaching the
  boundary zero through the annulus drives the member to `0` while ξ holds its
  isolation floor.

**Sufficient:**
- `exists_dominating_split_of_configuration` (realizability): every placement
  confined to an inner radius `r₁ < r₀` with the polynomial margin
  `m·r₁·(R+r₁)^{m−1} < (r₀−r₁)^m` IS the zero list of a dominating member —
  built from the peel cofactor of ξ itself; the telescoping product bound
  (`list_prod_sub_prod_norm_le`) supplies the estimate.
- `exists_dominating_split_central`: the central placement (`m` copies of the
  centre) always realizes — the margin is vacuous at `r₁ = 0`, so the
  compatible set is nonempty for every geometry.

**The characterization** (`xi_dominating_configuration_iff`): under the margin,
a placement is compatible IFF its count is `m`. Positions inside the hole are
completely free; only the count is pinned.

## 4. Exhaustion audit

The goal's two clauses are discharged:

- Count identity onto the carrier: configuration form, one-circle parity form,
  negation surface. Full count EQUALITY holds (not just parity), so all dyadic
  levels are subsumed; nothing at count level remains.
- Constraint system: characterized — count pinned exactly, open-hole
  confinement necessary, positions otherwise free in the margin regime,
  compatible set never empty. Everything at one pinned annulus; `N` never
  flows.

The one residual is deliberately typed and carries no RH₂ content: the exact
radius threshold between the necessary condition (strict interior) and the
sufficient margin — a quantitative multiplicative-approximation question on one
annulus (can a ball-analytic nonvanishing cofactor track `(z−ρ)^m h/(z−w)`
within relative error 1 on the annulus when `w` sits near the hole boundary?).
Both directions of the negation surface are complete WITHOUT it: counts are
pinned regardless of position, and central placements realize at every
geometry. It is a sharpening of the map, not a gap in the rung's reduction.

## 5. Where the lane now stands

Docs 117–126: the base rung is equivalent, through machine-checked
reductions with no analytic interface remaining, to the parity of a pinned
finite count — the hole-zero count of the completed EM member's dominating
splits, whose EVERY OTHER degree of freedom (positions, cofactor, trace,
probe) is now proven irrelevant or free. The mathematics that decides RH₂ is
concentrated in one integer per hypothetical off-line zero, and the fork of
doc 121 stands: producing that integer's parity requires an input that is
neither steerable nor a re-expression — the arithmetic of the specific
truncations `emCarrier N`, which is exactly what the lane's constraint-side
program must now engage.
