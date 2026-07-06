# 109 — The carrier weld: milestone M built, the grammar gate answered [PROVED HERE, Lean: `CarrierWeld.lean`]

The three bricks of the weld plan (doc 108 §"combined verdict"; audit follow-up) are
machine-checked. The structural-pivot gate did **not** fire: the chain grammar accepts
the construction. Every declaration axiom-clean `[propext, Classical.choice, Quot.sound]`.

## The construction

For a hypothetical off-line ξ-zero ρ with annulus data `0 ≤ r₀ < R`, take a member `F`
that on the annulus charts

- **(S)** SPLITS: `F = ∏_{w ∈ zs} (z−w) · u` with every centre `w` in the hole
  (`‖w−ρ‖ ≤ r₀`) and `u` analytic nonvanishing on the ball, and
- **(D)** DOMINATES: `‖ξ − F‖ < ‖F‖` pointwise on the charts.

Then the canonical chain runs from the cofactor `u` to ξ inside the ledger grammar:

- `ledgerChainE_prod_jumps` — **the jump-extraction gate, answered positively**: each
  listed zero enters by an exact monomial `jump_in` between consecutive *partial
  products* — the factorisation is an identity, not an approximation. (The gate worry —
  that consecutive *pencil members at different ratios* never factor exactly — is
  dissolved by choosing the chain's intermediate members as the partial products of the
  split itself.)
- `ledgerChainE_to_xi_of_split_domination` — one dominated move closes the gap from the
  full product to ξ. Event list: `zs.length` ones.

## Brick 1 — Rouché-type counting, no argument principle

`enclosed_count_eq_of_split_domination`: on an *isolating* annulus,
`ord_ρ(ξ) = zs.length` exactly. Proof mechanism: the chain transports the cofactor's
global root to roots of ξ with deck class `exp(2πi·zs.length/N)` (flux = number of
jumps); the isolating deck-class identity (doc 108, F1b) reads the same class as
`exp(2πi·m/N)`; at level `N = m + zs.length + 1` the classes agree only if the counts
do. The classical Rouché statement is recovered as a corollary of the ledger transport —
the argument principle is never used.

## Brick 3 — the weld (milestone M)

- `anchoredEventLedger_of_carrier_domination`: (S) + (D) + `Even zs.length` ⟹
  `AnchoredEventLedger ρ r₀ R ξ` — the pairing constructed, every clause supplied.
- `rhLadder_one_of_carrier_domination`: if every hypothetical off-line zero admits an
  isolating annulus with such an even split dominating member, then **every off-line
  vanishing order is even** (`RHLadder 1`). Composed through the single-annulus rung.

## Tightness — the interface is exactly the parity

`exists_split_domination_of_isolating`: the supply clause is never vacuous — the peel
itself (`ξ = (z−ρ)^m · h`) is a split dominating member with count `m`. Together with
brick 1 (any supply has count = m), this certifies the weld as a **lossless
re-coordinatization**: (D) and (S) are always satisfiable, and the evenness clause is
*equivalent* to the conclusion's content. Nothing was smuggled and nothing was lost.

Two readings, both important:

1. **The D–H filter is passed at the interface level automatically.** The weld theorem
   is FE-generic, as doc 108 predicted every producer-side statement must be; at an
   odd-order Davenport–Heilbronn zero the evenness clause is simply unsatisfiable. No
   false genericity was introduced.
2. **The content is now located with no remainder**: produce the split member
   *independently of knowing ord_ρ(ξ)* — from the carrier side — with its count parity
   certified by carrier data. By brick 1, any such certificate immediately decides the
   order parity. The route's open problems are now exactly:
   - **(D-supply)**: `‖ξ − c·A·gN‖ < ‖c·A·gN‖` on the annulus charts at a hypothetical
     off-line zero — mollifier/second-moment territory (the charts exclude the hole
     where both functions are small, so this is domination on an annulus, not at the
     zero);
   - **(S-supply)**: the split of the anchored carrier member near ρ — Hurwitz splitting
     of the carrier's nearby zeros, with centres pushed into the hole;
   - **(parity certificate)**: the count parity of the *carrier's* hole-zeros read from
     carrier boundary data — where the anchored tilt/orientation instruments
     (`incidence_anchored_mirror`, the defect steering of doc 108's addendum) are the
     designated tools, since the carrier's boundary behaviour, unlike ξ's, is an object
     with explicit finite structure.

Next object: **(D-supply) on the annulus charts** — the domination inequality for the
mollified anchored member in the chart region `r₀ < |z−ρ| < R`, which is a
carrier-closeness statement of exactly the shape the banked second-moment and
line-sup budgets (`SecondMoment`, `CarrierLineSup`, `completedGNFirstMomentBudget`)
control on vertical segments; carrying them onto the two slit charts is quantitative
work with existing instruments, and it is the single clause standing between the banked
machinery and a fully carrier-sided rung interface.
