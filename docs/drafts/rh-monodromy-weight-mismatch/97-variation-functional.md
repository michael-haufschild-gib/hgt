# 97 — The variation functional; the closed discrete zero-set; the Stieltjes content

The three objects doc 96 §5 named are built.  One new Lean module — `Variation.lean` — realises the
variation functional `V k T`, its zero-set as a closed discrete subset of ℝ, and the Stieltjes
content of the census profile.  All typecheck axiom-clean `[propext, Classical.choice, Quot.sound]`;
integrated in `RHTower.lean`.

## 1. The variation functional

- **`badHeights k T`** — the rung-failing heights below `T`: box-zero heights whose jump divisor is
  not `2^k`-divisible.  **`V k T := (badHeights k T).card`**.
- **`V_mono`** — monotone in the height.
- **`V_eq_zero_iff`** — `V k T = 0 ↔ ∀ z ∈ boxZeros T, 2^k ∣ discJump z.im`: the variation vanishes
  exactly when every enclosed jump is `2^k`-divisible.
- **`V_eq_zero_of_windowCertificate`** — the rung certificate forces `V k T = 0` (per-zero
  divisibility ⟹ every jump divisible ⟹ no failing height).
- **`dvd_discJump_iff_finiteDiscJump`** — the decidable finite-carrier shadow: under the height-`t`
  transport data, `2^k ∣ discJump t ↔ 2^k ∣ finiteDiscJump H mg t`.  ξ's rung-failure at a height is
  decidably testable on the finite carrier.

## 2. (a) The variation zero-set — closed, discrete

**`badHeightSet k := {t | ¬ 2^k ∣ discJump t}`**.

- **`badHeightSet_inter_ball_finite`** — locally finite: each rung-failing height carries a box
  ξ-zero, and those are confined to a ball, so only finitely many lie in any bounded interval.
- **`isClosed_badHeightSet`** — closed in ℝ (a locally finite set is closed, via
  `LocallyFinite.isClosed_iUnion` on the singleton family).
- **`badHeightSet_isolated`** — discrete: every rung-failing height is isolated (a punctured ball
  around it meets the set nowhere), extracted from the finite intersection with a unit ball.
- **`rh_iff_forall_badHeightSet_empty`** — `RiemannHypothesis ↔ ∀ k, badHeightSet k = ∅`.  The
  boundary target is reduced to the emptiness of discrete subsets of the line — at every level, and
  the full tower recovers RH because only `0` is divisible by all `2^k`.

## 3. (b) The Stieltjes content

**`censusIncrement k a b := censusProfile k b − censusProfile k a`** — the census increment over
`(a,b]`, a `ZMod (2^k)`-valued content.

- **`censusIncrement_add`** — finite additivity over adjacent intervals.
- **`censusIncrement_eq_sum_sdiff`** — the content over `(a,b]` is the total ξ-order of the zeros
  with height in `(a,b]`, mod `2^k`.
- **`censusAtom k t := (discJump t : ZMod (2^k))`** with **`censusIncrement_eq_atom_of_slice`**: when
  the newly enclosed zeros sit at a single height, the content is that height's atom — the content
  is the atomic measure with weights `censusAtom`, supported on the zero heights.
- **`censusIncrement_eq_finite`** — under the transport data the ξ content equals the finite-carrier
  content `finiteCensusIncrement` over every interval.
- **`censusAtom_sub_finite`** / **`censusAtom_eq_finite`** — the atom difference equals the divisor
  difference `jumpDiff` reduced mod `2^k`; since `jumpDiff` is `2^k`-valued
  (`two_pow_dvd_jumpDiff`), the ξ and finite-carrier atomic measures coincide in `ZMod (2^k)`.  The
  divisor-difference measure of doc 96 §3 is exactly what vanishes mod `2^k`, and it is why the two
  contents agree.

## 4. Status and the three-object weld

All unconditional over the ξ divisor; the finite carrier enters only through its (finite) zero
Finsets and the boundary congruences.  The variation functional counts failures, the zero-set locates
them as a discrete subset of the line, the Stieltjes content weighs them mod `2^k` — three views of
the same jump data, with the finite carrier tracking each through the transport.

## 5. What this opens

The zero-set `badHeightSet k` is a closed discrete subset of ℝ whose emptiness is the rung; it is the
first fully **line-native** target — no charts, no configurations, just a subset of ℝ built from the
bulk.  The next object is the **level filtration** `badHeightSet 0 ⊇ badHeightSet 1 ⊇ …` (a height is
`k+1`-failing only if `k`-failing, since `2^{k+1} ∣ n ⟹ 2^k ∣ n`): a decreasing tower of closed
discrete sets whose intersection `⋂_k badHeightSet k` is the set of heights whose jump has infinite
2-adic valuation — exactly the heights forced empty by RH.  Two forward moves: (a) the **2-adic
valuation profile** `t ↦ v₂(discJump t) ∈ ℕ∪{∞}`, a line-native function whose sub-`k` level sets are
the `badHeightSet`s and whose finiteness everywhere is a graded rung; (b) the **filtration length**
`t ↦ min{k : t ∉ badHeightSet k}` as a height-indexed integer (the first level at which a height
stops failing) — a discrete profile on the zero heights whose boundedness on a window is a finite
certificate the transport can shadow.
