# 101 — The liminf mean density; the density–depth defect; the equal-order rigidity locus

The two objects doc 100 §5 named are built.  One new Lean module — `ValDefect.lean` — realises the
liminf mean-valuation density and the density–depth defect.  All typecheck axiom-clean
`[propext, Classical.choice, Quot.sound]`; integrated in `RHTower.lean`.

## 1. (a) The liminf mean-valuation density

A zero-free window is rung-clean, so the density there is set to `⊤` — otherwise the empty-window
`0/0 = 0` convention would invert the polarity (RH → no zeros → density `0`).  With this lift:

- **`meanValE T := if #enclosed = 0 then ⊤ else ENNReal.ofReal (meanVal T)`** — the density in `ℝ≥0∞`.
- **`one_le_meanValE_of_V_one_eq_zero`** — `V 1 T = 0 → 1 ≤ meanValE T`: the level-1 rung (every
  enclosed jump has even order) floors the density at `1` (empty window → `⊤`, nonempty →
  `windowDepth ≥ 1 → meanVal ≥ 1`).
- **`meanValLiminf := liminf (meanValE ·) atTop`** — a single `ℝ≥0∞` invariant of ξ.
- **`one_le_meanValLiminf_of_rhLadder_one`** — `RHLadder 1 → 1 ≤ meanValLiminf`: the level-1 rung
  forces positive liminf density.  Its positivity is a producer-relevant analytic target; the
  density is finite-carrier-shadowable through the filtration length.

## 2. (b) The density–depth defect

- **`windowDepthNat T := (windowDepth T).toNat`** and **`defect T := meanVal T − windowDepthNat T`**
  — the gap between the average and the minimal enclosed 2-adic valuation.
- **`defect_nonneg`** — `0 ≤ defect T`: the average valuation is at least the minimal one (mean ≥
  min; the empty window gives `0 − 0`).
- **`defect_eq_zero_iff_equalOrder`** — for a window carrying zeros, `defect T = 0 ↔ ∀ enclosed
  height, filtrationLength = windowDepthNat`: the defect vanishes exactly on the **equal-order
  windows**, those whose enclosed jumps all share one 2-adic valuation.
- **`equalOrderLocus := {T | defect T = 0}`** — the rigidity locus: where it holds the valuation
  atomic measure reduces to a single-weight counting measure on the enclosed heights.

## 3. Status and the invariant ledger

All unconditional over the ξ divisor.  The two invariants sit atop the line-native ledger: the liminf
density is the eventual valuation floor (a graded-rung witness), the defect the valuation spread (a
rigidity witness).  Both are computed from the filtration lengths, hence finite-carrier-shadowable.

## 4. What this opens

The equal-order locus is a rigidity object made from bulk data; its structure is the next question.
Two forward moves: (a) the **equal-order value** `T ↦ windowDepthNat T on equalOrderLocus` — on an
equal-order window every enclosed jump has the same valuation `d`, so the atomic measure is `d · (#
enclosed) · uniform`; the map `T ↦ d` is a locally constant integer profile on the locus whose
constancy across a height band is a strong (all-equal-order) rigidity, and whose value `d = 0` is the
all-odd (level-1-failing) window; (b) the **defect variance** `∑ (filtrationLength t − meanVal T)²` —
the second moment of the valuation distribution over a window, a nonnegative rational profile whose
vanishing is again the equal-order condition and whose growth measures how far the window is from
valuation-rigid, a quantitative refinement of the defect that the transport can shadow.
