# Route E forward-interval Hall reduction — formalized closure

- **ID:** `route-e-forward-interval-hall-reduction-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./route-e-forward-interval-hall-reduction.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NO RH INPUT]`

## Lean module

`GaloisForLFunctions.HTGeometry.ForwardWindowHallMatching`
(umbrella: `GaloisForLFunctions.HTGeometry`).

## Formal theorem chain

`forwardWindow T H e = T ∩ Ioc e (e+H)` is the one-sided window neighbourhood;
`HasForwardWindowMatching E T H` is the existence of `f` with `Set.InjOn f E` and
`f e ∈ T`, `e < f e ≤ e + H` for every `e ∈ E`;
`ForwardWindowIntervalCondition E T H` is `#(E ∩ Icc a b) ≤ #(T ∩ Ioc a (b+H))` for all `a, b`;
`ForwardWindowHallCondition E T H` is the full family of Hall subset inequalities.

1. `forwardWindowIntervalCondition_of_hasMatching` — necessity of `(2)`.
2. `inter_Ioc_subset_biUnion_forwardWindow` (private) — a gap-free source subset has neighbour set
   containing the whole interval `(min s, max s + H]`.
3. `forwardWindowHallCondition_of_intervalCondition` — interval sufficiency, by strong induction
   splitting the subset at its largest interior window gap; the two parts have disjoint
   neighbour sets.
4. `hasForwardWindowMatching_of_hallCondition` — Hall's marriage theorem
   (`Finset.all_card_le_biUnion_card_iff_existsInjective'`) applied to the source subtype.
5. `hasForwardWindowMatching_iff_intervalCondition` — the card's boxed equivalence `(1)` ⇔ `(2)`.
6. `forwardWindowHallCondition_iff_intervalCondition` — the exponentially many Hall inequalities
   collapse exactly to the interval inequalities.
7. `card_inter_Icc_le_min` — the only two trivial bounds available from global cardinality.
8. `exists_windowExponent_iff_quarter_lt` — the sharp threshold `(7)`:
   `(∃ η, 0 < η ∧ η < κ ∧ 1/2 ≤ η + κ) ↔ 1/4 < κ`.

Scaling displays `(3)`–`(6)` on the paper card are asymptotic design statements with
unquantified implied constants, not theorems; their exact deterministic content is `(2)`, `(7)`
and the trivial bounds above, all formalized.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ForwardWindowHallMatching.lean` — clean, no
  warnings.
- `lake build GaloisForLFunctions.HTGeometry.ForwardWindowHallMatching` — green.
- `#print axioms` on statements 1, 3–8: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella import present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

The Route E source obligation `(4)` (a Carleson-type local exceptional-set estimate) remains open
on the parent card `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`.
