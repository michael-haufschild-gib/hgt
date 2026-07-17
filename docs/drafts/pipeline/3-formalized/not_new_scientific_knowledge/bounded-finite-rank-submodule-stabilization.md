# Bounded finite-rank submodule stabilization

- **ID:** `bounded-finite-rank-submodule-stabilization`
- **Stage:** 3-formalized
- **Type:** EXACT STABILIZATION LEMMA / CORPUS BRIDGE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [PARENT LINEAR ALGEBRA] [NOT NEW SCIENCE]`
  `[NOT AN RH RESULT]`
- **Source:** research programme 5 successor from
  `../../5-failed/operator-presentation-bounded-innovation-stabilization.md`
- **Statement:** A monotone chain of finite-dimensional submodules whose total ranks are uniformly
  bounded is eventually constant.

## Exact theorem

Let `F` be a division ring, `E` an `F`-module, and

```text
V_0 <= V_1 <= V_2 <= ... <= E
```

a monotone sequence of finite-dimensional submodules.  If there is `B in N` such that

```text
finrank_F(V_n) <= B    for every n,                         (1)
```

then there is `N` such that

```text
V_n = V_N             for every n >= N.                    (2)
```

In particular, `(2)` holds if every `V_n` is contained in one finite-dimensional submodule `W`.

## Paper proof

Monotonicity of the submodules makes `n |-> finrank_F(V_n)` a monotone sequence of natural numbers.
The bound `(1)` makes this sequence eventually constant.  For `n >= N`, one has both
`V_N <= V_n` and equality of finite ranks; equality of finite-dimensional submodules follows.
If all `V_n <= W`, their ranks are bounded by `finrank_F(W)`, giving the final assertion.  Every
dependency is explicit and there is no open core.

## Programme-5 significance

This is the exact repair of the programme's ambiguous word “bounded” in the linear transition
axis.  A bound on each increment says nothing: a chain may add one dimension forever.  A uniform
bound on the **total** finite rank forces stabilization.  Strict compatibility alone is orthogonal
to this Noetherian condition.

The corpus already proved eventual constancy for a bounded monotone natural-number sequence in
`HolonomicityLimit.lean`; the missing reusable result was the lift from stabilized ranks to
stabilized submodules.

## Lean theorem surface

Module: `formal/GaloisForLFunctions/HTGeometry/FiniteRankSubmoduleStabilization.lean`.

- `monotoneSubmodule_eventually_constant_of_finrank_bddAbove`
- `monotoneSubmodule_eventually_constant_of_le_finiteDimensional`

## Gates

- [x] 0 -> 1: exact total-rank hypothesis isolated
- [x] 1 -> 2: dependency-closed paper proof complete
- [x] existing Lean surface checked before formalization
- [x] novelty and parent-theory verdict assigned
- [x] 2 -> 3: unconditional Lean theorem batch
- [x] targeted touched-file check
- [x] touched-slice formal lint and axiom audit

## Log

- 2026-07-17 -- Extracted as the exact stabilization residue of programme 5; per-increment
  boundedness and strictness were explicitly excluded from the theorem.
- 2026-07-17 -- Promoted to Stage 3 after direct cached compilation.  `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  The project lint reports no proof debt or
  reachability defect for this module; its nonzero repository-wide exit is an unrelated pre-existing
  umbrella-reachability baseline.
