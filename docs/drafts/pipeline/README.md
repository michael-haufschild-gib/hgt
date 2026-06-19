# The Pipeline — a board for turning conjectures into certified theorems

One **card** per pursued item. A card lives in exactly one column and moves left → right as it clears
each gate. The columns are the stages of one lifecycle:

```
0-backlog → 1-in-progress → 2-fully-proven → 3-formalized → 4-publication-ready
                                                                  (5-failed = off-ramp)
```

The full catalog of every statement is `../door/00-status.md`. The pipeline holds **only the items being
actively pursued** — it is the work queue, not the encyclopedia.

## Columns and gates

A card enters a column only when it clears that column's gate (the definition of done for the step
before it).

| Column | Holds | Gate to enter it |
|---|---|---|
| **0-backlog** | a conjecture queued to work on | well-posed; **source-pure** (built from primes / μ / ζ-data, not from the zeros it constrains); has at least one attack idea; carries a Door passport sketch (why it would be native) |
| **1-in-progress** | being worked on now | someone has started; the card records the current line of attack and what is blocking |
| **2-fully-proven** | a complete proof on paper | a full proof exists in the drafts, marked `[PROVED HERE]`, with every dependency discharged (no open lemma); a reader could follow it end to end |
| **3-formalized** | the theorem in Lean | a Lean theorem states it; `lake build` green; `bash scripts/check_axioms.sh` PASS (axiom-clean); it is in the audit and the `README.md` ledger |
| **4-publication-ready** | a standalone paper | a self-contained writeup gives the theorem, its proof, its Lean certificate, and why it is native (Door-2). **This is the quality gate** — not to publish, but to certify the conjecture really became a proven, formalized theorem |
| **5-failed** | disproven | a counterexample or disproof is recorded with the argument |

A card that reaches **4-publication-ready** is **done**: the conjecture has become a proven, formalized,
written-up theorem.

## Moving a card (always these three steps together)

1. `mv` the card from its current column into the next.
2. Edit its `Stage:` line to the new column.
3. Add a dated line to its `## Log`.

A card is always in exactly one column. To start a new card, copy `_card-template.md` into `0-backlog/`.

## Off-flow items (case by case)

Not everything fits the linear flow — framings and metaphors (embassy), structural syntheses, grading
decisions, or apex problems too large to attack head-on. These stay in the catalog
(`../door/00-status.md`) and are handled case by case; they get a card only once a **source-pure,
provable statement** has been carved out of them. A card whose work is suspended may stay in its column
with a `PARKED` note on its `Stage:` line.

## Naming

One card per item, `<short-id>.md`. Keep the id stable as the card moves between columns.
