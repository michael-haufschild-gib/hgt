# Exact closed relation of the prime augmentation

- **ID:** RIAC-prime-boundary-closure
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Completed prime boundary](../3-formalized/riac-completed-prime-boundary.md)
- **Statement:** The closure of the actual finite weighted boundary graph is the graph of its bounded Riesz extension when `2 Re(s)+δ>1`, and the entire Hilbert-space product when `2 Re(s)+δ≤1`.

## Proposed exact classification

The existing finite embedding is dense and faithful. Above the threshold,
its boundary extends continuously and uniquely. The closed graph of that
extension contains the finite graph; density and continuity should give the
reverse inclusion in the closure.

At and below the threshold, the existing explicit packets put `(0,1)` in
graph closure. This closure is a complex linear subspace, hence contains
every `(0,z)`. Subtracting the vertical part of each finite boundary pair
gives `(Jδa,0)`. Density of `Jδ` then gives every horizontal pair, so the
closed relation is the whole product. Thus the original graph should be
dense exactly in this latter range.

## Positive survivor and scope

This would sharpen failure of closability to an exact classification of the
closed arithmetic relation. Inside the obstructed region even the closed
relation carries no distinction between parameters on the same fixed
carrier. The surviving bounded region retains the explicit Riesz functional
and its exact prime-series norm.

This is a consequence of the already formalized density and packet results,
not a new prime-density estimate. The graph-closure classification itself
remains to be checked in Lean; no higher homology or zero detection follows.
