# Finite-family synchronized jet escape law

- **ID:** finite-family-synchronized-jet-escape-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** whole-corpus closure of `iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental` and the four-source synchronization proof
- **Statement:** For any finite family of constant-coefficient differentially transcendental functions and finite-dimensional dictionary `V`, every finite order set of size greater than `card ι * finrank V` contains one derivative order missed by `V` for every family member simultaneously.

## Goal

Replace the hard-coded Gamma--digamma--zeta--xi initial-interval synchronization with the complete
finite-family, arbitrary-window capacity law it witnesses.

## Gates

- [x] 0 → 1  in-progress: unconsumed finite-union abstraction identified from exact Lean statements
- [x] 1 → 2  fully-proven: dependency-closed finite-capacity proof
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

For each source `i`, filter the requested order set by derivatives that lie in `V`.  The existing
one-source capacity theorem bounds this captured set by `finrank V`.  The union over all sources
therefore has cardinality at most `card ι * finrank V`.  A larger test set cannot be covered by
that union, so one order is outside `V` for every source.  Taking the first
`card ι * finrank V + 1` orders gives the bounded initial-segment corollary.

## Audit

- **[CORPUS]:** one-source exact capacity exists for arbitrary order sets
- **[CORPUS]:** `exists_synchronized_gamma_digamma_zeta_xi_jet_escape` repeats a four-set union argument only for an initial segment
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; arbitrary source arity and arbitrary finite test windows are absent
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — theorem-statement closure found; finite-union paper proof closed
