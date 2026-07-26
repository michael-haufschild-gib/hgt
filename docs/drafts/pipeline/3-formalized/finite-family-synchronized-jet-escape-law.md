# Finite-family synchronized jet escape law

- **ID:** finite-family-synchronized-jet-escape-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus closure of `iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental` and the four-source synchronization proof
- **Statement:** For any finite family of constant-coefficient differentially transcendental functions and finite-dimensional dictionary `V`, every finite order set of size greater than `card ι * finrank V` contains one derivative order missed by `V` for every family member simultaneously.

## Goal

Replace the hard-coded Gamma--digamma--zeta--xi initial-interval synchronization with the complete
finite-family, arbitrary-window capacity law it witnesses.

## Gates

- [x] 0 → 1  in-progress: unconsumed finite-union abstraction identified from exact Lean statements
- [x] 1 → 2  fully-proven: dependency-closed finite-capacity proof
- [x] 2 → 3  formalized: `HTGeometry.exists_common_iteratedDeriv_not_mem_of_card_mul_finrank_lt`
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

## Lean certificate

File: `formal/GaloisForLFunctions/HTGeometry/FiniteFamilySynchronizedJetEscapeLaw.lean`.

- `HTGeometry.exists_common_iteratedDeriv_not_mem_of_card_mul_finrank_lt` — the arbitrary-window
  law: for a finite family `f : ι → ℂ → ℂ` of constant-coefficient differentially transcendental
  sources and a finite-dimensional dictionary `V`, every `s : Finset ℕ` with
  `Fintype.card ι * finrank ℂ V < s.card` contains an order `n ∈ s` with
  `iteratedDeriv n (f i) ∉ V` for every `i`;
- `HTGeometry.exists_common_iteratedDeriv_not_mem_le_card_mul_finrank` — the initial-segment
  corollary, a common escape order `n ≤ Fintype.card ι * finrank ℂ V`.

Instantiated at the four classical sources in
`formal/GaloisForLFunctions/RHTower/GammaDigammaZetaXiArbitraryWindowEscapeUniversalityLaw.lean`
as `GaloisForLFunctions.exists_synchronized_gamma_digamma_zeta_xi_jet_escape_in_finset`, which
subsumes the hard-coded initial-interval statement
`exists_synchronized_gamma_digamma_zeta_xi_jet_escape`.

The proof is exactly the paper argument: `captured i = s.filter (iteratedDeriv · (f i) ∈ V)` has
card at most `finrank ℂ V` by the one-source capacity theorem
`HTGeometry.iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental`,
and `Finset.card_biUnion_le_card_mul` bounds the union.

All three theorems build clean and use only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-07-22 — theorem-statement closure found; finite-union paper proof closed
- 2026-07-26 — verified formalized in the tree, axiom-clean; card moved to `3-formalized`
