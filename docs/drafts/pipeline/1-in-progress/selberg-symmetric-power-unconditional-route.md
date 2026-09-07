# Selberg quarter conjecture through symmetric-power amplification

- **ID:** SELBERG-SYMMETRIC-POWER-UNCONDITIONAL
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** User-requested proof search, 2026-09-07; existing `selberg-quarter-conjecture-corpus-audit.md`.
- **Statement:** Prove the quarter bound for nonzero weight-zero congruence Maass cusp eigenfunctions by constructing compatible generic unitary symmetric-power lifts in unbounded degree and applying their archimedean exponent bounds.

## Goal

A closed Lean proof of the actual spectral assertion. A scalar strip identity, a theorem with a lift-existence premise, or an artificial positive packet is not this result. No extra mathematical axioms, admitted proofs, numerical experiments, or computational certificates.

## Plan

- [x] Read prior Selberg research and current local representation status.
- [x] Search the whole declaration index for lift constructions and alternative mechanisms: converse theorems, tensor/character identities, descent, positivity, and limiting arguments.
- [ ] Inspect exact definitions and hypotheses of every candidate retained for the route; verify current primary sources.
- [ ] Derive a dependency-closed paper proof before formalizing any new assertion.
- [ ] Check any resulting Lean work in foreground, one Lean process at a time; perform only targeted final builds, umbrella wiring, lint, and scratch axiom audits.
- [ ] Record exact progress and remaining mathematical obligations without marking the conjecture proved.

## Initial evidence

The existing source already proves the exact positive-degree scalar strip locus, all-degree and all-even-degree amplification, invariant forms on explicit spherical complementary-series models, and corresponding product-packet statements. None of their definitions constructs an automorphic symmetric-power lift. The generic GL(n,R) bridge and the global Maass lift construction require separate proofs.

There are concurrent changes in the principal-series derivative modules and the RHTower umbrella. Preserve those changes; inspect current contents before any narrowly scoped umbrella edit.

## Dependency-closed scalar extension: paper proof

For a set `D` of natural degrees, let `L(D)` be the real parameters whose symmetric-power exponent packets lie in the open half-strip at every degree in `D`. The exponent formula already proved in the corpus gives

`ν ∈ genericUnitarySymPowerLocus d ↔ d |ν| < 1/2`,

including degree zero: the endpoint `j=0` proves necessity, and `|d-2j| ≤ d` proves sufficiency.

**[PROVED HERE] Exact degree-set classification:** `L(D) = {0}` if and only if `D` is infinite. Equivalently, for each nonzero real `ν`, only finitely many natural degrees pass the strip test.

Proof: if `ν ≠ 0`, every passing degree satisfies `d < 1/(2|ν|)`, hence belongs to a finite initial segment of the naturals. An infinite `D` cannot be contained in that segment. Zero passes every test. Conversely, if `D` is finite, choose a natural upper bound `N` for it and set `ν = (1/2)/(N+2)`. Then `0 < ν < 1/2`, and for every `d ≤ N`, `dν < (N+2)ν = 1/2`. Thus `ν ∈ L(D)` and `ν ≠ 0`.

The converse also supplies positive scalar eigenvalues `1/4−ν² < 1/4` passing every bounded-degree strip test. These are scalar parameters, not asserted congruence Maass eigenvalues. Arbitrarily sparse unbounded degree sets suffice; a theorem constructing only bounded degrees cannot close the scalar amplification argument by itself.

This is an elementary extension of the existing all-degree/all-even-degree calculation, not a new functoriality theorem or a proof of Selberg. The route is not retired.

## Log

- 2026-09-07 — Opened before substantive proof search. `docs/architecture.md` and `docs/testing.md` absent. Serena Selberg memory and formal project entrypoints read. The `update_plan` tool is unavailable; this card carries the plan.
