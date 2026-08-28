# JAS ell-two amplified prime-Poisson superselection

- **ID:** JAS-L2APPS-1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HARD ROUTE-CLASS FALSIFIER
- **Source:** read-only `rh-current-frontier-map.md`, JAS `ORIENT + COMP` open core

## Hard frontier target

JAS and RFHM retain arbitrarily many valuation, compound, and finite-prime-support channels. A
naive cofinal completion places those channels as Hilbert multiplicities beside the ordinary-prime
`C(PrimeTorus)` representation. Determine whether this amplification can create a reflected
source-linear sewing that is absent in each prime-Poisson fibre.

For arbitrary Hilbert spaces `H1`, `H2`, index family `A`, `B`, and multiplicity type `Gamma`, form
the diagonal actions on `ell2(Gamma, H1)` and `ell2(Gamma, H2)`. Prove:

1. `OperatorFamiliesDisjoint A B` implies disjointness of both amplified families;
2. reflected prime-Poisson amplification has a nonzero closed densely-defined
   `C(PrimeTorus)`-linear sewing iff `sigma = 1/2`;
3. on the wall, actual completed-theta grade norms mark a nonzero linearly independent countable
   packet family in the amplified carrier.

If C1--C2 hold, every diagonal/separable prime x grade completion is terminal: multiplicity,
countably many valuation depths, and finite compounds cannot evade off-wall superselection. JAS
then requires genuinely nonseparable prime--grade incidence whose `C(PrimeTorus)` action mixes the
completion coordinates. C3 is the mandatory positive survivor.

## Corpus basis

All conjecture-forming searches used `scripts/formal_tools.py research`. Corpus provides:

- `OperatorFamiliesDisjoint`, defined by vanishing of bounded intertwiners in both directions;
- exact prime-Poisson reflected sewing iff `sigma = 1/2` before amplification;
- `ell^p` coordinate-single density and continuous-map extensionality;
- actual completed-theta all-grade nonvanishing and `L2` linear independence;
- faithful finite-support/history RFHM packets, but no amplified disjointness theorem.

The block-matrix proof is forced by corpus structure: every coordinate projection of an amplified
intertwiner is a base intertwiner, hence zero; density of coordinate singles then kills the whole
operator. No spectral theorem or zero data is inserted.

## Conjecture loop

### C1 — arbitrary ell-two amplification stability

Build bounded coordinatewise amplification for a bounded operator, bounded coordinate injections
and projections, then prove every amplified intertwiner has all matrix coefficients zero.

### C2 — reflected prime-Poisson exact wall

Apply C1 to corpus mutual-singularity disjointness off wall. At wall, use diagonal graph on one
nonzero coordinate single.

### C3 — completed-theta source-marked survivor

Weight the `r`-th coordinate single by the nonzero norm of actual completed-theta grade `v_r`.
Prove the full countable packet family linearly independent and compatible with the critical
diagonal sewing.

## Hostile falsification

1. Arbitrary multiplicity type, not fixed finite rank.
2. Closed densely-defined relations, not bounded intertwiners alone.
3. Actual `C(PrimeTorus)` prime-Poisson representation.
4. Actual completed-theta grade nonvanishing in positive survivor.
5. No Xi zero, RH premise, numerical computation, new axiom, or compact cutoff.

## Novelty status

`[CONJECTURED HERE] [INTERNAL SEARCH COMPLETE] [EXTERNAL AUDIT PENDING PROOF]`

## Log

- 2026-08-28 — selected after all-grade completed-theta Mellin chain closure. Frontier map read-only.
  Target derived from exact corpus search no-match for disjointness under Hilbert multiplicity.
