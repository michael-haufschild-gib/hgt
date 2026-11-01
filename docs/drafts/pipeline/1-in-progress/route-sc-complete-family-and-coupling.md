# SC: complete-family realization and coupling

- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-0111/route-SC.md`.
- **Goal:** Resolve the seven main obligations and four heat obligations, with unconditional Lean proofs.

## Current obligations

1. Realize rational correlation Grams by smooth packets of the complete Weil family, including normalization and the boost-mass-zero constraint. Distinguish a multiple chosen for each finite family from one multiple valid for every family.
2. Exclude bounded cone coupling with unattained maximal zero width.
3. Exclude finite nonzero Weil index.
4. Transfer finite-sieve Hodge positivity to the global inter-tower form.
5. Prove an arithmetic finite-index ceiling.
6. Prove a square decomposition for the dilation form itself.
7. Prove glued index at most one, equivalently bounded two-prime lattice coupling.

Heat: certified upper-time calibration; subcritical heat count; uniform heat count; absence of index jumps on `(0, 1/8]`.

## Verified boundary

`exists_ratCorr_gram_limit_at_critical_multiple` realizes each finite rational Gram using the smooth Steklov profile at `K·loglog N·(logloglog N)²`. Its `K` depends on that family. It does not provide a universal fixed multiple or identify the normalized complete-matrix compression.

`riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log` gives the smooth complete-family receiver at `2(log N)^α`, every `α>0`. Neither result proves positivity.

## Complete-matrix normalization

Set `φ(u)=2·steklovDCProfile(2u−1)`, `w=c/N`, and `G=∫φ(u/w)² du>0`.
An atomic coefficient vector `x` becomes `v_n=x_n/w` in the complete matrix.
Its mixed Weil pairing is exactly `G⟨A_N(c)v_i,v_j⟩`. Thus the existing rational
Gram limit at dilation `N/(K·dcScale N)` gives a literal complete-matrix
compression limit at overlap `2K·dcScale N`.

Lean candidate: `TransMetzlerWeilPositivity/ReceiverRate/ABoundedOverlapRateSeesASemilocalWindow.lean`,
`exists_ratCorr_completeWeil_gram_limit`.
Direct compilation and axiom audit pending. Exact preservation of the boost
hyperplane is not yet supplied by this Gram limit.

## Cone obstruction

The existing double-pole argument requires an attained maximal real part.
Below the supremum its geometric expansion diverges for deeper zeros.
Continuation across the boundary does not by itself isolate residues of an
infinite accumulating pole series. A quantitative lower weight versus joint
two-prime spacing estimate remains necessary for that argument.

## Gates

- [x] Exact requested scope recorded.
- [ ] Complete-family realization and hyperplane equivalence audited.
- [ ] Remaining source estimates proved.
- [ ] Exact Lean statements, direct checks, standard-only axiom audits, umbrella imports.
