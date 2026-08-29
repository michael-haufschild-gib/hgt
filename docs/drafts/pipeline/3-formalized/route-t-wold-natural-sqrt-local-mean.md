# Route-T natural Wold critical-window local mean

- **ID:** `route-t-wold-natural-sqrt-local-mean`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** T / C5b.11
- **Statement:** Critical square-root-window normalized `L1` means of the natural Wold residual
  have exactly the complementary Xi zero-width spectrum; width zero is equivalent to RH.

## Goal

Replace pointwise natural Wold residual decay by a genuinely diffuse local statistic while
preserving the complete RH proof burden. The center has relative window mass
`1/(2*sqrt(N)+1)`, so reverse implication must use arithmetic source rigidity rather than a
pointwise term hidden inside the mean.

## Gates

- [x] 0 -> 1 in-progress: frozen C0/C0.1 before proof search; corpus origin and full RH chain stated
- [x] 1 -> 2 fully-proven: dependency-closed paper proof below
- [x] 2 -> 3 formalized: Lean endpoint
  `riemannHypothesis_iff_woldNatResidualSqrtMeanSpectrum_zero`; targeted build green; axiom audit
  has only `propext`, `Classical.choice`, `Quot.sound`
- [ ] 3 -> 4 publication-ready: standalone paper not yet prepared

## Corpus origin and frozen conjecture

`[CORPUS]` `xiHeatCassiniWoldNatWeight` is nonnegative, and natural residual is

```text
R(N) = W(N) - log N - H.
```

`[CORPUS]` C5b.10 had already proved

```text
XiZeroHalfPlaneBound alpha iff WoldNatResidualPowerSpectrum alpha
```

for `0 <= alpha < 1/2`; at `alpha=0` this is RH. Corpus search found no natural local-average or
successor recovery theorem, while generic global Cesaro bounds allow sparse spikes. Before proof
search, C0.1 froze conjecture

```text
XiZeroHalfPlaneBound alpha
  iff for every 0<c<1/2-alpha,
      average_(n in Icc(N-sqrt(N),N+sqrt(N))) n^c |R(n)|
      is eventually bounded.
```

No computation contributed to statement or proof.

## Paper proof

`[PROVED HERE]` Nonnegativity makes `W(N)` monotone. Thus, for `M <= N`,

```text
R(M) <= R(N) + log N - log M.
```

For a positive central residual, this gives a lower bound throughout right half-window; for a
negative residual it gives a lower bound for its absolute size throughout left half-window. Each
half contains `sqrt(N)+1` nodes, while full window contains `2*sqrt(N)+1`, so a bounded
full-window normalized sum bounds either inherited half-window at constant loss. For
`n in Icc(N-sqrt(N),N+sqrt(N))` and large `N`, `n` and `N` differ by at most factor two, and

```text
log(N+sqrt(N))-log N <= N^(-1/2),
log N-log(N-sqrt(N)) <= 2*N^(-1/2).
```

If `0<c<1/2-alpha` and `alpha>=0`, multiplication by `N^c` makes these drift errors bounded.
Therefore bounded local means imply `|R(N)|=O(N^(-c))` for every strict complementary exponent.
Reverse direction averages pointwise bound uniformly on comparable window. Hence local mean
spectrum and pointwise natural Wold spectrum are equivalent at every admissible width.

## Full RH chain

```text
critical square-root local L1 spectrum
  -> one-sided Wold/log persistence
  -> WoldNatResidualPowerSpectrum 0
  -> exact inverse Abel / ChebyshevErrorPowerSpectrum 0
  -> XiZeroHalfPlaneBound 0
  -> RH,
```

with every arrow reversible. No ordered-prime gap, mesh-energy premise, endpoint `c=1/2`, or
external hypothesis enters.

## Novelty audit

`[SOTA, checked 2026-08-29]` Primary-source search covered logarithmic Tauberian recovery, averaged
prime-counting and Mertens-error RH criteria, weighted-prime correlations, smooth zero-free-region
transfer, and explicit Mertens bounds. No source found this Wold residual, its critical symmetric
square-root absolute local mean, or exact all-strict-rate Xi-width classification. Adjacent
sources: Moricz--Nemeth (arXiv:1206.6963), Johnston (arXiv:2201.06184), Angot
(arXiv:2404.13019), Zhao (arXiv:2411.18903), Han (arXiv:2505.23795),
Bhattacharya--Martin--Simpson (arXiv:2507.13504), and
Broadbent--Fiori--Kadiri--Ng--Wilk (arXiv:2608.01498).

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualNaturalSqrtMeanSpectrum.lean`
- Main exact theorem: `xiZeroHalfPlaneBound_iff_woldNatResidualSqrtMeanSpectrum`
- Closed endpoint: `riemannHypothesis_iff_woldNatResidualSqrtMeanSpectrum_zero`
- Umbrella: imported by `formal/GaloisForLFunctions/RHTower.lean`
- Verification: direct `lake env lean` and targeted
  `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualNaturalSqrtMeanSpectrum` pass
  (`12542/12542`); axiom audit reports only standard foundational axioms
- Lint: no new module finding; repository-wide non-build lint remains red only on unrelated,
  pre-existing unreachable modules

## Log

- 2026-08-29 — C0/C0.1 frozen in stage 1 after corpus and literature audits
- 2026-08-29 — paper proof closed; theorem formalized and promoted to stage 3
