# Matomäki--Teräväinen Lemma 2.3(ii) logarithmic-absorption no-go

- **ID:** MT-L23II-ABSORB-NOGO
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Matomäki--Teräväinen, *Almost primes in almost all short intervals II*, Lemma 2.3(ii), equations (2.15)--(2.16), final paragraph of proof
- **Statement:** At `z₀ = exp(log X/(log log X)^3)` and `L = floor(log(4X)/log z₀)`, the claimed estimate `((log(4X)/log z₀)+1)^(2L²) = (log X)^o(1)` is false.

## Goal

Audit the last absorption step in published Lemma 2.3(ii) before importing its claimed
`Y(log X)^(-2A)` error into Lean.

## Gates

- [x] 0 → 1 in-progress: exact source statement and dependency chain identified
- [x] 1 → 2 fully-proven: elementary asymptotic comparison closes the negative audit
- [ ] 2 → 3 formalized: the false absorption itself is not imported; positive survivors are formalized
- [ ] 3 → 4 publication-ready: external author/journal audit or repaired proof required

## Approach

Substitute the paper's literal scale. Since

```text
log z₀ = log X/(log log X)^3,
L = (1+o(1))(log log X)^3,
```

the logarithm of the displayed loss is

```text
2L² log((log(4X)/log z₀)+1)
  = (6+o(1))(log log X)^6 log log log X.
```

But the logarithm of `(log X)^ε` is only `ε log log X`. Thus the loss dominates every fixed
power of `log X`; it is not `(log X)^o(1)`. Both arXiv v2 and the 2023 accepted manuscript retain
the same line, so this is not an HTML transcription issue.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** `L ≍ (log log X)^3` makes the equation-(2.16) factor `L^(2L²)` super-polynomial in `log X`; it cannot be absorbed from `(log X)^(-3A)` into `(log X)^(-2A)` for fixed `A`.
- **Strongest positive survivor:** Equation (2.15)'s finite Buchstab algebra, literal `c₁+c₂+c₃` provenance, exact adjacent geometric block schedule, sharp `B K^d` coefficient growth, pointwise terminal-remainder vanishing, and the correct cumulative exponent `sum_{0≤j≤J}2j` all survive.
- **New insight:** Open core is analytic layer control or a different stopping/schedule argument, not finite Buchstab algebra. Any repair must beat the published worst-case cumulative loss; repeating its final absorption cannot work.
- **Status:** Positive survivors are dependency-closed and formalized in `MatomakiTeravainenBlockConvolution`, `MatomakiTeravainenFiniteIteration*`, `MatomakiTeravainenAdjacentSchedule`, `MatomakiTeravainenGeometricSchedule`, `MatomakiTeravainenCoefficientGrowth`, `MatomakiTeravainenErrorLayers`, `MatomakiTeravainenErrorGrowth`, `MatomakiTeravainenMainLayers`, and `MatomakiTeravainenLemma23IIExact`. Final source-scale Lemma 2.3(ii) error remains open.

## Log

- 2026-08-27 — source arithmetic re-audited; false absorption confirmed in arXiv v2 and accepted manuscript; positive survivors formalized; route retired in its published form.
