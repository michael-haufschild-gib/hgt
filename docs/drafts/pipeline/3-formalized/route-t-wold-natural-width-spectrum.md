# Route-T exact natural Wold residual width spectrum

- **ID:** `route-t-wold-natural-width-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** T / C5b
- **Statement:** For every `0 ≤ alpha < 1/2`, Xi zero width `alpha` is equivalent to every
  natural-cutoff Wold residual rate `c < 1/2-alpha`.

## Corpus origin and full RH chain

Corpus search found RH endpoint natural-Wold classification, generic inverse Abel, generalized
von Koch, and forward arbitrary-width Mertens-to-Wold transport. Their exact all-width closure was
absent. Lean now proves

```text
XiZeroHalfPlaneBound alpha
  -> ChebyshevErrorPowerSpectrum alpha
  -> theta and centered Mertens decay
  -> |R_nat(N)| = O_c(N^(-c)) for every c<1/2-alpha,

all natural Wold rates c<1/2-alpha
  -> inverse Abel theta bounds at cofinal c
  -> ChebyshevErrorPowerSpectrum alpha
  -> XiZeroHalfPlaneBound alpha.
```

At `alpha=0`, this is an unconditional RH classification. No ordered-prime gap interpolation,
mesh-energy assumption, or endpoint rate is used.

## Formal result

- `WoldNatResidualPowerSpectrum alpha`
- `xiZeroHalfPlaneBound_iff_woldNatResidualPowerSpectrum`
- `riemannHypothesis_iff_woldNatResidualPowerSpectrum_zero`

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualNaturalWidthSpectrum.lean`.

## Consequence

Natural cutoff is now an exact zero-width coordinate at every partial width, not only RH endpoint.
Future Tauberian, local-average, or physical-cutoff producers can target this spectrum directly;
ordered prime gaps no longer contaminate statement of required decay invariant.

## Novelty audit

`[SOTA, checked 2026-08-29]` Current primary literature covers zero-free-region/PNT-error
transfer and weighted Mertens error criteria, but targeted searches found no Wold natural
residual or its exact all-width zero-geometry spectrum. Classical components are acknowledged;
new content is exact centered Wold invariant and unconditional two-way all-width transport.

## Lean audit

- Direct `lake env lean`: passed.
- Single targeted `lake build`: passed (`12541/12541`).
- Umbrella: wired into `GaloisForLFunctions.RHTower`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-29 — corpus-derived all-width conjecture and Lean proof completed.
