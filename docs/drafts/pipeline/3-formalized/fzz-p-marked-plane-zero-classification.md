# FZZ-P marked-plane zero classification

## RH proof chain

Fixed theta/FZZ source → exact marked-plane source selector → source-fixed mixed
replica–momentum Ward identity → shared Ward charge zero → FZZ-P endpoint → RH.

This result closes exact zero-locus premise for first original one-screening mark in complete
positive convergence chart.

## Formal result

Write normalized first mark as difference of symmetric Gamma-log slopes

`F(a+b-1) - F(a)`, where `F(s) = ψ(s) + ψ(1-s)`.

Trigamma series proves `F` strictly increasing on `(0, 1/2]`; reflection proves
`F(s) = F(1-s)`. Hence equality in unit chamber occurs exactly at reflected pair. Chamber
inequalities exclude diagonal alternative, leaving `2a+b=2`, equivalent in exponential chart to
`y=0`.

Premise-free Lean theorem:

- `fzzScreeningPlaneMarkedMoment_first_eq_zero_iff (x y : ℝ) :
    fzzScreeningPlaneMarkedMoment x y 1 0 = 0 ↔ y = 0`.

## Consequence and boundary

No hidden cancellation locus exists for original convergent one-screening source: every `y ≠ 0`
has nonzero first logarithmic mark. Remaining FZZ-P burden is continuation to physical collision
exponents, higher screenings, fixed phase frame, and integrated mixed replica–momentum Ward law.

## Novelty and verification

Corpus deep search found only proved `y=0 → mark=0`, not converse or zero-locus classification.
Targeted literature search through August 2026 found classical trigamma series/monotonicity but no
classification of this Dotsenko–Fateev marked-plane response. Classical analytic input is DLMF
§5.15.1; exact screening-source consequence and Lean proof are new here.

Verified directly with one Lean worker:

```text
lake env lean -j1 GaloisForLFunctions/RHTower/FZZCigarPlaneScreeningMarkedZeroClassification.lean
```

Result: exit 0 in 9.5 seconds. No `lake build` was run.
Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only; no project-added axiom.
