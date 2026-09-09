# Uniformity from complete quadratic generator-word costs

Status: this coefficient shortcut is retired. Its strongest positive survivors
have a dependency-closed paper proof and audited Lean formalization. SQB itself
remains open.

## Exact excluded claim

The literal S and T generators yield a finite coefficient C_N controlling the
complete original congruence variance. The excluded step is treating these
coefficients as bounded uniformly over N, or obtaining such a bound merely by
choosing different complete generator-word representatives.

Lean proves that C_N is built from the least certified word costs and that
`k>0` and `2*5^k<N+1` force `C_N>k²/2`. Hence C_N tends to infinity. Every
other complete certified word-cost family has quadratic average at least C_N,
so it also admits no uniform upper bound.

## Positive survivor and scope

For every actual level, C_N is positive and finite, with

```
sum_q |F_q(z)-mean(z)|² ≤ C_N * E_ST(z).
```

The two energies are literal original S/T pullbacks. The full density bound
retains the mean; when that mean is zero, it controls the entire source.
Original density times normalized chord distance equals source displacement
energy even at common zeros. At positive density and zero mean, the two
normalized generator chords have sum at least 1/C_N. Generator-fixed vectors
are exactly vectors fixed by the full average.

The separate counting survivor is
`k²(card G-5^k) ≤ sum_g cost(g)²`, with the derived explicit group-size bound
under a coefficient ceiling. Distinct actual translation classes supply
`N+1 ≤ card(Deck N)` without numerical enumeration.

This does not exclude a uniform optimal S/T spectral gap, a comparison using
source correlations, compensation by separately proved geometric estimates,
or another route to the quarter bound. The obstruction concerns exactly the
complete quadratic word-cost average used here.

[Complete paper proof, actual-source scope, four Lean modules and audits](../3-formalized/sqb-congruence-generator-cost.md).
The four modules contain 45 indexed declarations; all 52 declarations,
constructors and named local instances in the axiom audit passed with only
Lean's standard axioms. All four sole-target final builds passed.
All indexed declarations and single umbrella imports were verified; repository
formal lint passed. The negative claim and its positive survivors are fully audited.
