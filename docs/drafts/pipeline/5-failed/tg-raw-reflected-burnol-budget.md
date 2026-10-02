# TG raw coherent-reflection cubic budget

- **ID:** TG-C4-RAW-BUDGET
- **Stage:** 5-failed
- **Type:** FALSIFIED candidate, positive survivor formalized
- **Route:** TG

## Candidate

Retain the cross terms between a literal Burnol packet and its opposite-clock packet, rather
than use the orthogonal theta doubling. Their source Gram moves the neutral reference, so its
cubic might escape the old zero-trace obstruction while inheriting a uniform source budget.

## Exact killing theorem

`RHTower.primeBurnolReflectedThetaCubicTrace_imag_atTop` proves that, at every prime-depth
label and every nonzero actual theta twist, the imaginary part of the literal density-weighted
cubic tends to positive infinity as the positive clock parameter tends to zero. This already
excludes a uniform raw budget for the candidate on single-cell packets. It does not retire TG
or the required four-leg relative completion.

## Strongest positive survivor

The literal Gram, its inverse away from collision, and the complete trace formula are explicit.
The singular response has one second-order real counterterm and one first-order imaginary
counterterm. Subtracting both gives a finite real limit and vanishing imaginary limit, proved in
`primeBurnolReflectedThetaCubicTrace_real_finitePart` and
`primeBurnolReflectedThetaCubicTrace_imag_finitePart`.

This strengthens the previous zero-charge obstruction: coherent reflection can carry a
response, but any bounded completion must first cancel these source-determined poles. The
balanced rotation does not avoid the obstruction; its imaginary pole remains. A serious second
pass extracted this exact finite-part law rather than declaring all coherent reflection dead.

## Status

Dependency-closed paper proof and direct Lean audit complete. Full formulas, module, audit
command, and remaining mixed-prime/Gamma comparison are recorded in
`../3-formalized/tg-reflected-burnol-cubic-collision.md`. No RH proof or falsification follows.
