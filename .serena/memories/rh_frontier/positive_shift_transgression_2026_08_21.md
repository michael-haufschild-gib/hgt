# Positive-shift source transgression frontier (2026-08-21)

## Formalized result
New module:
`formal/GaloisForLFunctions/RHTower/XiWardCubicPositiveShiftArithmeticCovariance.lean`.

It defines a source-first positive real shift covariance from the arithmetic logarithmic derivative and proves:
- exact pole–Gamma/von-Mangoldt splitting;
- exact equality with continued Hedenmalm translated-divisor transgression on source chamber;
- local residue germ `(m ρ - m (ρ - ε)) / ε`;
- analyticity/eventual equality;
- at a left translation boundary with regular predecessor, exact positive charge `m ρ / ε`.

Important provenance: Xi divisor is not selected in covariance definition; divisor multiplicity appears only after scalarization.

Verification passed:
- direct Lean compile;
- targeted lake build;
- formal lint;
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

Research card:
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/xi-ward-positive-shift-arithmetic-covariance.md`.

## Fresh corpus synthesis
- `Sieve/InghamDetectorDensityPolylog.lean` has a zeta Littlewood count above β=7/10 bounded by `K X^(82571/118590) (1+log X)^2`, exponent < 1.
- `RiemannVonMangoldt.lean` has N(T) asymptotic control. Together these should yield deep count β≥0.7 = o(N(T)); bridge is not yet packaged as one Lean ratio theorem.
- `XiWardSourceWindowMultiplicity.lean` has exact receiver `three_quarters_line_of_shallowEnergy_and_deepCount`.
Thus ε=1/5 is the natural positive shift: discard deep band with zero density, attack only shallow band (1/2, 0.7).

## Ruled-out direct closures
- Stationary aperture-translation intertwining is impossible by `XiWardCubicApertureIntertwiningRateNoGo.lean`.
- Suzuki uniform positive-mixture boundedness is RH-equivalent, not an unconditional producer.
- Direct scalar capacity comparison remains RH-equivalent.
- Abel/exterior Cesàro projectors select Xi divisor before scalarization and do not meet source-only provenance.

## Exact open core
No unconditional 75% theorem yet. Still need a height-local source trace/shorting theorem for ε=1/5:
[
B_{corrected}(K_T) \leq \widetilde B_T + o(N(T)),qquad
\widetilde B_T \leq \frac{4}{25}N(T)+o(N(T)).
]
It must exploit polar–Gamma boundary defect / primitive source incidence, not stationary aperture covariance. The new theorem solves source-to-divisor provenance and diagonal-multiplicity separation, but not global `4/25` contraction.