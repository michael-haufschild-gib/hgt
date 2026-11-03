# The linear inverse chord cannot pay the full first moment

- **ID:** F1-LC
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [Joint low-moment payment](../3-formalized/f1-joint-low-moment-chord-payment.md)
- **Rejected claim:** The polynomial reflection comparison with spectral bracket
  `[19/50,37/20]` pays the full first-moment coefficient `β=5123/1280` by its linear inverse chord.

## Obstruction

For `p₁(u)=u`, its polynomial energy is at most `1/2`. Therefore the first diagonal
of the inverse chord is at least

`((19/50+37/20)/3−1/2)/((19/50)(37/20))=730/2109>1280/5123=1/β`.

The chord already misses the first charge without the third charge. Improving only
the mixed-entry estimate cannot fix this. This does not refute the exact logarithmic
two-moment form or complete Weil positivity.

## Positive survivor

The same comparison jointly pays `3/2` of the first charge and the entire third charge:
`E_B₀(G)−(3/2)(∫uG)²−(63/20)(∫P₃G)²≥∫G²/1000`.
Consequently `Q(F)+(3203/320)(∫xF)²≥∫F²/1000` for every real odd C² unit-window test.
Further payment requires a sharper inverse comparison or more of the logarithmic potential.

The dependency-closed paper proof and Lean declarations are in the linked card.
WTZ `firstFold_linear_chord_exceeds_first_capacity` and
`weilQuad_add_reduced_first_moment_ge_mass` pass individual Lean and standard-only
transitive axiom audits.
