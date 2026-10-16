# CHMD: literal spatial-order preservation

Date: 2026-10-16. Status: failed; positive survivor formalized; leaf builds and direct audits passed.

Conjecture: the positive full Doob jump source preserves spatial order, allowing
an order-based first-mode argument for primitive-sector positivity.

Obstruction: the original full upward rate violates the upper-set monotonicity
condition. At the first arithmetic threshold b = x+log 2, and for
y = x+log 2/2, eventually x < y < b but R(y,b) < R(x,b). Both the complete
archimedean integral and all original prime atoms are retained and convergent.
The endpoint convention is exact: the archimedean singleton has zero mass;
the prime atom at b remains included.

## Strongest positive survivor

The full source recovers its arithmetic atom at every threshold m ≥ 2:
cosh(x/2)R(x,x+log m)/Θ(x+log m) → aₘ. A fixed advance smaller than the
preceding logarithmic integer gap changes this limit to zero. This classifies
the threshold mechanism of the order obstruction, rather than merely bounding
an error or exhibiting a truncated counterexample.

Dependency-closed paper proof and exact Lean artifacts:
`../3-formalized/chmd-full-jump-tail-selection-2026-10-16.md`.
Paper status: complete. Lean status: all tail laws, unconditional rate reversal,
source integrability and summability compiled. Both final plain Lean audits
passed. All 40 declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. Index refresh passed. Global lint exited 1 for the unrelated
unwired `PaperThetaCutMeyerCurrent` module; no CHMD error was reported. All owned scratch files were removed and their
absence verified; all owned processes reached terminal exit.

Second-pass salvage: retain the entire countable arithmetic tail, prove its
dominated-convergence selection law, retain the full archimedean tail, and
identify rates directly with the existing Doob graph densities. This yields
the positive invariant above; no arbitrary source replacement is introduced.

## Frontier implication

The missing primitive-sector positivity cannot be obtained from literal
spatial-order monotonicity of these source rates. No semigroup theorem is
claimed without constructing its domain and generator. The original signed
quadratic form and RH remain unresolved. Further work must use structure that
survives the arithmetic threshold reversals, such as the already established
complete prime-chain decomposition, rather than assume local order preservation.
