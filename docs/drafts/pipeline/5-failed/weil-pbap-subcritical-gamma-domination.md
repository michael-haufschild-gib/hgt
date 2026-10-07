# No subcritical gamma domination on the full integer-null cone

- **ID:** weil-pbap-subcritical-gamma-domination
- **Stage:** 5-failed
- **Type:** FALSIFIED; obstruction and positive analytic survivor formalized
- **Source:** `../1-in-progress/weil-work-01-pbap.md`; `../../../reports/weil-work/results/01-pbap/CRITICAL-SLOPE.md`
- **Rejected statement:** for some `0<=a<1` and real `C`, every nonnegative finite smooth integer-null mixture obeys `-Pole<=a Gamma+C Mass`.

## Exact closure

For every `0<=a<b` and every real `C`, there is an actual nonnegative finite smooth mixture, null at every symmetric integer-log sample, with `a Gamma+b Pole+C Mass<0`. Its mass-one energy can be below any real threshold. No coefficient-sign, growth, summability, analytic-continuation, spectral-measure, or positive-producer premise remains in the witness theorem.

## Positive survivor

For every actual modified completion, positivity itself supplies absolute convergence of its coefficient Dirichlet series on every real exponent above one, the exact actual-series residue `(s-1)D(s)->b`, and a sharp signed Abel ceiling `s^2 D(1+s) zeta(1+s)<=a+2 epsilon+M_epsilon s^2`. The residue comes from translated Gram positivity and an exact narrow-window Laplace identity; its convergence is derived by primitive-set mean square. These are quantitative analytic consequences, not an assumed producer package or merely the restated negation. Comparing them gives the necessary boundary `b<=a`.

The strongest normalized negative witness and the exact positive analytic consequences are dependency-closed on paper in [CRITICAL-SLOPE.md](../../../reports/weil-work/results/01-pbap/CRITICAL-SLOPE.md). Lean certificates are `criticalDirichletReal_residue`, `summable_abs_div_rpow_critical`, `critical_dirichlet_product_ceiling`, `critical_pole_weight_le_gamma`, and `exists_normalized_critical_null_below`, in the ten `RHTower/WeilWorkPBAPCritical*` leaves.

## New insight and limit

The older gamma-free obstruction extends to every strict deficit in the gamma coefficient, with arbitrary mass slack. The residue comparison erases that slack. It therefore cannot decide the literal equal-weight normalization. Full PBAP at `a=b=1,C=0` remains open; only the subcritical domination route is retired. Scientific novelty is unestablished, and no publication-ready claim is made.

## Verification

- Dependency-closed paper proof complete.
- Ten targeted `lake build --old +<leaf>` builds pass.
- Ten final direct `lake env lean <leaf>` audits pass without diagnostics.
- Twenty-two axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- All ten modules wired into `RHTower.lean`; no umbrella/full build or heartbeat increase.
- Global lint still has nine unrelated reachability errors; exact snapshot and source hashes are in [EVIDENCE.md](../../../reports/weil-work/results/01-pbap/EVIDENCE.md).

## Log

- 2026-10-07 — Scoped domination route retired after both the negative theorem and its quantitative analytic survivor passed paper and Lean audits. WP01 goal remains active.
