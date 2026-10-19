# Fixed energy and full-grid zeros do not bound exact cycle order

- **Stage:** 5-failed
- **Route:** a singular-energy ceiling and simultaneous integer-log blindness force a uniformly bounded exact closed-cycle detection order.
- **Closure:** disproved by actual smooth compact sources; positive survivors proved on paper and in Lean.
- **Package:** [proof, prior-work audit and verification](../3-formalized/biscale-energy-controlled-cycle-observability-2026-10-18.md).

One K>0 works for every prescribed order m: two actual smooth `LevyEnergySource K` objects vanish at every log(n), n≥2, agree on every normalized closed product of length at most m, and have different signed correlations. `GridCycleAmbiguity.exists_full_grid_bounded_energy_cycle_aliases` proves this without an analytic premise. A finite cross-correlation corrector cancels the relevant grid sites; support handles all remaining sites. A shape-dependent amplitude keeps energy below the same K. Thus the existing identical-copy energy obstruction cannot be extended to arbitrary two-shape sources.

The strongest audited positive survivors are explicit finite noisy recovery from closed cycles plus the signed grid trace (`EnergyCycle.global_recovery`), and an O(n^(-1/2)) diameter bound for equal signed traces and equal cycles through order n+2 (`order_ambiguity_square_bound`). The energy ceiling supplies the origin collar and continuity modulus. Exact finite-order ambiguity persists while its possible size shrinks. No optimal-rate claim is made.

Both survivors have dependency-closed paper proofs, passing direct named-source Lean checks and imported axiom audits using only `propext`, `Classical.choice`, `Quot.sound`. Four leaves are umbrella-wired. Repository lint has one unrelated BVI import error, documented on the package card. Negative statement and survivors constitute one contribution; this closure card adds no count.
