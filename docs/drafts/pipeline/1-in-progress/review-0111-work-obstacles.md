# Formalization of review-0111 work obstacles

- **ID:** review-0111-work-obstacles
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, §2.1, A1–A29.
- **Statement:** Discharge each listed task with its exact unconditional Lean theorem,
  direct leaf compilation, transitive axiom audit, and umbrella import.

## Open obligations

All A1–A29 remain required. Numerical certificates must be proved in the kernel;
the task forbids numerical experiments and trusted computation.

| Item | Verified mathematical boundary |
|---|---|
| A1 | Collective packet coercivity below `1/4` and logarithmic confinement below `1/9` are already formalized. All-vector `1/8` still requires improving three `c⁹` payments: prefix–terminal, band–terminal, and inverse-energy residual. See `off-pole-nonratio-cross-and-one-eighth-weil-positivity.md`. |
| A2 | [Formalized](../3-formalized/sharp-logarithmic-overlap-budget.md): explicit coefficient `1/[103424(8π/3+3000)]`; exact ceiling for the specified reciprocal-floor budget. Both leaf audits pass with standard axioms; optimality across all absolute estimates is not established. |
| A3 | [Paper proof](../2-fully-proven/rvm-isolated-pair-critical-multiple.md): global edge `exp(min(x/δ,L))`, where `x>0` solves `sinh x−x=2δL`. The new lattice-null test exposes every pair above Nyquist. Lean verification pending. |
| A4 | [Paper proof](../2-fully-proven/one-ninth-exponent-through-edge-and-hodge-theory.md): source statements upgraded to `1/9`; direct audits pending. |
| A5 | Existing `CompleteConductorResidualsRetainTheirHorizonDecay` gives explicit inequalities in proved existential constants, for `c≥1` and uniformly for `0<c≤1`. Numerical constants and effective growing-overlap schedules remain to be extracted. |
| A6 | Existing `nonneg_of_sincCritical_multiple` reaches radius `R` only when `K>1152e·sincTailConst·blockSize(R+1)`. Completeness over all radii is proved for all multiples or a divergent rate; one universal fixed multiple is not supplied by that argument. |
| A7–A29 | Exact conclusions remain as specified in the source table; none discharged by this card. |

## Gates

- [x] Scope fixed to all 29 source tasks.
- [ ] Dependency-closed proofs of all tasks.
- [ ] Exact Lean statements, direct checks, axiom audits, and umbrella imports.
