# Sharp infinite two-grid trace interpolation

- **ID:** two-grid-coprime-trace-extension
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Actual joint ℓ²-to-L² trace extension has exact adjacent energy,
  attained arithmetic stability constants, closed range and unique minimum energy.

## Exact result

For m=d+2,n=e+2, assign shared nodes to the first grid. The concrete closed
kernel D={(a,b):P_lcm(E_e b)=0} is proved equivalent to deleting second-family
coefficients at shared nodes. Arbitrary ℓ² pair data canonically produce D.
E(a,b)=E_d a+E_e b has every prescribed integer/log trace and zero off-union
integer traces. With M=‖a‖²+‖b‖²,

    ‖E(a,b)‖² = 2M−2Σ_j a_j[B(m(j+1)−1)+B(m(j+1)+1)].

B is the second-family primitive; the scalar series is proved summable and its
terms have an explicit arithmetic nodal formula. This enumerates adjacent union
pairs once. Sharp energy bounds relative to M are (2,2) if gcd(m,n)≥2,
(1,3) if gcd(m,n)=1 and m,n≥3, and (2−√2,2+√2) if one coprime spacing is two.
Both endpoints are attained by actual data of positive mass. E is injective,
its range is closed, and equals the algebraic sum of the individual tent ranges.

For arbitrary physical q, an unconditional competitor identity retains the two
residual-curvature pairings. When every integer trace matches, excess energy is
exactly ‖q−E(a,b)‖², with equality iff q=E(a,b). Fixing only union traces is a
different problem. The product's Banach norm is a maximum; nodal mass M is a
separate sum of squares. No unproved analytic admission premise.

## Proof and scope

[PROVED HERE] Paper: `docs/reports/BiScaleUncertainty/TwoGridCoprimeTraceExtension.md`.
Convergent synthesis supplies traces and scalar sums. Reduced projection norm
√c bounds cross energy. The positive square T* T supplies attained extremizers.
Uniform lower bound on the complete kernel yields closed range. Moving the
common component between families identifies the original algebraic sum.

Classical interpolation and Hilbert-space methods are not claimed externally
novel. No unweighted log H¹, full affine unitary representation, or RH claim.

## Verification

- [x] Complete paper proof before Lean.
- [x] Four serial direct `lake --old env lean -o <normal-output> <leaf>` checks;
  final logs empty and compiled outputs newer than current sources.
- [x] All 49 public declarations: 40 theorems, seven definitions, one abbreviation,
  one instance. Exact axiom coverage; only propext, Classical.choice, Quot.sound.
- [x] Thirteen main signatures and mathlib API probes inspected in `/tmp`.
- [x] Four unique umbrella imports; all 48 catalog-supported public declarations
  indexed at current source lines. Named instance audited separately.
- [x] Scoped whitespace and stage consistency checked.
- [ ] Global repository lint: ten unrelated concurrent unreachable modules;
  none concerns this package, proof debt or generated-file freshness.
- [ ] Publication-ready external novelty audit.

Leaves: `TwoGridTraceData`, `TwoGridTraceStability`, `TwoGridTraceSharpness`,
`TwoGridTraceMinimality`, all under `formal/GaloisForLFunctions/BiScaleUncertainty/`.
Main declarations: `twoGridExtension_energy`, `twoGridExtension_stability`,
`twoGridExtension_sharp`, `isClosed_sum_coprimeExtension_ranges`,
`twoGrid_competitor_energy`, `twoGrid_minimum_energy_defect`,
`twoGrid_minimum_energy_eq_iff`, in namespace `SobolevShear`.

Evidence: `/tmp/two-grid-{data,stability,sharpness,minimality}-build.log`,
`/tmp/two_grid_axioms.lean`, `/tmp/two-grid-axioms.log`,
`/tmp/two-grid-audit-names.json`, `/tmp/two-grid-index-final.log`,
`/tmp/two-grid-lint-final.log`. Exact global errors are recorded in the fact ledger.

Corpus audit: all 16 focused candidate lemmas and 17 source arguments inspected;
partial=false/errors=[], semantic coverage unmeasured, background refresh incomplete.
Earlier interrupted query left no usable output and was replaced after its handle
was confirmed missing. Parent interpolation theory checked from primary textbook.

Count once as package 12/100. Next unproved candidate:
`../0-backlog/finite-grid-run-length-coercivity.md`.
