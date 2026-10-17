# Infinite two-grid trace extension and sharp Dirichlet stability

- **ID:** two-grid-coprime-trace-extension
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Construct the actual infinite minimum-energy extension of
  square-summable nodal data on the union of two divisor grids, with exact
  adjacent-node energy and sharp arithmetic stability constants.

For m,n≥2 let U be the positive integers divisible by m or n, counting common
nodes once. For actual ℓ² data v on U, propose an L² velocity E_U(v) whose
primitive has value v_a at every a∈U and zero at all other nonnegative integers.
Its logarithmic primitive should have the corresponding values at log a.
Proposed exact energy:

    ‖E_U(v)‖² = 2Σ_(a∈U) v_a² − 2Σ_(a,a+1∈U) v_a v_(a+1).

Proposed sharp lower/upper constants multiplying Σv_a²:

    2, 2                 if gcd(m,n)≥2;
    1, 3                 if gcd(m,n)=1 and m,n≥3;
    2−√2, 2+√2           if gcd(m,n)=1 and min(m,n)=2.

The adjacent-pair/star geometry exposed by the angle package suggests these
constants, but the extension, infinite energy identity, sharpness and minimality
remain unproved and uncounted. Common-node compatibility must be encoded in
the actual data space, not hidden in an unverified interface.

Audit tasks: construct the convergent velocity series or unit-cell derivative
from actual ℓ² data; prove every integer trace; handle adjacent hats and shared
nodes without double-counting; derive summability of cross terms; prove a sharp
closed-range estimate and equality witnesses; establish an exact competitor
energy defect before claiming minimum-energy interpolation. Do not replace the
construction with assumed trace support, summability or closedness. Distinguish
prescribed-value interpolation from the orthogonal projection's curvature data.

Fresh corpus query: `two divisor grids union trace interpolation adjacent tents
minimum energy joint extension`, 60-second hybrid budget, all 20 candidate
lemmas and 20 source arguments inspected. Existing single-grid infinite
extension and finite trace defects found; no matching two-grid construction.
No partial stages or execution errors; coverage snapshot older than current
index, semantic coverage unmeasured, background refresh incomplete. Reaudit
corpus and primary interpolation theory before the paper proof and Lean.

This would turn arithmetic noncommutation into a stable joint continuum trace
domain, directly extending the multiplicative-to-additive Dirichlet bridge.

Dependency-closed paper proof: `docs/reports/BiScaleUncertainty/TwoGridCoprimeTraceExtension.md`. Actual kernel data space assigns common nodes once. Lean construction, sharpness, closed range and competitor audits pending; count remains 11/100.


## Proof and implementation obligations

- [x] Full paper proof, concrete shared-node kernel, convergent synthesis,
  every trace, summable adjacent energy, sharp constants and extremizers,
  closed algebraic sum, unconditional mismatch identity and exact constrained defect.
- [x] Focused corpus audit: all 16 candidates and 17 source arguments inspected;
  partial=false/errors=[], semantic coverage unmeasured, background refresh incomplete.
- [ ] Direct leaf checks: TwoGridTraceData, TwoGridTraceStability,
  TwoGridTraceSharpness, TwoGridTraceMinimality.
- [ ] Every public declaration's axiom report and main signatures inspected.
- [ ] Umbrella, generated API, lint, exact-source freshness and whitespace.

Main domain is an actual closed kernel in ℓ²×ℓ²; its equivalence to deleting
second-family common-node values is proved. Product Banach norm is a maximum;
union nodal mass is the separate sum of squared component norms. Minimum-energy
claim fixes off-union integer traces as zero. Union-only interpolation remains
a different problem. No added analytic admission hypothesis.
