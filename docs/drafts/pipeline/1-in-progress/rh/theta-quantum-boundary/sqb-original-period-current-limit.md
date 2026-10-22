# SQB original current-period limit and joint path costs

Status: original-source current limit, joint products and regulator-free
block comparison are formalized and audited. RH remains open. Frontier map
is read-only.

Full chain: original modular source → independent current comparison or
full-Xi spectral occurrence → critical-line classification → RH.

Resistance is now classified at every fixed source and height. To analyze
its product with current energy, first determine the current factor without
discarding nodal concentration. For the complete source F, D=||F||² and
r=√(D+e²), direct differentiation gives

    r_xx = H_e + Re Σ(F_q,xx conjugate F_q)/r.

Periodicity cancels the integral of r_xx. Each remaining component is bounded
in absolute value by |F_q,xx| because |F_q|≤√D≤r. Original C² regularity on
the compact period therefore supplies a regulator-independent integrable
majorant. Dominated convergence gives the complete current limit

    E_e(y) → −∫₀¹ Re Σ(F_q,xx conjugate F_q)/√D dx,

with zero value of each quotient at a common zero. This is the limit of the
full integrated current, not an integral of its pointwise current limit.
The source acceleration expression must retain all components and exact
periodic boundary cancellation.

- [x] Broad OR corpus searches and actual source/derivative/limit inspection.
- [x] Prove the source second-derivative identity and complete period formula.
- [x] Derive source majorant, integrability and full regulator convergence.
- [x] Combine with resistance classification, preserving undecided zero-limit cases.
- [x] Audit scratch/source, targeted build, all axioms, wiring, indexing and lint.
- [ ] Establish the quotient-area lower bound retaining original nodal curvature.

No derivative bound or integrability hypothesis is added to the original
source. A finite current limit alone supplies no quarter inequality.

The complete current limit is finite and nonnegative at every positive height,
and bounded by the integral of original second-derivative norms. A zero-free
period gives C_e→R₀E₀. A common zero with E₀>0 gives C_e→+∞. Conversely,
a bounded nodal product requires E₀=0; that zero-limit case still needs rates.

On the original two-period zero-free domain, regulator removal gives the
same source/mean comparison with D replacing D+e². For positive mean-zero
sources, the limiting two-period requirement has coefficient (4/3)N(2N+1),
without the factor two introduced by an elementary regulator threshold.
These are domain-qualified source statements, not global nodal exclusion or
a quotient-area lower bound.

All 33 public declarations pass scratch/source checks, the sole-target build
and standard-only axiom audits. All are indexed once, with both local
helpers also indexed; the module is wired once. Repository formal lint passed.
[Complete proof and audit](../../../3-formalized/sqb-original-period-current-limit.md).

The [zero-limit source-rigidity audit](../../sqb-zero-period-current-rigidity.md)
now forces pair/phase vanishing, a common real radial derivative, and zero
first horizontal derivatives at common nodes. Nonflat horizontal nodes
force positive E₀ and product divergence. Exceptional Maass zero means
also force positive E₀ on every zero-free period. The remaining zero-limit
case contains a common zero with zero horizontal derivative energy; this
necessary alternative is not excluded and need not be exclusive.
