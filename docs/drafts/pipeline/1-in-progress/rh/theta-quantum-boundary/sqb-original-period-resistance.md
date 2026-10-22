# SQB original-source period resistance classification

Status: complete original-period classification is formalized and audited.
RH remains open. Frontier map is read-only.

Full chain: original modular source → independent current comparison or
full-Xi spectral occurrence → critical-line classification → RH.

The actual complete block path cost is now the explicit quadratic level factor
times resistance/current products at two original heights. The next question
is whether these resistances stay finite as the regulator is removed. A toy
nodal profile already diverges, but an original-source classification is needed.

For a zero-free horizontal source period, compactness gives a positive actual
amplitude floor. Prove convergence of the regulated reciprocal integral to the
finite original reciprocal integral, with an explicit source-floor error bound.
For an original common zero, source C¹ regularity bounds amplitude above by a
constant times distance from that zero. Comparison with the reciprocal affine
profile gives logarithmic divergence. Periodicity identifies the same complete
one-period resistance regardless of the node's horizontal location.

- [x] Broad OR corpus discovery and current-source/nodal/weight inspection.
- [x] Derive actual finite-family amplitude control near a common zero.
- [x] Prove logarithmic divergence of original resistance at every nodal height.
- [x] Prove finite limit and a bound on each zero-free original period.
- [x] Close the exact boundedness/nodal-free classification.
- [x] Audit scratch/source checks, sole-target builds, axioms, index and lint.
- [ ] Use the classification in a quotient-area comparison retaining nodal curvature.

No original nodal point is assumed to exist. No source-specific floor is
promoted to a uniform floor over height, level or varying sources.

The exact positive result is source-specific: if d>0 is the compact period
amplitude floor, then 0≤R₀−R_e≤e/d² and R_e≤R₀≤1/d. No extra floor is
assumed in the zero-free classification; compactness constructs it.

At any actual common zero, C¹ bounds for the complete finite family give
√D(x+iy)≤L(x−a) on [a,a+1] for a source-dependent L≥1. Therefore

    R_e(y) ≥ [log(L+e)−log(e)]/L → +∞.

Literal period invariance identifies this node-started integral with R_e(y).
Thus finite regulator limit, boundedness over all positive regulators, and
absence of a node on [0,1] are equivalent. Divergence is equivalent to a node.
The reciprocal current factor cannot be removed using source smoothness.
The full current product and nodal curvature still require joint analysis.

All 17 declarations pass source/scratch, targeted build and standard-only
axiom checks, are indexed once, and are wired once in the umbrella.
Repository formal lint passed; no owned compiler remains.
[Complete proof and audit](../../../3-formalized/sqb-original-period-resistance.md).

The [full original current-period limit](../../sqb-original-period-current-limit.md)
is now formalized through nodal concentration. It gives finite product limits
on zero-free periods and product divergence at nodal heights with positive
limiting current. Bounded nodal products require zero limiting current;
relative rates and the quotient-area comparison remain open.
