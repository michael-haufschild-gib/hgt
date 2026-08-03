# Route R finite common-Hardy reporter

- **Status:** finite theorem formalized; arithmetic incidence open
- **Parent:** `rh-current-frontier-map.md`, Route R
- **Open core:** `PRELIMIT_NONCOMPACT_GAMMA_HARDY_REPORTER_MATE`

## Frontier statement

Pointwise one-corner contraction is already proved, but it does not yet give one Hardy source
working at all nodes.  For finite Fisher data, construct the literal scalar cutoff field

\[
  c(u)=\sum_{i,j}\mathbf 1_{h_j<u\le h_i}
  p_i p_j(h_i+h_j-2m)(d_i+d_j).
\]

Prove unconditionally that:

1. `c` is one element of `L²((0,∞),du)`;
2. `‖c‖² ≤ 1/2` times the complete one-corner coarea energy;
3. its Laplace transform at every right-half-plane node is the finite sum of the exact
   semigroup divided differences already carried by the hard-cut/soft-damping theorem.

This is the finite common-test theorem missing between the pointwise codiagonal estimate and
Route R's infinite Gamma/co-Poisson reporter mate.  It is not an RH criterion and does not assert
the arithmetic mate.  No Sonin continuation is used or proposed: prior corpus no-gos exclude that
route from supplying the source-to-Ward projection.

## Hostile gate

The theorem moves the frontier only if the reporter is a single `Lp` vector independent of the
Hardy node and the Laplace identity is simultaneous in the node.  Merely restating the existing
pointwise estimate, choosing one vector per node, or representing the full scalarized Xi trace
would be theatre.  The latter is impossible by `XiWardInteriorSourceBudgetDivergence`.

After this theorem, remaining hard content is exactly the infinite presentation-independent
ordinary-prime Gamma/co-Poisson mate, including affine terms before overlap division.  No weak
compactness argument may identify the full Xi logarithmic trace with a bounded Hardy vector.

## Formal certificate

- `formal/GaloisForLFunctions/HTGeometry/FisherOneCornerCommonHardyReporter.lean`
- one literal `Lp ℂ 2 halfLineLaplaceMeasure` reporter, independent of Hardy node;
- squared norm bounded by one half of complete finite holonomy energy;
- simultaneous Laplace/divided-difference identity for every right-half-plane node;
- targeted module build passes;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Updated hard boundary

The updated Hellinger--Hodge Green-descent paper does not turn this finite reporter into a global
completion theorem.  Pointwise invariant gauges suffice logically, while the actual Route-R
consumer still needs a source-derived Ward column.  The next theorem must therefore construct a
finite-parameter, precritical family acting on the actual one-corner field, retain affine
prime/Gamma terms before division, converge locally uniformly to
`continuedXiAntiCausalWardResponse`, and preserve the critical four-unit energy.  Landing the full
completed Xi trace is excluded by `XiWardInteriorSourceBudgetDivergence`; identifying a target
divisor factor before this construction is circular.

The internal Möbius--theta exponent cofaces now also form a literal all-order
`ell2(N;L2)` physical horizon, with exact codiagonal equal to every theta/Xi jet; see
`../3-formalized/riemann-mobius-theta-internal-jet-source-horizon-admission.md`. Hence the missing
infinite object is no longer an arbitrary countable completion grade. It is the specific
polarized Gamma/co-Poisson/Hodge comparison from that admitted horizon to the Ward column, with
four-unit energy preservation.
