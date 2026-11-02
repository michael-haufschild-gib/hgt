# SC: complete-family realization and coupling

- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-0111/route-SC.md`.
- **Goal:** Resolve all seven main obligations and four heat obligations with unconditional Lean proofs.

## Completed

**SC1.** One fixed nonnegative smooth unit profile realizes every finite
`ratCorr` Gram as a positive-mass-weighted complete-matrix compression limit
at the same overlap `2·loglog N·(logloglog N)²`. Positivity on the rational
boost-mass-zero hyperplane is equivalent to eventual complete-family
pole-hyperplane positivity at this single multiple. The equivalence uses
compression index at most one and zeta index parity, without assuming exact
moment preservation by the approximating packets.

Proof and exact declarations:
[universal critical overlap](../3-formalized/finite-rational-correlation-grams-at-critical-overlap.md).
The new profile, Gram limit and final direct hyperplane audit pass with only
`propext`, `Classical.choice`, and `Quot.sound`. Both umbrellas are wired.
Actual positivity remains unproved.

**Heat a.** `negIndex_heatArchState_eq_one_of_eighth_le` gives index one for
every `c>0` and `t≥1/8` in `TheHeatDeformedArchimedeanState.lean`.
Its transitive axiom audit and that of
`riemannHypothesis_iff_negIndex_heatArchState_const` pass with only standard
axioms. This supplies the certified upper-time calibration.

## Remaining source obligations

2. Bounded coupling on the natural-exponent cone implies RH when maximal zero width is unattained.
3. Exclude finite nonzero Weil index.
4. Transfer finite-sieve Hodge positivity to the global inter-tower form.
5. Prove an arithmetic finite-index ceiling.
6. Prove a square decomposition for the dilation form itself on a boost-zero two-prime lattice.
7. Prove glued index at most one, equivalently bounded two-prime lattice coupling.

Heat b: `N(t)≤exp(A·t^(−a))`, `a<1`; heat c: a uniform count;
heat d: no index jumps on `(0,1/8]`.

## Cone boundary

The [polynomial boundary-repulsion theorem](../3-formalized/cone-coupling-polynomial-boundary-repulsion.md)
proves that bounded natural-cone coupling implies RH or
`D-|Re ρ-1/2|≥c/(1+|Im ρ|)^A`, with `c>0` and integer `A>0`.
It combines exact spline lower bounds, Baker separation of the two prime
clocks, phase-coherent cluster control, and a finite sixth residue moment.
It handles arbitrarily close clusters and arbitrary actual multiplicities.
The bound permits unattained positive width; SC2 remains open.

The [exact spline model with bounded local density](../3-formalized/cone-cancellation-with-bounded-local-density.md)
has distinct sign/conjugation quartets, exact coefficients `(sinh z/z)^8`,
unit multiplicities, and real parts cofinal at an unattained positive width.
Every positive two-prime cone moment vanishes, and quartet coupling is
bounded by twenty. Core unit-height windows embed into `Fin 3`; quartet
windows embed into `Fin 12`. All real moments converge absolutely.
The existence theorem and transitive axiom audit pass direct Lean checks
with only standard axioms.

Thus exact spline weights, integer multiplicities, joint clock separation,
and even uniformly bounded local counts do not settle SC2. These strengthen
the earlier [positive-weight](../3-formalized/two-prime-cone-positive-moment-obstruction.md),
[eighth-power](../3-formalized/two-prime-cone-spline-sized-weights.md), and
[exact-coefficient](../3-formalized/two-prime-cone-prescribed-spline-weights.md)
models. A further property of actual zeta zeros is required.

The [Gaussian-damped criterion](../3-formalized/gaussian-damped-natural-cone-rigidity.md)
is formalized for actual zeros. For every fixed `τ>0`, multiplying the spline
residues by `exp(τ(ρ−1/2)²)` makes natural two-prime cone growth at rate
`σ≥0` equivalent to `zetaZeroWidth≤σ`. Bounded coupling is equivalent to RH,
without simplicity, uniform spacing, or an attained boundary. The direct
capstone audit uses only standard axioms. No transfer from bounded coupling
of the original spline kernel is proved; SC2 remains open.

The [zero-exponent density extension](../3-formalized/cone-cancellation-zero-exponent-of-convergence.md)
is formalized for the same exact-spline quartet model. Every positive
inverse-power absolute-ordinate sum converges, while all cancellation,
unit-multiplicity, symmetry, local-count and unattained-width conclusions
persist. Its direct capstone and transitive axiom audits use only standard
axioms. Polynomial upper density bounds therefore do not supply the
missing generic rigidity; the actual arithmetic source remains essential.

## Other boundaries

The [growing-packet prime–pole theorem](../3-formalized/growing-packet-full-prime-pole-cancellation.md)
controls the literal remainder divided by `√Y`, uniformly for bounded
coefficients and cell indices at most `exp(√log Y/23040000)`, with error
`O(exp(−√log Y/7680000))`. Its recorded direct and transitive audits use only
standard axioms. This extends fixed-family cancellation; a uniform upper
bound for the complete Weil index is still missing.

The [all-detail source extension](../3-formalized/all-detail-prime-pole-cancellation.md)
is formalized in the original squared Hilbert masses. For unit Haar and
coarse sections, every detail horizon is allowed and
`M≤exp(√log Y/184320000)` gives normalized remainder
`O(exp(−√log Y/92160000))`. The literal common-horizon all-prime source
satisfies the same bound. The normalized prime matrix approaches its
separable leading pole at that rate. All six module audits use only
standard axioms. The retained `√Y` normalization still leaves the complete
Weil index ceiling open.

The finite-sieve Hodge theorem concerns the matched prime form after a scalar
subtraction. The Gamma and mixed-term comparison needed for the complete
Weil form is not supplied by that uniform index bound.

`exists_nonrealZeroCount_and_collisionMass_le_twoThirds` bounds the heat count
by `C·R(t)·log(2+3R(t))`, where
`R(t)=max(X₀,2π·exp((2/3+ε)/t))+1`. The `2/3` improves the coefficient of
`1/t`, not its power; it does not provide heat b.
