# Localized vertical energy through heat-zero collisions

- **ID:** wd-heat-localized-energy-flux
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [WD](wd-directed-source-extinction.md), heat transport investigation
- **Target:** An unconditional upper evolution bound for the actual localized squared-depth energy, uniform as heat tends to zero and valid through multiple zeros.

## Role in WD

The existing heat persistence theorem is a lower-count transfer. Global
squared-depth dissipation can have an infinite initial budget. A localized
upper estimate must pay horizontal flux without assuming simple or separated
zeros and without charging critical zeros as off-line energy.

For a fixed nonnegative smooth horizontal cutoff `w`, study the finite sum

`E_X(t) = sum_z mult(H_t,z) w(Re z-X) (Im z)^2`.

Seek an upper right-derivative bound whose error is controlled by nearby
vertical energy times `C log X`, retaining the negative interaction terms.
An absolute `O((log X)^2)` bound is a preliminary estimate, not the desired
upper-count result. Neither estimate alone closes WD; the arithmetic
absorption/counting step must still be proved.

## Proposed proof mechanism

1. Extract a conjugation-invariant packet of actual heat zeros around `X`.
   The existing Euler anchor and cofactor bounds supply degree `O(log X)`.
   Removing the remaining nearby factors should give an analytic exterior
   logarithmic derivative with derivative `O(log X)`, real on the real
   axis. Its imaginary part is then `O(|Im z| log X)`.
2. Symmetrize the pair forces before taking absolute values. A Lipschitz
   gradient cancels the singularity of `1/(z_i-z_j)`. For the vertical
   energy, the internal vertical term is negative; only the horizontal
   cutoff terms need an upper estimate.
3. At a zero of multiplicity `m`, use the forward Hermite model and local
   multiplicity conservation. The cluster centroid has first-order drift
   `2m` times the regular logarithmic derivative. Its leading splitting
   is horizontal, so a real collision does not create a positive first-order
   vertical-energy term. No assumption of simple zeros is allowed.
4. Pass the uniform upper right-derivative estimate to a finite-time
   inequality, including the unheated endpoint by continuity.

## Open proof obligations

- **Formalized:** conjugation-invariant actual packet and exterior derivative
  estimate; see [the completed input](../3-formalized/wd-heat-exterior-force.md).
- **Formalized:** local simplicity immediately after an arbitrary complex
  collision; see [the completed input](../3-formalized/wd-heat-forward-simple-clusters.md).
  Weighted zero-sum continuity and integration must still turn it into
  collision passage for the energy estimate. An explicit centroid expansion
  is an alternative, no longer the only proposed route.
- **Formalized at the pair level:** the horizontal cutoff error is paid by
  squared heights without an inverse-gap loss; see
  [the completed estimate](../3-formalized/wd-heat-localized-pair-force.md).
  Its finite-packet sum and identification with the actual derivative remain.
- **Formalized:** continuity of the actual localized zero sum, including
  time zero; see [the completed continuity theorem](../3-formalized/wd-heat-localized-energy-continuity.md).
  Derivative identification and integration through collisions remain.
  Do not hide them in a path, simplicity, or flux hypothesis.

## Status

The active draft `RHTower/Heat/HeatLocalizedEnergyEvolution.lean` contains
work on the regular-part velocity identity, full complex zero motion,
local simple-zero branches, and compact forward simplicity. Those additions
have not passed a Lean check and are not exported by the umbrella. The
folder move preserved this draft; it did not certify these claims.

For the derivative identification, choose disjoint isolating disks around
the finitely many zeros in a zero-free enclosing circle. At simple zeros,
local count one gives unique actual branches. The full complex motion
estimate gives their right derivatives `H''/H'`. On the compact complement
of the disks, the initial function has a positive modulus minimum;
compact-open heat continuity therefore excludes extra nearby zeros.
The actual weighted sum is consequently a finite branch sum and can be
differentiated. Compact forward simplicity will discharge the temporary
simple-configuration condition on a right interval after every positive
time. Continuity at the starting time remains essential for collision
passage; right isolation alone is not a finite-collision claim.

`HeatExteriorForce.exists_uniform_riemannHeat_exterior_force` is formalized;
the final plain Lean check passed without errors or warnings. The
localized-energy evolution theorem and the full WD arithmetic upper-bound
requirement remain open.

## Exterior-field input: paper proof and Lean formalization complete

For sufficiently large `X`, `0 <= t <= 1/8`, and `t log X <= 1`, there
is a finite set `S` consisting exactly of the zeros with `|Re z-X| <= 2`,
of total multiplicity at most `C log X`. On the inner rectangle
`|Re z-X| <= 1`, `|Im z| <= 1/2`, there is an analytic exterior field `Q`
such that, off the zeros,

`H_t'/H_t = sum_{a in S} mult(H_t,a)/(z-a) + Q(z)`,

and `|Q|, |Q'| <= C log X`, `|Im Q(z)| <= C log X |Im z|`.

Proof. Apply `exists_uniform_riemannHeat_local_cofactor` at
`c = X-16i`, discard factors of exponent zero, and translate its finite
factorization back to the original coordinate. Each exponent is the
analytic order at its zero: remove that factor, and the product of the
remaining factors and the cofactor is nonzero there. The total degree is
at most `C0 log X`.

All actual heat zeros have imaginary part at most `1/2` in absolute
value, including time zero. Thus every zero with `|Re z-X| <= 2` lies
strictly inside the cofactor's zero-free disk of radius `18` about `c`
and occurs in this factorization. Filter the factors by this horizontal
condition to obtain `S`. It is invariant under conjugation, with invariant
multiplicities. Every remaining factor is at horizontal distance at least
`1` from the inner rectangle.

Let `q` be the translated cofactor logarithmic derivative plus the poles
from the remaining factors. On the inner rectangle, the distance to `c`
is at most `sqrt(1+(33/2)^2) < 67/4`. Hence both the cofactor field and
its derivative have norm at most `C0 log X`. Each remaining pole of
multiplicity `m` contributes at most `m` to either bound. Consequently
`|q|, |q'| <= 2 C0 log X`, with analyticity on a neighborhood of each
point of the rectangle.

Set `Q(z) = (q(z) + conjugate(q(conjugate z)))/2`. Conjugate symmetry of
`H_t` and of the local pole packet shows that `Q=q` off the zeros in
the rectangle, so the logarithmic-derivative identity is preserved.
Conjugation preserves both bounds and analyticity, and `Q` is real on
the real axis by construction. Apply the derivative bound on the vertical
segment from `Re z` to `z`. It gives
`|Q(z)-Q(Re z)| <= 2 C0 log X |Im z|`, proving the claimed imaginary-part
bound. No separation, simplicity, or noncollision assumption enters.

This discharges only the exterior-field input. The local
cluster expansion, cutoff estimate, and arithmetic extinction step remain
unproved.

## Pairwise cutoff calculation

For two distinct zeros write `d = x_i-x_j`, `e = y_i-y_j`,
`w_i = w(x_i)`, and `v_i = w'(x_i)`. Their combined contribution to
the derivative of `sum w(x_i)y_i^2` is

`2 ((v_i y_i^2-v_j y_j^2)d - 2(w_i y_i-w_j y_j)e)/(d^2+e^2)`.

Its numerator before the outside factor `2` is exactly

`-(w_i+w_j)e^2 + (v_i-v_j)d(y_i^2+y_j^2)/2`
`+ ((v_i+v_j)d/2-(w_i-w_j))(y_i+y_j)e`.

If `|w''| <= M` on the horizontal interval, then
`|v_i-v_j| <= M|d|` and the trapezoid remainder in the last line is
at most `M d^2/2`. Also `|(y_i+y_j)e| <= y_i^2+y_j^2`.
Thus the contribution is at most

`-2(w_i+w_j)e^2/(d^2+e^2) + 2M(y_i^2+y_j^2)`.

This estimate is uniform as the distinct zeros approach one another.
For a conjugate pair, the negative term is exactly `-4 w_i`; it
does not deteriorate when the common height approaches zero. The
normalization counts each unordered pair once; summing the ordered
root velocities gives precisely the outside factor `2` above.

The displayed algebra and bounds concern distinct roots. They are not
yet a proof of a derivative bound for the actual heat-zero measure.
At a multiple root, the horizontal Hermite splitting and cluster
centroid expansion must supply the missing collision term.

Formalization is complete in `RHTower/Heat/LocalizedHeatPairForce.lean`.
The trapezoid estimate follows from the mean value theorem applied to
`w(r) - (w'(x_i)+w'(x_j))r/2`: between the endpoints its derivative
has absolute value at most `M |x_i-x_j|/2`. This gives the stated
quadratic remainder without a third-derivative assumption. The source
passed its final plain Lean check without errors or warnings.

## Alternative collision passage under investigation

`exists_norm_riemannHeat_sub_heatModelFwd_le` already treats an arbitrary
complex center. Its degree-`k` model has `k` distinct real roots. The
minimum-modulus argument used in `exists_nonreal_zeros_backward` should
give one distinct actual future zero near each of these roots, without
requiring the collision center to be real. Stable local zero counts then
force all these zeros to have multiplicity one and exhaust the isolating
disk.

Target: for every positive heat time and every center, a sufficiently
small isolating disk has only simple zeros at all sufficiently close
strictly later times. The time interval may depend on the center; the
force bounds used on it remain uniform. Local weighted zero-sum
continuity would then pass the integrated simple-root estimate through
the initial collision. This could replace the explicit centroid and
second-moment expansion. Neither this extension nor the integrated
energy estimate is claimed proven yet.

The source `RHTower/Heat/HeatForwardSimpleZeros.lean` now proves
`exists_ball_simple_riemannHeat_zeros_forward`; the final plain Lean
check passed without errors or warnings. Its argument is dependency-closed:
the scaled
Hermite roots produce `k` distinct heat zeros by the minimum-modulus
principle, and the preserved total multiplicity is exactly `k`. A zero
with vanishing derivative would contribute at least two and exceed
that count. The theorem's center is arbitrary complex and its initial
heat time is positive. It does not assert a uniform duration for the
interval of simplicity.

## Next exact obligations

1. Define the actual localized weighted zero sum, retaining multiplicity,
   and prove its continuity from stable local counts. For a zero-free
   enclosing circle, take disjoint small disks around the finitely many
   initial zeros. Nearby local and total counts are fixed; hence the
   disks exhaust all zeros inside the circle. Uniform continuity of the
   weight bounds the sum's variation. This also needs the right-hand
   version at time zero.
2. At simple zeros, identify the derivative of that sum using the full
   complex motion estimate and `H_t''/H_t'`. Sum the proved pair estimate,
   pair conjugates, and apply the actual exterior-field bound.
3. Use the proved local future simplicity and continuity to pass the
   estimate through collisions, then integrate. Do not replace these
   steps with a path or flux assumption.

All four completed input modules have passed their final plain checks
and are wired into the appropriate umbrellas. No olean for these new
modules has been generated yet. The arithmetic upper bound and WD
extinction remain open after these analytic inputs.

### Weighted continuity proof plan

Use `exists_radius_no_boundary_zero` to enclose the compact support in a
zero-free circle. Its finite zero set is `S`. Choose disjoint small
isolating disks around the points of `S`, contained in the enclosing
disk, on which the weight varies by less than
`epsilon/(sum_{a in S} mult(H_t,a)+1)`.

For nearby times, the count in each small disk and the total count in
the enclosing disk are fixed. The small disks therefore exhaust the
zeros of the enclosing disk: any remaining zero has positive
multiplicity and would exceed the total count. The weighted-sum error
is bounded by the fixed total multiplicity times the chosen weight
oscillation, hence is less than `epsilon`.

For the unheated endpoint, use locally uniform convergence within
nonnegative times (the same time Taylor bound already used for positive
times), then the existing general local-count transfer. This extends
the count argument to the right-hand limit at zero without assuming a
uniform interval of simplicity there. The source inputs are
`PoissonJensenUpperBound.exists_radius_no_boundary_zero`,
`LocallyUniformZeroCountTransfer`, and the actual heat-time Taylor bound.

`RHTower/Heat/HeatZeroSumContinuity.lean` now proves
`continuousOn_heatLocalizedVerticalEnergy` for every continuous compactly
supported horizontal weight. The final plain Lean check passed without
errors or warnings. The zero sum is defined with actual analytic multiplicity;
finite-support identities are proved from the critical-strip bound and
the enclosing zero-free circle. No summability, root-path, or continuity
premise is assumed for the actual zero measure.
