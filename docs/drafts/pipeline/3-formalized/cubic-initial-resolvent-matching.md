# Initial matching with the cubic Eisenstein series

- **ID:** cubic-initial-resolvent-matching
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** For `Re s>4`, `Im s>0`, and cutoff heights `1<a<b`, the actual quotient Eisenstein series minus its incoming seed equals `R(s(2−s))F(s)` in `L²`.

Normalize each nonzero cusp row by its Euclidean norm. The normalized rows
lie in a compact sphere; the scalar weights are the absolutely summable
base-point Eisenstein terms. On each compact spatial set, every derivative
of the normalized kernel is uniformly bounded. Termwise differentiation
therefore gives smoothness and the equation `ΔE=s(2−s)E` for `Re s>2`.

Write `r_s(v)=(1−χ(v))v^s`. In a Bianchi reduced chart, with `‖z‖≤1`
and `v≥1/2`, a coprime row `(c,d)` with `c≠0` satisfies
`height(c,d)·‖coordinates(c,d)‖≤5`. If `c=0`, then `d` is a unit and
the coordinate norm is at most two. Consequently each remainder term is
bounded by `max(5,2b)^(Re s)·‖coordinates(c,d)‖^(−Re s)`.
The row map is injective into `ℤ⁴`, so this majorant is summable for
`Re s>4`, uniformly over the quotient.

The logarithmic height gradient has hyperbolic norm one. The identity
`v r_s′(v)=v^s[(1−χ(v))s−vχ′(v)]`, together with the compact support
of `χ′`, bounds each differentiated remainder by a fixed multiple of
the remainder profile with cutoff heights `b+1,b+2`. Its absolute sum
has the same uniform lattice bound. Thus the actual remainder and its
hyperbolic gradient are bounded and square-integrable on the finite-volume
quotient.

The proper invariant cusp barrier gives compact smooth cutoffs, eventually
one near every point, with uniformly bounded hyperbolic gradients. Their
products with the remainder converge in both mass and gradient by dominated
convergence. On each compact test support the cutoffs are eventually one;
Green's identity therefore puts the remainder in the actual Laplacian graph,
with `Δ(E−seed)=F+s(2−s)(E−seed)`. Since `s(2−s)` is nonreal in the
stated region, the established resolvent uniqueness identifies the two
`L²` vectors.

Formalized as `CubicEisenstein.kernelEisensteinL2Correction_initial_overlap`
in `TheCubicInitialResolventMatching.lean`. Spatial derivatives, the actual
Laplace equation, uniform remainder and gradient bounds, and compact cutoff
approximation are kernel-checked. The operator-graph and matching endpoints
use only `propext`, `Classical.choice`, and `Quot.sound`.
This establishes an initial source identity; it supplies neither residue
nonvanishing nor arithmetic cancellation.

Adapted from OpenAI's smooth-summand, cusp-remainder, and initial-resolvent
arguments; the quotient, seed, and resolvent inputs are locally formalized.
