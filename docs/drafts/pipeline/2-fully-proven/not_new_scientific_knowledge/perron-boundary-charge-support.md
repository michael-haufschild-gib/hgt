# Perron boundary charge gives exact arithmetic support

- **ID:** perron-boundary-charge-support
- **Stage:** 2-fully-proven
- **Type:** THEOREM, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Lean:** `formal/GaloisForLFunctions/RHTower/PerronBoundaryCharge.lean`
- **Parent:** `quiet-flank-growth-support-radius.md`

## Medalist lens

The quiet-crossing proof does not use a uniform bound inside a rectangle. It uses only the four
oriented boundary integrals in Cauchy's rectangle identity. It also never compares the height
sequence chosen at depth `M` with the sequence chosen at another depth.

The native constraint is therefore boundary charge with quantifiers

`for every (M,delta), there exists a height exhaustion`,

not a single flow-like height sequence that works uniformly for all contours.

## Definition

For an entire carrier `F`, coefficient index `n`, knot width `0<delta<1`, right abscissa `c`, and
depth `M`, put

`G_{n,delta}(s)=F(s) E_{n,delta}(s)`,

where `E_{n,delta}` is the entire variable Perron regularization.

Say that `G_{n,delta}` has boundary charge at most `L` at depth `M` if there is a sequence
`T_k->infinity` such that:

1. the truncated right integrals converge to the full right vertical integral;
2. the top horizontal integrals tend to zero;
3. the bottom horizontal integrals tend to zero;
4. every truncated left integral has norm at most `L`.

No pointwise or uniform bound on the rectangle interior is part of the definition.

## Theorem A `[PROVED]`: boundary charge controls the right edge

If `F` and `E_{n,delta}` are entire and the boundary charge at depth `M` is at most `L`, then

`|integral_R G_{n,delta}(c+it) dt| <= L`.                         (1)

### Proof

Apply Cauchy's theorem to the rectangle with corners `-M-iT_k` and `c+iT_k`. With the standard
orientations,

`i I_right = I_top - I_bottom + i I_left`.

Hence

`|I_right| <= |I_top|+|I_bottom|+|I_left|`.

Let `k->infinity`. The first two terms vanish, the left term is at most `L`, and the truncated
right integral converges to the full integral. This proves (1).

## Theorem B `[PROVED]`: normalized charge discharges the coefficient Prop

Assume `F` agrees with the absolutely convergent Dirichlet series

`sum a_m m^{-s}`

on `Re(s)>=c>0`. If for every admissible `delta` and all sufficiently large `M` the boundary charge
is at most

`2 pi H(M) (n-delta)^(1-M)`,                                    (2)

then

`|delta a_n| <= H(M) (n-delta)^(1-M)` eventually.               (3)

### Proof

The variable Perron identity gives

`delta a_n = (1/(2 pi)) integral_R G_{n,delta}(c+it)dt`.

Combine it with (1) and (2). This is exactly the project Prop
`HasVariableQuietFlankCoefficientBound`.

## Theorem C `[PROVED]`: exact support radius

If additionally

`0<=H(M)<=C R^M`

eventually, then

`a_n != 0  ==>  n <= R`.                                        (4)

Indeed, if `R<n`, choose `0<delta<min(1,n-R)`. Then `R<n-delta`, and the right side of (3) is a
constant times `(R/(n-delta))^M`, which tends to zero. Thus `delta a_n=0`, a contradiction.

## Theorem D `[PROVED, Lean]`: strip-mass producer

Fix `M,n,delta`, and suppose:

1. `t -> G_{n,delta}(c+it)` is integrable;
2. the functions

   `u_+(T)=|integral_{-M}^c G_{n,delta}(x+iT)dx|`,

   `u_-(T)=|integral_{-M}^c G_{n,delta}(x-iT)dx|`

   have integrable sum on `[0,infinity)`;
3. `integral_R |G_{n,delta}(-M+iy)|dy <= L`.

Then the boundary charge at `(M,delta)` is at most `L`.

### Proof

Right-edge convergence follows from integrability. Since `u_++u_-` is nonnegative and integrable,
its integral over `[k,k+1]` tends to zero. Choose `T_k in [k,k+1]` where its value is at most that
interval integral (up to an arbitrarily vanishing error). Then `T_k->infinity` and both horizontal
charges tend to zero. Finally,

`|integral_{-T_k}^{T_k}G(-M+iy)dy|
 <= integral_R |G(-M+iy)|dy <= L`.

This supplies all four boundary constraints.

A sufficient source condition for item 2 is finite strip area

`integral_0^infinity integral_{-M}^c
  (|G(x+iT)|+|G(x-iT)|) dx dT < infinity`,

by the norm-integral inequality and Tonelli.

## Attack and scope

- `[PROVED]` A single common quiet-height sequence is unnecessary. The exhaustion may depend on
  `M`, `n`, and `delta` without weakening the support conclusion.
- `[PROVED]` Uniform strip quietness is merely one producer of boundary charge; it is not the native
  hypothesis.
- `[PROVED]` The boundary-charge theorem is exact at the arithmetic support level: no half-unit
  rounding remains.
- `[BRIDGE]` The rectangle identity itself is ordinary complex analysis. The new content is the
  normalized constraint object, the quantifier correction, and its composition with exact
  arithmetic support.
- `[PROVED]` `HasPerronStripMassAt` formalizes right integrability, integrable horizontal charge,
  and bounded left `L1` mass, and constructs `HasPerronBoundaryChargeAt`.
- `[PROVED]` `perron-carrier-flank-mass.md` removes the remaining kernel dependence. Geometric
  negative-line `L2` energy supplies the quantitative flank mass, while finite weighted horizontal
  carrier mass supplies the escaping heights; right-edge convergence is automatic.
- `[OPEN CORE]` These two coefficient-independent masses have not yet been proved for the target
  source-built carrier. This is the precise analytic input to seek from the L2/Mellin transport.

## Novelty and significance gates

- **NOVEL:** the project previously encoded quietness as a uniform supremum along one common height
  sequence. The boundary-charge object removes the rectangle interior, reverses the common-height
  quantifier, and still yields the exact same support conclusion.
- **SIGNIFICANT:** this replaces a hard sup-norm hypothesis by an edge-mass constraint that can in
  principle be discharged by integral estimates. It moves the remaining RH-facing input from
  pointwise quietness to a source-compatible strip-mass problem.

## Gates

- [x] 0 -> 1: minimal boundary constraint and quantifier order isolated.
- [x] 1 -> 2: boundary, coefficient, exact-support, and strip-mass proofs complete.
- [x] 2 -> 3: Theorems A--D formalized and axiom-audited.
- [x] Coefficient-independent flank and horizontal mass producers formalized in
  `PerronCarrierFlankMass.lean`.
- [ ] 3 -> 4: requires proving those carrier masses for the target source and paper integration.
