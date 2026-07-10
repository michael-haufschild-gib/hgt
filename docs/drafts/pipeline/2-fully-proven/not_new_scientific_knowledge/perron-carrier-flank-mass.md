# Coefficient-independent Perron carrier mass gives exact support

- **ID:** perron-carrier-flank-mass
- **Stage:** 2-fully-proven
- **Type:** THEOREM, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parent:** `perron-boundary-charge-support.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PerronCarrierFlankMass.lean`

## Medalist lens

The kernel-dependent boundary-charge Prop conflates two different tasks:

1. quantitative growth on the left vertical edge, which determines arithmetic support;
2. qualitative escape of the other edges, which only permits contour passage.

Neither task intrinsically depends on a coefficient index. The right question is therefore whether
the Perron kernel can be eliminated from both hypotheses before the coefficient `a_n` is selected.

The answer is yes. Two carrier-only masses suffice:

`A_M(F) = integral_R |F(-M+it)| / (1+t^2) dt`,

and

`Q_M(F) = integral_(1,infinity) integral_(-M,c)
  (|F(x+iT)|+|F(x-iT)|)/(1+T^2) dx dT`.

The first carries the geometric radius. The second is qualitative and produces the escaping
heights. Both are independent of `n` and `delta`.

## Theorem A `[PROVED]`: coefficient-independent left-flank envelope

Let `M>=2`, `n>=1`, and `0<delta<n`. Put `D=n-delta`. Then for every real `t`,

`|E_(n,delta)(-M+it)| <= 4 D^(1-M)/(1+t^2)`.               (1)

### Proof

Away from the removable points,

`E_(n,delta)(s) = K_(n,delta)(s)/(s(s+1))`,

where the numerator is the three-knot second difference. On `Re(s)=-M`, the exponent `1-M` is
nonpositive, so each of the three positive bases is bounded above by the smallest base `D` after
raising to that exponent. Hence

`|K_(n,delta)(s)| <= 4 D^(1-M)`.

For `M>=2`, both `|-M+it|` and `|1-M+it|` are at least `sqrt(1+t^2)`. Therefore

`|s(s+1)| >= 1+t^2`,

which proves (1).

## Theorem B `[PROVED]`: carrier flank mass gives normalized charge

Separate **boundary escape** at `(M,n,delta)` from the left bound: there is a nonnegative sequence
`T_k->infinity` along which the truncated right integral converges and the top and bottom horizontal
integrals vanish. If boundary escape holds and `A_M(F)<=A`, then

`boundary charge <= 4 A D^(1-M)`.                            (2)

Indeed, (1), the norm-integral inequality, and monotonicity of the integral give

`|integral_(-T_k,T_k) F(-M+it)E(-M+it)dt|
 <= 4 D^(1-M) A_M(F)`.

In particular, if

`A_M(F) <= (pi/2) H(M)`,                                     (3)

then (2) is exactly

`boundary charge <= 2 pi H(M) D^(1-M)`,                      (4)

the normalization consumed by `HasVariablePerronBoundaryCharge`.

## Theorem C `[PROVED]`: Hilbert flank energy supplies the mass

Let

`B_M(F) = (integral_R |F(-M+it)|^2 dt)^(1/2)`.

Then

`A_M(F) <= sqrt(pi) B_M(F)`.                                 (5)

### Proof

Apply Holder with exponents `(2,2)` to `|F(-M+it)|` and `(1+t^2)^(-1)`. The second factor has
`L2` norm at most `sqrt(pi)` because

`integral_R (1+t^2)^(-2) dt <= integral_R (1+t^2)^(-1) dt = pi`.

Thus geometric growth of the vertical `L2` norm gives geometric growth of the carrier flank mass
with exactly the same radius. The normalization loss is the fixed positive constant

`kappa = 2 sqrt(pi)/pi`.

## Theorem D `[PROVED]`: right convergence is automatic

Suppose `F` agrees with an absolutely convergent Dirichlet series on `Re(s)>=c>0`. Then

`t -> F(c+it) E_(n,delta)(c+it)`

is integrable for every admissible `n,delta`.

### Proof

Absolute Dirichlet convergence bounds `F` uniformly on the half-plane. The Perron numerator is
uniformly bounded on the fixed line, while `1/(s(s+1))` is integrable there. Therefore the whole
right-edge integrand is dominated by a constant multiple of the banked Perron kernel. Hence right
truncation convergence is not an independent hypothesis.

## Theorem E `[PROVED]`: carrier horizontal mass gives escape

For `-M<=x<=c` and `|T|>=1`, there is an explicit finite constant
`K(n,delta,M,c)` such that

`|E_(n,delta)(x+iT)| <= K(n,delta,M,c)/(1+T^2)`.              (6)

The constant is obtained by bounding each positive-base real power on the exponent interval
`[1-M,c+1]` by the sum of its two endpoint powers. The denominator satisfies

`|s(s+1)| >= T^2 >= (1+T^2)/2`.

If `Q_M(F)<infinity`, (6) implies that the sum of the top and bottom horizontal integral norms is
integrable on `(1,infinity)`. It is continuous, hence integrable on `(0,1]` as well. Unit-interval
averaging therefore selects `T_k->infinity` along which both horizontal integrals vanish. Combined
with Theorem D, this produces full boundary escape without a kernel-dependent hypothesis.

## Theorem F `[PROVED]`: coefficient-independent exact support

Let `F` be entire and agree with

`sum_(m>=1) a_m m^(-s)`

on an absolutely convergent half-plane `Re(s)>=c>0`. Assume:

1. `Q_M(F)<infinity` eventually;
2. `B_M(F)<=B(M)` eventually;
3. `0<=B(M)<=C R^M` eventually.

Then for every `n>=1`,

`a_n != 0  ==>  n <= R`.                                    (7)

### Proof

Theorem C turns the `L2` energy into carrier flank mass. Theorem E produces horizontal escape,
Theorem D supplies right convergence, and Theorem B produces normalized variable Perron boundary
charge. The previously proved exact-support theorem then gives (7).

The formal capstone is

`coefficient_index_le_exact_flank_radius_of_carrierL2StripMass`.

## Attack and scope

- `[FAILED]` A single critical-line `L2` class does not control the negative flank. For example,
  `exp((s-1/2)^2)` is square-integrable on `Re(s)=1/2`, while its `L2` norm on `Re(s)=-M` grows like
  `exp((M+1/2)^2)`. The missing datum is an exponential-moment or analytic-strip constraint, not
  abstract Hilbert membership.
- `[BRIDGE]` Holder, endpoint power bounds, and contour averaging are standard analysis.
- `[PROVED HERE]` The new content is their exact factorization through two coefficient-independent
  carrier masses and composition with variable Perron extraction and exact arithmetic support.
- `[PROVED]` No common quiet-height sequence, rectangle interior bound, coefficient-dependent strip
  mass, or separate right-edge convergence hypothesis remains.
- `[PROVED / OBSTRUCTED]` Exact common-source cross-line Mellin coherence produces the geometric
  negative-line `L2` energy, but combining it with finite horizontal mass forces finite Dirichlet
  support. For an infinite-support target, exact coherence is therefore not the missing producer.
- `[PROVED]` `perron-mellin-seam-residue.md` constructs an additive cross-line defect whose
  coefficient-indexed Perron residues recover the infinite arithmetic tail without imposing a
  finite geometric defect-norm radius.
- `[OPEN CORE]` Construct that seam for the target completed carrier and constrain its recovered
  coefficient coordinates by off-critical divisor or cocycle data.

## Novelty and significance gates

- **NOVEL:** the growth-bearing quantity is now a carrier invariant defined before choosing any
  coefficient or Perron kernel. The contour hypothesis has been factored into quantitative flank
  energy and qualitative horizontal mass, and both kernel-dependent Props have been discharged.
- **SIGNIFICANT:** this exposes the exact source theorem required for the RH-facing endgame: an
  exponential-moment/strip-mass estimate for the actual carrier. It replaces the former quietness
  hypothesis by Hilbert and weighted-area quantities compatible with Mellin source transport.

## Gates

- [x] 0 -> 1: carrier-only invariants and the critical-line `L2` counterexample isolated.
- [x] 1 -> 2: Theorems A--F proved on paper.
- [x] 2 -> 3: all interfaces and the exact-support capstone formalized in Lean.
- [ ] 3 -> 4: the viable defect-bearing seam and its arithmetic coordinates are proved; promotion
  requires a target construction and a divisor/cocycle constraint on those coordinates.
