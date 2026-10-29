# Quantitative gap stability and precision of the dyadic probe

- **ID:** ACP-GAP-STABILITY-PROBE-PRECISION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Statement:** Total added conductor mass controls squared loss of the greatest finite-prime gap; arbitrarily remote prime flips evade every fixed positive tolerance in the dyadic selector.

## Exact bounds

Put g0=2 log 2 and c_F=prod_(p in F)(p-1)/(p+1).
For finite prime sets F subset G, let Delta=c_G^(-2)-c_F^(-2). Then:

`0<=Phi_G(s)-Phi_F(s)<=Delta/(g0-s)` for 0<s<g0;

`(delta_F-delta_G)(g0-delta_G)<=delta_G delta_F Delta`,

hence `(delta_F-delta_G)^2<=g0^2 Delta`.

The product inequality is the stronger primary statement. For the fixed
submaximal dyadic calibration it also gives the sharper linear estimate

`delta_{2}-delta_{2,p} <=
 16 g0^2/(p c_{2}^2 (g0-delta_{2}))`.

Indeed, delta_{2,p}<=delta_{2}<g0, so the nonnegative loss times
(g0-delta_{2}) is at most its product with (g0-delta_{2,p}). The primary
bound and the prime mass increment bound then give the estimate after
division by the strictly positive calibration margin. This improves the
uniform square-root modulus to order 1/p at the fixed interior calibration.
It is a direct algebraic consequence, with no new analytic premise.

For every prime p, including p already in F, this gives

`(delta_F-delta_(insert p F))^2<=16 g0^2/(p c_F^2)`.

For every B and epsilon>0, there is a prime p>B, p>=11, with
maximal singleton gap but

`delta_{2}-epsilon<delta_{2,p}<delta_{2}`.

Thus an exact second gap reading selects the finite-prime source, while no
fixed positive tolerance does. This is a precision boundary inside the finite
sign-gauge family, not a claim about complete Weil positivity.

## Dependency-complete proof

Unit squared coefficient mass gives sum_m w_F(m)=c_F^(-2). The difference
w_G-w_F is nonnegative, has total mass Delta, and vanishes at conductors
zero and one. All positive reciprocal denominators at s are at least g0-s,
giving the first inequality with the entire mass included.

If delta_G<g0, its secular reading is zero. For delta_G<t<delta_F,
nonpositivity at t and monotonicity of the positive tail give

`1/delta_G-1/t <= -Phi_F(delta_G) <= Delta/(g0-delta_G)`.

Take t up to delta_F; positivity of both gaps justifies reciprocal continuity.
After multiplication,

`(delta_F-delta_G)(g0-delta_G)<=Delta delta_G delta_F`.

The left side bounds the squared gap loss below, and the right side is at
most Delta g0^2. If delta_G=g0 both gaps equal g0, so the result is trivial.

More explicitly, first separate the equality case delta_G=delta_F; its
left side is zero and Delta is nonnegative by the nonnegative weight
difference. Otherwise delta_G<delta_F<=g0, so delta_G is an interior root.
The interval (delta_G,delta_F) is a left neighborhood of delta_F.
The continuous function 1/delta_G-1/t has the stated finite limit there.
Passing its upper bound to that limit uses closedness of a real half-line.
The denominators delta_G delta_F and g0-delta_G are positive. Multiplying
them yields exactly the displayed product inequality, without an endpoint
value of Phi_F at g0. Finally,
`(delta_F-delta_G)^2 <= (delta_F-delta_G)(g0-delta_G)`
and `delta_G delta_F<=g0^2`, with Delta>=0. This handles the plateau
without asserting continuity of the secular series at its excitation.

For a new prime p, the product density gives
`Delta=4p/((p-1)^2 c_F^2)<=16/(p c_F^2)` since p>=2. An already present prime
changes nothing. Unbounded primes make the resulting squared loss smaller
than epsilon^2. At F={2}, strict inclusion makes the loss strictly positive;
the existing p>=11 theorem gives the singleton maximum simultaneously.

For the numerical constant, p>=2 implies
`4p/(p-1)^2<=16/p`; clearing positive denominators reduces this to
`(p-2)(3p-2)>=0`. Put C=16 g0^2/c_{2}^2. Choose an integer k>C/epsilon^2,
then a prime p>=max(11,B+1,k). The squared loss is less than epsilon^2,
so the positive loss is less than epsilon. Proper inclusion of {2} in
{2,p} makes it strictly positive.

## Audit and gates

The needed mass, strict inclusion, root and singleton theorems are already
formalized. Corpus searches found their definitions and exact statements.
No experiment, unproved analytic estimate or common horizon is involved.
The proof uses exact mass rather than assuming uniform convergence of all
finite spectral coordinates. The only dyadic input is delta_{2}<g0, already
proved by the small-prime obstruction; the selector leaf packages it.
No exhaustive literature novelty claim is made.

- [x] Well-posed arithmetic candidate with explicit constants and quantifiers.
- [x] Dependency-complete paper audit, including endpoint reciprocal limit.
- [x] Lean formalization and transitive axiom audit.

## Formalization

`ConductorMassBoundsGapLossAndProbePrecision.lean` proves:

- `hasSum_finiteFlipSpectralWeight`
- `finiteFlipSecular_increment_le`
- `finiteFlipGreatestGap_loss_mul_ceiling_le`
- `finiteFlipGreatestGap_loss_sq_le`
- `finiteFlipGreatestGap_insert_loss_sq_le`
- `dyadicGreatestGap_prime_response_loss_le`
- `exists_maximal_flip_with_almost_unchanged_dyadic_gap`

Scratch 84190 and canonical installed-source check 36557 exited zero without
diagnostics. All seven transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The adjacent audit preserves commands,
source hash and actual output. The umbrella imports this leaf. No olean was
built because no subsequent draft yet imports it.

External background checked against the primary abstracts: generalized
Liouville signs are studied in [Borwein–Choi–Coons](https://arxiv.org/abs/0809.1691),
and multiplicative Ramanujan expansions and finite Euler factorizations in
[Coppola–Ghidelli](https://arxiv.org/abs/2009.14121). Those constructions are
background, not a claimed novelty here. The scoped contribution concerns
actual constrained prime-matrix gaps and their response to prime toggles.
