# Route L: weighted admission and original boundary of the damped limit

- **ID:** L-C44
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** concrete source comparison / paper mechanism, Lean pending
- **Depends on:** [C43 actual half-density limit](../3-formalized/route-l-damped-half-density-source-limit.md)
- **RH status:** unproved

Chain: complete original Green/BV source → agreement with the fixed physical
reader → conormal vanishing → RH. C43 attacks actual source formation in a
weaker topology. This card attacks the outstanding weighted and boundary
admission of that same limit. No C44 Lean module exists yet.

## Exact next source calculation

Let `H_c g(t)=exp(c*t)g(t)`. C43's general-weight flow identity gives the
literal paired factor

`H_c E_(p,a) H_c^-1 = (Id-u_p U_(-log p))(Id-v_p U_(log p))`,
`u_p=p^(-(a+c))`, `v_p=p^(-(a+1-c))`.

The shifts here use `U_d f(t)=f(t-d)`; the repository's additive translation
parameter has the opposite sign. At c=1/2 these factors are adjoints. At
other c they need not be adjoints, but the same source has two exact weights.

If `1-a<c<a`, both exponent series are summable. For 0<=u,v<=1, the triangle
inequality and translation isometry give

`||E f|| <= exp(u+v)||f||`,
`||E f-f|| <= (u+v+uv)||f|| <= 2*(u+v)||f||`.

The same prime-prefix successive-difference proof as C43 therefore supplies
weighted L1 and L2 limits. This is a paper proof mechanism awaiting Lean
implementation; do not transfer L2 convergence through an unbounded weight.

## Same-source and Mellin obligations

1. Construct those weighted limits using the ACTUAL original finite sources.
   Identify their representatives on every bounded interval: the change of
   exponential weight is bounded there, and the original finite functions
   agree exactly. Use exhaustion to obtain one locally integrable function.
2. At a=1, every c in (0,1) is available. Weighted L1 convergence makes the
   literal Mellin integrals continuous at Re(s)=c. For every finite jet,
   bound its polynomial factor by two nearby admitted exponential weights.
3. Identify the finite Euler product limit, retaining the original Gaussian:
   `M(g_a)(s)=M(g0)(s)/(zeta(a+s)*zeta(a+1-s))` in `1-a<Re(s)<a`.
   Both zeta arguments have real part greater than one there. Prove this
   using the actual prime products and corpus Euler convergence theorem,
   rather than defining the source by this formula.
4. At a=1, every actual Xi point is interior to the admitted Mellin strip.
   The denominator is nonzero and finite, so the source retains its nonzero
   Xi value. Prove normalization and transport of the full divisor packet,
   native Tate depth, unchanged Gamma residue normalizer and first nonzero
   Xi coefficient. Pointwise Mellin identity is not the full packet bound.

## Original boundary attack

For a>1 (for example the fixed value 2), the weighted admission interval
contains c=0 and c=1. This gives a concrete starting region for original
unweighted and reflected integrals. Prove corresponding derivative control
and original prime-circle summability before applying the complete Green/BV
boundary. The finite operators commute with source differentiation, but the
actual derivative limits and periodization must be justified.

At a=1, the endpoint weights c=0 and c=1 are outside the absolute estimate.
Failure of that estimate does not prove divergence of the complete signed
source. An endpoint cancellation argument must retain the full arithmetic
sum and boundary terms. Do not assume the endpoint estimate or replace it
by a meromorphic multiplier identity.

The main target is the FULL difference between the admitted original
boundary and the fixed physical reader. A nonzero source, finite-factor
positivity, or a holomorphic Mellin formula does not make that difference
zero. No fixed-reader agreement, source incidence, stationarity, radial
balance, isometry or common-normalization premise is allowed as its producer.

## Full fixed-reader transport in the initial region

For fixed a>1 and 0<=Re(s)<=1, each of the two prime amplitudes is bounded
by p^(-a). Thus `|A_p(s)|<=(1+p^(-a))^2` and
`|A_p(s)-1|<=3*p^(-a)`. The exact finite products are uniformly bounded and
Cauchy on the entire closed strip. At every interior point the limiting
product is nonzero by the absolutely convergent log-product.

This supplies a concrete proposed bound for the complete Xi packet, stronger
than retaining the finite `4^length(P)` estimate. After the SAME-source
weighted Mellin identity is established, use this bound to extend C39's
full Green/provenance/native-Tate/fixed-Sonin transport. Its expected fixed
image is the nonzero limiting multiplier times the original image; the
initial damped limit therefore should preserve, rather than annihilate,
the physical discrepancy. Prove that equality for the actual limit before
using it in the boundary comparison. No infinite-transport Lean theorem is
claimed yet.

## Damping continuation

The half-density multiplier suggested by the admitted Euler formula is
`1/|zeta(a+1/2+i*tau)|^2`, with the repository's 2*pi Fourier scale retained.
Every zero encountered on this parameter/frequency surface requires an
actual local source prescription. Its multiplicity and nonzero leading
coefficient must remain in that prescription. A bound excluding such a
pole cannot be assumed to justify continuation. The initial a>1/2 source
proof does not provide continuation to zero damping or conormal vanishing.

## Search coverage

`/tmp/route_l_c43_weighted_pole_deep.json`: all 20 candidate lemmas and
20 source arguments inspected, with empty generated idea/ingredient lists.
Generation 875519; semantic 2354275/2354825; partial due to deadline,
filter/judge and source refresh. Most hits addressed unrelated leading
coefficients or pole notation. No source-domain premise was adopted.
The query was rephrased around Cauchy convergence under exponential weights
and continuity of actual Mellin integrals; its report is
`/tmp/route_l_c44_weighted_mellin_deep.json`. All 20 candidates and
20 source arguments were inspected, with empty generated idea/ingredient
lists. Generation 875564; semantic 2354579/2354944; partial due to deadline,
filter/judge and source refresh. The concrete-function lemma
`MeasureTheory.Lp.cauchy_complete_eLpNorm` in mathlib's `LpSpace/Complete.lean`
(361–378) is a candidate for compatible representatives. Its explicit
MemLp and finite-tail majorant obligations must be discharged for the actual
weighted sources; it is not yet used in a C44 proof.
