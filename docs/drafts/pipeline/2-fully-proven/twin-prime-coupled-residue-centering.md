# Keep the coupled residue inside the rough-shift average

- **ID:** twin-prime-coupled-residue-centering
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper deduction) / BRIDGE
- **Source:** [fixed-determinant audit](../1-in-progress/twin-prime-fixed-determinant-uniformity.md).
- **Statement:** Liouville and Möbius rough-shift centering is uniform in a common progression modulus, even after choosing a different residue and a unit-bounded complex coefficient at every shift and an arbitrary unit-bounded second row.

## Exact statement

Let `f` be either Liouville `lambda` or Möbius `mu`, and let
`g` be any complex sequence with `|g(n)|<=1`. Fix an integer `h>=1`.
Let `A>=1000`, let `L` be sufficiently large, and suppose

`Y>=exp(L^A/2)`,
`exp(L^0.995)/2<=D<=exp(2L)`, with `Y,D` positive integers.

Let `Z` be any subset of the integers in `[D,2D)` having no
prime factor at most `exp(L^0.99)`. For every positive integer
`l`, every residue assignment `r:Z -> Z/lZ`, and every complex
weight `c(z)` with `|c(z)|<=1`,

`|(1/Y) sum_(1<=v<=Y) sum_(z in Z)
    c(z)/z * 1_(v == r(z) mod l) * f(v)g(v+h z)|
 <= C_h L^(-21/20)`.

The constant and the lower threshold for `L` are independent of
`l`, `r`, `c`, `g`, `Z`, `D`, and `Y`. In particular, this holds for
`r(z)=b z` with no loss from summing `l` separate estimates.

Equivalently, by choosing a maximizing residue and a phase at
each shift, the stronger-looking positive statement also holds:

`sum_(z in Z) (1/z) max_(r mod l)
 |(1/Y) sum_(1<=v<=Y, v == r mod l) f(v)g(v+h z)|
 <= C_h L^(-21/20)`.

This is an average over rough shifts. It does not estimate an
individual fixed shift or give a bound normalized by `Y/l`.

## Checked analytic input and parent argument

[Matomaki--Radziwill--Tao, corrected v3](https://arxiv.org/pdf/1503.05121v3),
Theorem 1.3, page 3, bounds the starting-point average of each
fixed-frequency short Liouville exponential sum. Its frequency
supremum lies outside the starting-point integral. That exact
order is sufficient here; no stronger supremum is used.

The rough-set second and fourth moment counts follow the finite
sieve proof in Lemma 4.2, pages 13--14, of the
[ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf).
The following proof checks that these bounds tolerate arbitrary
complex shift weights, then retains the coupled congruence.

## Complete deduction

Write `e(t)=exp(2 pi i t)`.

### The Möbius short-interval input

No qualitative Möbius theorem is converted into a quantitative
one. Instead use the exact square-divisor identity

`mu(n)=sum_(d^2|n) mu(d)lambda(n/d^2)` for positive integers `n`.

Both sides are multiplicative. At a prime power of exponent zero
or one they agree immediately; at exponent at least two the two
possible nonzero terms cancel. This proves the identity.

For real `100<=H<=Y`, set `K=floor(H^(1/4))`. In the short sum
`sum_(x<n<=x+H) mu(n)e(alpha n)`, first retain `d<=K`. After the
change of variables `u=x/d^2`, the starting-point integral of
each retained term is bounded by MRT Theorem 1.3 by

`C HY/d^2 * (log log H/log H + (log Y)^(-1/700))`.

Here `H/d^2>=sqrt(H)>=10`, `Y/d^2>=H/d^2`,
`log(H/d^2)>=log(H)/2`, and `log(Y/d^2)>=log(Y)/2`.
The frequency is `alpha*d^2`, still in the theorem's uniform
range. Summing `1/d^2` costs an absolute constant.

For the omitted square divisors, integrate the absolute
majorant. Every integer `n<=Y+H` belongs to windows of total
starting-point length at most `H`. Thus the tail is at most

`H sum_(K<d<=sqrt(Y+H)) floor((Y+H)/d^2)
 <=H(Y+H) sum_(d>K) 1/d^2
 <=C HY H^(-1/4)`.

This proves, uniformly in `alpha`, the Möbius short-sum bound

`integral_0^Y |sum_(x<n<=x+H) mu(n)e(alpha n)| dx
 <=C HY (log log H/log H + (log Y)^(-1/700) + H^(-1/4))`. (0)

Window endpoint conventions differ only on a set of measure
zero. The last term is harmless on the scales below. Hence
both allowed first rows have the required short-interval bound.

### The weighted rough shifts

First prove the stronger twisted
estimate, uniformly in real `alpha` and all `|w(z)|<=1`:

`|(1/Y) sum_(v<=Y,z in Z)
 w(z)/z * f(v)g(v+h z)e(alpha v)|
 <= C_h L^(-21/20)`.                                      (1)

Put `B(theta)=sum_(z in Z) w(z)e(h z theta)/z`.
The rough integer count gives

`||B||_infinity <= C L^(-0.99)`.

On expanding the fourth moment, orthogonality imposes
`z1+z2=z3+z4`; the integer factor `h` cancels from that equality.
Taking absolute values of its coefficients only increases the
bound. The rough additive-quadruple count consequently gives

`integral_0^1 |B(theta)|^4 dtheta <= C D^(-1)L^(-3.96)`.    (2)

For completeness, the counts used here concern the one-variable
form `x` and the four forms `x1,x2,x3,x1+x2-x3` on their integer
boxes. Their bad residue densities are `m/p+O(p^(-2))`, for
`m=1,4`, and are strictly below one for every prime. Even-order
inclusion--exclusion truncated at `2 ceil(500 log L)` bounds the
good density by `O((log(exp(L^0.99)))^(-m))`. The truncation tail
is a negative power of `L` of exponent larger than ten, using
the factorial denominator and the elementary reciprocal-prime
upper bound. The total CRT endpoint error is at most
`D^(-1) exp(O(L^0.99 log L))`, hence smaller than every fixed
negative power of `L`. Thus the one-variable count is
`O(D L^(-0.99))`, and the additive-quadruple count is
`O(D^3 L^(-3.96))`. Each fourth-moment weight is at most `D^-4`.
The fourth linear form is positive on `[D,2D)^3`; requiring its
value to lie in `[D,2D)` can be dropped for this upper bound.
These counts do not depend on the phases of `w`.

Average the left side of (1), before its absolute value, over
translations by `j=1,...,D`. Moving a prefix by `j` changes at
most `2j` terms, so the total normalized boundary error is
`O(D/Y)`, uniformly in `alpha` and `w`.

For each starting point `v`, define

`F_v(theta)=sum_(1<=j<=D)
 f(v+j)e(alpha(v+j))e(theta j)`,

`G_v(theta)=sum_(1<=a<=(2h+1)D) g(v+a)e(-theta a)`.

Fourier orthogonality represents the translated average exactly as

`(1/(YD)) sum_(1<=v<=Y) integral_0^1 B(theta)F_v(theta)G_v(theta) dtheta`.

Indeed the surviving index is `a=j+h z`, which lies within the
displayed range of `G_v`. All sums are finite.

MRT Theorem 1.3 or (0), at frequency `alpha+theta`, gives

`sum_(v<=Y) |F_v(theta)| <= C YD L^(-0.8)`                 (3)

uniformly in `alpha,theta`. To pass from real to integer starting
points, integrate on `(v,v+1)` and apply the theorem with
`H=D` and long endpoint `Y+1`. On that interval the integers in
the short window are exactly `v+1,...,v+D`. The hypotheses give
`log log D/log D + (log(Y+1))^(-1/700) + D^(-1/4)=O(L^(-0.8))`.

On `|B|<=L^(-1.05)`, Parseval and Cauchy--Schwarz give
`integral |F_v G_v| <= sqrt(2h+1)D`. The normalized contribution
is `O_h(L^(-1.05))`.

On the complement, (2) bounds its measure by
`O(D^-1 L^0.24)`. Use `|B|<=C L^-0.99`,
`|G_v|<=(2h+1)D`, and (3). The contribution is

`O_h(L^(0.24-0.99-0.8))=O_h(L^-1.55)`.

Finally `D/Y` is smaller than `L^-1.05`. This proves (1).

Expand the coupled congruence exactly:

`1_(v == r(z) mod l)
 =(1/l) sum_(a=0,...,l-1) e(a v/l)e(-a r(z)/l)`.

For each `a`, apply (1) with `alpha=a/l` and
`w(z)=c(z)e(-a r(z)/l)`. All weights remain unit bounded.
There are `l` estimates, each multiplied by `1/l`, so no factor
depending on `l` remains. Choosing the maximizing residue and
the phase conjugate to each resulting finite sum proves the
positive formulation. No limiting exchange is needed. QED.

## Scope, audit, and next obligation

Verdict **BRIDGE**: this is a deduction from the known short
exponential-sum method, not a claimed new cancellation mechanism.
It improves the bookkeeping in the inspected centering argument.
The key fact is that arbitrary phases in the rough polynomial
do not worsen its fourth-moment majorant.

The fixed-determinant problem still requires cancellation on
the affine sample scale. This theorem is normalized by `Y`,
not by the number of points in one progression. Multiplying its
error by a growing `l` loses the saving. Its Möbius version is
proved above, but only for the rough-shift average. No quantitative
fixed-affine Möbius estimate follows from that average.

No Lean theorem with either analytic estimate as an unproved
premise is introduced. A certificate for this full statement
requires unconditional formalization of its short exponential-sum
input and the finite sieve/Fourier argument; that is outstanding.

The corpus search returned `averagedMeanSquare_moebius` in
`Sieve/MoebiusMeanSquare.lean`. Its actual definition, checked in
`PairFibreMeanSquare.lean`, averages reciprocal fibres. It does
not supply the integer-start, fixed additive-frequency input (3).
`MoebiusMeanSquareUnconditional.lean` gives an explicit window
majorant, but its underlying `moebiusTwist` is `n^(-i tau)`, and
its displayed bound has not been shown to give (3) at these scales.

The next [uniform Ramaré-cofactor deduction](twin-prime-ramare-weighted-cofactor-cancellation.md)
now has a complete paper proof from the checked corpus prefix
theorem. It controls the actual reciprocal factor-count weight
for growing designated prime sets. This is a Mellin-frequency
input; assembling the additive-window estimate remains separate.

- [x] Exact quantifiers and a complete paper deduction.
- [x] Frequency supremum, complex phases, and endpoint errors checked.
- [x] Möbius transfer with the full square-divisor truncation error.
- [x] Primary short-exponential-sum statement checked directly.
- [ ] Unconditional Lean certificate of this analytic theorem.
- [ ] Relative progression saving for the fixed-determinant target.

## Log

- 2026-10-23 — Derived the coupled-residue bound during the
  coefficient audit. Strengthened it to arbitrary residue choices
  and complex shift weights, then to Möbius against an arbitrary
  unit-bounded second row. Neither prime-pair positivity nor
  twin-prime infinitude follows.
