# The shifted Thue--Morse Dirichlet series has exact order two

- **ID:** thue-morse-entire-dirichlet-order-two
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Date:** 2026-07-10
- **Status banner:** `[SEARCH]` The entire continuation is classical (Allouche--Cohen, 1985).
  `[PROVED HERE]` Its exact Hadamard order and type are computed below. No proof of RH is claimed.
- **Source:** attack on `../../1-in-progress/cocycle-shape-rigidity-gamma-extremality.md`,
  Wave 8, claims 30--31.
- **Statement:** If `epsilon_n=(-1)^{s_2(n)}` is the signed Thue--Morse sequence and
  `T(s)=sum_{n>=0} epsilon_n/(n+1)^s` on `Re(s)>1`, then `T` extends to an entire function of
  exact Hadamard order `2` and exact order-two type `(log 2)/2`. Its coefficients are bounded
  integers, 2-automatic, and not eventually periodic.

## Goal

The theorem falsifies both proposed Wave-8 growth gates:

1. an automatic bounded-integer sequence can have an entire Dirichlet series without being
   eventually periodic;
2. a bounded-integer Dirichlet series can be entire of order strictly larger than `1`.

The corrected residue is structural. Integrality, boundedness, and finite-state self-similarity do
not control the radial flatness of the ordinary generating function at `q=1`. Any order-one theorem
intended to isolate zeta must use a genuinely stronger source condition, such as multiplicativity,
Euler compatibility, or a constraint coupling the prime and archimedean sides.

## Literature boundary

`[SEARCH]` Allouche and Cohen, *Dirichlet Series and Curious Infinite Products*, Bull. London Math.
Soc. 17 (1985), 531--538, prove the analytic continuation of the Thue--Morse Dirichlet series and an
infinite functional equation. Later automatic-Dirichlet-series literature also records the entire
continuation. A targeted search of those sources and later papers located no determination of the
Hadamard order or type used here.

The novelty claim is therefore deliberately narrow: the continuation is imported; the exact growth
law

`log M_T(r) = ((log 2)/2) r^2 + o(r^2)`

is the result proved here.

## Brick 1 `[PROVED]`: the automatic product is infinitely flat at the radial seam

Let `s_2(n)` be the number of `1` digits in the binary expansion of `n`, and set

`epsilon_n = (-1)^{s_2(n)}`.

Unique binary expansion gives, first for finite products and then for `|q|<1`,

`prod_{k=0}^{m-1} (1-q^{2^k}) = sum_{n=0}^{2^m-1} epsilon_n q^n`,

`prod_{k>=0} (1-q^{2^k}) = sum_{n>=0} epsilon_n q^n`.

Put

`phi(x) = e^{-x} prod_{k>=0}(1-e^{-2^k x})`, for `x>0`.

Every factor lies in `(0,1)`. For every integer `m>=0`, the inequality `1-e^{-u}<=u` gives

`0 < phi(x)
   <= prod_{k=0}^{m-1}(2^k x)
   = 2^{m(m-1)/2} x^m`.                                      (1)

Thus `phi(x)=O_m(x^m)` as `x->0+` for every `m`. At the other end,

`0 < phi(x) <= e^{-x}`.                                      (2)

This is the mechanism missed by the automatic-substitution heuristic: the nested substitutions do
not force a pole lattice here. Their finite Prouhet cancellations accumulate to a zero of infinite
radial order.

**House status:** the source kernel is positive, exponentially decaying at infinity, and flatter
than every power at zero.

## Brick 2 `[SEARCH, reproved]`: Mellin continuation is entire

Define

`H(s) = integral_0^infinity phi(x) x^{s-1} dx`.

For a compact set `K subset C`, choose an integer `m > -min_{s in K} Re(s)`. Estimate (1) controls
the integral uniformly near zero, and (2) controls it uniformly near infinity. The same bounds with
arbitrary powers of `|log x|` justify differentiation under the integral. Hence `H` is entire.

For `Re(s)>1`, absolute convergence permits termwise integration:

`phi(x) = sum_{n>=0} epsilon_n e^{-(n+1)x}`,

so

`H(s)
 = sum_{n>=0} epsilon_n integral_0^infinity e^{-(n+1)x}x^{s-1} dx
 = Gamma(s) sum_{n>=0} epsilon_n/(n+1)^s
 = Gamma(s) T(s)`.

Since `1/Gamma` is entire,

`T(s) = H(s)/Gamma(s)`

is the entire continuation.

**House status:** entirety is classical and is included to fix the exact continuation used by the
growth proof.

## Brick 3 `[PROVED HERE]`: the upper order-two bound has sharp quadratic coefficient

Let `r>=2`, `|s|<=r`, and choose the integer `m=ceil(r)+1`. On `(0,1)`, (1) gives

`|integral_0^1 phi(x)x^{s-1}dx|
 <= 2^{m(m-1)/2} integral_0^1 x^{m-r-1}dx
 <= 2^{m(m-1)/2}`.

On `(1,infinity)`, (2) gives a Gamma-tail bound `exp(O(r log r))`. Therefore

`log max_{|s|<=r}|H(s)| <= ((log 2)/2)r^2 + O(r log r)`.       (3)

The reciprocal Gamma function is entire of order one; its Weierstrass product, or Stirling on
sectors plus the reflection formula near the negative axis, gives

`log max_{|s|<=r}|1/Gamma(s)| = O(r log r)`.                   (4)

Combining (3) and (4),

`log M_T(r) <= ((log 2)/2)r^2 + O(r log r)`.                  (5)

Consequently `T` has order at most `2`, and if its order is `2`, its type is at most `(log 2)/2`.

**House status:** the coefficient `(log 2)/2` comes directly from the accumulated binary scales
`sum_{k<m} k log 2`.

## Brick 4 `[PROVED HERE]`: the product has the matching lower flatness exponent

Let `L=log 2` and `y=log(1/x)`. For `0<x<=1`, put `J=floor(y/L)`. Then

`2^J x <= 1 < 2^{J+1}x`.

For `0<=u<=1`, `1-e^{-u}>=u/2`. Hence the factors with `k<=J` satisfy

`prod_{k=0}^J(1-e^{-2^k x})
 >= prod_{k=0}^J(2^k x/2)`.

For the remaining factors,

`2^{J+1+j}x > 2^j`,

and therefore

`prod_{k>=J+1}(1-e^{-2^k x})
 >= prod_{j>=0}(1-e^{-2^j}) =: c_0 > 0`.

The last product is positive because `sum_j e^{-2^j}<infinity`. Taking logarithms and using
`J=y/L+O(1)` yields constants `A,B>0` such that

`phi(e^{-y}) >= A exp(-y^2/(2L)-B y)` for all `y>=0`.          (6)

Together with (1), optimized by taking `m` nearest to `y/L`, this also identifies the radial
flatness scale

`log phi(e^{-y}) = -y^2/(2 log 2) + O(y)`.                    (7)

**House status:** the upper and lower product estimates match at quadratic scale; no asymptotic
formula or numerical input is used.

## Brick 5 `[PROVED HERE]`: exact order and exact type

For real `r>0`, positivity and the substitution `x=e^{-y}` give

`H(-r) >= integral_0^infinity phi(e^{-y}) e^{r y} dy`.

Using (6) on a unit interval around the maximum of

`(r-B)y-y^2/(2L)`,

whose maximizing point is `y=L(r-B)`, gives

`log H(-r) >= (L/2)r^2 - O(r)`.                              (8)

Take `r=n+1/2`. The half-integer Gamma formula

`Gamma(1/2-m)=(-4)^m m! sqrt(pi)/(2m)!`

shows

`log |1/Gamma(-r)| = O(r log r)`

(in fact it is positive of that size). From `T(-r)=H(-r)/Gamma(-r)`, (8) gives

`log |T(-n-1/2)| >= ((log 2)/2)r^2 - O(r log r)`.             (9)

The lower bound (9) and upper bound (5) prove

`limsup_{r->infinity} log M_T(r)/r^2 = (log 2)/2`.

Thus `T` has exact Hadamard order `2` and exact order-two type `(log 2)/2`.

The use of half-integers is essential only to avoid the zeros of `1/Gamma` at the nonpositive
integers. Indeed the continuation has `T(0)=T(-1)=T(-2)=...=0`; these zeros do not reduce its maximum
modulus growth between the integers.

**House status:** the exact growth law is closed.

## Brick 6 `[PROVED]`: the coefficient sequence is not eventually periodic

The coefficients lie in `{+1,-1}` and are 2-automatic by

`epsilon_{2n}=epsilon_n`, `epsilon_{2n+1}=-epsilon_n`.

Suppose they had eventual period `p>=1`, starting after `N`. For every sufficiently large `k`,
`2^k-p>=N`, so periodicity would give

`epsilon_{2^k-p}=epsilon_{2^k}=-1`.

But the `k` binary digits of `2^k-p=(2^k-1)-(p-1)` are the bitwise complement of the padded binary
digits of `p-1`. Therefore

`epsilon_{2^k-p}=(-1)^{k-s_2(p-1)}`,

which alternates with `k`. Contradiction.

**House status:** the counterexample is bounded, integer, automatic, and genuinely nonperiodic.

## Attack and scope

- `[SEARCH]` Entire continuation alone is not new; presenting it as discovery would fail the novelty
  gate.
- `[PROVED HERE]` The exact order and type do not follow from the published continuation statement or
  from the existence of an automatic functional equation. They come from the two-sided radial
  flatness law (7).
- `[PROVED]` The initial factor `e^{-x}` corresponds to the shift `(n+1)^{-s}` and is necessary for
  decay at infinity. It does not alter boundedness, integrality, automaticity, or nonperiodicity.
- `[PROVED]` The counterexample is not multiplicative. It therefore kills the integrality and
  automaticity gates but leaves a multiplicative/Euler growth theorem available.
- `[PROVED]` This theorem is a source-class obstruction, not a zero-localization theorem. It prevents
  a false route to RH; it supplies no RH-equivalent positivity statement.
- `[OPEN CORE]` Find the weakest multiplicative constraint which rules out infinite radial Prouhet
  flatness. A viable order-one theorem must prove that constraint from the Euler side rather than add
  finite order as an assumption.

## Novelty and significance gates

- **NOVEL:** the exact order-two type `(log 2)/2` was not present in the project corpus and was not
  located in the targeted primary-source/literature audit. The classical entire continuation is
  explicitly excluded from the novelty claim.
- **SIGNIFICANT:** the result falsifies the active `INT-ORDER <= 1` and
  `AUTOMATIC-COBHAM-RIGIDITY` conjectures with one exact object, and identifies the missing invariant:
  control of infinite radial cancellation, not coefficient quantization or finite-state structure.

## Lean target

The formalization should proceed through reusable constraint interfaces rather than a theorem naming
the final Mellin integral only:

1. `thueMorsePolynomial`: the finite identity
   `prod_{k<m}(1-X^(2^k)) = sum_{n<2^m} epsilon_n X^n`;
2. `thueMorseKernel_flat_bound`: inequality (1), uniformly for every requested order `m`;
3. `mellin_differentiableAt_of_superpolynomial_zero`: discharge the existing Mellin big-O strip
   interface at an arbitrary `s` from all-order flatness at zero and exponential decay at infinity;
4. `thueMorseMellin_entire`: the entire continuation;
5. the two-sided estimate (7), then the exact order/type theorem once the project exposes a reusable
   Hadamard-type interface.

## Gates

- [x] 0 -> 1: exact counterexample and growth invariant isolated; degenerate and literature cases
  attacked.
- [x] 1 -> 2: complete proof of exact order and type, with no computational dependency.
- [ ] 2 -> 3: finite-product, flatness, Mellin, and growth layers remain to be formalized.
- [ ] 3 -> 4: requires a standalone paper and an independent priority audit of the exact type.

## Next generative move

Define the **radial cancellation depth** of a bounded integer sequence by the best quadratic constant
in `-log|sum a_n e^{-nx}|` as a function of `log(1/x)`. The theorem computes that depth exactly for
the binary substitution carrier. The next constraint theorem should prove that a nonzero
multiplicative sequence cannot have positive infinite-depth radial cancellation without acquiring a
natural boundary or a finite abscissa singularity.

## Formalization update

- 2026-07-10 — the all-order upper-flatness and Mellin-interface layers are formalized in
  `../../3-formalized/new/thue-morse-mellin-flatness.md` and
  `formal/GaloisForLFunctions/RHTower/ThueMorseMellinFlatness.lean`. The exact finite coefficient
  `2^(m(m-1)/2)`, natural-to-real exponent discharge, whole-plane Mellin convergence, and analytic
  capstone are axiom-clean. The stage-2 card remains here because the infinite product construction,
  matching lower bound, and exact order/type theorem are not yet in Lean.
