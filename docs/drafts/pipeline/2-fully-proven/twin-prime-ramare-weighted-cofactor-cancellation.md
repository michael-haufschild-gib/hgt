# Pay the reciprocal factor-count weight before changing windows

- **ID:** twin-prime-ramare-weighted-cofactor-cancellation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper deduction) / BRIDGE
- **Source:** [coupled-residue centering](twin-prime-coupled-residue-centering.md) and the existing [Möbius mean-square gap](../3-formalized/new_scientific_knowledge/matomaki-radziwill-moebius-short-interval-mean-square.md).
- **Statement:** Transfer the corpus's proved twisted Möbius prefix saving to the actual reciprocal-Ramaré cofactor weight, uniformly for designated primes below a stretched-logarithmic cutoff.

## Exact target

For a finite set of primes `P`, let `omega_P(n)` count the
distinct designated primes dividing `n`. Fix `0<beta<1` and
`0<kappa<1`. Set `y_X=exp((log X)^beta)`.

There are `c,C>0` such that, for all sufficiently large
`X`, every `P` contained in the primes at most `y_X`, and every
`|tau|<=X^kappa`,

`|sum_(1<=n<=X) mu(n)n^(-i tau)/(omega_P(n)+1)|
 <= C X exp(-c (log X)^(min(1/20,1-beta)))`.

The constants are independent of `P` and `tau`. The stronger
intermediate statement replaces `1/(omega_P(n)+1)` by
`u^(omega_P(n))`, uniformly for every `0<=u<=1`.

This is a paper deduction from established one-variable
cancellation, not a claimed new two-point theorem. No analytic
input is to be assumed in Lean. Even success would not supply
the fixed-shift prime-pair lower bound.

## The coefficient and the exact two-scale bound

Define the nonnegative multiplicative coefficient

`a_(P,u)(p^j)=1-u` for `p in P`, `j>=1`,
`a_(P,u)(p^j)=0` for `p notin P`, `j>=1`, and `a_(P,u)(1)=1`.

Prime-power inspection gives

`mu(n)u^(omega_P(n)) = (mu * a_(P,u))(n)`.

The coefficient is at most one and supported on `P`-smooth
integers. Write

`M(T,tau)=sum_(1<=n<=T) mu(n)n^(-i tau)`.

The corpus theorem
`RHTower.Sieve.exists_norm_sum_moebiusTwist_le_rate` gives absolute
`K,T0>0` such that

`|M(T,tau)|<=K T exp(-(log T)^(1/20))`

for every real `T>=T0` and every `|tau|<=T`. Its Lean statement
and proof in `Sieve/RouteTMoebiusTwistRate.lean` were inspected;
the zero coefficient at `n=0` agrees with this positive-integer
normalization. This is a proved input, not a hypothesized rate.

For every `y>=exp(2)`, every designated prime set below `y`,
every `u in [0,1]`, and sufficiently large `X` with
`|tau|<=X^kappa`, the proof below gives

`|sum_(n<=X) mu(n)u^(omega_P(n))n^(-i tau)|
 <= X(1+log y)^45 *
    [K exp(-(kappa log X)^(1/20))
     + exp(-(1-kappa)log X/log y)]`.                         (1)

The large-horizon threshold is independent of `P,u,y,tau`.
It only requires `X^kappa>=T0` and `X>1`.

## Complete proof

### Uniform finite-prime moment

Set `a=1/log y`, so `0<a<=1/2`. For each prime `p<=y`, put
`q=p^(-1+a)` and `r=p^(-1-a)`. Then

`0<q<=1/sqrt(2)<3/4`, and `q/r=p^(2a)<=exp(2)<9`.

For `0<=x<=3/4`, the inequality `exp(4x)>=1+4x` gives
`(1-x)exp(4x)>=1+3x-4x^2>=1`. Consequently

`(1-q)^(-1)<=exp(4q)<=exp(36r)<=(1-r)^(-36)`.

The last inequality follows from `exp(r)<=(1-r)^(-1)`, or
`exp(-r)>=1-r`. Multiplication over the designated primes gives

`prod_(p in P) (1-p^(-1+a))^(-1)
 <=[prod_(p in P) (1-p^(-1-a))^(-1)]^36
 <=[sum_(n>=1) n^(-1-a)]^36
 <=(1+1/a)^36 <=(1+log y)^45`.                            (2)

The middle comparison is the nonnegative finite Euler expansion
and unique factorization. The final series bound follows from
the decreasing-function integral `integral_1^infinity t^(-1-a)dt=1/a`.
Thus no Mertens estimate or prime number theorem is needed for
this moment bound. Geometric convergence at each of the finitely
many primes justifies the Euler expansion even at exponent `1-a`.

Since `a_(P,u)` is at most the smooth indicator, (2) proves

`sum_d a_(P,u)(d)d^(-1+a) <=(1+log y)^45`.                 (3)

The same bound holds at exponent `1`, because `d>=1`.

### Preserve the signed prefix before paying the tail

The finite convolution identity gives exactly

`sum_(n<=X) mu(n)u^(omega_P(n))n^(-i tau)
 =sum_(d<=X) a_(P,u)(d)d^(-i tau) M(X/d,tau)`.

Split at `D=X^(1-kappa)`. For `d<=D`, the inner horizon
`T=X/d` satisfies `T>=X^kappa>=T0` and `|tau|<=T`.
The checked prefix theorem therefore bounds this entire part by

`K X exp(-(kappa log X)^(1/20)) sum_d a_(P,u)(d)/d`.

For `d>D`, use `|M(X/d,tau)|<=X/d`. Rankin's elementary
inequality `d^-1<=D^-a d^(-1+a)` bounds this part by

`X exp(-(1-kappa)log X/log y)
   sum_d a_(P,u)(d)d^(-1+a)`.

Insert (3) into both bounds. This proves (1), including every
cutoff and without any cancellation assumption on the smooth
coefficient. The signed cancellation is taken only from the
already-proved inner Möbius sum.

### The moving prime cutoff and the reciprocal weight

At `y=y_X`, the two exponent scales in (1) are
`kappa^(1/20)(log X)^(1/20)` and
`(1-kappa)(log X)^(1-beta)`. Write
`rho=min(1/20,1-beta)>0`. Both dominate a positive constant
times `(log X)^rho`. Meanwhile
`45 log(1+(log X)^beta)=o((log X)^rho)`.
Absorbing this polynomial factor proves the asserted
`C X exp(-c(log X)^rho)` bound, uniformly in `P,u,tau`.

Finally

`1/(omega_P(n)+1)=integral_0^1 u^(omega_P(n))du`.

The physical sum is finite and each integrand is continuous.
Interchange that finite sum and integral, take its norm, and
integrate the uniform bound over an interval of length one.
This proves the exact Ramaré-cofactor theorem. QED.

## Attack and comparison with the existing route

The original decomposition idea was:

- retain the actual signed prefix on small smooth divisors;
- pay large smooth divisors by their reciprocal moment;
- average the damping parameter only after proving uniformity.

The cutoff dependence is essential: at a polynomial prime cutoff
`y=X^theta`, the displayed Rankin saving is only a constant. This
argument therefore does not justify polynomial sieve localization.

`DampedCofactorIntegral.lean` already proves the final averaging
identity. `DampedCofactorLowFreqBound.lean` proves a bound with a
fixed-prime-set threshold and the explicit correction
`dampedCorrBound P c`. `RouteTDampedTwistRate.lean` makes the
threshold uniform in `P`, but retains that correction. The
checked `DampedCorrectionMassBudget.lean` measures when it can
overwhelm the contour saving. Those statements do not by themselves
give (1) for the moving cutoff.

Here the Euler product is used at the independently chosen
abscissa `1-1/log y`, only to bound a positive smooth tail. The
Möbius sum keeps its own proved rate. This avoids multiplying
the full contour estimate by the growing correction factor.
Verdict **BRIDGE**, no scientific novelty claim: the ingredients
are a known signed-prefix theorem and elementary convolution and
Rankin estimates. This is a new deduction checked here, not a
claimed new mechanism beyond the literature.

## Inputs checked so far

- `Sieve/MoebiusTwistSharpRate.lean`,
  `exists_norm_sum_moebiusTwist_rate`: explicit unconditional
  sharp-prefix saving, with the twist range tied to the actual
  contour parameter. The smoothing error has exponent `1/20`.
- `Sieve/MoebiusTwistPerron.lean`: `moebiusTwist` is the
  multiplicative phase `n^(-i tau)`, not an additive Fourier phase.
- `Sieve/PairFibreMeanSquare.lean`: `AveragedMeanSquare` sums
  reciprocal fibres. It is not the integer-start expression used
  by the rough-shift argument.
- `Sieve/RamareBlockSplit.lean`: the cofactor weight is shared by
  every selected prime, so its cancellation can feed the existing
  block decomposition. `RamarePhaseBilinear.lean` defines the exact
  coefficient `mu(m)/(card(primeFactorsIn P m)+1)`, agreeing above.

## Remaining formal and arithmetic work

The formalization uses the following stronger finite statement. There
exist absolute `K>0` and `T0>1` such that, for `X>0`, `H>=T0`,
`0<a<=1/2`, `u in [0,1]`, `|tau|<=H`, and a finite prime set
satisfying `a log p<=1` for every designated prime,

`|sum_(n<=X) mu(n)u^(omega_P(n))n^(-i tau)|`
` <= X(1+1/a)^36 [K exp(-(log H)^(1/20))+(X/H)^(-a)]`.

The split is at `d=X/H`. The signed prefix theorem is used only
on `X/d>=H`; on the remaining divisors the fractional moment
pays the tail. No assumption `H<=X` is necessary. When `H>X`,
the head is empty and the tail factor is at least one. Taking
`H=X^kappa` and `a=1/log y` recovers (1), with exponent `36`
in place of the looser `45`.

### Frequency close to the cofactor length

The finite statement also removes the need to keep `kappa` fixed
away from one. Write `S=log y>=2` and `H=X exp(-Delta)`,
with `H>=T0`. Substitution gives exactly

`X(1+S)^36 [K exp(-(log X-Delta)^(1/20))+exp(-Delta/S)]`.

The identities are `a=1/S`, `log H=log X-Delta`, and
`(X/H)^(-a)=exp(-Delta/S)`. Thus `Delta/S` exceeding a
sufficiently large multiple of `log S` pays any specified
polynomial loss in `S`, provided the signed-prefix exponential
also pays that loss. This is a direct specialization of the
proved paper estimate, not a new cancellation conjecture.

For the rough-shift scales `S=R^(99/100)` and
`Delta=R^(199/200)-R^(99/100)`, the tail factor is exactly
`exp(1-R^(1/200))`. Its saving beats every fixed power of `R`.
This matches the scale separation between the selected-prime
and short-window parameters in the coupled-centering route.
The required signed-prefix horizon condition must still be
checked at each actual cofactor block. The subsequent frequency
integral, large-value estimates and integer-start window transfer
are not consequences of this pointwise bound alone.

Verdict for this specialization: **BRIDGE**. It exposes the
useful two-scale range of the same convolution proof; no new
number-theoretic mechanism or fixed-shift result is claimed.

The imported signed-prefix capstone's transitive axiom audit
returned only `propext`, `Classical.choice`, and `Quot.sound`.
The new leaf is `twin-prime/RamareSmoothCofactorTransfer.lean`;
its fractional moment, exact twisted convolution and both finite
prefix estimates have passed their standard-foundation axiom
audits. The two asymptotic rate capstones are implemented and
under the final leaf check; their certificate is not yet claimed.

The paper proof has no open analytic dependency. Its unconditional
Lean formalization remains outstanding. The existing corpus
provides finite-prime summability, the reciprocal-Ramaré integral,
and the signed-prefix rate, but the precise uniform positive-tail
transfer above has not yet been certified here.

This Mellin-frequency statement does not supply the additive
frequency estimate in the rough-shift argument or an integer-start
mean-square theorem automatically. The intervening Ramaré block,
window and frequency estimates still require their exact errors to
be assembled. The fixed-shift twin-prime estimate is further away.

## Gates

- [x] Exact statement and proposed coefficient identity.
- [x] Corpus comparison and attack of all cutoff losses.
- [x] Complete dependency-closed paper proof.
- [ ] Unconditional Lean certificate of the actual weighted estimate.
- [ ] Determine what additional window and additive-frequency work remains.

## Log

- 2026-10-23 — Started after the corpus audit distinguished its
  reciprocal-fibre theorem from the needed additive-window input.
- 2026-10-23 — Completed the uniform proof using the existing
  all-height signed-prefix theorem. Strengthened the twist range
  from powers of `log X` to every fixed `X^kappa`, `kappa<1`.
  The finite Euler moment needs no new prime-distribution input.
