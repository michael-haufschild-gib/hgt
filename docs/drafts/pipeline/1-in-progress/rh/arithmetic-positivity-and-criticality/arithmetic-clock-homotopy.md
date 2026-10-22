# Arithmetic spacing under an exponential clock

- **Stage:** 1-in-progress
- **Type:** CONJECTURES
- **RH chain:** actual arithmetic remainder -> source sign at unit term of every zero -> exclusion of off-line zeros. The unit-term constraint remains missing.

## Source and frozen statements

The proved constant-speed prefix law and the open clock conjecture C in [the phase-block card](arithmetic-log-phase-blocks.md) suggest interpolating the clock while retaining the same arithmetic quadratic.

Let `b(y)=(fract(y)^2-fract(y))/2`, `q_h(v)=(exp(h*v)-1)/h` for `h>0`, and `q_0(v)=v`. Define

`F(h,lambda,V)=integral_(0..V)b(q_h(v))*sin(lambda*v) dv`.

**D1 [BRIDGE], independently frozen:** for `0<h<=1`, `0<lambda<2*pi`, and `V>=0`, `F(h,lambda,V)<=0`.

**Dall, independently frozen:** the same inequality for every `h>0`.

These do not replace C. When `h=1/n`, with integer `n>=1`, `b(q_h(v))=b(n*exp(v/n))` because b has integer period. Substituting `v=n*w` gives `F(1/n,lambda,V)=n*integral_(0..V/n)b(n*exp(w))*sin(lambda*n*w) dw`. Thus D1 would imply C; the constant-speed theorem gives only h=0. Dall tests whether acceleration alone suffices without the scale restriction.

## Proof attack and numerical plan

For `a=1/h`, substitution `x=a*exp(h*v)` changes F into `a*integral_(a..a*exp(h*V))b(x-a)*sin((lambda/h)*log(x/a))/x dx`. At complete turns `V=2*pi*K/lambda`, the endpoint phase returns exactly. The kernel remains tied to its original integer grid in `x-a`; it must not be replaced by `b(x)` at noninteger a.

The direct proof would need to control the slope-jump contributions of the changing grid. The corpus first-derivative bounds control absolute values and do not prove the sign. A claimed monotonic homotopy also needs its own proof: the existing constant-speed prefix has exact zero-margin endpoints.

Run the diagnostic only on Runpod, with up to eight workers and one BLAS thread each. Test `h={0.01,0.1,0.25,0.5,1,2,4,8}`, `lambda/(2*pi)={0.25,0.5,0.75,0.99}`, and complete-turn numbers `K={1,2,4}`. Use exact finite-cell primitives and a shifted Hurwitz endpoint representation to avoid enumerating enormous intervals; force direct Euler--Maclaurin evaluation, with no reflection formula. Precision must grow with endpoint size. Verify selected signs by a separate finite integral or an explicit tail error bound. Retain all signs and parameters, including failures. This experiment concerns the clock transfer, not zeta zeros.

No novelty or RH implication is asserted. D1 and Dall remain unproved until this attack establishes otherwise; any replacement must be separately named and frozen.

## Independently frozen layer test E [BRIDGE]

The corpus's `HTGeometry.FiniteProbabilityGiniLayerCake` decomposes quadratic lower-cut masses into interval indicators. Applying the same change of viewpoint to the literal quadratic gives the pointwise identity

`-b(y)=integral_(0..1/2)(1/2-delta)*1_[delta<=fract(y)<=1-delta] ddelta`.

**E:** for integer `n>=1`, `0<t<2*pi*n`, `0<=delta<1/2`, and every `V>=0`,

`integral_(0..V)1_[delta<=fract(n*exp(v))<=1-delta]*sin(t*v) dv >= 0`.

If true for every layer, finite-interval integration in the opposite order would prove C. E is stronger than C and independently frozen; a failed layer does not refute the integrated quadratic. The endpoints of each layer in x are `m+delta` and `m+1-delta`, so its integral is an exact finite sum of cosine endpoint differences divided by t. This may reveal which arithmetic spacings force or defeat the sign.

The Runpod attack tests `n={1,4,16,128}`, ratios `t/(2*pi*n)={0.25,0.5,0.75,0.99}`, `delta={0,0.05,0.25,0.45,0.499}`, and turn numbers `{1,2,4,8}`, omitting endpoints spanning more than 3,000 cells. Work at 100 decimal digits. Delta=0 is an exact-zero control at complete turns; deviations smaller than `1e-70` are inconclusive numerical zeros. Any negative layer must be independently checked. No numerical sign is a Lean input.

## Additional frozen diagnostic

The first homotopy grid has no positive prefix. It mostly tests reciprocal-integer h in D1's range, so extend it to `h={0.37,0.63,0.83,0.97}` at the same ratios and turn numbers. Separately test `h={16,64,256,1024}` at ratios `{0.5,0.99}` and K=1. This does not change D1 or Dall.

For very large upper endpoints, retain the Bernoulli mean explicitly and bound the centered tail by its bounded periodic primitive. If `a=1/h`, `t=lambda/h`, and `X=a*exp(h*V)` is a complete-turn endpoint, the limiting endpoint expression is `a*Im[a^(-i*t)*T_u(a)]+a/(12*t)`, with `u=-1-i*t`. Its difference from the actual finite prefix is at most `a*(1+|1-i*t|)/X`. This estimate follows by one integration by parts with the centered primitive bounded by one; it is an analytic truncation bound, not a floating-point error certificate. Selected results must be checked without the shifted Hurwitz evaluator.

## Frozen source-scaling survivor S

The computations give positive fast-clock prefixes, while the below-threshold literal logarithmic B1 already has positive turns. Freeze the exact source transfer, independently of D1/Dall/E:

For fixed real `sigma>=-1`, fixed `lambda`, and `0<=a<=b`, let `N=n+1` and

`J_n=integral_(a..b) b(N*exp(v/N))*exp(-(sigma+1)*v/N)*sin(lambda*v) dv`.

**S:** `J_n -> integral_(a..b)b(v)*sin(lambda*v) dv` as `n->infinity`.

This is a closed paper proof: integer periodicity replaces `b(N*exp(v/N))` by `b(N*(exp(v/N)-1))`; the derivative of exp at zero gives the argument's limit v; continuity of b and the uniform bound `|b|<=1/8` give finite-interval dominated convergence. The exponential weight is bounded by one on these intervals and converges to one.

Substitution `x=N*exp(v/N)` identifies J with `N^(2*sigma+2)` times the actual fixed-anchor imaginary remainder integral at height `t=lambda*N`, from `N*exp(a/N)` to `N*exp(b/N)`. The Jacobian and the phase anchor must both be checked. At `lambda=4*pi/3`, `[a,b]=[3/2,3]`, the limiting integral is strictly positive by the previous Lean theorem. Thus S and that substitution would prove that the second actual logarithmic turn is positive for every sufficiently large N, still with `t<2*pi*N`. For a complete prefix whose constant-speed endpoint is noninteger, S instead forces eventual strict negativity. The integer-endpoint equality cases require a separate next-order argument, now supplied by F below. This does not prove C or the RH unit constraint.

## Current conclusions and exact next cut

S is now proved in `ArithmeticLogarithmicPhaseScaling`, including the exact Jacobian, real power normalization, and original complex phase anchor. It formally refutes the literal logarithmic B1 at the second complete turn for arbitrarily large cutoffs with height `(4*pi/3)*N`. The positive survivor also transfers every fixed noninteger complete-prefix endpoint to an eventual strict negative source prefix. See the [formal certificate](../../../3-formalized/arithmetic-logarithmic-phase-scaling.md).

The Runpod scans found all 108 D1-range evaluations negative, and seven of eight fast-clock tests positive. Three fast-clock positives were independently checked using 512 explicit arithmetic cells plus a bounded centered tail. These are numerical centers with analytic truncation bounds, not certified roundoff enclosures or Lean counterexamples. Dall has strong counterevidence; D1 remains open. The layer scan evaluated 290 of 320 planned cases, including 58 exact-zero controls; none of the 232 nonzero-layer tests was negative. E remains open. All scripts, results, limitations, and interpretations are in the [computation report](../../../2-fully-proven/computations/arithmetic-clock-homotopy/REPORT.md).

The integer endpoint cases of S have zero limiting margin. The independently frozen [first-variation identity F is now proved](../../../3-formalized/arithmetic-clock-first-variation.md), retaining every integer slope jump. Its strictly negative coefficient gives eventual strict negativity at precisely those endpoints. Combined with S, every fixed positive complete prefix is eventually negative. The cutoff may depend on the turn number; this is not a sign theorem for all turns at one cutoff or for every positive clock parameter. C, B2, D1, E, and R remain unchanged and unproved; none of these results forces the unit remainder's sign at a zeta zero.
