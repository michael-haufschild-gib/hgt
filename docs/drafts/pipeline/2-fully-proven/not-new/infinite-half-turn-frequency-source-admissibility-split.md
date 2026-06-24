# Infinite half-turn frequency source admissibility split

- **ID:** infinite-half-turn-frequency-source-admissibility-split
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer splitter
- **Source:** `finite-half-turn-repaired-packets-not-markov.md`;
  `seam-log-markov-pick-rh-equivalence.md`

## Statement

Let `mu` be a positive measure on `(0,infty)` with finite positive moments

`M_k=int x^k dmu(x)`, `k>=1`,

and define the half-turn repaired shifted moments

`U_k=M_k/(2k-1)!`.

### A. Markov positivity forces factorial moment curvature

If `(U_k)` is a Stieltjes/Markov moment sequence on `R_+`, then for every `k>=1`

`M_k M_(k+2) / M_(k+1)^2
 >= ((2k+2)(2k+3))/((2k)(2k+1))`.

In particular, any repaired-frequency source whose moment ratios satisfy

`limsup_{k->infty} k (M_k M_(k+2)/M_(k+1)^2 - 1) < 2`

cannot be Markov/Stieltjes after the half-turn repair.

### B. Without a source-admissibility restriction, infinite repaired sources
have no selecting power

Let `(S_k)_{k>=1}` be any Stieltjes moment sequence:

`S_k=int y^k dnu(y)`

for some positive measure `nu` on `R_+`, with all displayed moments finite. Then
there is a positive sigma-finite measure `mu` on `(0,infty)` with finite positive
moments such that

`M_k/(2k-1)! = S_k`

for every `k>=1`.

Thus the infinite positive repaired-frequency model can realize every
Stieltjes target if sigma-finite mass accumulating at zero frequency is allowed.
It becomes RH-bearing only after a source gate excludes this reservoir or
replaces it with a specific Euler/Gamma/FE distribution law.

## Proof

### A. Curvature gate

Every Stieltjes moment sequence is log-convex in the adjacent shifted sense:

`U_k U_(k+2)-U_(k+1)^2 >= 0`.

Substituting `U_j=M_j/(2j-1)!` gives

`(M_k M_(k+2) / M_(k+1)^2)
 * ((2k+1)!^2)/((2k-1)!(2k+3)!) >= 1`.

The factorial factor is

`((2k+1)!^2)/((2k-1)!(2k+3)!)
 = ((2k)(2k+1))/((2k+2)(2k+3))`.

Since this factor is below `1`, the required lower bound on the raw moment ratio
is its reciprocal:

`M_k M_(k+2) / M_(k+1)^2
 >= ((2k+2)(2k+3))/((2k)(2k+1))`.

The right side is

`1 + (8k+6)/(4k^2+2k) = 1 + 2/k + O(k^-2)`.

This proves the limsup obstruction.

### B. Zero-frequency reservoir

Define a positive sigma-finite measure `alpha` on `(0,infty)` by

`dalpha(x)=e^(-sqrt(x)) dx/(2x)`.

For every `k>=1`,

`int x^k dalpha(x)
 = 1/2 int_0^infty x^(k-1) e^(-sqrt(x)) dx`.

With `r=sqrt(x)`, `dx=2r dr`, this becomes

`int_0^infty r^(2k-1) e^(-r) dr = Gamma(2k) = (2k-1)!`.

Now let `nu` be any positive representing measure for the target Stieltjes
sequence `(S_k)`. Any atom of `nu` at `0` contributes nothing to the positive
moments `S_k`, so discard it. Let `mu` be the pushforward of `alpha x nu` under
multiplication:

`x = a y`.

Then, for every `k>=1`,

`M_k=int x^k dmu(x)
    = (int a^k dalpha(a))(int y^k dnu(y))
    = (2k-1)! S_k`.

Hence `U_k=M_k/(2k-1)!=S_k`.

The measure `alpha` has infinite total mass near `0`, but all its positive
moments are finite. This is why the construction is admissible at the level of
formal positive moments and inadmissible as an Euler-prime source unless the
source category explicitly permits a zero-frequency reservoir. ∎

## Consequence for the RH Route

This theorem is the infinite counterpart of
`finite-half-turn-repaired-packets-not-markov.md`.

Finite positive repaired packets fail because the top frequency eventually
dominates. Infinite positive repaired measures split into two sharply different
classes:

1. **Unrestricted sigma-finite sources:** too flexible. They can realize every
   Stieltjes moment target by hiding the factorial repair in infinite mass near
   frequency `0`. This cannot select `xi` or prove RH.
2. **Source-admissible Euler/Gamma/FE sources:** must satisfy a real curvature
   law, at least
   `M_k M_(k+2)/M_(k+1)^2 >= 1+2/k+O(k^-2)`, without using a zero-frequency
   reservoir.

The next RH-bearing theorem therefore cannot merely say "use an infinite
positive repaired frequency measure." It must prove one of:

- the actual Euler/Gamma/FE source moments have the required factorial
  curvature and all higher Hankel square tests;
- the source category forbids the zero-frequency reservoir and supplies a
  canonical substitute;
- the Markov cone is produced by a boundary/index object rather than by an
  additive positive frequency measure.

## 2026-06-24 finite-mass repaired sources are impossible for compact Markov targets

The zero-frequency reservoir above is not an artifact that survives every
reasonable source restriction. For compact Markov targets, requiring the
repaired frequency source `mu` to have finite total mass rules out the entire
positive repaired-frequency model.

Let `nu` be a nonzero finite positive measure with compact support in
`[0,R] subset R_+`, and put

`S_k=int y^k dnu(y)`, `k>=1`.

Assume there is a positive finite measure `mu` on `(0,infty)` with

`int x^k dmu(x)=(2k-1)! S_k`, for every `k>=1`.

Define the finite measure

`dlambda(x)=x dmu(x)`.

Then

`int x^n dlambda(x)=int x^(n+1)dmu(x)=(2n+1)! S_(n+1)`, for `n>=0`.

This moment problem is determinate by Carleman's criterion. Indeed, since
`nu` is compactly supported and nonzero, `S_(n+1)<=C R^(n+1)` for some `C,R`,
so

`((2n+1)! S_(n+1))^(-1/(2n)) >= C' / n`

for all large `n`, and the Carleman series diverges.

One representing measure is

`lambda_0 = pushforward of lambda_base(a) x (y dnu(y)) under x=a y`,

where

`dlambda_base(a)=e^(-sqrt(a)) da/2`.

Indeed,

`int a^n dlambda_base(a)=(2n+1)!`,

and therefore

`int x^n dlambda_0(x)
 = int (a y)^n y dlambda_base(a)dnu(y)
 = (2n+1)! S_(n+1)`.

By determinacy, `lambda=lambda_0`. Hence

`mu((0,infty)) = int x^(-1) dlambda_0(x)`

`= int (a y)^(-1) y dlambda_base(a)dnu(y)`

`= nu((0,infty)) int a^(-1) dlambda_base(a)`.

Since `nu` is nonzero and any atom at `0` contributes nothing to all positive
moments, discard such an atom if present. The remaining mass on `(0,R]` is
positive. But

`int a^(-1) dlambda_base(a)
 = int_0^infty e^(-sqrt(a)) da/(2a) = infinity`,

because the integrand is asymptotic to `1/(2a)` at `0`.

Thus the unique representing `lambda` has infinite inverse moment, so no finite
positive repaired frequency source `mu` can realize a compact Markov target not
supported only at `0`.

The constant target `S_k=1` is the special case `nu=delta_1`; the same argument
shows the obstruction is universal for compact positive Markov targets.

Consequently, the half-turn repaired positive-frequency route cannot produce
the RH Markov target by any finite positive source measure, even assuming RH.
The finite-mass version of the route is dead; the infinite-mass version needs an
independent source admissibility law, because unrestricted infinite mass has no
selecting power.

### Exact finite-mass passport

More generally, for a target Stieltjes sequence `(S_k)_(k>=1)`, a finite
positive repaired frequency source `mu` satisfying

`int x^k dmu(x)=(2k-1)! S_k`, for `k>=1`,

exists if and only if the shifted factorial sequence

`N_n=(2n+1)! S_(n+1)`, `n>=0`,

has a positive representing measure `lambda` on `(0,infty)` with finite inverse
moment

`int x^(-1) dlambda(x)<infty`.

Indeed, given `mu`, set `dlambda=x dmu`; then

`int x^n dlambda=(2n+1)!S_(n+1)`

and

`int x^(-1) dlambda=mu((0,infty))<infty`.

Conversely, given such a `lambda`, set `dmu=x^(-1)dlambda`; then `mu` is finite
and has the required positive moments.

Thus finite-mass source admissibility is exactly an inverse-moment condition on
the representing measure of the shifted factorial target. The zero-frequency
reservoir fails precisely because this inverse moment diverges.

## Boundary

This does not prove RH and does not disprove an infinite repaired-frequency
route. It proves that such a route needs a source-admissibility theorem. Without
that theorem the model is either too weak, by the curvature obstruction, or too
flexible, by the zero-frequency reservoir.

## Theatre Test

For any infinite repaired-frequency proof:

1. What source rule excludes arbitrary sigma-finite mass at frequency `0`?
2. What source rule proves the factorial curvature
   `M_k M_(k+2)/M_(k+1)^2 >= 1+2/k+O(k^-2)`?
3. Which higher Hankel gates are proved beyond adjacent log-convexity?
4. If the proof can choose the representing frequency measure freely, this card
   shows it can manufacture any Stieltjes target and is not a selector.

## Novelty Status

The proof is elementary, but the route impact is significant: it identifies the
exact admissibility split left open after finite positive repaired packets were
killed. The live problem is no longer "finite versus infinite"; it is
"source-admissible infinite distribution versus arbitrary zero-frequency
reservoir."

## Gates

- [x] 0 -> 1 in-progress: infinite repaired-frequency loophole isolated.
- [x] 1 -> 2 fully-proven: curvature necessity and zero-frequency reservoir
  universality proved.
- [ ] 2 -> 3 formalized: optional moment-ratio and Mellin-kernel proof.

## 2026-06-24 local zero-frequency mass is forced for compact Markov targets

The finite-mass obstruction above can be sharpened to a local border statement.
For a compact Markov target not supported only at `0`, every positive
repaired-frequency source realizing the positive moments has infinite mass in
every neighborhood of frequency `0`. Thus the zero-frequency reservoir is not
merely a bad choice of one representing measure; it is forced by the shifted
factorial moments.

Let `nu` be a finite positive measure supported in `[0,R]`, not supported only
at `0`, and set

`S_k=int y^k dnu(y)`, `k>=1`.

Assume `mu` is a positive measure on `(0,infty)` with finite positive moments
and

`int x^k dmu(x)=(2k-1)! S_k`, for every `k>=1`.

Set `dlambda=x dmu`. Since `int x dmu<infty`, `lambda` is finite, and

`int x^n dlambda=(2n+1)! S_(n+1)`, for every `n>=0`.

As in the finite-mass proof, this moment problem is determinate by Carleman's
criterion. Its representing measure is

`lambda_0 = pushforward of lambda_base(a) x (y dnu(y)) under x=a y`,

where

`dlambda_base(a)=e^(-sqrt(a)) da/2`.

Therefore `lambda=lambda_0`, and since `lambda=x mu` on `(0,infty)`,

`dmu=x^(-1) dlambda_0`.

Fix `delta>0`. Because `nu` is not supported only at `0`, there is `eta>0`
such that `nu([eta,R])>0`. For `y in [eta,R]` and `0<a<delta/R`, one has
`a y<delta`. Hence

`mu((0,delta))
 >= int_(y in [eta,R]) int_(0<a<delta/R) a^(-1) dlambda_base(a) dnu(y)`

`= nu([eta,R]) int_0^(delta/R) e^(-sqrt(a)) da/(2a)
 = infinity`.

Thus `mu((0,delta))=infinity` for every `delta>0`.

Consequently, any source category that requires local finiteness at the
zero-frequency border, or any finite border counterterm, cannot realize even a
compact Markov target not supported only at `0` through the positive half-turn
repaired-frequency model. The remaining possible positive-frequency route must
either permit this locally infinite border reservoir and then add a noncircular
selector, or leave the additive repaired-frequency model for a completed
boundary/index theorem.

## 2026-06-24 exact local Mellin threshold at zero frequency

The local-infinity statement has been sharpened in
`zero-frequency-repaired-source-mellin-threshold.md`. Under the same compact
Markov-target hypotheses, every positive repaired-frequency source has exact
local integrability threshold exponent `0` at the zero-frequency border: for
all `q>0`, `int_(0,delta) x^q dmu(x)<infinity`; for `q<=0`, the corresponding
local integral is infinite.

Thus positive fractional moment finiteness is not a source-admissibility gate:
the arbitrary zero-frequency reservoir already passes every such test. Local
finiteness, by contrast, excludes the compact Markov targets in this additive
model. The remaining source-selection problem is structural, not a Mellin
integrability cutoff above exponent `0`.

## 2026-06-24 local weighted-integrability classification

`zero-frequency-repaired-source-dx-over-x-law.md` strengthens the local border analysis. Under the same compact Markov-target hypotheses, the forced positive repaired-frequency source is locally comparable to `dx/x`: for every nonnegative local weight `w`,

`int_(0,delta) w dmu < infinity <=> int_0^delta w(x) dx/x < infinity`.

Therefore source admissibility cannot be a local weighted-finiteness condition. Such a condition either accepts the arbitrary zero-frequency reservoir or rejects the compact Markov targets themselves.

## 2026-06-24 local measure-class nonselection

`zero-frequency-repaired-source-dx-over-x-law.md` also gives a bounded-equivalence corollary: repaired reservoirs for any two compact Markov targets not supported only at `0` are mutually comparable on every zero-frequency interval `(0,delta)`.

Thus the infinite positive repaired-frequency route cannot be rescued by a local measure-class or local regularity selector at zero frequency. The remaining selector, if any, must be nonlocal or source-coupled.

## 2026-06-24 density profile is Laplace-equivalent to the target

`zero-frequency-reservoir-density-laplace-equivalence.md` identifies the exact density of the zero-frequency reservoir against `dx/x`:

`h(x)=(1/2) int_(0,R] exp(-sqrt(x/y)) dnu(y)`.

Its leading logarithmic divergence reads only `nu((0,R])/2`; its full profile is the Laplace transform of the pushforward of `nu|_(0,R]` under `y->y^(-1/2)`, and therefore determines the target measure. Thus the infinite repaired-frequency route cannot be rescued by treating the reservoir density as a softer independent source coordinate.

## 2026-06-24 complete-monotone reservoir profiles are exactly Markov targets

`reservoir-density-complete-monotonicity-markov-equivalence.md` completes the reservoir-profile classification. After setting `H(t)=2h(t^2)`, compact positive Markov targets are exactly finite Laplace transforms whose representing measure is supported away from `0`; equivalently, the corresponding complete-monotonicity condition is the target positivity cone in reservoir coordinates.

Thus the infinite repaired-frequency route cannot be rescued by replacing Markov positivity with complete monotonicity of the reservoir profile. That condition must itself be source-derived.
