# Maximal HT with one-point parabolic orbit collapse

- **ID:** `maximal-ht-parabolic-orbit-collapse`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; translation dynamics; universality and recurrence boundary
- **Statement:** A bounded outer function can have a differentially algebraically independent
  continuum of parabolic translates at every algebraic power while the compact-open closure of its
  real orbit adds only one constant limit point.  Maximal algebraic orbit freedom therefore
  coexists with complete topological escape and failure of strong self-recurrence.  The collapse
  mechanism holds for every finite positive Stieltjes measure on a half-line; maximal HT is realized
  by a comeager atomic subfamily inside that universally collapsing class.

## Goal

Separate two notions that are often conflated in the HT landscape:

1. algebraic freedom of distinct translates, measured by differential transcendence degree;
2. topological richness of one translation orbit, measured by compact-open universality or strong
   recurrence.

The theorem realizes the strongest possible first property together with an extremely small orbit
closure for the second.  This is a general law about HT functions; the zeta application is only its
route boundary.

## Setup

Fix a bounded real sequence `u=(u_j)` in the comeager free set of
`herglotz-full-translation-ht-krein-index-orthogonality.md`.  Put

`lambda_j=j+1`, `w_j=2^(-j-1) exp(u_j)`,

`m(z)=sum_(j>=0) w_j/(lambda_j-z)`.                            (1)

Then `m` is Herglotz on the upper half-plane `H`, and the full complex translation family

`{m(z+h):h in C}`                                             (2)

is differentially algebraically independent over `C(z)`.

Let

`phi(w)=i(1+w)/(1-w)`,

`sigma(w)=(m(phi(w))-i)/(m(phi(w))+i)`,

`O(w)=exp(sigma(w))`.                                         (3)

For real `t`, define the parabolic disk automorphism

`tau_t=phi^(-1) o (z |-> z+t) o phi`.                         (4)

Thus `phi o tau_t=phi+t`.

## Theorem `[PROVED HERE]`

1. `O,O^(-1) in H^infinity(D)`, and `O` is outer and cyclic in `H^2(D)`.
2. For every `N>=1`, the continuum

   `{(O o tau_t)^N:t in R}`                                  (5)

   is differentially algebraically independent over `C(w)`.
3. For every `N>=1`,

   `(O o tau_t)^N -> exp(-N)`                                (6)

   locally uniformly on `D` as `t->+infinity` and as `t->-infinity`.
4. In the compact-open topology of `Hol(D)`,

   `closure{(O o tau_t)^N:t in R}`

   ` ={(O o tau_t)^N:t in R} union {exp(-N)}`.                (7)

5. The orbit in (5) is not compact-open universal, even among nonvanishing targets.  For `N=1`,
   it also fails strong self-recurrence: there are a compact `K subset D` and `epsilon>0` for which

   `{t>=0:sup_(w in K)|O(tau_t(w))-O(w)|<epsilon}`             (8)

   is bounded and therefore has lower asymptotic density zero.

## Proof

### 1. Bounded outer maximal-HT carrier

Strict Herglotz positivity and the Cayley transform give `|sigma(w)|<1` on `D`.  Hence

`exp(-1)<|O(w)|<exp(1)`,                                      (9)

so `O` and its inverse lie in `H^infinity`.  Since `O=exp(sigma)` with bounded analytic exponent,
it is outer; therefore it is cyclic in `H^2`.

The proof in `hardy-cyclicity-maximal-ht-field-blindness.md` transports (2) through the rational
domain Cayley map and invertible rational codomain Cayley map, then recovers the independent
derivative orbit from

`D(O o tau_t)/(O o tau_t)=D(sigma o tau_t)`.                  (10)

Thus the `N=1` family is differentially algebraically independent.  For distinct
`t_1,...,t_r`, every `O o tau_(t_j)` is algebraic over its `N`-th power.  If the powers were
differentially algebraically dependent, their generated differential field would have differential
transcendence degree below `r`; adjoining the algebraic `N`-th roots could not raise that degree to
`r`.  This contradicts the independence at `N=1`.  Hence (5) is independent for every `N`.

### 2. Finite-measure Stieltjes collapse

The decay mechanism is more general than the atomic free family.  Let `mu` be any finite positive
Borel measure on `[0,infinity)` and define its Stieltjes transform on `H` by

`m_mu(z)=integral_[0,infinity) 1/(lambda-z) dmu(lambda)`.      (11)

Then

`m_mu(z+t)->0` locally uniformly on `H` as `t->+-infinity`.    (12)

Fix a compact `L subset H`.  Choose

`delta=inf_(z in L) Im z>0`, `A=sup_(z in L)|Re z|`,

and write `W=mu([0,infinity))<infinity`.  For `t<0` with `|t|>2A`,

`|lambda-z-t|>=lambda+|t|-A>=|t|-A`

for every `z in L` and `lambda>=0`, so

`sup_(z in L)|m_mu(z+t)|<=W/(|t|-A)->0`.                      (13)

Now take `t>2A+2` and split the integral at `lambda=t/2`.  The lower part has modulus at most

`W/(t/2-A)`.                                                   (14)

On the upper part every denominator has modulus at least `delta`, hence its modulus is at most

`delta^(-1) mu((t/2,infinity))`.                              (15)

The tail in (15) tends to zero by finiteness of `mu`.  The bounds are uniform on `L`, proving (12).

The atomic measure `mu=sum_j w_j delta_(lambda_j)` in (1) is finite, so (12) gives the required
decay of `m`.  Thus every finite positive Stieltjes carrier on a half-line has the same two-ended
topological collapse after the Cayley--exponential transform; the transversality theorem selects a
comeager atomic subfamily for which the orbit is simultaneously maximally HT.

### 3. One-point collapse

For compact `K subset D`, the image `phi(K)` is compact in `H`.  By (12) and
`phi(tau_t(w))=phi(w)+t`,

`m(phi(tau_t(w)))->0`                                        (16)

uniformly on `K` at both ends.  The codomain Cayley map sends `0` to `-1`.  Continuity of the Cayley
map and exponential therefore gives

`O(tau_t(w))->exp(-1)`                                       (17)

locally uniformly.  Taking powers proves (6).

To identify the closure, consider any convergent sequence of orbit points with parameters `t_n`.
If `(t_n)` is unbounded, a subsequence tends to one of the two infinities and (6) forces the limit
`exp(-N)`.  If `(t_n)` is bounded, a subsequence tends to some real `t`; continuity of translation,
composition, and the locally uniform topology gives the orbit point `(O o tau_t)^N`.  Conversely,
the constant in (7) is attained as the limit at infinity.  This proves (7).

### 4. Failure of universality and strong recurrence

Equation (9) gives

`exp(-N)<|(O o tau_t(w))^N|<exp(N)`                           (18)

for all `t,w`.  The orbit cannot approximate, even at one point, a nonzero constant of modulus less
than `exp(-N)`.  Thus it is not universal among nonvanishing holomorphic targets.

The function `O` is nonconstant because `m` is nonconstant and both transforms in (3) are
nonconstant and locally injective.  Choose `w_0 in D` with `O(w_0)!=exp(-1)` and put

`epsilon=|O(w_0)-exp(-1)|/3`.                                 (19)

By (15), for all sufficiently large `|t|`,

`|O(tau_t(w_0))-exp(-1)|<epsilon`.                            (20)

The triangle inequality and (17) then give

`|O(tau_t(w_0))-O(w_0)|>epsilon`.                             (21)

Taking `K={w_0}` shows that the set (8) is bounded.  Its lower asymptotic density is zero, proving
failure of strong self-recurrence. `QED`

## Law extracted

**Algebraic-freedom/topological-collapse law.**  Differential-algebraic independence measures the
absence of every finite differential relation among distinct orbit points; it imposes no recurrence,
density, ergodicity, or universality on the parameterized orbit.  The separation persists after
every algebraic power normalization: each power orbit remains maximally free while both ends of the
real parameter line collapse to one constant.

This is not a statement that HT functions are generally nonuniversal.  It is a sharp independence
theorem: the strongest available algebraic orbit freedom does not imply even weak topological
richness of that orbit.

## RH-route consequence

Voronin universality and Bagchi strong recurrence are translation-dynamical properties of the
zeta function.  The theorem rules out the implementation claim

> Full translation hypertranscendence, or differential-algebraic independence of all distinct
> translates (even at every power level), supplies universality or the strong self-recurrence needed
> for a Bagchi-type RH argument.

It does not refute Voronin's theorem or Bagchi's RH equivalence.  Those results use a distinguished
vertical zeta orbit, Euler-product probability/limit-distribution structure, and a pointed target
equal to zeta itself.  The theorem proves that none of that topological recurrence is contained in
maximal HT freedom alone.  A viable recurrence proof must consume an additional arithmetic measure,
phase distribution, Euler marking, or equivalent topological input.

## Parent-theory and preliminary novelty audit

- `[SEARCH]` Voronin's primary theorem concerns approximation by vertical zeta translates:
  `https://doi.org/10.1070/IM1975v009n03ABEH001485`.
- `[SEARCH]` The effective-universality literature states Voronin approximation and Bagchi's limiting
  density refinement: `https://arxiv.org/abs/1611.10325`.
- `[SEARCH]` Birkhoff-type translation hypercyclicity and common hypercyclic vectors show that dense
  translation orbits are abundant in large holomorphic function spaces; for example
  `https://arxiv.org/abs/1411.7815`.
- `[SEARCH]` Classical work also studies linear independence of translates and translation-generated
  closed subspaces separately; Edwards' 1951 paper is
  `https://www.numdam.org/item/AIF_1951__3__31_0/`.

Preliminary searches did not locate the exact coexistence proved here: an uncountable
differentially algebraically independent translation family at every power, carried by an invertible
outer function, whose continuous real orbit has the one-point closure (7) and zero-density
self-recurrence.  The proof depends on the separately novelty-unverified Herglotz full-orbit theorem,
but the topological collapse and all-power strengthening add a distinct exact law.  It passes the
proof and significance gates; scientific priority remains provisional pending specialist audit in
differential algebra and linear dynamics.

## Lean status

`CayleySchur.lean` supplies only pointwise Cayley bounds.  The repository does not formalize locally
uniform convergence on `Hol(D)`, outer functions, translation hypercyclicity/recurrence, the atomic
Herglotz series with uniform tail estimates, or differential independence of the parabolic orbit.
Every one of those layers occurs in the theorem.  No stage-3 promotion is justified until the full
unconditional statement is formalized in Lean.

## Gates

- [x] 0 -> 1: algebraic-freedom versus orbit-topology separation isolated
- [x] 1 -> 2: complete unconditional paper proof
- [ ] independent proof audit of the two-sided uniform decay and closure classification
- [ ] full parent-theory and literature audit sufficient for novelty promotion
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready preprint and independent novelty review

## Log

- 2026-07-11 -- Proved two-sided local-uniform decay of the positive atomic Herglotz translate and
  transported it through Cayley and exponential maps to a one-point parabolic orbit closure.
- 2026-07-11 -- Proved that every algebraic power orbit remains differentially algebraically
  independent while universality and strong self-recurrence fail.
- 2026-07-11 -- Strengthened the two-sided decay from the exponentially weighted atomic example to
  every finite positive Stieltjes measure on a half-line, separating the universal collapse
  mechanism from the residual maximal-HT selection.
