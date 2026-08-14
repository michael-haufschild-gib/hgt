# Titchmarsh--Jordan formation reserve, functional-equation action, and information blindness

- **ID:** ULF-CJFM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Causal Jordan Formation Mechanics; ULF-SGOGM causal-delay law; ULF-PFM split-recovery law
- **Statement:** A finite word of signed source drifts has a canonical positive two-leg formation refinement. Convolution adds the two legs exactly, functional equation swaps them, Titchmarsh support detects their uncancelled causal cost, and every exponential-family endpoint observer and common recovery kernel in this chart sees only their signed difference. Opposite drifts therefore generate a positive hidden reserve even when the recovered observer closes exactly.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [FIVE-DOCTRINE SCALAR FUSION] [LEAN-FORMALIZED ALGEBRA/PROPERNESS CORE] [NOT RH]`

## 1. Why this is not another endpoint theorem

An endpoint deformation records only its net displacement. A formation history records how much
positive and negative displacement was produced before cancellation. The distinction is already
forced by causal convolution: support endpoints add before signed displacement cancels.

This card couples five structures without identifying them:

1. source intervention words;
2. positive/Jordan decomposition;
3. causal convolution support;
4. functional-equation reflection;
5. endpoint information after a common recovery kernel.

The theorem is not that convolution support is new. Its load-bearing external input is the classical
Titchmarsh convolution theorem. The corpus delta is the exact positive refinement and its fusion
with functional-equation and split-recovery laws.

## 2. Signed drift words and their positive refinement

Let

\[
 w=(\delta_1,\ldots,\delta_n),
 \qquad \delta_i\in\mathbb R\setminus\{0\}.
 \tag{CJF.1}
\]

Define

\[
 P(w)=\sum_i\delta_i^+,
 \qquad
 N(w)=\sum_i\delta_i^-,
 \tag{CJF.2}
\]

where

\[
 \delta^+=\max(\delta,0),
 \qquad
 \delta^-=\max(-\delta,0).
\]

The recovered displacement, total variation, and cancellation reserve are

\[
 D(w)=P(w)-N(w)=\sum_i\delta_i,
 \tag{CJF.3}
\]

\[
 V(w)=P(w)+N(w)=\sum_i|\delta_i|,
 \tag{CJF.4}
\]

\[
 R(w)=\min(P(w),N(w))
 ={V(w)-|D(w)|\over2}.
 \tag{CJF.5}
\]

Thus

\[
 P(w)=D(w)^++R(w),
 \qquad
 N(w)=D(w)^-+R(w).
 \tag{CJF.6}
\]

The pair `(P,N)` is the **positive formation refinement**. The endpoint map is

\[
 \pi(P,N)=P-N.
 \tag{CJF.7}
\]

Its fibre over `D` is canonically the half-line

\[
 \pi^{-1}(D)
 =\{(D^++r,D^-+r):r\ge0\}.
 \tag{CJF.8}
\]

The coordinate `r` is information erased by endpoint cancellation.

## 3. Exact reserve-generation law

Concatenation of words is denoted by `uv`. Positive legs add strictly:

\[
 P(uv)=P(u)+P(v),
 \qquad
 N(uv)=N(u)+N(v).
 \tag{CJF.9}
\]

Define the cancellation birth term

\[
 c(x,y)={|x|+|y|-|x+y|\over2}\ge0.
 \tag{CJF.10}
\]

### Theorem 3.1 -- opposite drift generates positive reserve

For all nonempty drift words `u,v`,

\[
 \boxed{
 D(uv)=D(u)+D(v),
 \qquad
 R(uv)=R(u)+R(v)+c(D(u),D(v)).}
 \tag{CJF.11}
\]

Moreover

\[
 c(x,y)=0
 \iff xy\ge0,
 \tag{CJF.12}
\]

and when `xy<0`,

\[
 c(x,y)=\min(|x|,|y|).
 \tag{CJF.13}
\]

The operation

\[
 (x,r)\star(y,s)
 =\bigl(x+y,r+s+c(x,y)\bigr)
 \tag{CJF.14}
\]

is associative and commutative on

\[
 \mathcal F=\mathbb R\times\mathbb R_{\ge0}.
\]

The map

\[
 (P,N)\longmapsto(P-N,\min(P,N))
 \tag{CJF.15}
\]

is a monoid isomorphism from the additive cone
`R_{>=0}^2` to `(F,star)`.

#### Proof

Equation `(CJF.9)` is termwise. Since total variation is additive under word concatenation,

\[
\begin{aligned}
 R(uv)
 &=\frac{V(u)+V(v)-|D(u)+D(v)|}{2}\\
 &=R(u)+R(v)
   +\frac{|D(u)|+|D(v)|-|D(u)+D(v)|}{2},
\end{aligned}
\]

which proves `(CJF.11)`. Triangle inequality gives nonnegativity. The equality and opposite-sign
classifications follow by the two real-line cases. Associativity also follows directly from

\[
 c(x,y)+c(x+y,z)
 =c(y,z)+c(x,y+z)
 \tag{CJF.16}
\]

because both sides equal

\[
 {|x|+|y|+|z|-|x+y+z|\over2}.
\]

Finally `(CJF.6)` gives inverse maps between `(P,N)` and `(D,R)`; `(CJF.9)` transports addition to
`(CJF.14)`. QED.

The cocycle `(CJF.10)` is a coboundary of `|x|/2`. No nontrivial group-cohomology or curvature
claim is made. Its content is order-theoretic: cancellation in the signed quotient becomes positive
birth in the formation fibre.

## 4. Functional-equation action

Define reflection of a word by

\[
 w^\dagger=(-\delta_1,\ldots,-\delta_n).
 \tag{CJF.17}
\]

### Theorem 4.1 -- reflection swaps positive legs and fixes reserve

Reflection acts by

\[
 \boxed{
 (P,N)\longmapsto(N,P),
 \qquad
 (D,R)\longmapsto(-D,R).}
 \tag{CJF.18}
\]

It is an involutive automorphism of both formation monoids. In particular,

\[
 R(w^\dagger)=R(w),
 \qquad
 c(-x,-y)=c(x,y).
 \tag{CJF.19}
\]

#### Proof

For every scalar, `(-delta)^+=delta^-` and `(-delta)^-=delta^+`. Sum over the word. Formula
`(CJF.18)` follows from `(CJF.3)` and `(CJF.5)`. Additivity in `(P,N)` proves the automorphism law;
equivalently use `c(-x,-y)=c(x,y)` in `(CJF.14)`. QED.

This is the coordinate-free functional-equation action on the refined formation law: it reverses
visible signed drift while retaining cancellation history.

## 5. Causal histories and Titchmarsh support

Give each event a nonnegative delay `b_i` and a window width `T_i>0`. Define

\[
 h_{\delta,b,T}(t)
 ={1\over T}
 \left(
 \mathbf 1_{[b-\delta,b-\delta+T]}(t)
 -\mathbf 1_{[b,b+T]}(t)
 \right).
 \tag{CJF.20}
\]

For `delta!=0` this is a nonzero compactly supported `L^1` and `L^2` function. Its bilateral
Laplace transform is

\[
 \mathcal Lh_{\delta,b,T}(z)
 =e^{-bz}(e^{\delta z}-1){1-e^{-Tz}\over Tz},
 \tag{CJF.21}
\]

with the removable value at `z=0` understood.

For a word with event data `(delta_i,b_i,T_i)`, put

\[
 h_w=h_{\delta_1,b_1,T_1}*\cdots*h_{\delta_n,b_n,T_n},
 \tag{CJF.22}
\]

and

\[
 B(w)=\sum_i b_i,
 \qquad
 T(w)=\sum_iT_i.
 \tag{CJF.23}
\]

For a nonzero compactly supported integrable function `f`, let `ell(f)` and `r(f)` be the left and
right endpoints of its essential support.

The Titchmarsh convolution theorem states

\[
 \ell(f*g)=\ell(f)+\ell(g),
 \qquad
 r(f*g)=r(f)+r(g)
 \tag{CJF.24}
\]

for nonzero compactly supported integrable `f,g`. In particular, their convolution is nonzero.

### Theorem 5.1 -- exact causal support and common-delay law

For every drift word,

\[
 \boxed{
 \ell(h_w)=B(w)-P(w),
 \qquad
 r(h_w)=B(w)+T(w)+N(w).}
 \tag{CJF.25}
\]

Consequently

\[
 \boxed{
 r(h_w)-\ell(h_w)=T(w)+V(w).}
 \tag{CJF.26}
\]

The formed history is causal exactly when

\[
 B(w)\ge P(w).
 \tag{CJF.27}
\]

The same total delay admits both `w` and its functional-equation reflection exactly when

\[
 B(w)\ge\Lambda(w),
 \qquad
 \Lambda(w):=\max(P(w),N(w)).
 \tag{CJF.28}
\]

The least common causal delay is therefore

\[
 \boxed{
 \Lambda(w)
 ={V(w)+|D(w)|\over2}
 =|D(w)|+R(w).}
 \tag{CJF.29}
\]

#### Proof

If `delta>0`, inspection of `(CJF.20)` gives

\[
 \ell(h_{\delta,b,T})=b-\delta,
 \qquad
 r(h_{\delta,b,T})=b+T.
\]

If `delta<0`, it gives

\[
 \ell(h_{\delta,b,T})=b,
 \qquad
 r(h_{\delta,b,T})=b+T-\delta.
\]

Both cases are

\[
 \ell(h_{\delta,b,T})=b-\delta^+,
 \qquad
 r(h_{\delta,b,T})=b+T+\delta^-.
 \tag{CJF.30}
\]

Apply Titchmarsh repeatedly to obtain `(CJF.25)`. Subtraction gives `(CJF.26)`. Causality is
`ell(h_w)>=0`, proving `(CJF.27)`. Reflection exchanges `P,N`, so both legs are causal exactly when
`B>=max(P,N)`. The identities in `(CJF.29)` follow from `(CJF.3)`--`(CJF.5)`. QED.

The reserve has acquired an operational meaning: `R(w)` is exactly the common-delay cost that
remains after the visible absolute displacement `|D(w)|` is paid.

## 6. Closed observer, positive formation reserve

### Corollary 6.1 -- exact closed-loop reserve

If

\[
 D(w)=0,
 \tag{CJF.31}
\]

then

\[
 P(w)=N(w)=R(w)={V(w)\over2}
 \tag{CJF.32}
\]

and

\[
 \boxed{
 \Lambda(w)=R(w)={1\over2}\sum_i|\delta_i|.}
 \tag{CJF.33}
\]

Thus every nonempty closed word has strictly positive formation reserve. Its recovered displacement
is zero, but its least common causal delay and its extra support width are nonzero.

This gives a strict lifted-history object: the additive pair `(P,N)` is open in the positive cone
even when its signed projection `P-N` closes.

## 7. Endpoint information and common recovery are blind to reserve

Let `A` be a finite or countable state space, let `q(x)>0`, and let `X(x)` be a real statistic. On an
open interval `I`, suppose

\[
 Z(u)=\sum_{x\in A}q(x)e^{uX(x)}
 \tag{CJF.34}
\]

is finite and nonzero. Define the exponential-family observer

\[
 P_u(x)={q(x)e^{uX(x)}\over Z(u)}.
 \tag{CJF.35}
\]

Sequential tilts by the word act only through net displacement:

\[
 P_u\xrightarrow{\delta_1}\cdots\xrightarrow{\delta_n}P_{u+D(w)},
 \tag{CJF.36}
\]

provided the intermediate parameters are admitted.

Let `K` be any parameter-independent Markov recovery kernel and put

\[
 Q_u=\mathsf E_K(P_u)=P_u\otimes K.
 \tag{CJF.37}
\]

### Theorem 7.1 -- exact reserve blindness after common recovery

Endpoint observer and recovered packet depend on the word only through `D(w)`:

\[
 \boxed{
 P_u^w=P_{u+D(w)},
 \qquad
 Q_u^w=Q_{u+D(w)}.}
 \tag{CJF.38}
\]

Every KL or Jeffreys endpoint quantity therefore depends only on `D(w)`. In particular, if `D(w)=0`,

\[
 Q_u^w=Q_u,
 \qquad
 D(Q_u^w\Vert Q_u)=0,
 \qquad
 J(Q_u^w,Q_u)=0,
 \tag{CJF.39}
\]

while every nonempty closed word has the positive reserve `(CJF.33)`.

For each fixed `D`, reserve is completely unbounded inside the endpoint fibre: for every `r>=0`,
the two-leg formation

\[
 (P,N)=(D^++r,D^-+r)
 \tag{CJF.40}
\]

has endpoint `D` and reserve `r`. Hence no statistic factoring through `P_{u+D}` or through the
common-recovery packet `Q_{u+D}` can reconstruct, bound, or select formation reserve.

#### Proof

Multiplying the density in `(CJF.35)` by `e^{delta X}` and renormalizing sends `P_u` to
`P_{u+delta}`. Induction proves `(CJF.36)` and the first identity in `(CJF.38)`. Split formation is a
function of its observer law and fixed kernel, proving the second. The exact common-recovery KL law

\[
 D(P\otimes K\Vert P'\otimes K)=D(P\Vert P')
 \tag{CJF.41}
\]

shows that no divergence is created in the latent packet. If `D(w)=0`, endpoint laws are identical,
so `(CJF.39)` follows. Formula `(CJF.40)` is exactly the fibre classification `(CJF.8)`. QED.

### Euler-shell specialization

Take

\[
 A=A_m,
 \qquad
 q(n)=n^{-\sigma},
 \qquad
 X(n)=\log n,
\]

with `sigma-u>1`. Then

\[
 P_u(n)={n^{-\sigma+u}\over S_m(\sigma-u)}.
 \tag{CJF.42}
\]

This is the same source family used in the single-event causal-delay/information-undercapacity law.
The present theorem predicts its exact multi-event behavior: a zero-sum sequence of radial
interventions returns every normalized Euler-shell observer and every common recovered packet to
its starting law, while its causal formation reserve is half its total radial variation.

### Theorem 7.2 -- reciprocal common-delay properness

The corpus's source-formation harmonic chart already supplies the positive radial edge history. For
`q>0` and aperture `n`, retain both reciprocal magnitudes

\[
 L_n^+(q)=|1-q|q^n,
 \qquad
 L_n^-(q)=|1-q^{-1}|q^{-n},
 \tag{CJF.42a}
\]

and define the common causal budget

\[
 \Lambda_n(q)=\max\{L_n^+(q),L_n^-(q)\}.
 \tag{CJF.42b}
\]

Functional equation is the exact leg swap

\[
 L_n^+(q^{-1})=L_n^-(q),
 \qquad
 L_n^-(q^{-1})=L_n^+(q),
 \qquad
 \Lambda_n(q^{-1})=\Lambda_n(q).
 \tag{CJF.42c}
\]

Moreover

\[
 \boxed{
 \exists C\ \forall n,\ \Lambda_n(q)\le C
 \quad\Longleftrightarrow\quad q=1.}
 \tag{CJF.42d}
\]

If `q>1`, then `|1-q|>0` and `L_n^+(q)` is unbounded because `q^n` is unbounded. If `0<q<1`,
then `q^{-1}>1`, `|1-q^{-1}|>0`, and `L_n^-(q)` is unbounded. At `q=1`, both legs vanish. This
proves `(CJF.42d)`.

This is a genuine global formation/properness theorem, but not a new source producer. It is a new
causal receiver for the already Lean-certified source radial edge history in
`SourceFormationHarmonicMechanics`. Its selection force is conditional on admitting one uniform
common-delay budget across all apertures.

## 8. Fusion/conservation table

| organ | exact shadow |
|---|---|
| source interventions | signed word `(delta_i)` |
| positivity | additive Jordan pair `(P,N)` |
| causal formation | Titchmarsh endpoints `B-P`, `B+T+N` |
| functional equation | leg swap `(P,N)->(N,P)` |
| endpoint observer | signed quotient `D=P-N` |
| common recovery | split packet `P_D tensor K`; exact KL isometry |
| recurrence/closed execution | `D=0` with reserve `R=V/2>0` |

The conservation identity is not a scalar slogan. It is the commutative diagram

\[
\begin{array}{ccc}
 \mathbb R_{\ge0}^2&\xrightarrow{\ +\ }&\mathbb R_{\ge0}^2\\
 \downarrow(P,N)\mapsto(P-N,R)&&\downarrow\\
 (\mathcal F,\star)&\xrightarrow{\ \star\ }&(\mathcal F,\star)\\
 \downarrow(D,R)\mapsto D&&\downarrow\\
 (\mathbb R,+)&\xrightarrow{\ +\ }&(\mathbb R,+),
\end{array}
 \tag{CJF.43}
\]

with functional equation acting by the compatible involutions `(P,N)->(N,P)`, `(D,R)->(-D,R)`,
and `D->-D`.

## 9. Hostile conjecture loops

### Loop A -- support additivity is the new field

- **Verdict:** `[REDISCOVERED]`.
- **Killing mechanism:** `(CJF.24)` is the classical Titchmarsh theorem.
- **Positive survivor:** support additivity makes causal latency a faithful positive reporter of
  the Jordan refinement.

### Loop B -- functional equation cancels formation work

- **Verdict:** `[FALSIFIED]`.
- **Killing mechanism:** reflection fixes `R` and `Lambda`; it swaps the two positive legs.
- **Positive survivor:** functional equation is an automorphism of refined formation, not a
  dissipative selector.

### Loop C -- zero endpoint information means zero formation history

- **Verdict:** `[FALSIFIED]`.
- **Killing mechanism:** every nonempty zero-sum word satisfies `(CJF.39)` and `(CJF.33)`
  simultaneously.
- **Positive survivor:** exact fibre classification `(CJF.40)`; endpoint information is maximally
  blind to reserve.

### Loop D -- cancellation birth is nontrivial curvature

- **Verdict:** `[FALSIFIED]`.
- **Killing mechanism:** `c(x,y)` is the coboundary of `|x|/2` and obeys `(CJF.16)` tautologically.
- **Positive survivor:** the additive `(P,N)` chart is the strict higher object; the nonlinear
  reserve cocycle is its signed-quotient shadow.

### Loop E -- source origin forces zero reserve

- **Verdict:** `[FALSIFIED]`.
- **Killing mechanism:** any canonical source origin admits a zero-sum word with positive total
  variation unless source law forbids opposing events.
- **Positive survivor:** the selection premise must be a source law bounding the positive Jordan
  legs, not a coordinate choice of time origin.

## 10. Literature and parent boundary

- Titchmarsh support additivity is classical. A modern primary proof is Thomas Ransford,
  *A short complex-variable proof of the Titchmarsh convolution theorem*,
  <https://arxiv.org/abs/2011.05420>.
- The higher-dimensional convex-support theorem is the Titchmarsh--Lions theorem; the distribution
  form appears in Lars Hoermander, *Supports and singular supports of convolutions*.
- Jordan decomposition, total variation, exponential-family tilting, KL data processing, and
  sufficient Markov recovery are established parent mathematics.
- Source Formation Harmonic Mechanics already supplies a literal Moebius source with coherent
  execution, positive variation, recurrence/open history, HT rank, and bilateral radial energy
  selection. The present theorem does not rediscover that source refinement. Its delta is the
  strict two-leg reserve composition law, Titchmarsh causal reporter, common-recovery blindness, and
  the reciprocal common-delay properness receiver on that refinement.

This card is a `[BRIDGE]`, not a priority claim for its ingredients. Its significance is a hard
constraint on the new field: the primitive cannot be net deformation or endpoint information. It
must retain refinement-positive formation before cancellation.

## 11. Exact next gate

The theorem does not select RH. It changes the producer target.

The literal Moebius source refinement already exists in Source Formation Harmonic Mechanics. The
next theorem must construct a coefficient-faithful comparison from that refinement to the causal
Titchmarsh and common-recovery charts, and then prove one of:

1. cofinal boundedness of both legs;
2. passivity that forbids cancellation birth;
3. a source conservation law fixing reserve on complete functional-equation orbits; or
4. a proper action for which every nonzero reserve escapes.

Endpoint functional equations, KL isometries, and common recovery cannot supply this premise by
Theorem 7.1.

## Gates

- [x] exact positive refinement and fibre classification
- [x] reserve-generation/cocycle law
- [x] functional-equation automorphism
- [x] Titchmarsh causal-support law
- [x] common-delay formula
- [x] endpoint/common-recovery information no-go
- [x] Euler-shell specialization
- [x] hostile audit and parent classification
- [x] Lean formalization of algebraic reserve/reflection and cofinal properness core
- [x] literal Moebius source positive/coherent refinement (parent SFHM theorem)
- [ ] coefficient-faithful source-to-causal/common-recovery comparison functor
- [ ] RH selection

## Log

- 2026-08-13 -- conjectured entrance latency as convolution valuation; hostile audit demoted the
  raw support law to classical Titchmarsh.
- 2026-08-13 -- strengthened primitive from scalar delay to positive Jordan formation. Proved exact
  reserve birth, functional-equation leg swap, Titchmarsh support realization, closed-observer
  reserve, and common-recovery endpoint blindness. Promoted dependency-closed theorem to Stage 2.
- 2026-08-13 -- hostile corpus audit found the literal Moebius positive/coherent refinement already
  in Source Formation Harmonic Mechanics. Narrowed new delta to reserve composition, causal
  reporting, recovery blindness, and properness. Lean formalized the algebraic/reflection core and
  proved reciprocal common-delay boundedness iff `q=1`.
