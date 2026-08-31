# Compact-effect formation properness, singular category fracture, and analytic escape law

- **ID:** ULF-TAFM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** fixed-source formation capital's mutually-singular loophole; whole-frontier demand for
  cofinal equicontinuity and source-admitted completion
- **Statement:** Exact tensor formation conserves target distinguishability as a pulled-back source
  effect; one compact source effect family has a strict formation-depth bound even when the two
  source laws are mutually singular, while arbitrary-depth measurable formation is possible only
  through topologically escaping effects.
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [GLOBAL PROPERNESS]`
  `[FUNCTIONAL-EQUATION NEUTRAL] [ACTUAL PRIME/GAMMA CALIBRATIONS] [NOT RH] [LEAN OPEN]`

## 1. Problem closed by this theorem

Fixed-source Hellinger capital proves that one overlapping experiment cannot form arbitrarily many
independent copies of a nonneutral target. It has an exact loophole: mutually singular source laws
already reveal their hidden mark measurably and can therefore form any finite target at every depth.

That loophole is too large for the arithmetic corpus. Reflected prime-Poisson and Gamma-six laws are
mutually singular off the wall, yet every finite-coordinate source neighbourhood has positive mass
for both laws. Their separating event is a tail event invisible to the source's finite-observation
topology. This theorem distinguishes two formation categories:

\[
 \boxed{
 \text{measurable formation can spend a tail separator,}\qquad
 \text{compactly admitted formation cannot.}}
 \tag{TAF.1}
\]

The resulting noncompactness is not an analogy. It is forced by an exact conservation identity.

## 2. Formation data

Let `X` be a nonempty compact metrizable space. Let `mu_0,mu_1` be Borel probability measures on
`X`, both with full topological support. Let `Y` be a nonempty finite set and let `p_0,p_1` be
probability mass functions on `Y`.

For a positive integer `d`, a finite-output Feller kernel is a Markov kernel

\[
 K_d:X\rightsquigarrow Y^d
 \tag{TAF.2}
\]

such that, for every event `B subseteq Y^d`, the pulled-back effect

\[
 e_{d,B}(x)=K_d(x,B)
 \tag{TAF.3}
\]

is continuous. It is an exact depth-`d` formation when

\[
 \int_XK_d(x,\{y\})\,d\mu_i(x)=p_i^{\otimes d}(y)
 \quad(i=0,1; y\in Y^d).
 \tag{TAF.4}
\]

Let `C(X,[0,1])` carry the uniform norm. A formation family is **compact-effect admitted** when all
effects `(TAF.3)` lie in one compact subset `E subseteq C(X,[0,1])`.

Define target Hellinger affinity

\[
 A(p_0,p_1)=\sum_{y\in Y}\sqrt{p_0(y)p_1(y)}.
 \tag{TAF.5}
\]

## 3. Full-support compact-effect gap

### Lemma 3.1 -- no continuous perfect separator

For every `e in C(X,[0,1])`,

\[
 \left|\int e\,d\mu_1-\int e\,d\mu_0\right|<1.
 \tag{TAF.6}
\]

#### Proof

If the difference were `1`, boundedness of `e` would force

\[
 \int e\,d\mu_1=1,
 \qquad
 \int e\,d\mu_0=0.
\]

A nonnegative continuous function with zero integral against a full-support measure is identically
zero: if it were positive at one point, it would be bounded below by a positive constant on a
nonempty open neighbourhood, which has positive measure. Hence `e=0` from the second equality and
`e=1` from the first, contradiction. The difference `-1` is identical after replacing `e` by
`1-e`. QED.

### Lemma 3.2 -- compact effect families have a uniform gap

For a compact `E subseteq C(X,[0,1])`, put

\[
 \eta_E=1-\max_{e\in E}
 \left|\int e\,d\mu_1-\int e\,d\mu_0\right|.
 \tag{TAF.7}
\]

Then

\[
 \boxed{\eta_E>0.}
 \tag{TAF.8}
\]

#### Proof

Integration is continuous for the uniform norm. The displayed maximum is attained on compact `E`
and is strictly below one by Lemma 3.1. QED.

This is the topological capital unavailable in the unrestricted measurable category.

## 4. Exact formation-current conservation

For probability masses `u,v` on a finite set, use

\[
 \operatorname{TV}(u,v)
 =\max_B\bigl(v(B)-u(B)\bigr)
 =1-\sum_z\min(u(z),v(z)).
 \tag{TAF.9}
\]

Since `min(a,b) <= sqrt(ab)`,

\[
 \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 \ge 1-A(p_0,p_1)^d.
 \tag{TAF.10}
\]

Choose an event `B_d subseteq Y^d` attaining the maximum in `(TAF.9)` and let
`e_d=e_{d,B_d}`.

### Theorem 4.1 -- pulled-back decision-current identity

Every exact depth-`d` formation satisfies

\[
 \boxed{
 \int_Xe_d\,d(\mu_1-\mu_0)
 =\operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 \ge1-A(p_0,p_1)^d.}
 \tag{TAF.11}
\]

#### Proof

Linearity and `(TAF.4)` give

\[
 \int e_d\,d\mu_i
 =\int K_d(x,B_d)\,d\mu_i(x)
 =p_i^{\otimes d}(B_d).
\]

Subtract and use `(TAF.9)`--`(TAF.10)`. QED.

Equation `(TAF.11)` is the fusion identity. Target tensor information, positive decision effects,
source topology, and formation history are four readings of one current. Information is not lost
when a route closes; it must remain in the source effect family.

## 5. Global formation/properness theorem

### Theorem 5.1 -- compact-effect depth bound

Assume every effect of an exact depth-`d` formation belongs to one compact family `E`. If
`0<A(p_0,p_1)<1`, then

\[
 \boxed{
 d\le {\log\eta_E\over\log A(p_0,p_1)}.}
 \tag{TAF.12}
\]

In particular, one compact-effect admitted family can form all positive depths only if
`p_0=p_1`.

#### Proof

By `(TAF.7)` and `(TAF.11)`,

\[
 1-A^d\le \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 =\int e_d\,d(\mu_1-\mu_0)
 \le1-\eta_E.
\]

Thus `A^d >= eta_E`. Taking logarithms and dividing by the negative number `log A` gives
`(TAF.12)`.

If `A=0`, already depth one would require a continuous perfect separator, contradicting Lemma 3.1.
If arbitrary depths exist, neither `A=0` nor `0<A<1` is possible, so `A=1`. Equality in
Cauchy--Schwarz for the two unit square-root vectors gives `p_0=p_1`. QED.

### Corollary 5.2 -- exact noncompactness alternative

If `p_0 ne p_1` and exact Feller formations exist at unbounded depths, their total effect family is
not relatively compact in `C(X,[0,1])`.

Because it is uniformly bounded, Arzela--Ascoli gives the sharper conclusion:

\[
 \boxed{\text{the pulled-back decision effects are not equicontinuous.}}
 \tag{TAF.13}
\]

Thus unbounded nonneutral formation creates an open source history even when every individual
effect is continuous and every finite target is exact.

## 6. Singular category fracture

Assume additionally that `mu_0` and `mu_1` are mutually singular. Choose a measurable `S subseteq X`
with

\[
 \mu_0(S)=0,
 \qquad
 \mu_1(S^c)=0.
 \tag{TAF.14}
\]

### Lemma 6.1 -- every singular witness is bi-dense

Both `S` and `S^c` are dense in `X`. Consequently `1_S` is discontinuous at every point.

#### Proof

Every nonempty open set has positive `mu_0`-mass and therefore meets `S^c`; it has positive
`mu_1`-mass and therefore meets `S`. QED.

### Theorem 6.2 -- measurable arbitrary-depth formation

For every finite target experiment `(p_0,p_1)` and every `d`, define

\[
 K_d(x,y)=
 \begin{cases}
 p_1^{\otimes d}(y),&x\in S,\\
 p_0^{\otimes d}(y),&x\notin S.
 \end{cases}
 \tag{TAF.15}
\]

Then `K_d` is a measurable exact formation. If `p_0 ne p_1`, some pulled-back event effect is a
nonconstant affine function of `1_S` and is therefore nowhere continuous.

#### Proof

Measurability and the Markov normalization are immediate. Equation `(TAF.14)` gives `(TAF.4)`.
Choose an event on which the two target laws differ. Its effect has two distinct constant values on
the dense sets `S` and `S^c`, so it is discontinuous everywhere. QED.

The displayed measurable implementation has infinite formation depth and is nowhere Feller. This
does **not** imply that other Feller implementations have bounded depth. ULF-TAFM-4 subsequently
proves the exact opposite for every common-support finite target: each finite depth is Feller
admitted, while no cofinal decision family remains uniformly admitted. The category fracture is
between measurable perfect separation and compact-uniform control, not between measurable and
pointwise Feller existence.

## 7. Functional-equation neutrality

Let `h:X -> X` be a homeomorphism. Transport source laws by `h` and formation kernels by
precomposition with `h^{-1}`. Pullback

\[
 h^*:C(X)\longrightarrow C(X),\qquad e\longmapsto e\circ h^{-1}
 \tag{TAF.16}
\]

is a uniform-norm isometry. It preserves compact effect families and preserves the integral
contrast in `(TAF.7)` exactly. Output bijections only relabel maximizing events.

### Theorem 7.1 -- information-neutral symmetry lift

The formation-current identity, compact-effect gap, exact depth bound, and effect escape are
invariant under every homeomorphic source action and every bijective target action.

#### Proof

Change variables in the two integrals and use the isometry `(TAF.16)`. Tensor target laws and total
variation are invariant under a coordinatewise bijection. QED.

Functional equation can move the obstruction but cannot finance or annihilate it.

## 8. Fourth-organ prediction: analytic and prolongation escape

### Corollary 8.1 -- Lipschitz escape

If `X` is compact metric and a nonneutral target is formed at unbounded depth, the pulled-back
decision effects have no common Lipschitz bound.

#### Proof

The `[0,1]` range gives uniform boundedness. A common Lipschitz bound gives equicontinuity, hence
relative compactness by Arzela--Ascoli, contradicting Corollary 5.2. QED.

On a compact interval, any differentiable realization therefore satisfies

\[
 \sup_d\|e_d'\|_\infty=+\infty.
 \tag{TAF.17}
\]

### Corollary 8.2 -- normal-family escape

Suppose the decision effects extend holomorphically to one fixed complex neighbourhood of a compact
real source set. If those extensions are uniformly bounded on that neighbourhood, unbounded
nonneutral exact formation is impossible.

#### Proof

Cauchy estimates give a common derivative bound on a smaller neighbourhood, hence equicontinuity on
the real compact set. Apply Corollary 8.1. QED.

Thus a holomorphic or differential realization of a completion phantom must pay with escaping
derivatives, shrinking domains, or loss of uniform bounds. This is a precise route from formation
noncompactness to prolongation growth; differential hypertranscendence is not identified with that
growth, but any HT interpretation now has a necessary mechanism to realize.

## 9. Two actual corpus calibrations

### 9.1 Gamma-six occupancy source

Push `gammaSixLaw(delta)` through coordinatewise occupancy

\[
 \mathbb N^{\mathrm{GammaSixLabel}}\longrightarrow
 \{0,1\}^{\mathrm{GammaSixLabel}},
 \qquad k\longmapsto 1_{k\ne0}.
\]

The target is a compact Cantor product. Every coordinate occupancy probability is strictly between
zero and one, so every nonempty finite cylinder has positive mass: both reflected laws have full
support. For `delta ne 0`, the finite-occupancy event or its complement separates the two laws by
the proved Borel--Cantelli polarity theorem. Hence Theorem 6.2 gives arbitrary measurable packet
formation, while Theorem 5.1 says every unbounded nonneutral Feller realization has noncompact,
nonequicontinuous effects.

This converts Gamma-six mutual singularity from a false selector into an exact topological-escape
prediction.

### 9.2 Prime-Poisson torus source

The literal prime torus is a compact product of circles. Each one-prime Poisson kernel with disk
parameter has a strictly positive continuous density and therefore full support; the product law
has full support. The corpus's Kakutani theorem makes the reflected laws mutually singular away
from neutral horizontal grade. The same category fracture follows.

The prime and Gamma calibrations are structurally different presentations of the theorem: one uses
a compact occupancy quotient and Borel--Cantelli; the other uses a compact harmonic torus and
Kakutani. Neither uses Xi divisor specialization.

## 10. Scope and RH boundary

This theorem does not prove RH. It proves the global formation/properness law required by a viable
selection architecture and closes the singular-source loophole in ordinary formation capital.

An RH consequence would require two further source theorems, both before divisor specialization:

1. an actual Xi-source formation sending a hypothetical off-line completed error to unbounded
   tensor depth of one nonneutral finite target; and
2. a source-derived common compact hull for its pulled-back decision effects, obtained from a
   uniform modulus, normal-family bound, compact graph domain, or equivalent properness theorem.

Assuming either statement only on Xi zeros would merely rename RH. Their construction is the live
producer problem.

## 11. Parent mathematics and external boundary

Ingredients are classical: Feller kernels, total variation and Hellinger testing, full-support
Radon measures, Arzela--Ascoli, Kakutani product dichotomy, and Cauchy/Montel normality. Recent
categorical work characterizes measurable Markov categories and probability sheaves, while
semi-uniform Feller theory studies continuity under integration. None supplies the arithmetic
compact-effect formation law required here.

Relevant primary sources:

- Rischel, *The Universal Property of Measure-Theoretic Probability*,
  <https://arxiv.org/abs/2512.15485>.
- Stein, *Random Variables, Conditional Independence and Categories of Abstract Sample Spaces*,
  <https://arxiv.org/abs/2503.02477>.
- Feinberg--Kasyanov--Zgurovsky, *Semi-Uniform Feller Stochastic Kernels*,
  <https://arxiv.org/abs/2107.02207>.
- Krukowski, *Arzela--Ascoli theorem in uniform spaces*,
  <https://arxiv.org/abs/1602.05693>.

No novelty claim is needed for the parents. Corpus contribution is the exact conservation/properness
fusion, the measurable-versus-admitted category fracture, and its literal prime/Gamma calibration.

## Gates

- [x] 0 -> 1: source-pure theorem, exact falsifier, no Xi divisor premise
- [x] 1 -> 2: dependency-closed proof of all claims above
- [ ] 2 -> 3: Lean formalization and axiom audit
- [ ] 3 -> 4: publication-ready standalone paper and priority audit

## Log

- 2026-08-31 -- theorem extracted after ordinary `lim^1` and measurable formation capital were
  shown to be receiver-level or category-dependent; compact-effect gap, exact current conservation,
  global depth bound, singular fracture, FE neutrality, and analytic escape proved.
