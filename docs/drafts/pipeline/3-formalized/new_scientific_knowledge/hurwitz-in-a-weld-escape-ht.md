# Hurwitz zeta is hypertranscendental in its shift variable

- **ID:** `hurwitz-in-a-weld-escape-ht`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOVELTY AUDITED]`
- **Publication score:** **82/100** — publication-worthy, below field-defining scale

## Result

Fix `s ∈ ℂ` with `Re s > 1` and `s ∉ ℚ`. For every `N ≥ 0`, the functions

\[
  a\longmapsto \zeta(s,a),\zeta(s+1,a),\ldots,\zeta(s+N,a)
\]

are algebraically independent over `ℂ(a)` on the upper half-plane. Consequently the single
function `a ↦ ζ(s,a)` is hypertranscendental over `ℂ(a)` there: it satisfies no nonzero
algebraic ordinary differential equation of any finite order or degree.

The exact value relation joining the two statements is

\[
  \boxed{\partial_a^r\zeta(s,a)=(-1)^r(s)_r\zeta(s+r,a)}
  \qquad(r\geq0),
\]

where `(s)_r=s(s+1)\cdots(s+r-1)`. The first derivative is classical
([DLMF 25.11.17](https://dlmf.nist.gov/25.11.E17)); its all-order iteration is an invertible
diagonal coordinate change because `Re s>1` implies `(s)_r≠0`.

The derivative identity is `[SEARCH] [BRIDGE]`. The arbitrary-degree ladder independence and
the resulting fixed-`s`, one-variable hypertranscendence theorem are `[PROVED HERE]`.

## Theorem A — finite ladder independence

Let `N≥0` and

\[
 P\in \mathbb C[a][Y_0,\ldots,Y_N].
\]

If

\[
 P\bigl(a;\zeta(s,a),\zeta(s+1,a),\ldots,\zeta(s+N,a)\bigr)=0
\]

for every `a` in the upper half-plane, then `P=0`.

Clearing denominators gives the equivalent statement over `ℂ(a)`.

### Proof

Write `F_k(a)=ζ(s+k,a)` and `q=exp(-2πis)`. For `c=(c_0,\ldots,c_N)∈ℂ^{N+1}` define

\[
 F_k^c(a)=F_k(a)+\sum_{n=0}^{N}(c_n-1)(a+n)^{-s-k}.
\]

The original ladder is `F^{(1,…,1)}`.

1. **Independent monodromy deformation.** Around `a=-n`, only the `n`th singular summand has
   monodromy. In the coordinate `a=-n+e^z`, analytic continuation under `z↦z+2πi` replaces
   `c_n` by `qc_n` and leaves every other `c_j` fixed. The identity theorem propagates the
   continued relation back to the upper half-plane. Iterating independently at the `N+1`
   branch points gives

   \[
     P(a;F^{(q^{m_0},\ldots,q^{m_N})}(a))=0
     \quad(m_0,\ldots,m_N∈\mathbb N).
   \]

2. **Infinite product grid.** Since `s∉ℚ`, the powers `{q^m:m≥0}` are pairwise distinct.
   For fixed `a`, the left side is a polynomial in `c_0,…,c_N` vanishing on a product of
   infinite sets. It therefore vanishes for every `c∈ℂ^{N+1}`.

3. **Vandermonde surjectivity.** The linear part of `c↦(F_k^c(a))_{k=0}^N` has matrix

   \[
     W_{k,n}=(a+n)^{-s-k}=(a+n)^{-s}\bigl((a+n)^{-1}\bigr)^k.
   \]

   This is a Vandermonde matrix in the distinct values `(a+n)^{-1}`, multiplied by a
   nonsingular diagonal matrix. Hence the affine map is onto `ℂ^{N+1}`.

Thus `P(a;y)=0` for every `y∈ℂ^{N+1}` and every upper-half-plane `a`. Every coefficient of
`P` vanishes on an open set, hence is the zero polynomial. Therefore `P=0`. ∎

## Theorem B — hypertranscendence of one Hurwitz function

Let

\[
 P\in\mathbb C[a][Y_0,\ldots,Y_N]
\]

and suppose

\[
 P\bigl(a;\zeta(s,a),\partial_a\zeta(s,a),\ldots,
              \partial_a^N\zeta(s,a)\bigr)=0
\]

throughout the upper half-plane. Substitute

\[
 \partial_a^k\zeta(s,a)=c_k\zeta(s+k,a),
 \qquad c_k=(-1)^k(s)_k\ne0.
\]

This applies an invertible diagonal automorphism to the variables of `P`. Theorem A kills the
transformed ladder relation, and reciprocal diagonal scaling then gives `P=0`. Therefore
`a↦ζ(s,a)` is hypertranscendental over `ℂ(a)`. ∎

## Positive rational boundary

For every nonintegral `s` with `Re s>1`, including rational nonintegers, the same jet/ladder
coordinate change transports the project's all-order quadratic ladder theorem to a positive
classification:

> The finite differential jet of `a↦ζ(s,a)` is algebraically independent through total degree
> two, at every differential order.

This is formalized as `HurwitzLadder.hzeta_quadratic_differential_independent`. For irrational
`s`, Theorem B subsumes it. For rational nonintegral `s`, it remains the strongest certified
arbitrary-order statement; higher polynomial degree is the residual value-relation problem.

## Lean certificate

The formal result uses the genuine series

`hzeta s a = ∑' n : ℕ, ((n : ℂ) + a) ^ (-s)`.

- `formal/GaloisForLFunctions/Hurwitz/LadderDeformation.lean`
  proves `hzeta_hasDerivAt`, `hzeta_deriv`, `hzeta_iteratedDeriv`, nonvanishing of the rising
  factorial, and the normalized inverse jet/shift relation.
- `formal/GaloisForLFunctions/Hurwitz/LadderDeformationBridge.lean`
  formalizes the one-branch monodromy move and its independent iteration over a finite grid.
- `formal/GaloisForLFunctions/Hurwitz/LadderIndependence.lean`
  proves grid vanishing, injectivity of the monodromy powers, Vandermonde surjectivity, and
  `HurwitzLadder.hurwitz_ladder_independence` with no degree bound.
- `formal/GaloisForLFunctions/Hurwitz/Hypertranscendence.lean`
  defines the diagonal jet-scaling automorphism and proves
  `HurwitzLadder.hzeta_hypertranscendental_in_shift`.
- `formal/GaloisForLFunctions/Hurwitz/QuadraticDifferentialIndependence.lean`
  proves the rational-noninteger degree-two companion theorem.

The hypertranscendence theorem has only the ordinary foundational dependencies
`[propext, Classical.choice, Quot.sound]`.

## Novelty audit

The novelty search separated four nearby bodies of work from the exact theorem.

1. The `a`-derivative identity is classical and explicitly recorded by
   [DLMF 25.11.17](https://dlmf.nist.gov/25.11.E17).
2. Ostrowski's Dirichlet-series theorem concerns the joint two-variable polylogarithmic
   function and algebraic partial differential equations, not algebraic independence of a
   fixed-`s` Hurwitz shift ladder; see the
   [English translation of the 1920 paper](https://arxiv.org/abs/2211.02088).
3. Lerch-zeta differential-difference operators and joint-variable structures do not state
   the fixed-`s`, one-variable theorem; see
   [Lagarias–Li, Lerch Zeta IV](https://arxiv.org/abs/1511.08116).
4. Searches through fractional-polylog monodromy, hyperlogarithm independence,
   Hurwitz value distribution, and formal infinite-order differential equations found no
   theorem asserting finite fixed-`s` ladder algebraic independence over `ℂ(a)` or the resulting
   shift-variable hypertranscendence.

The literature conclusion is necessarily evidence-relative: no exact parent theorem was found
in the primary-source audit. A specialist referee should still test the claim before public
priority language is used.

## Significance and publication score

**Score: 82/100.** This is not a score for the classical derivative formula or for the formal
transport alone. It scores the combined theorem package.

- **Novelty, 23/30:** the exact fixed-`s` arbitrary-degree theorem was not located; confidence is
  reduced because the monodromy ingredients are classical in flavor.
- **Mathematical depth, 24/30:** independent branch monodromies create a product grid, and a
  Vandermonde value map converts that grid into full algebraic independence.
- **Significance, 21/25:** a classical special function is proved hypertranscendental in a
  parameter where the derivative visibly escapes into a shifted family; this is a clean founding
  example of constraint rather than finite differential generation.
- **Verification, 14/15:** the arbitrary-degree theorem and its differential transport are
  paper-proved and Lean-certified without project axioms; one point is reserved for independent
  specialist novelty review.

The result clears the dual gate: it is neither a new presentation of the classical derivative
identity nor a technically correct but low-consequence corollary. It supplies a new exact
hypertranscendence theorem and a reusable monodromy–grid–Vandermonde proof mechanism.

## RHTower and parent-folder use

- **Parent Hurwitz gap closed.** `LadderDeformation.lean` previously had the shifted analytic
  family but not the exact derivative ladder. The new value relation identifies every rung with
  a normalized derivative of one base function.
- **Parent theorem strengthened.** `LadderIndependence.lean` is now consumed by a single-function
  hypertranscendence theorem rather than remaining only a multi-function statement.
- **Quadratic theorem reused.** `AllNHZeta.lean` now yields the rational-noninteger differential
  classification through the same invertible value transform.
- **RHTower audit.** Current RHTower modules do not consume the custom complex-shift `hzeta`, so
  this relation does not syntactically discharge an RHTower hypothesis. Its concrete reuse is in
  the parent `Hurwitz` and HGT layers. This is a positive ownership classification: the theorem
  belongs at the Hurwitz value interface, available for any future RHTower consumer importing it.

## Gates

- [x] exact classical value relation isolated and formalized at all orders
- [x] arbitrary-degree ladder independence proved on paper
- [x] arbitrary-degree ladder independence formalized in Lean
- [x] single-function hypertranscendence transported and formalized in Lean
- [x] rational-noninteger degree-two boundary retained and formalized
- [x] parent and RHTower consumer audit completed
- [x] primary-source novelty search found no exact parent theorem
- [x] publication score exceeds 75/100
- [ ] independent specialist priority review before public novelty claim
