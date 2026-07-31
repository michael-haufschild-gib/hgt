# Adelic Kummer nuclear test scale

- **ID:** `deninger-adelic-kummer-nuclear-test-scale`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE`
- **Parent:** `deninger-adelic-kummer-gelfand-triple`
- **Statement:** logarithmic Kummer functions admit a canonical nuclear
  locally constant test-space closure densely embedded in the mixed
  Banach and adelic Hilbert completions.

## Setup

Let \(Y\) be the Allcock--Vaaler space.  It is a second-countable,
zero-dimensional, locally compact space, decomposed into compact-open
place components.  Let
\[
 \mathcal D(Y)=C_c^{\mathrm{lc}}(Y,\mathbb R)
\]
with its usual locally constant test-function topology.

Choose an increasing cofinal tower of finite Galois extensions of
\(\mathbb Q\) and an increasing exhaustion of rational places.  Let
\(\mathcal D_m\) be the finite-dimensional space of functions supported
on the first \(m\) place components and constant on the clopen
partitions induced by the \(m\)-th field.  Then
\[
 \mathcal D(Y)=\underset{m}{\operatorname{ind\,lim}}\mathcal D_m.   \tag{1}
\]
The topology is independent of the chosen cofinal exhaustion.

Let \(\mathcal F_{\mathbb R}\) be the real span of logarithmic Kummer
functions and define
\[
 \mathcal S_{\mathrm{Kum}}
 =\overline{\mathcal F_{\mathbb R}}^{\,\mathcal D(Y)}.              \tag{2}
\]

## Theorem

`[PROVED HERE] [DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE]`

The space \(\mathcal D(Y)\) is a complete nuclear LF space and
\(\mathcal S_{\mathrm{Kum}}\) is a closed nuclear subspace.  There is a
dense continuous scale
\[
 \mathcal S_{\mathrm{Kum}}
 \longhookrightarrow
 E_{\mathrm{Kum}}
 \longhookrightarrow
 H_{\mathrm{Kum}}=L^2(Y,\lambda),                                  \tag{3}
\]
and hence continuous dual injections
\[
 H_{\mathrm{Kum}}
 \longhookrightarrow
 E_{\mathrm{Kum}}'
 \longhookrightarrow
 \mathcal S_{\mathrm{Kum}}'.                                      \tag{4}
\]
Together `(3)`--`(4)` form a source-native nuclear
test/Banach/Hilbert/distribution scale.

The integral
\[
 I(f)=\int_Yf\,d\lambda
\]
is continuous on \(\mathcal D(Y)\), and
\[
 \mathcal S_{\mathrm{Kum}}\subseteq\ker I.                          \tag{5}
\]
Galois maps, normalized field-norm projections, and Tate-twisted power
maps act continuously on the entire scale and preserve `(5)`.

For the logarithmic suspension coordinate \(t=\log u\), the completed
projective tensor product
\[
 \mathcal S_{\mathrm{susp}}
 =
 \mathcal S_{\mathrm{Kum}}
   \widehat\otimes_\pi C_c^\infty(\mathbb R)                         \tag{6}
\]
is nuclear.  Translation in \(t\), the rational shifts
\(t\mapsto t-\log q\), and convolution by a compactly supported smooth
test function act continuously on `(6)`.

## Proof

Each \(\mathcal D_m\) is finite-dimensional and nuclear.  The
inclusions in `(1)` have closed image, so `(1)` is a strict countable
inductive limit of finite-dimensional spaces.  Standard LF-space
theory makes \(\mathcal D(Y)\) complete and nuclear.  Closed subspaces
of nuclear locally convex spaces are nuclear, proving the first claim
for `(2)`.

The inclusions
\[
 \mathcal D(Y)\longrightarrow L^1(Y,\lambda)\cap L^2(Y,\lambda)
\]
are continuous: on each finite-dimensional stage every norm is
continuous, and the LF topology is final.  They restrict to
\(\mathcal S_{\mathrm{Kum}}\) and factor through the mixed completion
\(E_{\mathrm{Kum}}\).  Their images contain
\(\mathcal F_{\mathbb R}\).  By definition this span is dense in
\(E_{\mathrm{Kum}}\), and by Allcock--Vaaler it is dense in \(L^2\);
therefore the arrows in `(3)` have dense image.  The dual arrows in
`(4)` follow from the \(L^2\) pairing and restriction of continuous
functionals.

The integral is continuous on every finite-dimensional stage and hence
on the LF limit.  It vanishes on logarithmic Kummer functions by the
product formula, so it vanishes on their closure, proving `(5)`.
Galois and power maps permute/refine finite clopen stages.  Fili--Miner
field-norm projections are conditional expectations onto such stages.
Thus all stated operations are continuous and preserve the Kummer
span and its closure.

The standard test-function space \(C_c^\infty(\mathbb R)\) is nuclear,
and completed projective tensor products of nuclear locally convex
spaces are nuclear.  Translation and convolution are continuous on the
second factor, proving the suspension corollary `(6)`.

## Consequence for Deninger's program

The source coefficient now has separate canonical layers:

- nuclear locally constant test topology for distributions;
- its nuclear tensor with the smooth suspension test topology;
- mixed \(L^1/L^2\) topology for product formula and residue closure;
- \(L^2\) Hilbert topology for positive Kummer energy.

This is enough to type Deninger's desired distributional trace on a
source test space.  It is not enough to prove that a
test-function-smoothed flow operator is nuclear or trace class.  That
requires the uniform finite-stage estimates in
`DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER`.

## Gates

- [x] complete paper proof
- [ ] Lean formalization of strict LF nuclearity and dense embeddings
- [ ] sheafwise extension from Kummer functions to the full
  Steinberg-corrected Milnor coefficient and real orientation

## References

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*: https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner, *Orthogonal decomposition of the space
  of algebraic numbers and Lehmer's problem*:
  https://arxiv.org/abs/0911.1975

## Log

- 2026-07-26 — Extracted the canonical nuclear test layer from the
  locally constant place-space geometry.
