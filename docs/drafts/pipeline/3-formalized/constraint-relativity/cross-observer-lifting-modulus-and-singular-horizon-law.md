# Cross-observer lifting modulus and singular horizon law

- **ID:** `cross-observer-lifting-modulus-and-singular-horizon-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [BRIDGE] [LEAN COMPLETE] [NO SORRY] [NO NEW AXIOMS]`
- **Novelty:** inverse-modulus and conditioning mathematics are parent theory. New value is exact
  placement between corpus recurrence, approximate QEC, cofinal observers, and law-deformation
  descent. No independent new-field claim.

## Goal

Measure how much separation in one realization can hide inside an arbitrarily small ball of a
second realization. Exact kernels see only scale zero; recurrence and holographic reconstruction
require all scales and cofinal conditioning.

## Definition

Let `S` be a set with maps

\[
 q:S\to B,
 \qquad
 p:S\to I
\]

to metric spaces. Define the cross-observer lifting modulus

\[
 \Lambda_{p\mid q}(\varepsilon)
 =
 \sup\left\{
 d_I(p(x),p(y)):
 d_B(q(x),q(y))\le\varepsilon
 \right\}.
 \tag{1}
\]

It is monotone in \(\varepsilon\). Its zero-scale value measures exact fibre ambiguity; its small
positive-scale behavior measures conditioning.

## Theorem 1: factorization, stability, and composition

Assume `S` is compact, `B` and `I` are compact metric spaces, and `p,q` are continuous. Replace
`B,I` by the compact images of `q,p`.

1. There is a unique map `r:q(S)->p(S)` with `p=r q` if and only if
   \[
   \Lambda_{p\mid q}(0)=0.
   \tag{2}
   \]
   In that case `r` is continuous.
2. Equivalently,
   \[
   p=rq\text{ continuously}
   \quad\Longleftrightarrow\quad
   \lim_{\varepsilon\downarrow0}\Lambda_{p\mid q}(\varepsilon)=0.
   \tag{3}
   \]
3. Every source trajectory `x_t` satisfies
   \[
   d_I(p(x_t),p(x_0))
   \le
   \Lambda_{p\mid q}\!\left(d_B(q(x_t),q(x_0))\right).
   \tag{4}
   \]
4. For a third metric realization `r:S->C`,
   \[
   \Lambda_{r\mid q}(\varepsilon)
   \le
   \Lambda_{r\mid p}\!\left(\Lambda_{p\mid q}(\varepsilon)\right).
   \tag{5}
   \]
5. If `f:B->B'` is `1`-Lipschitz, then
   \[
   \Lambda_{p\mid f q}(\varepsilon)
   \ge
   \Lambda_{p\mid q}(\varepsilon).
   \tag{6}
   \]

### Proof

Equation `(2)` says exactly that `p` is constant on every fibre of `q`, so the unique set map
`r(q(x))=p(x)` exists. A continuous surjection from compact `S` to Hausdorff `q(S)` is a quotient
map; hence `r` is continuous. Uniform continuity of `r` gives the forward implication in `(3)`.
The reverse implication gives `(2)` by monotonicity and then the preceding factorization.

Equation `(4)` is one of the pairs over which `(1)` takes its supremum. For `(5)`, any pair with
`q`-distance at most \(\varepsilon\) has `p`-distance at most
\(\Lambda_{p\mid q}(\varepsilon)\); applying the second modulus gives the result. For `(6)`, every pair
admissible for the right-hand supremum is admissible for the left because `f` is `1`-Lipschitz.
QED.

## Theorem 2: exact finite observers have a resolution floor

If `S` and `B` are finite and

\[
 \sigma_q
 =\min_{q(x)\ne q(y)}d_B(q(x),q(y))>0,
 \tag{7}
\]

then for \(0\le\varepsilon<\sigma_q\),

\[
 \Lambda_{p\mid q}(\varepsilon)=\Lambda_{p\mid q}(0).
 \tag{8}
\]

### Proof

Below \(\sigma_q\), the inequality \(d_B(q(x),q(y))\le\varepsilon\) forces `q(x)=q(y)`. Thus the
admissible pair set in `(1)` is exactly the zero-scale pair set. QED.

Consequently one fixed finite complete observer cannot hide an unbounded interior separation at
sufficiently accurate recurrence. Escape requires growing/cofinal dimension, singular
conditioning, noninjectivity, unbounded target diameter, or history dependence.

## Theorem 3: linear deformation-descent condition number

Let `E,B` be finite-dimensional Hilbert spaces and `J:E->B` linear. For `p=id_E`, `q=J`, define
`Lambda` on all of `E` by `(1)`.

- If `ker J` is nonzero, then
  \[
  \Lambda_{id\mid J}(\varepsilon)=\infty
  \qquad(\varepsilon\ge0).
  \tag{9}
  \]
- If `J` is injective and `sigma_min(J)>0` is its smallest singular value, then
  \[
  \boxed{
  \Lambda_{id\mid J}(\varepsilon)
  ={\varepsilon\over\sigma_{\min}(J)}.}
  \tag{10}
  \]

More generally, for a linear functional `ell:E->R`,

\[
 \Lambda_{\ell\mid J}(\varepsilon)
 =\varepsilon\,\|\ell J^\dagger\|
 \tag{11}
\]

when `J` is injective, with `J^dagger` the inverse on `ran J`.

### Proof

If \(0\ne v\in\ker J\), every pair `(0,tv)` has zero `J`-distance and unbounded source distance as
`t` grows, proving `(9)`. If `J` is injective,

\[
 \|Jv\|\ge\sigma_{\min}(J)\|v\|,
\]

so `(1)` is at most \(\varepsilon/\sigma_{\min}\). Equality is achieved on a unit right singular
vector for \(\sigma_{\min}\), scaled by \(\varepsilon/\sigma_{\min}\). For `(11)`, write `w=Jv`
in `ran J`; the supremum of \(|\ell J^\dagger w|\) over \(\|w\|\le\varepsilon\) is the operator
norm stated. QED.

This joins exact deformation obstruction and metric horizon:

```text
kernel appears                   -> exact descent fails
injective but sigma_min -> 0     -> exact descent survives, uniform descent fails
uniform sigma_min > 0            -> quantitatively stable descent
```

## Cofinal horizon invariant

For a sequence `(p_n,q_n)` define

\[
 \mathfrak H_{p\mid q}
 =\lim_{\varepsilon\downarrow0}
   \limsup_{n\to\infty}
   \Lambda_{p_n\mid q_n}(\varepsilon),
 \tag{12}
\]

when the extended-real limit exists; monotonicity guarantees it as an infimum over
\(\varepsilon>0\).

- `mathfrak H=0`: uniform cofinal reconstruction.
- `0<mathfrak H<infinity`: finite residual lifting horizon.
- `mathfrak H=infinity`: arbitrarily large target separation hides at arbitrarily fine source
  resolution.

## Exact counterexample: recurrence with singular decoding

Let

\[
 S_n=\{0,\ldots,n\},
 \qquad
 p_n(k)=k,
 \qquad
 q_n(k)=\exp\!\left({2\pi i k\over n+1/n}\right).
 \tag{13}
\]

Every `q_n` is injective, so its exact kernel pair is diagonal and every `p_n` factors through
`q_n`. Nevertheless

\[
 |q_n(n)-q_n(0)|
 =2\sin{\pi\over n^2+1}\longrightarrow0,
 \qquad
 |p_n(n)-p_n(0)|=n.
 \tag{14}
\]

Hence

\[
 \Lambda_{p_n\mid q_n}\!\left(2\sin{\pi\over n^2+1}\right)\ge n,
 \qquad
 \mathfrak H_{p\mid q}=\infty.
 \tag{15}
\]

Every exact decoder `r_n:q_n(S_n)->S_n` therefore obeys

\[
 \operatorname{Lip}(r_n)
 \ge {n\over2\sin(\pi/(n^2+1))}
 \sim {n^3\over2\pi}.
 \tag{16}
\]

This example has no hidden exact sector and no nontrivial deck transformation. Its horizon is
pure loss of uniform conditioning.

## Physical and arithmetic consequences

For calibrated boundary process `q_n` and independently defined bulk length/complexity `p_n`, a
recurrence pair satisfies

\[
 |\Delta L_n|
 \le\Lambda_{p_n\mid q_n}(\delta_n),
 \qquad
 \delta_n=d_\diamond(q_n(t_n),q_n(0)).
 \tag{17}
\]

If the decoder is `K_n`-Lipschitz, then

\[
 \boxed{K_n\ge {|\Delta L_n|\over\delta_n}.}
 \tag{18}
\]

Thus a long interior at increasingly accurate boundary recurrence requires diverging decoder
conditioning. Exact recurrence of a complete endpoint observer forces zero endpoint-defined bulk
separation.

For the RH programme, this theorem warns that exact route coexistence and exact conservativity
do not control source-law deformation uniformly. It does not select the critical line. A useful
source theorem would have to control the condition modulus of the literal arithmetic deformation
map, not only its kernel or support.

## No-go closure

- **Exact killing mechanism:** exact kernel pairs and finite ranks record only
  `Lambda(0)`; they cannot control small positive scales or cofinal conditioning.
- **Strongest positive survivor:** compositional lifting modulus and exact singular-decoder law.
- **New insight:** horizon can occur through loss of uniform descent even when every finite
  observer is faithful and exact.
- **Status:** paper proof closed. Abstract mathematics is a bridge, not cleared novelty.

## Lean-return note

Formalized; see `cross-observer-lifting-modulus-and-singular-horizon-law-formalized.md`.  The
three suggested groups are separate sections of one module: zero-scale factorization,
finite-resolution floor, and the finite-dimensional singular-value law.

## Log

- 2026-08-08 — extracted from holographic recurrence hostile audit.
