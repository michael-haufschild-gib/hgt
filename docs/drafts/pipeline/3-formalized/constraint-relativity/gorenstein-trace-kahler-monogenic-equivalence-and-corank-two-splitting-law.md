# Gorenstein trace--Kähler monogenic equivalence and corank-two splitting law

- **ID:** `gorenstein-trace-kahler-monogenic-equivalence-and-corank-two-splitting-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / CLASSIFICATION / SOURCE--OBSERVER NONMETRICITY
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [NO RH CLAIM] [FORMALIZED IN LEAN]`
  `[CLASSICAL DIFFERENT/LCI PARENTS] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent field:** `../../1-in-progress/constraint-relativity/source-soldering-bivariant-law-geometry.md`.
- **Phase card:** `../../1-in-progress/constraint-relativity/defect-duality-phase-geometry.md`.

## Setup

Let `R` be a discrete valuation ring with uniformizer `a`, fraction field `K`, and infinite residue
field `k`. Let

\[
 A\subset O=R^N
 \tag{1}
\]

be finite-index `R`-order, so `A tensor_R K=K^N`. Coordinate trace defines trace-dual lattice

\[
 A^\sharp=\{x\in K^N:\operatorname{Tr}(xA)\subset R\},
 \qquad
 L=A^\sharp/A.
 \tag{2}
\]

Assume `A` is relative Gorenstein: `A^sharp` is invertible `A`-module.

## Theorem 1: trace--Kähler equality is exactly monogenicity

Following statements are equivalent:

1. `L\cong Omega_(A/R)` as `A`-modules;
2. `Omega_(A/R)` is cyclic as `A`-module;
3. `A` is monogenic over `R`: there exists `theta in A` with `A=R[theta]`.

Thus, within split relative-Gorenstein orders, there is no genuinely higher-corank extension of
monogenic trace--Kähler module equality.

### Proof that `(1)` implies `(2)`

Because `A` is finite over local ring `R`, it is semilocal. Every invertible module over semilocal
ring is free rank one. Hence

\[
 A^\sharp=uA
 \tag{3}
\]

for some `u in K^N`. Since `A subset uA`, quotient `L=uA/A` is cyclic. If
`L\cong Omega_(A/R)`, then `Omega_(A/R)` is cyclic. QED.

### Proof that `(2)` implies `(3)`

Put

\[
 B=A/aA.
 \tag{4}
\]

Base change gives

\[
 \Omega_{B/k}\cong\Omega_{A/R}\otimes_A B,
 \tag{5}
\]

so `Omega_(B/k)` is cyclic. Ring `B` is finite-dimensional over `k`, hence product of local Artin
`k`-algebras `B_i`. Every residue field of `B_i` is `k`. Indeed `O` is finite integral over `A`.
For each maximal `p subset A` containing `a`, lying-over gives maximal `q subset O` above `p`.
Since `O=R^N`, `O/q\cong k`. Induced injection `A/p->O/q` and diagonal `k subset A/p` force
`A/p\cong k`.

For maximal ideal `m_i` of `B_i`, cotangent fibre is

\[
 \Omega_{B_i/k}\otimes_{B_i}k\cong m_i/m_i^2.
 \tag{6}
\]

Cyclicity forces `dim_k(m_i/m_i^2)<=1`. By Nakayama, `m_i` is principal. If `m_i=(t_i)`, its
nilpotence and `B_i=k+m_i` recursively imply `B_i=k[t_i]`. Kernel of `k[T]->B_i` has radical
`(T)`; because `k[T]` is a PID it equals `(T^(n_i))` for some `n_i>=1` (including `n_i=1` when
`m_i=0`). Hence

\[
 B_i\cong k[T]/(T^{n_i})
 \tag{7}
\]

for some `n_i>=1`.

Choose pairwise distinct `lambda_i in k`, possible because `k` is infinite. Element whose `i`-th
component is `lambda_i+t_i` monogenerates product `B`: polynomials
`(T-lambda_i)^(n_i)` are pairwise coprime, so Chinese remainder theorem gives

\[
 B\cong k[T]/\prod_i(T-\lambda_i)^{n_i}.
 \tag{8}
\]

Lift generator to `theta in A`. Element `theta` is integral over `R`, hence `R[theta]` is finite.
Equation `(8)` gives `A=R[theta]+aA`, so finite module `M=A/R[theta]` satisfies `M=aM`; Nakayama
gives `M=0`. Hence

\[
 A=R[\theta].
 \tag{9}
\]

QED.

### Proof that `(3)` implies `(1)`

Let `n=rank_R A`. Characteristic polynomial `P_theta` is monic degree `n` and kills `theta`.
Induced surjection `R[T]/(P_theta)->A` is between free `R`-modules of rank `n`, hence isomorphism.
Write

\[
 A\cong R[T]/(P),
 \qquad \theta=T\bmod P,
 \tag{10}
\]

with monic `P` and separable generic fibre. Standard monogenic formulas give

\[
 A^\sharp=(P'(\theta))^{-1}A,
 \qquad
 \Omega_{A/R}\cong A/(P'(\theta))\,d\theta.
 \tag{11}
\]

Multiplication by `P'(theta)` induces

\[
 A^\sharp/A\xrightarrow{\sim}A/(P'(\theta)),
 \tag{12}
\]

and `(11)--(12)` prove `L\cong\Omega_{A/R}`. QED.

## Theorem 2: codimension-two complete intersection keeps determinant but splits module

Let `R=C[[a]]` and

\[
 B=R[x]/(x(x-a)),
 \qquad
 A=B\otimes_RB
 =R[x,y]/(x(x-a),y(y-a)).
 \tag{13}
\]

Then `A` is split finite flat rank four, codimension-two complete intersection, relative
Gorenstein, with normalization `R^4`. Put

\[
 d_x=2x-a,
 \qquad d_y=2y-a.
 \tag{14}
\]

Trace-dual lattice and cotangent module satisfy

\[
 A^\sharp=(d_xd_y)^{-1}A,
 \tag{15}
\]

\[
 \boxed{
 L=A^\sharp/A
 \cong
 R/(a^2)\oplus R/(a^2)\oplus R/(a^4),}
 \tag{16}
\]

while

\[
 \boxed{
 \Omega_{A/R}
 \cong
 \bigl(R/(a^2)\bigr)^4.}
 \tag{17}
\]

They have same support and total length `8`, and Kähler/Dedekind different determinant is same
principal element `d_xd_y`, but modules are not isomorphic.

### Proof

For rank-two factor `B`, multiplication by `d_x=2x-a` in basis `(1,x)` has matrix

\[
 \begin{pmatrix}-a&0\\2&a\end{pmatrix},
 \tag{18}
\]

whose Smith form is `diag(1,a^2)`. Same holds for `d_y`.

For `B`, monogenic formula gives `B^sharp=d_x^(-1)B`. Under `A=B tensor_R B`, multiplication
trace is tensor product of traces. Tensoring dual bases therefore gives
`A^sharp=B^sharp tensor_R B^sharp=(d_xd_y)^(-1)A`, proving `(15)`. Multiplication by `d_xd_y` on
`A=B tensor_R B` is Kronecker product of two matrices `(18)`, hence has Smith form

\[
 \operatorname{diag}(1,a^2,a^2,a^4).
 \tag{19}
\]

Multiplication identifies `A^sharp/A` with `A/(d_xd_y)`, so `(19)` gives `(16)`.

For cotangent module, two independent hypersurface relations give

\[
 \Omega_{A/R}
 \cong A/(d_x)\,dx\oplus A/(d_y)\,dy.
 \tag{20}
\]

As `R`-modules, `B/(d_x)\cong R/(a^2)`. Tensor with other free rank-two factor shows each
summand in `(20)` is `(R/(a^2))^2`, proving `(17)`. Both modules have length `8`; their largest
Smith exponents `4` and `2` differ. QED.

## Exact structural consequence

Even finite-flat lci/Gorenstein geometry synchronizes only determinant-level shadows. Put

\[
 \omega_{A/R}=A^\sharp,
 \qquad
 \tau:A\hookrightarrow\omega_{A/R},
 \qquad
 \mathfrak D=\operatorname{Fitt}_0^A\Omega_{A/R}.
 \tag{21}
\]

Assume `A` is relatively Gorenstein and Kähler different
`D_K=Fitt_0^A(Omega_(A/R))` equals Dedekind different `D_D`; write common ideal `D` and put
`Q=A/D`. Locally choose `omega=A eta` and write trace section `tau=delta eta`. Then
`D_D=(delta)` and `A tau=D omega`, so canonically

\[
 L=\omega_{A/R}/A\tau
 =\omega_{A/R}/D\omega_{A/R}
 \cong\omega_{A/R}\otimes_AQ,
 \tag{22}
\]

whereas `D_K subset Ann_A(Omega_(A/R))`, so `Omega_(A/R)` is generally different `Q`-module. Thus:

- `(omega,tau)` is oriented trace/duality shadow;
- cotangent complex and `Omega=H_0(L_(A/R))` are directional response shadow;
- monogenicity is exact corank-one locus where these shadows collapse to same module.

Universal source--observer geometry must retain at least

\[
 \boxed{(O/A,\ \omega_{A/R},\ \tau,\ \mathbb L_{A/R})}
 \tag{23}
\]

rather than one module called “geometry.”

## Conjecture--attack loops

1. **Gorenstein implies `A^sharp/A\cong\Omega`.** False by `(13)--(17)`.
2. **Complete intersection repairs equality.** False by same example.
3. **Equality of Kähler and Dedekind differents repairs module equality.** False: different and
   total length agree in example, Smith partitions do not.
4. **Cyclic cotangent is weaker than monogenicity.** False in split DVR setting with infinite
   residue: Theorem 1 proves equivalence.
5. **One determinant/Fitting scalar is complete local law.** False by `(16)--(17)`.
6. **Surviving conjecture:** nonmonogenic law geometry is metric-affine: trace duality and
   infinitesimal response are independent fields coupled only by source-derived constitutive map.

Infinite residue hypothesis is essential. If `k=F_q` and `A=R^N` with `N>q`, then `L=Omega=0`
but `A` is not monogenic: generator of `R^N` would require `N` pairwise distinct residues.

## RH and hypertranscendence boundary

This theorem does not select critical line. It explains why routes agreeing on discriminant,
support, reflection, and total defect can remain incompatible at directional level. Any RH argument
using monogenic comparison as universal principle is confined to corank-one locus. Higher arithmetic
source must construct both trace-dual and cotangent data before scalarization.

For hypertranscendental towers, finite cotangent module should be replaced by full source-ordered
cotangent complex/resolution history. No theorem here identifies that history with Xi source or
physical time.

## Novelty boundary

Monogenic different formula, Gorenstein duality, complete-intersection equality of differents,
Kähler modules, cotangent homology, and generator schemes are classical. Primary parents checked:

- https://arxiv.org/abs/math/9909192
- https://arxiv.org/abs/2204.10427
- https://arxiv.org/abs/2205.04620
- https://arxiv.org/abs/2305.10022
- https://arxiv.org/abs/2604.01992
- https://pub.math.leidenuniv.nl/~desmit/papers/ja1995-desmit.pdf
- https://par.nsf.gov/servlets/purl/10282767

Likely new-to-corpus residue is exact equivalence in Theorem 1 plus explicit corank-two equal-energy
Smith splitting `(16)--(17)`. This is a bridge/classification theorem, not established new field.
Priority remains unverified.

## Lean-return note

Formalized; see `gorenstein-trace-kahler-monogenic-equivalence-and-corank-two-splitting-law-formalized.md`.  The note below was written before that work and is kept for the record: it is no longer a restriction.

> No Lean work authorized. Later formalization should split into finite semilocal algebra lemma,
> cyclic cotangent/embedding-dimension lemma, CRT monogeneration, Nakayama lift, and explicit `4x4`
> Smith computations. Search current corpus before choosing files.

## Gates

- [x] dependency-closed paper proof
- [x] exact classification with both directions
- [x] lci/Gorenstein hostile counterexample
- [x] positive surviving four-component ontology
- [ ] independent hostile proof audit
- [ ] specialist novelty review
- [x] Lean formalization

## Log

- 2026-08-08 -- proved trace--Kähler equality iff monogenic under split relative-Gorenstein DVR
  hypotheses; codimension-two tensor-square shows determinant equality without module equality.
