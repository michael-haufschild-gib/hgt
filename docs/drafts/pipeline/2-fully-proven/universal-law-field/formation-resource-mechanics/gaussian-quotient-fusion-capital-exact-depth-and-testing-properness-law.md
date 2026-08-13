# Gaussian quotient--fusion capital, exact depth, and testing-properness law

- **ID:** ULF-FRM-3
- **Stage:** 2-fully-proven
- **Type:** OPERATIONALIZATION OF QUOTIENT--FUSION GENESIS + EXACT FORMATION CLASSIFICATION
- **Parent:** Formation Resource Mechanics; Source-Coherent Synchronization Mechanics
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL FINITE THEOREM]`
  `[EXACT BLACKWELL CLASSIFICATION] [GLOBAL FORMATION PROPERNESS]`
  `[HYPOTHESIS-TESTING PREDICTION] [CLASSICAL GAUSSIAN/BLACKWELL PARENTS]`
  `[LEAN PENDING] [NOT RH]`
- **Statement:** Quotient--fusion genesis energy is exactly signal norm, Bhattacharyya capital,
  Jeffreys work, and testing exponent of a canonical Gaussian packet. A Gaussian source of finite
  signal budget forms `d` independent genesis packets exactly when its budget is at least `d` times
  genesis. Hence cofinal formation forces source synchronization, and a trivial synchronization
  equalizer forces neutral source displacement.

## 1. Coordinate-free formation packet

Let `I` be finite. For each `i in I`, let `H_i` be a finite-dimensional real Hilbert space,
`x_i in H_i`, and let `K` be a finite-dimensional real Hilbert space with linear map

\[
 A_i:K\longrightarrow H_i.
 \tag{GQF.1}
\]

Put `H=direct-sum_i H_i` and `A(u)=(A_i u)_i`. Let `z_i` be orthogonal projection of `x_i`
onto `ran A_i`, and put

\[
 \ell=(x_i-z_i)_i.
 \tag{GQF.2}
\]

Choose a minimizer `u_*` of

\[
 u\longmapsto\sum_i\|z_i-A_i u\|^2
 \tag{GQF.3}
\]

and define **genesis signal**

\[
 g=(z_i-A_i u_*)_i.
 \tag{GQF.4}
\]

Finite dimensionality guarantees a minimizer. Its image `Au_*` is unique even when `u_*` is not,
so `g` is canonical. Define

\[
 E_{\rm sep}=\|\ell\|^2,
 \qquad Q=\|g\|^2.
 \tag{GQF.5}
\]

Coordinate-free quotient--fusion gives

\[
 E_{\rm shared}=E_{\rm sep}+Q,
 \qquad Q=0\iff \exists u\;\forall i\;A_i u=z_i.
 \tag{GQF.6}
\]

For finite-dimensional real Hilbert `V` and `v in V`, write

\[
 \Gamma(v)=\bigl(V;N(0,I_V),N(v,I_V)\bigr)
 \tag{GQF.7}
\]

for binary unit-covariance Gaussian experiment. Formation means one Markov kernel working for both
marks.

## 2. Exact inherited/genesis factorization

### Theorem 2.1 -- quotient--fusion is Gaussian experiment factorization

The subspaces

\[
 L=\bigoplus_i(\operatorname{ran}A_i)^\perp,
 \qquad R=\bigoplus_i\operatorname{ran}A_i
 \tag{GQF.8}
\]

are orthogonal, `ell in L`, and `g in R`. Under `H=L direct-sum R`,

\[
 \boxed{\Gamma(\ell+g)\cong\Gamma(\ell)\otimes\Gamma(g).}
 \tag{GQF.9}
\]

Consequently

\[
 \boxed{
 A\bigl(\Gamma(\ell+g)\bigr)
 =A\bigl(\Gamma(\ell)\bigr)A\bigl(\Gamma(g)\bigr)
 =\exp\!\left(-{E_{\rm sep}+Q\over8}\right).}
 \tag{GQF.10}
\]

Genesis packet alone satisfies

\[
 \boxed{
 C_H(\Gamma(g))={Q\over8},\qquad
 D_0(\Gamma(g))=D_1(\Gamma(g))={Q\over2},\qquad
 J(\Gamma(g))=Q.}
 \tag{GQF.11}
\]

For `0<alpha<1`, its Rényi capital is

\[
 \boxed{C_\alpha(\Gamma(g))={\alpha(1-\alpha)Q\over2}.}
 \tag{GQF.12}
\]

Here `D_0,D_1` are two directed KL divergences between marked laws.

#### Proof

By construction, `x_i-z_i` is perpendicular to `ran A_i`, while both `z_i` and `A_i u_*`
belong to `ran A_i`. Hence `ell perpendicular g`. Gaussian measure factorization over an
orthogonal direct sum gives `(GQF.9)`. Direct completion of square gives, for any `v`,

\[
 \int\sqrt{dN(0,I)dN(v,I)}=e^{-\|v\|^2/8},
 \tag{GQF.13}
\]

\[
 D(N(0,I)\Vert N(v,I))
 =D(N(v,I)\Vert N(0,I))={\|v\|^2\over2},
 \tag{GQF.14}
\]

and

\[
 \int (dN(0,I))^\alpha(dN(v,I))^{1-\alpha}
 =e^{-\alpha(1-\alpha)\|v\|^2/2}.
 \tag{GQF.15}
\]

Use `||ell+g||^2=||ell||^2+||g||^2`. QED.

Equation is stronger than positivity of a Schur complement: it exhibits exact independent
experiment whose information is quotient--fusion genesis.

## 3. Exact Gaussian Blackwell order

For `b>=0`, let `G_b=Gamma(sqrt b)` be one-dimensional source Gaussian experiment. For
`m in R^n`, let `Gamma(m)` denote `n`-dimensional target experiment.

### Theorem 3.1 -- signal norm completely classifies Gaussian formation

There exists one Markov kernel

\[
 G_b\longrightarrow\Gamma(m)
 \tag{GQF.16}
\]

simultaneously carrying both marked laws iff

\[
 \boxed{b\ge\|m\|^2.}
 \tag{GQF.17}
\]

#### Proof

Necessity follows from KL data processing:

\[
 {b\over2}\ge {\|m\|^2\over2}.
\]

For sufficiency, `b=0` forces `m=0`; ignore input and draw standard Gaussian. Assume `b>0`. Put

\[
 a={m\over\sqrt b},
 \qquad \Sigma=I_n-aa^*.
 \tag{GQF.18}
\]

Condition `(GQF.17)` says `||a||<=1`, hence `Sigma` is positive semidefinite. Given source sample
`X`, independently draw `Z~N(0,Sigma)` and output

\[
 Y=aX+Z.
 \tag{GQF.19}
\]

Under first mark, `X~N(0,1)`, so `Y~N(0,aa^*+Sigma)=N(0,I_n)`. Under second mark,
`X~N(sqrt b,1)`, so `Y~N(m,I_n)`. Same kernel works for both marks. QED.

Thus scalar information bound merely necessary for general experiments is complete on Gaussian
shift chain.

### Corollary 3.2 -- exact independent genesis depth

Let `Q=||g||^2`. Fixed Gaussian source `G_b` forms `d` independent copies of `Gamma(g)` exactly
when

\[
 \boxed{b\ge dQ.}
 \tag{GQF.20}
\]

If `Q>0`, exact maximum depth is

\[
 \boxed{d_{\max}=\left\lfloor {b\over Q}\right\rfloor.}
 \tag{GQF.21}
\]

If `Q=0`, every depth is formable by ignoring input.

#### Proof

Product of `d` unit-covariance Gaussian shifts is Gaussian shift with signal `(g,...,g)`, whose
squared norm is `dQ`. Apply Theorem 3.1. QED.

## 4. Global formation properness and selection

### Theorem 4.1 -- cofinal genesis formation forces synchronization

Fix finite `b`. If `G_b` forms `Gamma(g)^tensor d` for arbitrarily large `d`, then

\[
 \boxed{Q=0,}
 \tag{GQF.22}
\]

equivalently

\[
 \boxed{\exists u\in K\;\forall i\in I,quad A_i u=z_i.}
 \tag{GQF.23}
\]

Conversely, `(GQF.23)` makes genesis packet neutral and formable at every depth.

#### Proof

If `Q>0`, `(GQF.20)` bounds `d` by `b/Q`. Thus unbounded depth forces `Q=0`. Zero
classification in quotient--fusion theorem gives `(GQF.23)`. Converse is immediate. QED.

### Corollary 4.2 -- exact equalizer-selection interface

Suppose vectors `x_i` arise from one source displacement `v in V` through linear response maps,
and sourced synchronization equations have trivial equalizer:

\[
 Q(v)=0\quad\Longrightarrow\quad v=0.
 \tag{GQF.24}
\]

If one fixed finite-capital Gaussian source forms genesis packet of `v` at arbitrarily large depth,
then

\[
 \boxed{v=0.}
 \tag{GQF.25}
\]

The logic is exact:

\[
 \boxed{
 \text{fixed source}
 +\text{cofinal source-coherent formation}
 +\text{trivial synchronization equalizer}
 \Longrightarrow\text{neutral displacement}.}
 \tag{GQF.26}
\]

This is global formation/properness theorem missing from finite quotient--fusion law. It proves
vanishing from unbounded operational production by one fixed finite source.

## 5. Fourth-organ prediction: exact testing law

Give two marks equal prior. Let `P_e(d)` be optimal Bayes error for distinguishing laws of
`Gamma(g)^tensor d`.

### Theorem 5.1 -- genesis determines complete Gaussian testing curve

\[
 \boxed{P_e(d)=\Phi\!\left(-{\sqrt{dQ}\over2}\right),}
 \tag{GQF.27}
\]

where `Phi` is standard normal distribution function. Consequently

\[
 \boxed{-\lim_{d\to\infty}{1\over d}\log P_e(d)={Q\over8}.}
 \tag{GQF.28}
\]

Exponent equals Bhattacharyya formation capital from `(GQF.11)`.

#### Proof

Log-likelihood ratio of `N(0,I)` against `N(m,I)` is

\[
 \langle m,Y\rangle-{\|m\|^2\over2}.
\]

Equal-prior optimum compares this with zero. Under first mark, `<m,Y>/||m||` is standard normal;
under second it is standard normal shifted by `||m||`. Both errors equal
`Phi(-||m||/2)`. For `d` copies, `||m||=sqrt(dQ)`. Standard Gaussian tail asymptotic gives
`(GQF.28)`. QED.

Thus quotient--fusion genesis predicts complete operational curve in a fourth organ--binary
hypothesis testing--not another quadratic representation of same Schur complement.

## 6. Functional-equation and recovery neutrality

Let `U_i:H_i->H_i` and `V:K->K` be orthogonal isomorphisms such that

\[
 U_iA_i=A_iV.
 \tag{GQF.29}
\]

Let `Ux=(U_ix_i)_i`. Projections, common minimizer image, and genesis transform equivariantly:

\[
 z(Ux)=Uz(x),\qquad g(Ux)=Ug(x).
 \tag{GQF.30}
\]

Hence

\[
 \boxed{Q(Ux)=Q(x).}
 \tag{GQF.31}
\]

Gaussian pushforward by `U` is experiment isomorphism

\[
 \Gamma(g(x))\cong\Gamma(g(Ux)),
 \tag{GQF.32}
\]

so every capital, exact depth, and testing value above is unchanged. Orthogonal
functional-equation involution is information-neutral.

More generally, if packet statistic and one common recovery kernel make two descriptions
Blackwell-equivalent, formation feasibility in either direction and every quantity in
`(GQF.10)--(GQF.28)` agree. Recovery can expose genesis packet but cannot finance extra copy.

#### Proof

Equation `(GQF.29)` carries `ran A_i` to itself, so orthogonal projections commute with `U_i`.
Replacing `u` by `V^-1 u` in `(GQF.3)` proves equivariance of minimizer image and `(GQF.30)`.
Orthogonality proves `(GQF.31)`. Gaussian pushforward by orthogonal map gives `(GQF.32)`.
Blackwell equivalence is composition by common Markov kernels in both directions; transport any
formation through those kernels. Data processing both ways gives equality of every listed
information monotone. QED.

## 7. Hostile audit

1. **Occupied parent mathematics.** Gaussian shifts, Blackwell comparison, Le Cam experiments,
   Schur complements, and Gaussian testing are classical. The theorem is a Frankenstein fusion
   and corpus mechanism, not external priority claim.
2. **Not every experiment is Gaussian.** One scalar is complete only on Gaussian shift chain.
   General finite packets need full Blackwell order.
3. **No free canonical Gaussianization.** Replacing arithmetic packet by `Gamma(g)` is legal only
   when source response supplies Hilbert metric and genesis vector before endpoint evaluation.
4. **Cofinal formation is load-bearing.** Positive `Q` is compatible with every fixed finite depth
   below `b/Q`. Selection follows from unbounded depth, not positivity alone.
5. **Singular source loophole.** Finite Gaussian source excludes infinite capital. General disjoint
   source supports reveal mark and can form arbitrary depth.
6. **Synchronization is not RH.** A pre-zero arithmetic theorem must produce cofinal formation and
   prove synchronization equalizer is critical displacement kernel.
7. **Functional equation is neutral.** It cannot provide source budget or cofinal premise.
8. **Testing is prediction, not selector.** Testing curve operationalizes capital but does not force
   RH.

## 8. Literature placement

- D. Blackwell, *Comparison of Experiments* (1951, 1953): Markov randomization order.
- E. Mariucci, Le Cam experiment theory survey, <https://arxiv.org/abs/1605.03301>.
- T. Fritz, Markov kernels and sufficient statistics, <https://arxiv.org/abs/1908.07021>.
- X. Wang and M. M. Wilde, asymmetric distinguishability resource theory,
  <https://arxiv.org/abs/1905.11629>.
- R. Salzmann et al., symmetric distinguishability as resource,
  <https://arxiv.org/abs/2102.12512>.
- J. Suzuki, nuisance-parameter quantum estimation, <https://arxiv.org/abs/1905.04733>.

Exact Gaussian Blackwell chain is routine from displayed kernel. Corpus contribution is closed
composition

\[
 \text{quotient--fusion genesis}
 \longrightarrow\text{canonical independent experiment}
 \longrightarrow\text{exact formation depth}
 \longrightarrow\text{cofinal properness}
 \longrightarrow\text{equalizer selection},
 \tag{GQF.33}
\]

with functional equation and common recovery proved information-neutral rather than proposed as
producers.

## 9. Lean gate

No Lean file was written or built in this research pass. Existing Lean certifies coordinate-free
quotient--fusion identity and zero classification. Future formalization must add only:

1. finite-dimensional Gaussian density formulas;
2. explicit Gaussian kernel `(GQF.18)--(GQF.19)`;
3. exact integer depth classification;
4. orthogonal functional-equation equivariance.

Promotion to Stage 3 is forbidden until declarations are closed and universal-law field umbrella
imports them.
