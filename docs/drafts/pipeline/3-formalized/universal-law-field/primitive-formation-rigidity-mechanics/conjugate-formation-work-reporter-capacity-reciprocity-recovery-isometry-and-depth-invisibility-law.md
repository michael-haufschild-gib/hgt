# Conjugate formation work--reporter capacity reciprocity, recovery isometry, and depth invisibility

- **ID:** ULF-PFRM-3
- **Stage:** 2 -- fully proven on paper
- **Type:** THEOREM / FORMATION--COFORMATION FUSION LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE]`
  `[FORMATION WORK] [DUAL REPORTER CAPACITY] [DIVIDED-DIFFERENCE CHARGE]`
  `[COMMON-RECOVERY ISOMETRY] [FUNCTIONAL-EQUATION INVARIANCE]`
  `[GRAM/SCHUR PREDICTION] [DEPTH-INVISIBILITY COUNTERTHEOREM] [NOT RH]`
- **Formal status:** not Lean-formalized. Under project rules this is not an accepted AI proof.
- **Parent:**
  `product-primitive-saturation-resolvent-and-formation-depth-properness-law.md`.

## 1. Mathematical delta

The parent theorem proves that a resolvent packet requires exact polynomial formation depth
`N-1` on `N` distinct clock nodes. That algebraic properness does **not** imply positive or metric
properness.

The missing invariant is conjugate: every formation subspace has a normalized annihilating
reporter. Its squared norm is the reciprocal of the least work needed to leave the formation
subspace. For the source resolvent, the reporter is the normalized divided difference.

The exact conservation law is

\[
 \boxed{
  \text{least formation work}\times
  \text{least normalized reporter capacity}=1.}
 \tag{CFR.1}
\]

Common recovery and functional-equation transport preserve both factors. Thus a completion can
make exact formation depth invisible only by forcing the conjugate reporter to escape to infinite
dual norm.

## 2. Abstract conjugate-formation theorem

Let `H` be a complex Hilbert space, let `L` be a closed linear subspace, and let `x\notin L`. Put

\[
 W(x\mid L)=\operatorname{dist}(x,L)^2
 \tag{CFR.2}
\]

and define the normalized reporter capacity

\[
 C(x\mid L)=
 \inf\{\|\varphi\|^2:
       \varphi\in H^*,\ \varphi|_L=0,\ \varphi(x)=1\}.
 \tag{CFR.3}
\]

### Theorem 2.1 -- exact formation--reporter reciprocity

The infimum in `(CFR.3)` is attained uniquely, and

\[
 \boxed{W(x\mid L)C(x\mid L)=1.}
 \tag{CFR.4}
\]

If `q=x-P_Lx`, then the unique minimizing reporter is

\[
 \varphi_{x,L}(y)=\frac{\langle q,y\rangle}{\|q\|^2},
 \qquad
 \|\varphi_{x,L}\|^2=\|q\|^{-2}.
 \tag{CFR.5}
\]

#### Proof

Because `L` is closed, `x=P_Lx+q` with `q\in L^\perp` and `q\ne0`. Formula `(CFR.5)` annihilates
`L`, takes value one at `x`, and has norm `1/\|q\|` by Riesz representation.

Conversely, if `\varphi|_L=0` and `\varphi(x)=1`, then `\varphi(q)=1`. Cauchy--Schwarz gives

\[
 1=|\varphi(q)|\le \|\varphi\|\,\|q\|.
\]

Hence `\|\varphi\|^2\ge\|q\|^{-2}`. Equality in Cauchy--Schwarz forces the Riesz vector of
`\varphi` to be the scalar multiple of `q` fixed by `\varphi(q)=1`, proving uniqueness and
`(CFR.4)`. QED.

### Corollary 2.2 -- charged reporter form

Suppose a nonzero continuous functional `delta` satisfies `L=ker(delta)` and `delta(x)\ne0`.
Then

\[
 \boxed{
  W(x\mid L)\,\|\delta\|^2=|\delta(x)|^2.}
 \tag{CFR.6}
\]

Indeed, `delta/delta(x)` is the unique normalized reporter from Theorem 2.1.

## 3. Weighted divided-difference specialization

Fix `N>=2`, pairwise distinct nodes `lambda_1,...,lambda_N in C`, nonzero source amplitudes
`v_i`, positive weights `w_i`, and `c` different from every `lambda_i`. Give `C^N` the norm

\[
 \|y\|_w^2=\sum_{i=1}^N w_i|y_i|^2.
 \tag{CFR.7}
\]

Let the depth-`N-2` formation subspace be

\[
 L_{N-2}=\{(v_iP(\lambda_i))_{i=1}^N:\deg P\le N-2\}
 \tag{CFR.8}
\]

and let the resolvent packet be

\[
 R_c=\left(\frac{v_i}{c-\lambda_i}\right)_{i=1}^N.
 \tag{CFR.9}
\]

Define

\[
 \delta_N(y)=
 \sum_{i=1}^N
 \frac{y_i/v_i}{\prod_{j\ne i}(\lambda_i-\lambda_j)}.
 \tag{CFR.10}
\]

The parent divided-difference theorem gives

\[
 \delta_N(R_c)=\prod_{i=1}^N(c-\lambda_i)^{-1}\ne0.
 \tag{CFR.11}
\]

### Theorem 3.1 -- explicit work--capacity conservation

One has `L_(N-2)=ker(delta_N)` and

\[
 \boxed{
 \|\delta_N\|_{w,*}^2=
 \sum_{i=1}^N
 \frac{1}
 {w_i|v_i|^2
  \left|\prod_{j\ne i}(\lambda_i-\lambda_j)\right|^2}.}
 \tag{CFR.12}
\]

Consequently the least squared work of approximating the resolvent by a depth-`N-2` formation is

\[
 \boxed{
 \begin{aligned}
 W_N
 &=\inf_{\deg P\le N-2}
   \sum_{i=1}^Nw_i|v_i|^2
   \left|\frac1{c-\lambda_i}-P(\lambda_i)\right|^2\\
 &=\frac{\displaystyle\prod_{i=1}^N|c-\lambda_i|^{-2}}
 {\displaystyle\sum_{i=1}^N
  \frac{1}
  {w_i|v_i|^2
   \left|\prod_{j\ne i}(\lambda_i-\lambda_j)\right|^2}}.
 \end{aligned}}
 \tag{CFR.13}
\]

Writing

\[
 \widehat C_N=
 \frac{\|\delta_N\|_{w,*}^2}{|\delta_N(R_c)|^2},
 \tag{CFR.14}
\]

the scale-free law is

\[
 \boxed{W_N\widehat C_N=1.}
 \tag{CFR.15}
\]

#### Proof

The evaluation map from polynomials of degree at most `N-2` to `C^N` is injective because a
nonzero such polynomial cannot vanish at all `N` distinct nodes. Hence `dim L_(N-2)=N-1`.
The divided difference annihilates that space and is nonzero, so its kernel also has dimension
`N-1`; therefore the two spaces coincide.

In the weighted Hilbert structure, the Riesz vector of `(CFR.10)` has coordinates

\[
 q_i=\frac{1}
 {w_i\overline{v_i\prod_{j\ne i}(\lambda_i-\lambda_j)}}.
 \tag{CFR.16}
\]

Its squared norm is `(CFR.12)`. Apply `(CFR.6)` and `(CFR.11)` to obtain `(CFR.13)`, then divide
by the nonzero charge to obtain `(CFR.15)`. QED.

## 4. Fourth-organ Gram/Schur prediction

Let `A` be the `N x (N-1)` formation matrix

\[
 A_{ik}=v_i\lambda_i^k,
 \qquad 0\le k\le N-2,
 \tag{CFR.17}
\]

let `Omega=diag(w_i)`, and let `r=R_c`. Put

\[
 G=A^*\Omega A,
 \qquad
 \widetilde G=
 \begin{pmatrix}
 A^*\Omega A&A^*\Omega r\\
 r^*\Omega A&r^*\Omega r
 \end{pmatrix}.
 \tag{CFR.18}
\]

Distinct nodes and nonzero amplitudes make `A` full column rank, so `G` is positive definite.
The Schur-complement formula gives the predicted positive-organ identity

\[
 \boxed{\frac{\det\widetilde G}{\det G}=W_N.}
 \tag{CFR.19}
\]

This theorem is not assumed in the construction of `delta_N`; it is forced by the conserved
formation/reporter pair. It is the exact fourth-organ shadow: the last Gram innovation is the
primal work, while the normalized divided difference is its dual capacity.

#### Proof

The Schur complement of `G` in `widetilde G` is

\[
 r^*\Omega r-r^*\Omega A(A^*\Omega A)^{-1}A^*\Omega r,
\]

the squared weighted distance from `r` to `ran A`, which is `W_N`. The determinant identity for a
block matrix with invertible leading block proves `(CFR.19)`. QED.

## 5. Common recovery and functional-equation invariance

Let `(X,mu)` be a finite or sigma-finite observer probability space and let `K(x,dh)` be a Markov
recovery kernel. The formed law is `mu(dx)K(x,dh)`. Define

\[
 J_K:L^2(\mu)\longrightarrow L^2(\mu K),
 \qquad (J_Kf)(x,h)=f(x).
 \tag{CFR.20}
\]

### Theorem 5.1 -- conjugate information neutrality

`J_K` is an isometry. For every closed formation subspace `L` and every `x notin L`,

\[
 \boxed{
 W(J_Kx\mid J_KL)=W(x\mid L),
 \qquad
 C(J_Kx\mid J_KL)=C(x\mid L).}
 \tag{CFR.21}
\]

If `R` is a measurable observer involution, the functional-equation transport
`f mapsto f circ R^{-1}` is unitary between the corresponding observer `L^2` spaces. Its
transform--discard--recover lift therefore preserves `(CFR.21)` as well.

#### Proof

Markov normalization gives

\[
 \|J_Kf\|_{L^2(\mu K)}^2
 =\int_X\int_H|f(x)|^2K(x,dh)\,d\mu(x)
 =\|f\|_{L^2(\mu)}^2.
\]

Hence distance to the image subspace is unchanged: the upper bound follows by embedding a nearest
sequence, while the reverse bound follows by applying the orthogonal projection from the joint
space onto the closed observer-coordinate range of `J_K`. The capacity equality then follows from
Theorem 2.1. Change of variables under `R` proves unitarity, and composition of isometries proves
the last claim. QED.

The theorem upgrades the earlier KL information-neutrality result: at tangent/Fisher level, common
recovery preserves not only total information but the complete conjugate formation pair.

## 6. Exact depth-invisibility countertheorem

Take

\[
 \lambda_i=i,\qquad v_i=w_i=1,\qquad c=0,
 \qquad 1\le i\le N.
 \tag{CFR.22}
\]

The exact polynomial formation depth of the resolvent packet `(-1/i)_(i=1)^N` is `N-1`. Yet the
least work at depth `N-2` is

\[
 \boxed{
 W_N=\frac1{N^2\binom{2N-2}{N-1}}\longrightarrow0.}
 \tag{CFR.23}
\]

The normalized reporter capacity is

\[
 \boxed{
 \widehat C_N=N^2\binom{2N-2}{N-1}\longrightarrow\infty.}
 \tag{CFR.24}
\]

#### Proof

For these nodes,

\[
 \prod_{j\ne i}(i-j)=(-1)^{N-i}(i-1)!(N-i)!,
\]

so

\[
 \|\delta_N\|^2
 =\sum_{i=1}^N\frac1{(i-1)!^2(N-i)!^2}
 =\frac1{(N-1)!^2}\sum_{k=0}^{N-1}\binom{N-1}{k}^2
 =\frac{\binom{2N-2}{N-1}}{(N-1)!^2}.
\]

The charge has squared magnitude `1/(N!)^2`. Formula `(CFR.13)` gives `(CFR.23)`; the limit
follows already from `W_N<=1/N^2`. Equation `(CFR.24)` is reciprocal. QED.

Thus unbounded exact generation history may be arbitrarily cheap to approximate positively. Depth
properness by itself cannot unlock selection.

## 7. Fusion table

| organ | exact law |
|---|---|
| primitive/differential formation | depth-`N-2` polynomial packet `L_(N-2)` |
| algebraic obstruction | nonzero divided-difference charge `delta_N(R_c)` |
| positivity/information | least Hilbert/Fisher formation work `W_N` |
| observer/coformation | normalized reporter capacity `C_hat_N` |
| topology/recovery | common Markov recovery preserves both conjugate factors |
| determinant/spectral receiver | last Gram innovation is `det(G_tilde)/det(G)=W_N` |

The mechanism is not “one scalar obstruction.” It is a conjugate pair with an exact evaluation
charge. Completion can move the obstruction from the primal side to the dual side but cannot erase
the product unless it kills the charge.

## 8. Hostile audit and exact limits

1. **Classical parent machinery.** The Hilbert projection theorem, Riesz representation,
   barycentric divided differences, weighted least squares, and Schur complements are classical.
   Therefore this theorem is a `[BRIDGE]`, not an external novelty claim.
2. **Corpus delta.** The exact coupling of the PFRM resolvent depth charge to positive work,
   normalized reporter blow-up, common-recovery isometry, and the explicit depth-invisibility
   family was not present in the audited corpus.
3. **Metric is constitutive.** Positive weights are not generated by the abstract source. Rescaling
   all weights rescales work. The scale-free pair `(W_N,C_hat_N)` and product one remain invariant,
   but selection needs a source-normal metric or bounded reporter law.
4. **No global properness follows.** `(CFR.23)` disproves it. A cofinal theorem must control
   normalized reporter capacities, not merely exact depth.
5. **Recovery scope.** `J_K` covers observer-coordinate tangent scores. It does not claim that
   arbitrary latent-history scores lie in its range.
6. **Functional equation is neutral.** It preserves the pair and cannot force either factor to
   vanish. Selection must come from source formation admissibility/properness.
7. **No RH implication.** No source theorem currently bounds the actual normalized reporter tower.

## 9. External parent audit

- Elsworth--Guettel, [Conversions between barycentric, RKFUN, and Newton representations of
  rational interpolants](https://arxiv.org/abs/1711.00707), gives the established
  barycentric/rational-Krylov representation interface.
- Adcock, [Optimal sampling for least-squares approximation](https://arxiv.org/abs/2409.02342),
  surveys Christoffel/leverage control of weighted recovery.
- Herremans--Adcock, [Refinement-based Christoffel sampling for least squares approximation in
  non-orthogonal bases](https://arxiv.org/abs/2510.08461), develops current inverse-Christoffel and
  nonorthogonal-Gram machinery.
- Al Daas--Palitta, [Minimal residual rational Krylov subspace method for sequences of shifted
  linear systems](https://arxiv.org/abs/2507.00267), and Massei--Robol,
  [Error formulas for block rational Krylov approximations of matrix functions](https://arxiv.org/abs/2504.05151),
  show that residual and rational-Krylov error geometry remain active parent fields.
- Wang--Xu, [Representer Theorems in Banach Spaces](https://arxiv.org/abs/2006.14101), places
  minimum-norm interpolation and dual representers in a broader established theory.

These parents occupy the abstract components. None supplies the HGT source normalization needed to
bound the cofinal normalized reporter tower or derive RH selection.

## 10. Conjecture loop and survivor

1. **Conjecture:** cofinal exact formation-depth escape implies positive formation selection.
2. **Verdict:** `[FALSIFIED]` by `(CFR.22)--(CFR.23)`.
3. **Exact why:** algebraic codimension is blind to the norm of its annihilating functional.
4. **Positive survivor:** work--capacity reciprocity `(CFR.15)` and recovery invariance
   `(CFR.21)`.
5. **Representation lesson:** retain both formation and coformation filtrations. A completion that
   forgets the dual reporter norm confuses exact generation complexity with positive properness.
6. **Stronger live conjecture:** source generation and source testing arise as one normalized
   conjugate process whose coevaluation law forbids unbounded normalized reporter capacity. This is
   recorded in the Stage-1 programme; it is not proved here.

## 11. Gates

- [x] exact primal/dual reciprocity theorem
- [x] explicit weighted divided-difference formula
- [x] common-recovery and functional-equation isometry
- [x] fourth-organ Gram/Schur prediction
- [x] exact counterexample to depth-only selection
- [x] external parent audit
- [x] hostile scope audit
- [x] Lean formalization
- [ ] source-normal cofinal reporter bound
- [ ] RH selection

## Log

- 2026-08-12 -- depth-only properness conjecture falsified; conjugate work/capacity conservation,
  recovery invariance, Gram prediction, and exact depth-invisibility family proved on paper.
- 2026-08-28 -- formalized unconditionally in
  `GaloisForLFunctions.HTGeometry.ConstitutiveConjugateFormationReciprocity`; imported by
  `GaloisForLFunctions.HTGeometry.UniversalLawField`. Direct Lean check and targeted leaf build
  passed. Axiom audit covered all 70 new declarations and found only standard dependencies
  (`propext`, `Classical.choice`, `Quot.sound`) or subsets. Formal lint confirms module is reachable;
  remaining unreachable-module findings are unrelated concurrent work.
