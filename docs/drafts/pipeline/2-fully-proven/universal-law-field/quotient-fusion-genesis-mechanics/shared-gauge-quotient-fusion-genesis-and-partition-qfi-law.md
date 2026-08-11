# Shared-gauge quotient--fusion genesis and partition-QFI law

- **ID:** `ULF-QFGM-1`
- **Stage:** 2 — fully proven on paper
- **Type:** COORDINATE-FREE FUSION MECHANISM / EXACT CONSERVATION / FOURTH-ORGAN PREDICTION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM FIRST]`
  `[CLASSICAL ALGEBRA] [CORPUS-WIDE INTERPRETATION] [LEAN-CERTIFIED FINITE CORE] [NOT RH]`

## 1. The mechanism

The field operation is the commutator between two procedures:

1. fuse source components, then eliminate one shared gauge;
2. eliminate one independent gauge in each component, then fuse the quotient residuals.

These procedures need not agree.  Their positive difference is the
**quotient--fusion genesis defect**.  It measures law created by compatibility, not information
already present in an individual component.

No curvature analogy is required.  No source dependence is required.  The mechanism exists even
for orthogonal direct sums and product probability laws.

## 2. Coordinate-free theorem

Let `I` be finite.  For each `i in I`, let `H_i` be a finite-dimensional real Hilbert space and
let `x_i in H_i`.  Let `K` be a finite-dimensional real Hilbert space and let

\[
 A_i:K\longrightarrow H_i
\]

be linear.  Define

\[
 E_{\rm shared}
 :=\min_{u\in K}\sum_i\|x_i-A_i u\|^2,
 \qquad
 E_{\rm separate}
 :=\sum_i\min_{u_i\in K}\|x_i-A_i u_i\|^2,
 \tag{QFG.1}
\]

and

\[
 \mathfrak Q(x,A):=E_{\rm shared}-E_{\rm separate}.
 \tag{QFG.2}
\]

Let `z_i` be the orthogonal projection of `x_i` onto `ran A_i`.

### Theorem 2.1 — quotient--fusion genesis

\[
 \boxed{
 \mathfrak Q(x,A)
 =\min_{u\in K}\sum_i\|z_i-A_i u\|^2\ge0.}
 \tag{QFG.3}
\]

Moreover,

\[
 \boxed{
 \mathfrak Q(x,A)=0
 \iff
 \exists u\in K\;\forall i,\; A_i u=z_i.}
 \tag{QFG.4}
\]

Thus genesis vanishes exactly when the locally optimal gauge histories have a common realization.

#### Proof

For every `u in K`,

\[
 x_i-A_i u=(x_i-z_i)+(z_i-A_i u).
\]

The first term lies in `(ran A_i)^perp`; the second lies in `ran A_i`.  Pythagoras gives

\[
 \|x_i-A_i u\|^2
 =\|x_i-z_i\|^2+\|z_i-A_i u\|^2.
\]

Summing and minimizing gives

\[
 E_{\rm shared}
 =\sum_i\|x_i-z_i\|^2
  +\min_u\sum_i\|z_i-A_i u\|^2.
\]

The projection theorem gives

\[
 E_{\rm separate}=\sum_i\|x_i-z_i\|^2.
\]

Subtracting proves `(QFG.3)`.  The minimum in `(QFG.3)` is zero exactly when one `u` solves all
equations `A_i u=z_i`, proving `(QFG.4)`.  Finite dimensionality makes every range closed and every
minimum attained. ∎

### Corollary 2.2 — inherited versus generated information

The shared quotient energy has the exact decomposition

\[
 \boxed{
 E_{\rm shared}
 =\underbrace{\sum_i\operatorname{dist}(x_i,\operatorname{ran}A_i)^2}
      _{\text{inherited local information}}
 +\underbrace{\operatorname{dist}
   \bigl((z_i)_i,\operatorname{ran}(u\mapsto(A_i u)_i)\bigr)^2}
      _{\text{collectively generated information}}.}
 \tag{QFG.5}
\]

The second term can be positive when every first term is zero.

## 3. Scalar exact conservation

Let `K=R` and `A_i(t)=t y_i`, with \(y_i\ne0\).  Put

\[
 c_i=\|y_i\|^2,
 \qquad b_i=\langle x_i,y_i\rangle,
 \qquad t_i={b_i\over c_i},
 \qquad C=\sum_i c_i,
 \qquad \bar t={1\over C}\sum_i c_i t_i.
 \tag{QFG.6}
\]

### Theorem 3.1 — common-gauge conservation

\[
 \boxed{
 E_{\rm shared}
 =E_{\rm separate}+\sum_i c_i(t_i-\bar t)^2.}
 \tag{QFG.7}
\]

The genesis defect has the pairwise form

\[
 \boxed{
 \mathfrak Q
 ={1\over C}\sum_{i<j}c_i c_j(t_i-t_j)^2.}
 \tag{QFG.8}
\]

#### Proof

Projection onto `R y_i` gives `z_i=t_i y_i`.  Theorem 2.1 gives

\[
 \mathfrak Q=\min_t\sum_i c_i(t_i-t)^2.
\]

Expanding the quadratic shows that the unique minimizer is `bar t`, proving `(QFG.7)`.  The
weighted variance identity

\[
 C\sum_i c_i(t_i-\bar t)^2
 =\sum_{i<j}c_i c_j(t_i-t_j)^2
\]

proves `(QFG.8)`. ∎

### Theorem 3.2 — partition and tree conservation

Let `P={B_alpha}` be a partition of `I`.  Put

\[
 C_\alpha=\sum_{i\in B_\alpha}c_i,
 \qquad
 t_\alpha={1\over C_\alpha}\sum_{i\in B_\alpha}c_i t_i.
 \tag{QFG.9}
\]

Then

\[
 \boxed{
 \sum_i c_i(t_i-\bar t)^2
 =\sum_\alpha\sum_{i\in B_\alpha}c_i(t_i-t_\alpha)^2
  +\sum_\alpha C_\alpha(t_\alpha-\bar t)^2.}
 \tag{QFG.10}
\]

Consequently any rooted fusion tree decomposes total genesis into the sum of its internal-node
genesis defects.  Reparenthesization moves defect between nodes but preserves total genesis.

#### Proof

For `i in B_alpha`, write

\[
 t_i-\bar t=(t_i-t_\alpha)+(t_\alpha-\bar t).
\]

The cross term in block `alpha` is

\[
 2(t_\alpha-\bar t)\sum_{i\in B_\alpha}c_i(t_i-t_\alpha)=0.
\]

Summing proves `(QFG.10)`.  Iteration along a tree proves the last assertion. ∎

## 4. Schur-complement form

Let

\[
 G_i=\begin{pmatrix}a_i&b_i\\b_i&c_i\end{pmatrix}\succeq0,
 \qquad c_i>0,
 \qquad \beta_i={b_i\over c_i},
 \qquad \beta={\sum_i b_i\over\sum_i c_i}.
 \tag{QFG.11}
\]

Write `Schur(G_i)=a_i-b_i^2/c_i`.  Then

\[
 \boxed{
 \operatorname{Schur}\!\left(\sum_iG_i\right)
 =\sum_i\operatorname{Schur}(G_i)
  +\sum_i c_i(\beta_i-\beta)^2.}
 \tag{QFG.12}
\]

Hence the Schur complement is superadditive, with exact equality defect.  If every `G_i` has rank
one, every local Schur complement vanishes, while the sum has positive Schur complement exactly
when the local slopes are not all equal.

#### Proof

The right-hand side is

\[
 \sum_i a_i-\sum_i{b_i^2\over c_i}
 +\sum_i{b_i^2\over c_i}
 -{(\sum_i b_i)^2\over\sum_i c_i},
\]

which is the left-hand side. ∎

## 5. Literal three-organ arithmetic fusion

Fix a finite prime aperture `F`, `|F|>=2`, and `sigma>0`.  Put

\[
 \lambda_p=\log p,
 \qquad
 w_p={p^\sigma\over(1+p^\sigma)^2}.
 \tag{QFG.13}
\]

For each prime cell let

\[
 x_p=\pi\sqrt{w_p},
 \qquad
 y_p=\lambda_p\sqrt{w_p}.
 \tag{QFG.14}
\]

Every cell is individually gauge-trivial:

\[
 \min_t|x_p-t y_p|^2=0,
 \qquad t_p={\pi\over\lambda_p}.
 \tag{QFG.15}
\]

But fusion followed by one shared clock quotient gives

\[
 \boxed{
 \mathfrak Q_F
 =\min_t\sum_{p\in F}w_p(\pi-t\lambda_p)^2
 =D_F>0.}
 \tag{QFG.16}
\]

This one number has three unlike forced readings.

1. **Boolean relation/capacity.**  It is the Route-E parity direction after the logarithmic clock
   quotient.
2. **Mass current.**  Its gauge weights are
   `c_p=w_p lambda_p^2=j_{sigma,p}^2`, the squared Gibbs-damped primitive-prime Mass current.
3. **Positive Hankel.**  Each local covariance block

   \[
    w_p\begin{pmatrix}\pi^2&\pi\lambda_p\\
      \pi\lambda_p&\lambda_p^2\end{pmatrix}
   \]

   has rank one.  Their sum has positive Schur complement exactly by quotient--fusion genesis.

The full mismatch packet reconstructs the source:

\[
 \lambda_p={\pi\over t_p},
 \qquad
 w_p={c_p t_p^2\over\pi^2}.
 \tag{QFG.17}
\]

It therefore reconstructs the marked prime aperture, Boolean Gibbs law, Mass current, and all
finite Hankel moments.  With

\[
 A=\sum_pw_p,
 \quad B=\sum_pw_p\lambda_p,
 \quad C=\sum_pw_p\lambda_p^2,
 \]

the conservation identity is

\[
 \boxed{
 D_F C=\pi^2(AC-B^2)=\pi^2\det
 \begin{pmatrix}A&B\\B&C\end{pmatrix}.}
 \tag{QFG.18}
\]

## 6. Fourth-organ theorem: partitioned recurrent QFI

On the Boolean configuration Hilbert space use the pure-state family

\[
 |\psi_{\alpha,t}\rangle
 =\sum_{S\subseteq F}\sqrt{\mathbb P_\sigma(S)}
   e^{i(\pi\alpha N(S)-tE(S))}|S\rangle.
 \tag{QFG.19}
\]

Its pure-state QFI quadratic form is four times the covariance of the generator.  Let

\[
 \mathcal I_{\rm shared}(F)=4D_F
 \tag{QFG.20}
\]

be parity QFI after eliminating one common clock nuisance.

For a partition `P={F_alpha}`, let

\[
 \mathcal I_P(F)=4\sum_\alpha D_{F_\alpha}
 \tag{QFG.21}
\]

be the QFI remaining when each block receives its own clock nuisance.  Singleton blocks have
`D_{\{p\}}=0`.

Put

\[
 C_\alpha=\sum_{p\in F_\alpha}w_p\lambda_p^2,
 \qquad
 \gamma_\alpha={\sum_{p\in F_\alpha}w_p\lambda_p\over C_\alpha},
 \qquad
 \gamma={\sum_\alpha C_\alpha\gamma_\alpha\over\sum_\alpha C_\alpha}.
 \tag{QFG.22}
\]

### Theorem 6.1 — common-clock quantum information genesis

\[
 \boxed{
 \mathcal I_{\rm shared}(F)-\mathcal I_P(F)
 =4\pi^2\sum_\alpha C_\alpha(\gamma_\alpha-\gamma)^2\ge0.}
 \tag{QFG.23}
\]

Equality holds exactly when every block has the same optimal normalized clock slope `gamma_alpha`.
For the singleton partition,

\[
 \boxed{
 \mathcal I_{\rm shared}(F)
 =4\pi^2\sum_{p\in F}w_p\lambda_p^2
 \left({1\over\lambda_p}-{B\over C}\right)^2.}
 \tag{QFG.24}
\]

Thus a product of recurrent prime cells, each carrying zero parity information after its own local
clock quotient, carries strictly positive parity information when the clock is required to be
common.  This is not entanglement and not source dependence; it is quotient--fusion genesis.

#### Proof

For a block `F_alpha`,

\[
 D_{F_\alpha}
 =\pi^2\left(A_\alpha-{B_\alpha^2\over C_\alpha}\right).
\]

Therefore

\[
 D_F-\sum_\alpha D_{F_\alpha}
 =\pi^2\left(\sum_\alpha{B_\alpha^2\over C_\alpha}
  -{(\sum_\alpha B_\alpha)^2\over\sum_\alpha C_\alpha}\right)
 =\pi^2\sum_\alpha C_\alpha(\gamma_\alpha-\gamma)^2.
\]

Multiplication by four proves `(QFG.23)`.  For singleton blocks,
`C_p=w_p lambda_p^2` and `gamma_p=1/lambda_p`, giving `(QFG.24)`.  Distinct prime logs make the
weighted variance positive for `|F|>=2`. ∎

## 7. Exact relationship to existing universal-law mechanisms

This law is not a renaming of source fusion.

- Norming-face fusion compares `sum ||v_i||` with `||sum v_i||`.  The present law compares the
  distance to one diagonal gauge image with distances to independent local gauge images.
- Generative response mechanics studies one centered tangent received by phase and positive-Gram
  observers.  The present law studies incompatibility among locally optimal quotient histories.
- Collective repair studies spectral threshold crossing under addition.  The present law gives an
  exact compatibility distance and equality classification even away from a threshold.

They can nevertheless be assembled: source intervention creates cells; quotient--fusion genesis
measures common-history incompatibility; norming fusion measures cancellation of the resulting
residuals; admission mechanics decides whether the cofinal residual remains executable.

## 8. Hostile boundaries

1. **Classical parent algebra.**  `(QFG.7)--(QFG.12)` are weighted least squares, weighted ANOVA,
   Cochran heterogeneity, and efficient-information Schur-complement identities.  No priority
   claim is made.
2. **No statistical interaction.**  The prime source is a product Bernoulli law.  Positive genesis
   records a shared constraint, not dependence.
3. **No orientation.**  Squared Hilbert distance and QFI do not recover phase or coorientation.
4. **No cofinal theorem.**  Infinite fusion requires a specified topology, closed gauge range, and
   an admission law.  Finite identities alone do not commute with completion.
5. **No universal scalar.**  `mathfrak Q` does not reconstruct a general source.  Reconstruction in
   Section 5 uses the full marked packet `(c_p,t_p)`.
6. **No automatic RH selector.**  `D_F` and the QFI are strictly positive at the critical
   half-density source.  Vanishing is the wrong selection rule.
7. **Shared gauge must be sourced.**  Declaring a common nuisance after inspecting an endpoint is
   curve fitting.  A live RH application must derive the diagonal gauge constraint before Xi zero
   specialization.

## 9. Parent sources

- W. G. Cochran, *Problems Arising in the Analysis of a Series of Similar Experiments* (1937),
  <https://doi.org/10.2307/2984123>.
- R. M. Fewster and P. E. Jupp, *Information on parameters of interest decreases under
  transformations* (2013), <https://doi.org/10.1016/j.jmva.2013.05.010>.
- J. Suzuki, *Nuisance parameter problem in quantum estimation theory: General formulation and
  qubit examples* (2019), <https://arxiv.org/abs/1905.04733>.

## 10. RH selection gate

The earlier proposed next step—impose equality of a forward and reflected transverse packet at Xi
zeros—is rejected as regression.  The corpus already shows that such equality is another form of
the critical-line condition unless a pre-zero source theorem forces it.

The next legal question is instead:

> Does the literal arithmetic source force one common gauge across two or more independently
> generated route organs, while every off-critical divisor necessarily produces incompatible
> local optimal gauges?

A valid selector must prove both clauses before divisor specialization.  The present theorem
supplies the exact obstruction and its conservation law; it does not supply that source theorem.

## 11. Lean certification

The unconditional denominator-free core is formalized in
`GaloisForLFunctions.HTGeometry.SharedGaugeQuotientFusion` and imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.  Lean certifies:

- pairwise reconstruction of the weighted genesis numerator;
- its centered common-gauge form;
- binary quotient--fusion conservation;
- unconditional nonnegativity and exact zero classification;
- parity--clock Gram normalization;
- binary partition-QFI conservation;
- one closed capstone joining those clauses.

The formal identities are polynomial: no positivity premise, denominator nonvanishing, minimizer,
computation certificate, project axiom, RH statement, or Xi specialization enters them.  The
coordinate-free projection theorem and divided metric interpretation remain paper proofs; Lean
certifies the algebraic kernel from which every finite scalar and QFI specialization follows.

## Gates

- [x] mechanism stated coordinate-free
- [x] exact nonnegative fusion law and zero classification
- [x] refinement/tree conservation
- [x] three structurally different arithmetic organs realized
- [x] joint reconstruction from the marked mismatch packet
- [x] fourth-organ partition-QFI theorem predicted and proved
- [x] circular reflected-packet selector rejected
- [x] unconditional finite algebra formalized and umbrella wired
- [ ] cofinal closed-range/admission extension
- [ ] source-forced common gauge spanning independent RH organs
