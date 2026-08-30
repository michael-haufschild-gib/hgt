# Posterior-contrast projection, Pythagoras, sufficiency, and global reconstruction

- **ID:** ULF-PMPG-1
- **Stage:** 2 — fully proven on paper
- **Type:** UNIVERSAL FORMATION/OBSERVATION MECHANISM / EXACT CONSERVATION LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [EXACT INFORMATION CURRENT]`
  `[GLOBAL ISOMETRIC RECONSTRUCTION] [COMMON-RECOVERY SUFFICIENCY CLASSIFIED]`
  `[FOURTH-ORGAN P/R PREDICTION VERIFIED] [LEAN NOT YET WRITTEN] [NOT RH]`
- **Parent failure:**
  `../likelihood-polarization-coherence-mechanics/reflected-binary-experiment-julia-lift-coherence-information-and-properness-law.md`

## 1. Pivot: observations act on contrast, not on an invented double

Let `X,Y` be standard Borel spaces, let `P,Q` be probability laws on `X`, and let

\[
 \eta=\frac{P+Q}{2}.
 \tag{PMP.1}
\]

Write

\[
 \frac{dP}{d\eta}=1+d_X,
 \qquad
 \frac{dQ}{d\eta}=1-d_X.
 \tag{PMP.2}
\]

Then `d_X` is the balanced posterior contrast, `|d_X|<=1`, and `P=Q` exactly when `d_X=0`
`eta`-almost everywhere.  If `P,Q` are equivalent, the half-log likelihood ratio is

\[
 \chi_X=\frac12\log\frac{dP}{dQ},
 \qquad
 d_X=\tanh\chi_X,
 \qquad
 a_X=\sqrt{1-d_X^2}=\operatorname{sech}\chi_X.
 \tag{PMP.3}
\]

Let `K:X -> Y` be a Markov kernel and put

\[
 P_Y=PK,\qquad Q_Y=QK,\qquad \eta_Y=\eta K.
 \tag{PMP.4}
\]

The source-typed comparison space is not an auxiliary Julia double.  It is the joint observation
law

\[
 \rho(dx,dy)=\eta(dx)K(x,dy).
 \tag{PMP.5}
\]

Every later object below is forced by `(PMP.1)`--`(PMP.5)`.

## 2. One-step posterior projection theorem

### Theorem 2.1 — posterior contrast is conditional expectation

Let `d_Y` be defined by

\[
 \frac{dP_Y}{d\eta_Y}=1+d_Y,
 \qquad
 \frac{dQ_Y}{d\eta_Y}=1-d_Y.
 \tag{PMP.6}
\]

Then, as functions on the joint law `rho`,

\[
 \boxed{d_Y(Y)=\mathbb E_\rho[d_X(X)\mid Y].}
 \tag{PMP.7}
\]

Define the vertical information current

\[
 j_K(X,Y)=d_X(X)-d_Y(Y).
 \tag{PMP.8}
\]

Then

\[
 \mathbb E_\rho[j_K\mid Y]=0,
 \qquad
 j_K\perp L^2(Y,\eta_Y).
 \tag{PMP.9}
\]

#### Proof

For every bounded measurable `g:Y -> R`,

\[
\begin{aligned}
 \int_Y g(y)d_Y(y)\,d\eta_Y(y)
 &=\frac12\left(\int_Yg\,dP_Y-\int_Yg\,dQ_Y\right)\\
 &=\frac12\int_X\int_Yg(y)K(x,dy)\,(dP-dQ)(x)\\
 &=\int_{X\times Y}d_X(x)g(y)\,d\rho(x,y).
\end{aligned}
\]

This is the defining identity for conditional expectation.  Subtracting `d_Y(Y)` proves
`(PMP.9)`.  No density positivity or finite-divergence hypothesis is required.

## 3. Exact information-current conservation

Define triangular discrimination by

\[
 \Delta(P,Q)=\int\frac{(dP-dQ)^2}{dP+dQ}
 =2\int_Xd_X^2\,d\eta,
 \tag{PMP.10}
\]

and define coherence work

\[
 \mathcal W(P,Q)=4\|d_X\|_{L^2(\eta)}^2=2\Delta(P,Q).
 \tag{PMP.11}
\]

### Theorem 3.1 — exact Pythagorean data-processing gap

For every common observation kernel `K`,

\[
 \boxed{
 \mathcal W(P,Q)
 =\mathcal W(P_Y,Q_Y)+4\|j_K\|_{L^2(\rho)}^2.}
 \tag{PMP.12}
\]

Equivalently,

\[
 \boxed{
 \Delta(P,Q)
 =\Delta(P_Y,Q_Y)+2\|j_K\|_{L^2(\rho)}^2.}
 \tag{PMP.13}
\]

#### Proof

Conditional expectation is the orthogonal projection from `L^2(rho)` onto the closed subspace of
`Y`-measurable functions.  By `(PMP.7)`--`(PMP.9)`,

\[
 \|d_X(X)\|_2^2=\|d_Y(Y)\|_2^2+\|j_K\|_2^2.
\]

The first two norms are the work terms in `(PMP.11)`.  Multiplying by four proves `(PMP.12)`;
dividing by two proves `(PMP.13)`.

This turns a data-processing inequality into an exact conservation law.  Observer-visible contrast
plus vertical current reconstructs the complete quadratic information.

## 4. Equality is exactly common recovery

### Theorem 4.1 — zero current, equality, and Blackwell sufficiency

The following are equivalent:

1. `j_K=0` `rho`-almost everywhere;
2. `d_X(X)=d_Y(Y)` `rho`-almost everywhere;
3. `Delta(P,Q)=Delta(P_Y,Q_Y)`;
4. there exists a Markov kernel `L:Y -> X` such that

   \[
    P_YL=P,\qquad Q_YL=Q.
    \tag{PMP.14}
   \]

Thus equality is not merely a scalar coincidence.  It is exact recoverability of the binary
experiment.

#### Proof

The equivalence of 1--3 follows from `(PMP.8)` and `(PMP.13)`.

Assume 2.  Standard Borelness supplies a regular conditional distribution

\[
 L(y,dx)=\rho(dx\mid y)
 \tag{PMP.15}
\]

of `X` given `Y` under the balanced law.  Since `d_X(X)=d_Y(Y)` under `rho`, for measurable
`A subset X`,

\[
\begin{aligned}
 (P_YL)(A)
 &=\int_Y(1+d_Y(y))L(y,A)\,d\eta_Y(y)\\
 &=\int_{X\times Y}\mathbf1_A(x)(1+d_X(x))\,d\rho(x,y)\\
 &=P(A).
\end{aligned}
\]

Replacing `+` by `-` gives `Q_YL=Q`, proving 4.

Conversely, if `(PMP.14)` holds, triangular-discrimination data processing along `K` and then `L`
gives

\[
 \Delta(P,Q)\ge\Delta(P_Y,Q_Y)\ge\Delta(P_YL,Q_YL)=\Delta(P,Q).
\]

Hence equality holds and 3 implies 1.

## 5. Finite observation histories

Let

\[
 X_0\xrightarrow{K_0}X_1\xrightarrow{K_1}\cdots
 \xrightarrow{K_{n-1}}X_n
 \tag{PMP.16}
\]

be a finite Markov chain of standard Borel observation spaces.  Let `rho_n` be its path law with
initial law `eta_0`.  For `f in L^2(eta_0)`, define

\[
 f_k(X_k)=\mathbb E_{\rho_n}[f(X_0)\mid X_k],
 \qquad
 r_k=f_k(X_k)-f_{k+1}(X_{k+1}).
 \tag{PMP.17}
\]

### Theorem 5.1 — orthogonal history decomposition

The residuals are pairwise orthogonal and orthogonal to `f_n(X_n)`.  Moreover,

\[
 \boxed{
 f(X_0)=f_n(X_n)+\sum_{k=0}^{n-1}r_k}
 \quad\text{in }L^2(\rho_n),
 \tag{PMP.18}
\]

and

\[
 \boxed{
 \|f\|_{L^2(\eta_0)}^2
 =\|f_n\|_{L^2(\eta_n)}^2+
   \sum_{k=0}^{n-1}\|r_k\|_{L^2(\rho_n)}^2.}
 \tag{PMP.19}
\]

#### Proof

The Markov property gives

\[
 \mathbb E[f_k(X_k)\mid X_{k+1}]=f_{k+1}(X_{k+1}),
\]

so `E[r_k | X_{k+1}]=0`.  Every later residual and `f_n(X_n)` is measurable with respect to the
future beginning at `X_{k+1}`.  Conditional expectation therefore makes `r_k` orthogonal to all
later terms.  Identity `(PMP.18)` telescopes.  Taking squared norms yields `(PMP.19)`.

### Corollary 5.2 — global reconstruction and properness

Define

\[
 \Gamma_n f=(f_n,r_0,\ldots,r_{n-1}).
 \tag{PMP.20}
\]

Then

\[
 \Gamma_n:L^2(\eta_0)longrightarrow
 L^2(\eta_n)\oplus\bigoplus_{k=0}^{n-1}L^2(\rho_n)
 \tag{PMP.21}
\]

is a linear isometry.  Hence it is injective, its image is closed, its inverse on its image is the
sum in `(PMP.18)`, and it is topologically proper onto its image.

#### Proof

Linearity follows from conditional expectation.  Equation `(PMP.19)` is the isometry identity.
An isometric image of a complete space is closed.  The inverse on that image is continuous; hence
the preimage of a compact subset of the image is compact.

This is the required global formation/properness theorem: observed endpoint alone can be lossy,
but endpoint plus every vertical current is an exact, closed, proper encoding of source data.

## 6. Infinite histories and tail selection

Let `(X_k)_{k>=0}` be an infinite Markov chain with path law `rho_infty`.  Put

\[
 \mathcal F_k=\sigma(X_k,X_{k+1},\ldots),
 \qquad
 \mathcal F_\infty=\bigcap_{k\ge0}\mathcal F_k.
 \tag{PMP.22}
\]

The Markov property identifies

\[
 f_k(X_k)=\mathbb E[f(X_0)\mid\mathcal F_k].
 \tag{PMP.23}
\]

### Theorem 6.1 — reverse-martingale polarization reconstruction

There is an `f_infty in L^2(F_infty)` such that `f_k -> f_infty` in `L^2`, and

\[
 \boxed{
 \|f\|_2^2=\|f_\infty\|_2^2+
 \sum_{k=0}^{\infty}\|r_k\|_2^2.}
 \tag{PMP.24}
\]

The analysis map

\[
 \boxed{
 \Gamma_\infty f=(f_\infty,(r_k)_{k\ge0})}
 \tag{PMP.25}
\]

is a linear isometry into

\[
 L^2(\mathcal F_\infty)\oplus
 \ell^2(\mathbb N;L^2(\rho_\infty)).
 \tag{PMP.26}
\]

#### Proof

The sigma-fields `F_k` decrease.  The reverse martingale convergence theorem gives
`f_k -> E[f|F_infty]` in `L^2`; call the limit `f_infty`.  Applying `(PMP.19)` to every finite
prefix and passing to the limit proves `(PMP.24)`.  Equation `(PMP.24)` proves `(PMP.25)` is an
isometry.

### Corollary 6.2 — exact selection gate

Apply Theorem 6.1 to the initial posterior contrast `d_0`.  Then

\[
 \boxed{
 \mathcal W(P_0,Q_0)=
 4\|d_\infty\|_2^2+4\sum_{k\ge0}\|r_k(d_0)\|_2^2.}
 \tag{PMP.27}
\]

Consequently

\[
 P_0=Q_0
 \quad\Longleftrightarrow\quad
 d_\infty=0\text{ and }r_k(d_0)=0\text{ for every }k.
 \tag{PMP.28}
\]

This is not an RH proof.  It replaces the vague requirement “all routes lose no decisive
information” by a typed target: prove that the physical source contrast has zero tail component and
zero vertical current at every declared observer exit.

## 7. Fisher tangent law

Let `P_t,Q_t` be a reflected regular exponential pair with balanced center `P_0=Q_0=eta`, score
`T in L^2(eta)`, and

\[
 d_t/t\longrightarrow T
 \quad\text{in }L^2(\eta).
 \tag{PMP.29}
\]

For a fixed observation `K`, Theorem 2.1 gives

\[
 \frac{d_{t,Y}}t\longrightarrow\mathbb E[T\mid Y],
 \qquad
 \frac{j_{K,t}}t\longrightarrow T-\mathbb E[T\mid Y].
 \tag{PMP.30}
\]

Hence

\[
 \boxed{
 \frac{\mathcal W(P_t,Q_t)}{t^2}
 \longrightarrow
 4\|\mathbb E[T\mid Y]\|_2^2+
 4\|T-\mathbb E[T\mid Y]\|_2^2
 =4\|T\|_2^2.}
 \tag{PMP.31}
\]

For a serial observation tower this becomes the martingale-difference ANOVA of Fisher information.

## 8. Independent fourth-organ prediction: P/R Möbius--Hardy cell

The mechanism above was derived without using the Hedenmalm P/R corpus.  It predicts that every
binary hyperbolic polarization should admit a two-point posterior experiment in which its squared
Cayley coordinate is exactly one-step vertical information loss.

The formal corpus independently proves, for `u,v>-1/2`,

\[
 c(u,v)=\tanh(\eta(u)-\eta(v)),
 \qquad
 g(u,v)=\operatorname{sech}(\eta(u)-\eta(v)),
 \tag{PMP.32}
\]

and

\[
 \boxed{c(u,v)^2+g(u,v)^2=1.}
 \tag{PMP.33}
\]

Here `c` is the source Cayley discrepancy and `g` the normalized Hardy Gram.  This is certified by

- `mobiusCriticalTwoSidedCayleyDiscrepancy_eq_tanh_rapidity_sub`;
- `mobiusCriticalTwoSidedUnitHardyGram_eq_inv_cosh_rapidity_sub`;
- `sq_mobiusCriticalTwoSidedCayleyDiscrepancy_add_sq_unitHardyGram`.

Set `delta=eta(u)-eta(v)`.  On `Omega={-1,+1}` with balanced law `eta_Omega({epsilon})=1/2`, define

\[
 P_\delta(\epsilon)=\frac{e^{\epsilon\delta}}{2\cosh\delta},
 \qquad
 Q_\delta(\epsilon)=\frac{e^{-\epsilon\delta}}{2\cosh\delta}.
 \tag{PMP.34}
\]

Their posterior contrast is

\[
 d_\Omega(\epsilon)=\epsilon\tanh\delta=\epsilon c(u,v),
 \tag{PMP.35}
\]

and their visibility is `sech(delta)=g(u,v)`.  Under the sign-forgetting observation
`Omega -> {*} `, the observed contrast is zero, so Theorem 3.1 gives

\[
 \boxed{
 \mathcal W(P_\delta,Q_\delta)=4c(u,v)^2,
 \qquad
 \|j\|_2^2=c(u,v)^2.}
 \tag{PMP.36}
\]

Thus the formal P/R Julia identity `(PMP.33)` is exactly the single-edge posterior projection law:
Hardy visibility is retained amplitude, while Cayley discrepancy is vertical contrast energy.
This is a fourth-organ verification, not an input or analogy.

## 9. Hostile conjecture loops

### Loop A — every positive Julia pair is an observation theorem

**False.**  An abstract pair `a^2+d^2=1` does not supply a Markov kernel or identify `d` as a
conditional expectation.

**Survivor.**  A Julia cell becomes source-typed exactly when a binary experiment and an observer
kernel realize its contrast projection.  Section 8 constructs such a realization for the P/R cell.

### Loop B — scalar data processing is enough

**False.**  The inequality `Delta(PY,QY)<=Delta(P,Q)` does not reconstruct lost information.

**Survivor.**  The residual `j_K` upgrades the inequality to the exact identity `(PMP.13)`.

### Loop C — endpoint plus total lost energy reconstructs the source

**False.**  A norm does not recover the direction of a residual.

**Survivor.**  Endpoint plus the residual vector reconstructs source contrast; a complete history
requires every `r_k`, not only their squared norms.

### Loop D — posterior martingales alone select RH

**False.**  Any binary experiment generates posterior martingales, on or off a distinguished
parameter locus.

**Survivor.**  Selection is the source theorem that the physical contrast has zero tail and zero
vertical currents in `(PMP.28)`.

### Loop E — global properness requires a uniform local likelihood gap

**False.**  One multiplication-current operator can have dense nonclosed range even though the
full history analysis map is an isometry.

**Survivor.**  Properness belongs to the joint endpoint-plus-current formation, not necessarily to
any scalar current projection.

### Loop F — hypertranscendence is noncompact posterior motion

**False.**  Posterior processes may be recurrent or precompact while analytic prolongation rank is
unbounded.

**Survivor.**  The present theorem controls information carried by a declared observer tower; it
does not identify differential-transcendence rank with topological escape.

## 10. Parent boundary and literature audit

The ingredients are established mathematics:

- conditional expectation and orthogonal martingale differences;
- Blackwell sufficiency and binary statistical experiments;
- triangular discrimination and `f`-divergence data processing;
- posterior probabilities as bounded martingales.

Reid--Williamson,
[*Information, Divergence and Risk for Binary Experiments*](https://arxiv.org/abs/0901.0356),
already unifies binary experiments, proper losses, and `f`-divergences.  Nogales,
[*Conditional Expectation of a Markov Kernel Given Another*](https://arxiv.org/abs/1306.0084),
develops conditional expectation and sufficiency for Markov kernels.  Campbell--Engelund,
[*Embedding martingale diffusions as binary posteriors in sequential inference*](https://arxiv.org/abs/2607.20373),
shows in current work that broad martingale diffusions can be realized as binary posteriors.

Therefore no external novelty claim is made for posterior martingales, Pythagoras, or sufficiency.
The corpus-level advance is the exact Frankenstein mechanism:

\[
 \boxed{
 \text{likelihood polarization}
 \to\text{Markov conditional projection}
 \to\text{vertical information current}
 \to\text{orthogonal history}
 \to\text{global isometric reconstruction}
 \to\text{P/R Julia realization}.}
 \tag{PMP.37}
\]

Unlike the failed two-lift proposal, every arrow is typed by an actual source/observer morphism.

## 11. Exact limits and next gate

This theorem does **not** prove that the corpus routes arise from one common binary experiment.  It
does **not** identify the physical Xi defect with any `r_k`.  It does **not** prove tail triviality,
and it does **not** prove RH.

The next theorem must construct a literal pre-zero observer tower from the arithmetic source and a
coefficient-faithful map

\[
 d_{\mathrm{source}}
 \longmapsto
 (d_\infty,r_0,r_1,\ldots)
 \tag{PMP.38}
\]

whose components land in at least the positive P/R, Mass/affine, and recurrence/history organs.
Only after that formation map exists can a source identity forcing the right side of `(PMP.38)` to
vanish become a selection theorem.

## 12. Lean boundary

The Lean corpus was audited read-only.  It already formalizes the independent P/R identities cited
in Section 8 and several Hellinger/common-recovery laws.  No Lean file was written or built in this
research pass.  Formalization is deferred until hostile review of this paper theorem and its
standard-Borel sufficiency hypotheses closes.

## Log

- 2026-08-14 — generated after hostile audit showed that the sign-blind Julia lift was not a
  source-derived recovery lift.
- 2026-08-14 — proved conditional-expectation transport, exact triangular-current conservation,
  common-recovery equivalence, finite/infinite orthogonal reconstruction, and properness.
- 2026-08-14 — predicted a two-point posterior realization of the P/R Cayley--Hardy Julia cell;
  verified it against three existing Lean-certified P/R identities.
- 2026-08-14 — hostile literature audit classified all parent ingredients as occupied; retained the
  typed corpus fusion and the explicit source-tower gate.
