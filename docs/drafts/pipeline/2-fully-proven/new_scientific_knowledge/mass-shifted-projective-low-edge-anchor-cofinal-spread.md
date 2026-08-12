# Low-edge anchoring forces cofinal Gauss spread and harmonic projective work

- **ID:** mass-shifted-projective-low-edge-anchor-cofinal-spread
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, cofinal projective curvature renewal
- **Type:** THEOREM + FRONTIER REDUCTION (paper)
- **Scientific status:** [PAPER-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [LEAN GATED] [NOT RH]
- **Depends on:** mass-shifted-projective-arithmetic-surplus,
  mass-shifted-projective-next-admission-renewal,
  mass-shifted-projective-gauss-root-renewal, and fixed-degree shifted-Xi arcsine recession
- **Statement:** Admission-root spread is strictly increasing with degree and diverges after
  hard-edge normalization on every cofinal positive-block schedule. Independently, fixed low
  Jacobi edge gives projective-clock work rate at least \((1-o(1))/(2n+1)\), uniformly over all
  escaping degrees.

## 1. Exact gain

Previous renewal classification allowed current hard-edge root spread, terminal mismatch, and both
boundary edges to collapse together. Absolute root-spread collapse is impossible. Root spread
contains every earlier positive Jacobi edge, while each fixed edge has nonzero shifted-arcsine
limit.

Same retained inventory gives more. One fixed diagonal coordinate and first positive Jacobi edge
anchor scale-free source work, regardless of all high-degree coordinates. Thus reciprocal
projective clock cannot move more slowly than harmonic order \(1/n\).

These conclusions use no computation, numerical bound, RH premise, root interval, or
degree-uniform moment convergence.

## 2. Degree-renewal identity for root spread [PROVED HERE]

Let \(s\) be a positive moment sequence through required finite block. Write

\[
 \alpha_j=\alpha_j(s),\qquad \beta_j=\beta_j(s)>0\quad(j\ge1)
\]

for monic Jacobi coordinates. For \(n\ge2\), current admission-root spread is

\[
 G_n
 =\sum_{j<n}\alpha_j^2
   -{1\over n}\left(\sum_{j<n}\alpha_j\right)^2
   +2\sum_{j<n}\beta_j.                                  \tag{LAR.1}
\]

Put

\[
 \bar\alpha_n={1\over n}\sum_{j<n}\alpha_j.
\]

Then

\[
 \boxed{\qquad
 G_{n+1}-G_n
 ={n\over n+1}(\alpha_n-\bar\alpha_n)^2+2\beta_n>0.
 \qquad}                                                  \tag{LAR.2}
\]

### Proof

Beta inventory in (LAR.1) gains exactly \(2\beta_n\). For diagonal dispersion, put
\(A=\sum_{j<n}\alpha_j\). Direct completion of square gives

\[
\begin{aligned}
 &\left(\sum_{j<n}\alpha_j^2+\alpha_n^2
       -{(A+\alpha_n)^2\over n+1}\right)
 -\left(\sum_{j<n}\alpha_j^2-{A^2\over n}\right)\\
 &\hspace{35mm}
 ={(n\alpha_n-A)^2\over n(n+1)}
 ={n\over n+1}(\alpha_n-\bar\alpha_n)^2.                 \tag{LAR.3}
\end{aligned}
\]

Finite positive-block admission gives \(\beta_n>0\), proving strictness. Current Gauss spread is
a capital account: adding one admission degree adds usual online-variance increment and one
strictly positive Christoffel edge.

## 3. Cofinal normalized spread divergence [PROVED HERE]

Let

\[
 s_w(k)= {2w^{2k+1}\over\log w}\Re M_{w^2}(k)             \tag{LAR.4}
\]

be exact shifted-Xi far-right normalized moment sequence. Suppose

\[
 w_\ell\longrightarrow\infty,\qquad
 n_\ell\longrightarrow\infty,
 \qquad
 H_{n_\ell+2}(s_{w_\ell})>0.                              \tag{LAR.5}
\]

Then

\[
 \boxed{\qquad
 G_{n_\ell}(s_{w_\ell})\longrightarrow+\infty.
 \qquad}                                                  \tag{LAR.6}
\]

### Proof without diagonal rate

For every fixed \(j\ge1\), corpus recession gives

\[
 \beta_1(s_w)\longrightarrow {1\over8},\qquad
 \beta_j(s_w)\longrightarrow {1\over16}\quad(j\ge2).      \tag{LAR.7}
\]

Fix arbitrary positive target \(A\). Choose fixed integer \(J\) so large that \(J/16>A\).
Because indices \(1\le j\le J\) form a finite set, (LAR.7) implies that, for all sufficiently
large \(\ell\),

\[
 2\sum_{1\le j\le J}\beta_j(s_{w_\ell})>A.               \tag{LAR.8}
\]

Also \(n_\ell>J+1\). Positive block in (LAR.5) makes diagonal dispersion nonnegative, so
(LAR.1) and (LAR.8) give

\[
 G_{n_\ell}(s_{w_\ell})
 \ge2\sum_{1\le j\le J}\beta_j(s_{w_\ell})>A.
\]

Since \(A\) was arbitrary, (LAR.6) follows. Quantifiers are load-bearing: \(J\) is fixed before
recession is invoked. No assertion uniform in all \(j\le n_\ell\) is used.

## 4. Literal hard-edge consequence

Let \(y=w^2\), and let \(G_n^{\rm raw}(y)\) be spread in actual reciprocal coordinate. Exact
Jacobi transport gives

\[
 \alpha_j(s_w)=y\alpha_j^{\rm raw}(y),\qquad
 \beta_j(s_w)=y^2\beta_j^{\rm raw}(y),
\]

and hence

\[
 G_n(s_w)=y^2G_n^{\rm raw}(y).                            \tag{LAR.9}
\]

For literal hard coordinate \(z=2yX-1\), affine spread covariance gives

\[
 G_n^{\rm hard}(y)=4y^2G_n^{\rm raw}(y)=4G_n(s_w).       \tag{LAR.10}
\]

Therefore every cofinal schedule in (LAR.5) satisfies

\[
 \boxed{\qquad G_{n_\ell}^{\rm hard}(w_\ell^2)\to+\infty.\qquad} \tag{LAR.11}
\]

Prior absolute-concentration escape \(G_n^{\rm hard}\to0\) is closed. This does not yet give
\(G_n^{\rm hard}/n\) bounded below: sublinear hard outliers can carry diverging unnormalized
spread while empirical spread per root vanishes.

## 5. Low-edge anchored projective coercivity [PROVED HERE]

Fix \(n\ge2\) in positive admission block. Put

\[
 c=2n+1,\qquad
 F=2\sum_{j<n}\alpha_j+\alpha_n,\qquad
 \mu={F\over c}.
\]

Let \(\mathfrak S_n=cD_n-F^2\) be literal projective arithmetic surplus. Its exact retained split
is

\[
 \mathfrak S_n=V_n+B_n,                                  \tag{LAR.12}
\]

where

\[
\begin{aligned}
 V_n&=c\left(2\sum_{j<n}\alpha_j^2+\alpha_n^2\right)-F^2,\\
 B_n&=c\left(4\sum_{j<n}\beta_j
             +2(n+1)(\beta_n+\beta_{n+1})\right).
\end{aligned}
\]

Variance term has exact centered form

\[
 V_n=c\left(
 2\sum_{j<n}(\alpha_j-\mu)^2+(\alpha_n-\mu)^2\right).     \tag{LAR.13}
\]

Set \(a=\alpha_0\) and \(b=\beta_1\). Positivity and \(n\ge2\) give

\[
 \mathfrak S_n
 \ge c\left(2(a-\mu)^2+4b\right).                        \tag{LAR.14}
\]

Define low-edge anchor

\[
 \lambda(s)={4b\over a^2+2b}>0.                          \tag{LAR.15}
\]

Following exact square proves sharp scalar optimization:

\[
 2(a-\mu)^2+4b-\lambda(s)\mu^2
 ={2\over a^2+2b}\left(a\mu-(a^2+2b)\right)^2\ge0.       \tag{LAR.16}
\]

Combining (LAR.14)--(LAR.16) yields degree-uniform source inequality

\[
 \boxed{\qquad
 \mathfrak S_n\ge{\lambda(s)\over 2n+1}F^2.
 \qquad}                                                  \tag{LAR.17}
\]

Whenever \(F\ne0\), projective-clock law therefore gives

\[
 {d\over dy}\left({2n+1\over F_n(y)}-y\right)
 ={\mathfrak S_n(y)\over F_n(y)^2}
 \ge{\lambda(s_y)\over2n+1}.                              \tag{LAR.18}
\]

This is not fixed-degree asymptotic. Right side depends only on first two Jacobi coordinates,
not on \(n\).

## 6. Uniform shifted-Xi harmonic work

Low normalized Jacobi limits are

\[
 \alpha_0(s_w)\to{1\over2},\qquad
 \beta_1(s_w)\to{1\over8}.                               \tag{LAR.19}
\]

Consequently

\[
 \lambda(s_w)\longrightarrow
 {4(1/8)\over(1/2)^2+2(1/8)}=1.                          \tag{LAR.20}
\]

Anchor is invariant under actual/normalized reciprocal-mass dilation because \(\alpha_0^2\) and
\(\beta_1\) have same coordinate weight. Hence there exists \(w_0\), independent of degree, such
that every \(w\ge w_0\), every \(n\ge2\), and every positive \((n+2)\) admission block obeys

\[
 \boxed{\qquad
 F_n(w^2)\ne0
 \Longrightarrow
 {d\over dy}\left({2n+1\over F_n(y)}-y\right)_{y=w^2}
 \ge {1\over2(2n+1)}.
 \qquad}                                                  \tag{LAR.21}
\]

Thus cofinal projective work cannot decay faster than harmonic degree order. This closes former
possibility of arbitrarily small work rate caused solely by diagonal Jacobi shape or monic norm
collapse.

## 7. Route-U consequence and exact residual

At parabolic first-contact scale, selected defective degrees satisfy \(n\asymp\sqrt y\). Across
an unbroken positive-chamber interval, (LAR.21) charges at least constant multiple of

\[
 \int {dy\over n(y)}\asymp\int {dy\over\sqrt y},
\]

which is non-summable. Route can no longer hide through absolute hard-root concentration or
through work rate \(o(1/n)\).

This does not yet prove RH. At degree change,

\[
 \left({2n+3\over F_{n+1}}-y\right)
 -\left({2n+1\over F_n}-y\right)
 ={2F_n-(2n+1)(\alpha_n+\alpha_{n+1})\over F_nF_{n+1}},  \tag{LAR.22}
\]

whose sign is not fixed by positive moment geometry. Sparse schedule can reset scalar clock
unless cumulative negative jumps are charged to a degree-monotone account.

Exact next conjecture is:

> **Discrete reset conjecture.** Total negative part of adjacent-clock jumps (LAR.22) along
> canonical strict-frontier schedule is bounded by increase of normalized weighted trace variance
> or hard Gauss spread.

Online-variance identity (LAR.2) is only current cross-degree positive account with right source
provenance. Proving or killing this jump-charge inequality is now hard synchronization problem.

## 8. Conjecture -> proof/failure -> pivot

1. **Conjecture:** retained hard-root spread may collapse absolutely on cofinal diagonal.
   **FALSIFIED** by (LAR.6)--(LAR.11). Fixed low Jacobi edges accumulate before degree limit and
   force divergence.
2. **Conjecture:** cofinal divergence requires uniform asymptotic for all recurrence coefficients
   below moving degree. **FALSIFIED.** Fixed-prefix argument in Section 3 uses no diagonal rate.
3. **Conjecture:** high-degree projective work rate can be arbitrarily smaller than \(1/n\)
   because weighted trace mean can dominate variance. **FALSIFIED.** Fixed pair
   \((\alpha_0,\beta_1)\) gives sharp anchor (LAR.17).
4. **Conjecture:** harmonic continuous work alone telescopes across degree renewals.
   **FAILED AS AN INFERENCE.** Exact reset (LAR.22) has no generic sign.
5. **Pivot:** charge negative discrete resets to strictly increasing spread account, or replace
   scalar clock by joint mean--variance potential whose continuous and discrete increments are
   both positive.

## 9. Higher universal principle

Projective arithmetic surplus is coefficient-of-variation energy of growing weighted empirical
Jacobi packet, plus positive edge inventory. Mass transport dissipates its mean; degree transport
adds two observations and one Christoffel edge. Earlier free-flight versus renewal language split
these two views. They are continuous and discrete parts of one mean--variance process:

\[
\begin{array}{c}
 \text{mass motion}\\[-1mm]
 F_n'=-D_n
\end{array}
\quad\longleftrightarrow\quad
\begin{array}{c}
 \text{degree motion}\\[-1mm]
 G_{n+1}-G_n=
 {n\over n+1}(\alpha_n-\bar\alpha_n)^2+2\beta_n.
\end{array}                                               \tag{LAR.23}
\]

Scalar clocks kept failing because they retain mean but discard variance capital that pays for
changing dimension.

## 10. Corpus, literature, and Lean audit

- **Corpus.** Existing projective-renewal modules prove positivity and exact root-spread
  decomposition. Searches found no degree-update identity (LAR.2), cofinal divergence theorem
  (LAR.6), low-edge anchor (LAR.17), or uniform harmonic clock bound (LAR.21).
- **Classical parentage.** Online variance updates and finite Jacobi trace identities are
  classical. Literature on recurrence coefficients and zero distributions, including Hardy,
  *Polynomial Ensembles and Recurrence Coefficients* (arXiv:1709.01287), studies global
  asymptotics under recurrence hypotheses. Located literature does not supply shifted-Xi
  fixed-prefix/cofinal argument or literal projective source bound.
- **Novelty status.** No priority is claimed for (LAR.2) or (LAR.16) as abstract algebra.
  Candidate-new content is source-specific fusion with shifted-Xi recession, yielding (LAR.6),
  (LAR.11), and degree-uniform literal bound (LAR.21).
- **Lean status.** No declaration is added yet. Theorem is literal and formalizable using existing
  Jacobi/root-spread modules, but formal work is gated until discrete reset conjecture is proved or
  falsified. Adding isolated algebraic wrappers now would not close synchronization wall and
  would violate no-theatre rule.

## 11. Log

- 2026-08-12 — degree-renewal spread identity, rate-free cofinal divergence, low-edge projective
  anchor, and uniform harmonic work bound proved; discrete reset isolated as sole surviving
  synchronization obstruction.
