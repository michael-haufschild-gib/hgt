# Low-edge anchoring forces cofinal Gauss spread and harmonic projective work

- **ID:** mass-shifted-projective-low-edge-anchor-cofinal-spread
- **Stage:** 3-formalized
- **Route:** U, cofinal projective curvature renewal
- **Type:** THEOREM + FRONTIER REDUCTION (paper)
- **Scientific status:** [PAPER-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [LEAN-PROVED SURVIVOR] [NOT RH]
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

whose sign is not fixed by positive moment geometry. Sparse schedule can reset scalar clock.
The natural first conjecture was that ordinary weighted variance or Gauss spread pays those
jumps. Sections 8--9 kill that conjecture at exact positive-moment level and identify missing
metric factor.

## 8. Exact adjacent-mean transport and denominator barrier [PROVED HERE]

Keep \(c=2n+1\), and define weighted packet mean and centered square sum

\[
 \mu_n={F_n\over c},\qquad
 E_n={V_n\over c}
 =2\sum_{j<n}(\alpha_j-\mu_n)^2+(\alpha_n-\mu_n)^2.       \tag{LAR.23}
\]

Passing from degree \(n\) to \(n+1\) adds one extra copy of \(\alpha_n\) and one new observation
\(\alpha_{n+1}\). Put

\[
 q_n={\alpha_n+\alpha_{n+1}\over2},\qquad
 \delta_n=\mu_{n+1}-\mu_n.
\]

The two-observation online-variance identity is

\[
 \boxed{
 E_{n+1}-E_n
 ={(\alpha_n-\alpha_{n+1})^2\over2}
  +{2c\over c+2}(q_n-\mu_n)^2,
 \qquad
 \delta_n={2(q_n-\mu_n)\over c+2}.}                     \tag{LAR.24}
\]

In particular,

\[
 E_{n+1}-E_n\ge {c(c+2)\over2}\delta_n^2.               \tag{LAR.25}
\]

If \(\mu_n,\mu_{n+1}>0\), write \(x^-=\max\{-x,0\}\). Since scalar projective clock is
\(\mathcal G_n=1/\mu_n-y\), (LAR.25) gives exact generic reset estimate

\[
 \boxed{
 (\mathcal G_{n+1}-\mathcal G_n)^-
 ={(\delta_n)^+\over\mu_n\mu_{n+1}}
 \le {1\over\mu_n\mu_{n+1}}
 \sqrt{{2(E_{n+1}-E_n)\over c(c+2)}}.}                  \tag{LAR.26}
\]

Thus Euclidean variance controls Euclidean mean displacement, while reciprocal-clock motion sees
singular metric \(d\mu/\mu^2\). Any reset theorem omitting denominator is structurally false.

### Proof

For weighted packet of total mass \(c\), mean \(\mu_n\), and centered square sum \(E_n\), adding
two unit observations \(x,z\) changes centered square sum by

\[
 {1\over2}(x-z)^2+{2c\over c+2}\left({x+z\over2}-\mu_n\right)^2.
\]

This follows by expanding both centered sums, or by decomposing new packet into old packet and
two-point packet. Substitute \(x=\alpha_n\), \(z=\alpha_{n+1}\). Mean update is direct;
substitution into between-packet term gives (LAR.25). Finally

\[
 {1\over\mu_{n+1}}-{1\over\mu_n}
 =-{\delta_n\over\mu_n\mu_{n+1}},
\]

which proves (LAR.26).

## 9. Exact positive-Jacobi counterfamily [FALSIFIES ORDINARY RESET CHARGE]

Fix \(a,b>0\), \(0<\varepsilon\le1\), and degree \(n=2\). Choose Jacobi diagonal data

\[
 \alpha_0=a,\qquad
 \alpha_1={\varepsilon\over4}-a,\qquad
 \alpha_2=\alpha_3={\varepsilon\over2},                 \tag{LAR.27}
\]

and positive edges

\[
 \beta_1=b,\qquad \beta_2=\varepsilon^2,
\]

with arbitrary positive bounded continuation. Such data are realized by spectral measure of
bounded infinite Jacobi matrix; positivity of every edge makes its moment Hankel blocks strictly
positive definite.

Exact substitution gives

\[
 F_2=\varepsilon,\qquad F_3=2\varepsilon,
\qquad
 \mathcal G_3-\mathcal G_2=-{3\over2\varepsilon}.       \tag{LAR.28}
\]

But ordinary variance and root-spread increments are

\[
 E_3-E_2={9\over70}\varepsilon^2,
 \qquad
 G_3-G_2={67\over32}\varepsilon^2.                     \tag{LAR.29}
\]

Moreover \(E_2\to4a^2\) and \(G_2\to2a^2+2b\). Hence negative reset diverges while both
increments vanish and both total accounts stay bounded. No uniform linear/coercive charge by
ordinary weighted variance or Gauss spread can hold; more strongly, no locally bounded function
of these four total accounts can bound reset. This failure persists with fixed positive low-edge
anchor \((\alpha_0,\beta_1)=(a,b)\).

This does not falsify Xi-specific theorem with extra arithmetic input. It proves exactly what
that input must do: control denominator in (LAR.26), or directly control hyperbolic reset action

\[
 \mathcal H_n={E_{n+1}-E_n\over\mu_n^2\mu_{n+1}^2}.      \tag{LAR.30}
\]

Two sufficient corrected Route-U mechanisms to seek on canonical strict frontier are:

1. scale-correct normalized-flux floor strong enough to reduce (LAR.26) to summable Euclidean
   variance budget; or
2. literal prime--Gamma/global-Xi upper budget on cumulative hyperbolic action (LAR.30).

Ordinary root spread and angular outlier energy do not supply either statement.

## 10. Conjecture -> proof/failure -> pivot

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
5. **Conjecture:** normalized variance or Gauss-spread increase pays negative reciprocal-clock
   resets. **FALSIFIED** by (LAR.27)--(LAR.29), even with fixed positive low-edge anchor.
6. **Pivot:** price degree transport in reciprocal-mean geometry. Exact survivor is (LAR.26);
   remaining arithmetic target is normalized-flux floor or cumulative hyperbolic-action budget.

## 11. Higher universal principle

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
\end{array}                                               \tag{LAR.31}
\]

Scalar clocks kept failing because they retain mean but discard variance capital that pays for
changing dimension. Reset no-go sharpens this: even retained Euclidean variance does not pay
motion after reciprocal projection. Projectivization changes metric. Correct discrete capital is
variance weighted by inverse fourth mean scale, exactly (LAR.30). Obstruction is not missing
positivity lemma; it is mismatch between Euclidean Jacobi transport and hyperbolic projective
observation.

## 12. Corpus, literature, and Lean audit

- **Corpus.** Existing projective-renewal modules prove positivity, exact root-spread
  decomposition, and failure of adjacent-clock sign. Existing angular-energy theorem prices
  outlier count by ordinary spread but does not control reciprocal-mean resets. Searches found no
  degree-update identity (LAR.2), cofinal divergence theorem (LAR.6), low-edge anchor (LAR.17),
  uniform harmonic clock bound (LAR.21), exact reset barrier (LAR.26), or counterfamily
  (LAR.27)--(LAR.29).
- **Classical parentage.** Online variance updates and finite Jacobi trace identities are
  classical. Literature on recurrence coefficients and zero distributions, including Hardy,
  *Polynomial Ensembles and Recurrence Coefficients* (arXiv:1709.01287), studies global
  asymptotics under recurrence hypotheses. Located literature does not supply shifted-Xi
  fixed-prefix/cofinal argument or literal projective source bound.
- **Novelty status.** No priority is claimed for (LAR.2), (LAR.16), or (LAR.24) as abstract
  algebra. Candidate-new content is source-specific fusion with shifted-Xi recession, yielding
  (LAR.6), (LAR.11), and degree-uniform literal bound (LAR.21), plus exact identification of
  hyperbolic reset action as remaining projective synchronization invariant.
- **Lean status.** Complete. The positive survivor—degree renewal, cofinal spread under
  positive-block admission, and uniform harmonic source work—is formalized in
  `XiShiftedCanonicalAdmissionProjectiveCofinalSpread.lean`. Sections 8–9 are now also fully
  formalized (2026-08-13) in `XiShiftedProjectiveAdjacentMeanResetBarrier.lean`: the
  two-observation online-variance identity (LAR.24, `projectiveAdmissionPacketEnergy_succ_sub`
  and `projectiveAdmissionPacketMean_succ_sub`), the variance–displacement bound (LAR.25,
  `projectiveAdmissionPacketEnergy_succ_sub_ge`), the exact reset barrier (LAR.26,
  `projectiveAdmissionScalarClock_reset_barrier`, plus its hyperbolic-action form for LAR.30,
  `projectiveAdmissionScalarClock_reset_barrier_action`), and the exact positive-Jacobi
  counterfamily (LAR.27–LAR.29): `resetCounter_clock_step` (`𝒢₃−𝒢₂ = −3/(2ε)`),
  `resetCounter_energy_step` (`= 9ε²/70`), `resetCounter_spread_step` (`= 67ε²/32`), the total
  accounts, all five limit statements, and the packaged falsification
  `resetCounter_no_locally_bounded_reset_charge` (no function of the four ordinary accounts that
  is bounded on bounded boxes dominates the negative reset). The counterfamily is realized as a
  genuine positive moment sequence through the new reusable constructive Favard module
  `HTGeometry/FavardJacobiMomentRealization.lean` (`exists_positiveMomentForm_of_jacobiData`);
  its Hankel blocks of every size are positive definite, so the falsification quantifies over
  honest admissible data. Both modules are umbrella-wired; module builds pass; axiom audit
  `[propext, Classical.choice, Quot.sound]` on all thirteen leading declarations. Lean still does
  not prove the shifted-Xi positive Hankel blocks themselves, a normalized-flux floor, the
  hyperbolic-action budget, or RH — those remain the open Route-U arithmetic target, exactly as
  Section 9 isolates.

## 13. Log

- 2026-08-12 — degree-renewal spread identity, rate-free cofinal divergence, low-edge projective
  anchor, and uniform harmonic work bound proved.
- 2026-08-12 — ordinary variance/spread reset-charge conjecture falsified by exact positive-Jacobi
  counterfamily; denominator-weighted hyperbolic action isolated as corrected synchronization
  invariant.
- 2026-08-12 — positive survivor formalized and built; semantic positive-block premise and
  denominator-weighted synchronization gap remain explicit.
- 2026-08-13 — Sections 8–9 formalized unconditionally: adjacent-mean transport, reset barrier,
  hyperbolic-action form, and the exact positive-Jacobi counterfamily with genuine moment
  realization via the new constructive Favard module. Falsification packaged as
  `resetCounter_no_locally_bounded_reset_charge`. All audits clean. Promoted to 3-formalized.
