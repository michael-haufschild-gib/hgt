# Frozen formed-history entropy classification and source-alternation no-go

- **ID:** ULF-RFDM-HIST-EXT-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md` and `reversible-formation-dilation-mechanics/endpoint-neutral-path-singular-functional-equation-reset-dilation-law.md`
- **Statement:** For a parameter frozen across the entire Bernoulli history, shift-conjugacy to its reflected frozen history is obstructed by formation entropy and geometric recovery selects the fixed point; however the source-natural functional-equation history alternates the two parameters and is shift-transported for every parameter, so the frozen selector is not a source-natural RH mechanism.
- **Status:** [PAPER-PROVED] [FROZEN-HISTORY CLASSIFICATION] [SOURCE-NATURAL SELECTOR FALSIFIED] [POSITIVE SURVIVOR RETAINED] [NOT RH]

## Goal

Separate two notions that the present corpus had not yet compared:

1. a **regenerative packet lift**, which may discard and resample the recovery coordinate; and
2. a **process lift**, which must be invertible, preserve formed history law, and commute with the
   declared clock.

The first is always information-neutral because packet recovery is split. The second has a genuine
extension obstruction. The obstruction is not fitted to an RH route: it is the entropy mismatch of
two generated processes. The Hasse--theta--KMS realization makes the same number visible in four
structurally different organs.

This card originally treated a stationary history with the formation parameter frozen at \(x\) as
the functional-equation execution. Hostile review showed that this is not the source-natural process:
the actual lift alternates \(x,-x,x,-x,\ldots\). One shift transports its phase-\(x\) law to its
phase-\(-x\) law for every \(x\). The stationary theorem below remains correct and useful as a
classification of a **frozen gauge**, but it is not a live source selector.

The surviving higher mechanism is proved in
`formation-holonomy-mechanics/split-formation-corner-flatness-vertical-normal-form-and-four-organ-conservation-law.md`:
common-recovery comparisons are flat, and only vertical transport beyond recovery can carry a
selection law.

## Gates

- [x] 0 → 1: endpoint and process lifts are separately typed; candidate is source-prior to zero specialization; exact attack supplied
- [x] 1 → 2: dependency-closed paper proof and hostile scope audit
- [ ] 2 → 3: Lean formalization
- [ ] 3 → 4: standalone publication treatment

## 1. Endpoint formation and its regenerative action

Let \(Y\) be a standard Borel observer space, let \(R:Y\to Y\) be a measurable involution, and let
\(\kappa_y\) be a measurable family of probability laws on a countable recovery alphabet \(A\).
For an observer law \(\mu\), define packet formation

\[
 \mathsf E_\kappa(\mu)(dy,da)=\mu(dy)\kappa_y(da).
 \tag{HEO.1}
\]

Projection \(\pi(y,a)=y\) recovers \(\mu\). The functional-equation action has the canonical Markov
lift

\[
 \widehat R((y,a),dy'\,da')
   =\delta_{Ry}(dy')\kappa_{Ry}(da').
 \tag{HEO.2}
\]

It recovers the observer, applies \(R\), and regenerates the recovery coordinate. Hence

\[
 \widehat R_*\mathsf E_\kappa(\mu)=\mathsf E_\kappa(R_*\mu).
 \tag{HEO.3}
\]

For any two observer laws for which extended relative entropy is defined, the split chain rule gives

\[
 D(\mathsf E_\kappa(\mu)\Vert\mathsf E_\kappa(\nu))
 =D(\mu\Vert\nu)
 =D(\mathsf E_\kappa(R_*\mu)\Vert\mathsf E_\kappa(R_*\nu)).
 \tag{HEO.4}
\]

The second equality uses that the measurable involution \(R\) is a bimeasurable bijection, so data
processing in both directions makes extended relative entropy invariant under \(R_*\).

Thus the lifted action is **endpoint-information-neutral**. Nothing in (HEO.2)--(HEO.4) makes it
deterministic on the recovery coordinate or invertible as an execution.

## 2. Formed-history lift and entropy anomaly

Fix a parameter space \(X\) with involution \(\theta\), and for each \(x\in X\) let \(p_x\) be a
probability law on a countable alphabet \(A\), with finite Shannon entropy

\[
 H(p_x)=-\sum_{a\in A}p_x(a)\log p_x(a)<\infty.
 \tag{HEO.5}
\]

Put

\[
 \Omega=A^{\mathbb Z},\qquad
 P_x=p_x^{\mathbb Z},\qquad
 (S\omega)_j=\omega_{j+1}.
 \tag{HEO.6}
\]

A **strict formed-history lift** of \(\theta\) at \(x\) is a mod-zero measurable bijection

\[
 \Theta_x:(\Omega,P_x)\longrightarrow(\Omega,P_{\theta x})
 \tag{HEO.7}
\]

with measurable inverse such that

\[
 (\Theta_x)_*P_x=P_{\theta x},
 \qquad
 \Theta_xS=S\Theta_x
 \quad\text{mod zero}.
 \tag{HEO.8}
\]

Define the formation-entropy anomaly

\[
 \mathfrak A_p(x)=H(p_x)-H(p_{\theta x}).
 \tag{HEO.9}
\]

### Theorem 2.1 -- history-extension obstruction

If a strict formed-history lift exists at \(x\), then

\[
 \boxed{\mathfrak A_p(x)=0.}
 \tag{HEO.10}
\]

Moreover,

\[
 \mathfrak A_p(\theta x)=-\mathfrak A_p(x).
 \tag{HEO.11}
\]

For two independent formation families \(p_x,q_x\), the product anomaly is additive:

\[
 \mathfrak A_{p\otimes q}(x)
 =\mathfrak A_p(x)+\mathfrak A_q(x).
 \tag{HEO.12}
\]

#### Proof

The coordinate partition of the bilateral Bernoulli shift is generating and has entropy \(H(p_x)\).
Independence makes the entropy of every \(n\)-coordinate join equal to \(nH(p_x)\), so the
Kolmogorov--Sinai entropy is

\[
 h_{\mathrm{KS}}(S,P_x)=H(p_x).
 \tag{HEO.13}
\]

A mod-zero measure-preserving conjugacy commuting with \(S\) preserves KS entropy. Applying this to
\(\Theta_x\) proves (HEO.10). Equation (HEO.11) follows from \(\theta^2=1\). Shannon entropy is
additive under independent products, which proves (HEO.12). ∎

The obstruction is exact for Bernoulli processes: by the Ornstein isomorphism theorem, in the form
extended to arbitrary standard bases by Seward, equal finite base entropy is also sufficient for
Bernoulli-shift isomorphism. The selection theorem below needs only necessity and the identity lift at
the fixed point.

## 3. Geometric recovery is reflection-separating

For logarithmic scale \(x\in\mathbb R\), put

\[
 q(x)=\frac{1-e^{-e^x}}2\in(0,1/2),
 \qquad
 p_x(n)=(1-q(x))q(x)^n\quad(n\ge0),
 \tag{HEO.14}
\]

and let \(\theta x=-x\). Its entropy is

\[
 h(q)=-\log(1-q)-\frac q{1-q}\log q.
 \tag{HEO.15}
\]

The derivatives are

\[
 q'(x)=\frac12e^{x-e^x}>0,
 \qquad
 h'(q)=-\frac{\log q}{(1-q)^2}>0.
 \tag{HEO.16}
\]

Define

\[
 \mathfrak A(x)=h(q(x))-h(q(-x)).
 \tag{HEO.17}
\]

### Theorem 3.1 -- central frozen-history classification

For the geometric formed histories \((\mathbb N^{\mathbb Z},p_x^{\mathbb Z},S)\), the following are
equivalent:

1. a strict formed-history lift from \(x\) to \(-x\) exists;
2. \(\mathfrak A(x)=0\);
3. \(x=0\).

Equivalently,

\[
 \boxed{
 (\mathbb N^{\mathbb Z},p_x^{\mathbb Z},S)
 \cong
 (\mathbb N^{\mathbb Z},p_{-x}^{\mathbb Z},S)
 \iff x=0.}
 \tag{HEO.18}
\]

#### Proof

Theorem 2.1 gives \(1\Rightarrow2\). Because \(q\) and \(h\) are strictly increasing,

\[
 h(q(x))=h(q(-x))iff q(x)=q(-x)iff x=-xiff x=0,
\]

so \(2\Rightarrow3\). At \(x=0\), source and target systems are identical, and the identity map is a
strict formed-history lift, proving \(3\Rightarrow1\). ∎

In fact \(\mathfrak A\) is odd and strictly increasing:

\[
 \mathfrak A'(x)
 =h'(q(x))q'(x)+h'(q(-x))q'(-x)>0.
 \tag{HEO.19}
\]

Thus its sign is the sign of the reflected formation displacement.

## 4. Four-organ conservation identity

For \(q=q(x)\), let

- \(P_x=p_q^{\mathbb Z}\) be the Bernoulli history law;
- \(\Delta_{p_q}\) be the diagonal two-step coupling;
- \(p_q\otimes p_q\) be the fresh-reset coupling;
- \(\rho_q=(1-q)q^N\) be the Toeplitz--KMS depth state.

The established reset and KMS calculations, together with (HEO.13), give

\[
 \boxed{
 h_{\mathrm{KS}}(S,P_x)
 =H(p_q)
 =D(\Delta_{p_q}\Vert p_q\otimes p_q)
 =S_{\mathrm{vN}}(\rho_q)
 =h(q).}
 \tag{HEO.20}
\]

Therefore the single history-extension anomaly has four exact realizations:

\[
 \boxed{
 \begin{aligned}
 \mathfrak A(x)
 &=h_{\mathrm{KS}}(S,P_x)-h_{\mathrm{KS}}(S,P_{-x})\\
 &=D(\Delta_{p_x}\Vert p_x^{\otimes2})
   -D(\Delta_{p_{-x}}\Vert p_{-x}^{\otimes2})\\
 &=S_{\mathrm{vN}}(\rho_x)-S_{\mathrm{vN}}(\rho_{-x}).
 \end{aligned}}
 \tag{HEO.21}
\]

This is not equality by analogy. Each line reduces to the same Shannon entropy of the complete
geometric recovery law.

## 5. Frozen-gauge mechanism and its exact boundary

For a parameter deliberately held fixed through every history coordinate, the theorem isolates the
law sequence:

\[
 \boxed{
 \text{split packet formation}
 \to\text{ regenerative endpoint symmetry}
 \to\text{ endpoint information isometry}
 \not\Rightarrow\text{ process symmetry};}
 \tag{HEO.22}
\]

the missing implication is governed by

\[
 \boxed{
 \text{clock-preserving process lift}
 \Rightarrow\text{ entropy-anomaly cancellation}.}
 \tag{HEO.23}
\]

When frozen formation makes entropy reflection-separating, cancellation forces the reflection fixed
point. It does not follow that the source-generated history freezes the parameter.

For the source-natural alternating product law

\[
 P_x^{\mathrm{alt}}=\bigotimes_{j\in\mathbb Z}p_{(-1)^j x},
 \tag{HEO.24}
\]

the bilateral shift satisfies

\[
 S_*P_x^{\mathrm{alt}}=P_{-x}^{\mathrm{alt}}
 \tag{HEO.25}
\]

for every \(x\). The two-step shift preserves each fibre law, and its two-coordinate entropy is

\[
 H(p_x)+H(p_{-x}),
 \tag{HEO.26}
\]

which is reflection-invariant. Thus the scalar anomaly
\(H(p_x)-H(p_{-x})\) is an orbit coboundary and cancels on the complete reflection orbit.

## 6. Hostile conjecture loops

### Loop A -- endpoint information neutrality implies process neutrality

- **Conjecture:** the common recovery-kernel lift already gives an invertible action on formed
  histories.
- **Failure:** recover--reflect--regenerate is a Markov operation. It discards the previous recovery
  coordinate and is not a shift conjugacy.
- **Positive survivor:** endpoint KL is exactly conserved, while process liftability has the separate
  obstruction \(\mathfrak A\).

### Loop B -- probability-space isomorphism is enough

- **Conjecture:** because all nonatomic bilateral products are abstractly isomorphic, the reflection
  always lifts.
- **Failure:** an arbitrary measure-space isomorphism need not commute with the declared shift.
- **Positive survivor:** fixed-clock equivariance turns Shannon/KS entropy into a complete Bernoulli
  conjugacy invariant.

### Loop C -- a noninvertible factor gives the same selector

- **Conjecture:** replace conjugacy by any shift-equivariant factor.
- **Failure:** factors need only decrease entropy. Equality and the fixed-point conclusion disappear.
- **Positive survivor:** invertibility, or an independently proved two-sided sufficiency law, is
  load-bearing.

### Loop D -- time change is harmless gauge

- **Conjecture:** allow an arbitrary induced clock or time rescaling.
- **Failure:** dynamical entropy rescales under induction/time change, so (HEO.10) is no longer the
  invariant equation.
- **Positive survivor:** the theorem classifies lifts for the source-declared fixed clock. A physical
  clock comparison must be constructed, not assumed.

### Loop E -- anomaly zero always selects a fixed point

- **Conjecture:** every recovery family is reflection-separating.
- **Failure:** a symmetric family \(p_x=p_{-x}\) has zero anomaly everywhere; product anomalies can
  also cancel.
- **Positive survivor:** strict cooriented formation, proved here for the geometric family, is the
  exact additional hypothesis.

### Loop F -- frozen process is the source process

- **Conjecture:** the theta functional equation generates the stationary histories compared in
  Theorem 3.1.
- **Failure:** its natural execution alternates the reflected kernels, and (HEO.25) gives an exact
  shift transport for every \(x\).
- **Positive survivor:** scalar antisymmetric entropy cannot survive a complete symmetry orbit.
  Selection must use a non-coboundary vertical transport, a marked phase not quotiented by the
  source action, or a positive complete-orbit work with an independently derived boundedness or
  passivity law.

## 7. Literature boundary

The parent dynamical theorem is Ornstein theory. Brandon Seward proves that Bernoulli shifts over any
countably infinite group with equal Shannon base entropy are isomorphic:

- Brandon Seward, *Bernoulli shifts with bases of equal entropy are isomorphic*,
  <https://arxiv.org/abs/1805.08279>.

The new corpus-level content is not the entropy classification itself. It is the exact comparison of
the regenerative endpoint lift with the strict formed-history lift, and the identity (HEO.21), which turns the previously known endpoint
information isometry into a process-extension obstruction shared by packet, path, KMS, and ergodic
history organs.

## 8. Corrected open gate

The frozen-history conjugacy is no longer a live producer target. The next theorem must construct a
comparison that does not factor solely through common recovery and does not become a coboundary on
the complete functional-equation orbit. Formation Holonomy Mechanics gives the exact test:

1. identify the vertical recovery fibres;
2. construct source-derived transport between them;
3. compute a nontrivial triangle defect;
4. verify the forced four-organ conservation law; and
5. derive positive/proper work before invoking any RH receiver.

## Log

- 2026-08-11 — Candidate extracted from the gap between the already formalized packet information
  isometry and the bilateral reset dilation. Corpus search found no KS/process-conjugacy comparison.
  Primary literature audit located the exact Ornstein/Seward parent. Complete proof and hostile loops
  recorded for Stage-2 audit.
- 2026-08-11 — Promoted after hostile audit. Necessity uses only KS entropy invariance; sufficiency at
  the selected point is the identity. Resampling, one-sided factors, time changes, symmetric kernels,
  and unproved arithmetic landing are explicitly excluded. Lean formalization remains open in the
  current read-only formal-audit phase.
- 2026-08-11 — Second hostile audit found the decisive source-naturality failure: functional-equation
  execution alternates reflected kernels, and one shift transports the alternating histories for
  every parameter. Card retained as a correct frozen-history classification; selector claim retired.
  Positive survivor generated Formation Holonomy Mechanics.
