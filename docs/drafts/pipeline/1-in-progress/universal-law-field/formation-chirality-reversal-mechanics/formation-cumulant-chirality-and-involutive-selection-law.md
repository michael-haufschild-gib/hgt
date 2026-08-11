# Formation cumulant chirality and involutive-selection law

- **ID:** ULF-FCRM-1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / PAPER-PROOF ATTACK
- **Source:** universal-law-field formation/properness and time-reversal likelihood mechanisms
- **Statement:** The exchange-generated abelian-zeta-gas formation has a strictly positive directed
  relative-entropy commutator at every positive displacement; the commutator is the integral of the
  third source cumulant, so no nonzero formation can be exchanged by an involutive source reversal.
- **Status:** `[CONJECTURE] [INTERNAL FRONTIER AUDITED] [EXTERNAL PARENTS AUDITED]
  [PAPER PROOF UNDER HOSTILE REVIEW] [NO LEAN YET] [NOT RH]`

## 1. Goal and higher pivot

The preceding global formation-properness theorem proves that a finite uniform bound on full source
Jeffreys work selects neutral formation. It does not produce that bound. The first conjecture for
this lane was therefore:

> source reversal or conservation automatically bounds the exchange-generated work.

This is false. The source work was proved proper precisely because every positive scale orbit has
unbounded work. A trace or conservation law cannot bound it without an additional compatibility
mechanism.

The stronger replacement retains the orientation discarded by Jeffreys symmetrization. For two
source laws (P,Q), define the directed information commutator

\[
 \chi(P,Q)=D(P\Vert Q)-D(Q\Vert P).
 \tag{FCRM.1}
\]

An involution exchanging (P) and (Q) forces (chi(P,Q)=0). The live question is whether the
literal source-generated formation has a fixed nonzero sign. If so, reversal compatibility itself,
not an assumed energy bound, selects the neutral formation.

## 2. Internal frontier

`AbelianZetaGas.LawCommutator` proves that the source-marked schedule commutator generates the
fugacity translation

\[
 [S,H_u]=V_u:(\sigma,\tau)\longmapsto(\sigma,\tau+u).
 \tag{FCRM.2}
\]

The class law is

\[
 P_t(A)=Z(t)^{-1}\exp\bigl(-\sigma\log|A|-(\tau+t)Q(A)\bigr),
 \qquad Q(A)=\log|\operatorname{soc}A|,
 \tag{FCRM.3}
\]

with

\[
 Z(t)=\prod_{j\ge1}\zeta(j\sigma+\tau+t),
 \qquad \sigma>0,\quad \sigma+\tau>1,quad t\ge0.
 \tag{FCRM.4}
\]

The corpus already proves mutual absolute continuity, Radon--Nikodym and log-likelihood formulas,
integrability of (Q), the exact symmetric work

\[
 D(P_0\Vert P_u)+D(P_u\Vert P_0)
 =u\bigl(\mathbb E_0Q-\mathbb E_uQ\bigr),
 \tag{FCRM.5}
\]

and source-scale properness. `ConstitutiveTimeReversalLikelihoodCocycle` proves KL invariance under
measurable embeddings and the exact likelihood law of a measurable involution. No existing card
computes the antisymmetric directed difference for this source.

## 3. External parent boundary

- `[LITERATURE]` Relative entropy of an exponential family is the Bregman divergence of its log
  partition function. This is standard information geometry.
- `[LITERATURE]` Time-reversal entropy production is relative entropy between forward and reversed
  path laws: Maes--Netocny, *Time-Reversal and Entropy*, arXiv:cond-mat/0202501; Parrondo--van den
  Broeck--Kawai, *Entropy production and the arrow of time*, arXiv:0904.1573; Lopes--Mengue,
  *On information gain, Kullback-Leibler divergence, entropy production and the involution kernel*,
  arXiv:2003.02030.
- `[LITERATURE]` The Bregman commutator
  \(\frac12(D_F(x,y)-D_F(y,x))\) and its vanishing for quadratic generators are explicit in the
  supplementary material of *Alternating Mirror Descent* (NeurIPS 2022). Global symmetry of a
  Bregman divergence characterizes quadratic generators under standard regularity hypotheses.

These parents occupy the abstract machinery. The source-specific residue is the exact sign and
cumulant formula forced by the abelian-group formation, and its incompatibility with involutive
realization of the generated central law.

## 4. General exponential-formation identities

Let ((\Omega,\mu)) be a probability space, let (Q\ge0), and suppose

\[
 Z(t)=\int e^{-tQ}\,d\mu
 \tag{FCRM.6}
\]

is finite and three times differentiable on ([0,u]), with differentiation under the integral
valid through order three. Put

\[
 dP_t=Z(t)^{-1}e^{-tQ}\,d\mu,
 \quad F(t)=\log Z(t),
 \quad m(t)=\mathbb E_tQ,
 \quad V(t)=\operatorname{Var}_t(Q),
 \quad \kappa_3(t)=\mathbb E_t[(Q-m(t))^3].
 \tag{FCRM.7}
\]

Then standard differentiation gives

\[
 F'=-m,\qquad m'=-V,\qquad V'=-\kappa_3.
 \tag{FCRM.8}
\]

The two directed works are

\[
\begin{aligned}
 D(P_0\Vert P_u)&=F(u)-F(0)+u m(0),\\
 D(P_u\Vert P_0)&=F(0)-F(u)-u m(u).
\end{aligned}
\tag{FCRM.9}
\]

Consequently their sum and difference obey

\[
 \boxed{J(u)=u\int_0^u V(t)\,dt,}
 \tag{FCRM.10}
\]

and

\[
\begin{aligned}
 \chi(u)
 &=u(m(0)+m(u))-2\int_0^u m(t)\,dt\\
 &=\int_0^u(u-2t)V(t)\,dt\\
 &=\boxed{\int_0^u t(u-t)\kappa_3(t)\,dt.}
\end{aligned}
\tag{FCRM.11}
\]

Thus Jeffreys work is integrated second response, while its directed orientation is integrated
third response. Together they reconstruct both directed costs:

\[
 D(P_0\Vert P_u)=\frac{J(u)+\chi(u)}2,
 \qquad
 D(P_u\Vert P_0)=\frac{J(u)-\chi(u)}2.
 \tag{FCRM.12}
\]

## 5. Source cumulant conjecture

### Conjecture 5.1 -- strict source chirality

For the class laws (FCRM.3),

\[
 \boxed{\kappa_3(t)>0\quad(t\ge0).}
 \tag{FCRM.13}
\]

Hence

\[
 \boxed{u>0\Longrightarrow
 D(P_0\Vert P_u)>D(P_u\Vert P_0).}
 \tag{FCRM.14}
\]

The exact open proof obligation is to justify the all-mode third-cumulant expansion and its local
uniform convergence in the full chamber.

## 6. Proposed involutive-selection theorem

Assume Conjecture 5.1. Let (\Theta) be a measurable involution of the finite-abelian-group class
space. If

\[
 \Theta_*P_0=P_u,
 \tag{FCRM.15}
\]

then (u=0). Indeed, involutivity gives (\Theta_*P_u=P_0), while invariance of KL under a
measurable bijection gives

\[
 D(P_0\Vert P_u)
 =D(\Theta_*P_0\Vert\Theta_*P_u)
 =D(P_u\Vert P_0),
 \tag{FCRM.16}
\]

contradicting (FCRM.14) for (u>0). Conversely, at (u=0), the identity involution works.

Therefore

\[
 \boxed{
 \exists\Theta,\ \Theta^2=1,\ \Theta_*P_0=P_u
 \quad\Longleftrightarrow\quad u=0.}
 \tag{FCRM.17}
\]

This is a selection law for generated formations admitting an actual involutive reversal, not a
claim that the physical Xi reflection has already been realized on this source law.

## 7. Hostile conjecture loops

### Loop A -- bounded conservation

**Conjecture.** Source conservation automatically bounds (J(d^nu)).

**Verdict:** `[FALSIFIED]`. The Lean-certified formation-properness theorem proves the opposite:
for (u>0), reporter work and full source work cannot have a finite uniform scale bound.

**Stronger survivor.** Retain the directed pair rather than its symmetric sum. Reversal predicts
equality of directions, while source skewness may force a strict orientation.

### Loop B -- universal positive chirality

**Conjecture.** Every nontrivial exponential formation has (chi(u)>0).

**Verdict:** `[FALSIFIED]`. A Gaussian location family has quadratic log partition, zero third
cumulant, and symmetric KL at distinct parameters. Other exponential families can have changing
third-cumulant sign.

**Stronger survivor.** Chirality is not a generic positivity axiom. It is a source-generated
orientation determined by the sign of the third response. The abelian zeta gas must prove its sign
from literal geometric modes.

### Loop C -- Jeffreys work alone

**Conjecture.** Symmetric work detects reversal compatibility.

**Verdict:** `[FALSIFIED]`. Jeffreys work is invariant under exchange of its arguments and therefore
forgets the arrow required to obstruct a reversal. It proves properness but not chirality.

**Stronger survivor.** The pair ((J,\chi)), equivalently the two directed works, is the minimal
information packet. Its second/third-cumulant hierarchy is reconstruction, not another scalar
observer.

### Loop D -- source star already closes selection

**Conjecture.** The existing gas adjoint automatically exchanges (P_0,P_u).

**Verdict:** `[FALSIFIED]`. `GasStar` reverses algebra words while preserving the fixed real Gibbs
weights. It does not push one chemical-potential law to another. A parameter-changing involution is
additional constitutive data.

**Positive survivor.** The theorem is an exact falsifier: any future source-reflection proposal
that claims to exchange a nonzero generated formation must either fail involutivity, fail law
transport, or erase the source chirality under a non-sufficient observer.

## 8. Fourth-organ prediction

The real Esscher, Fisher, and time-reversal organs cannot all be represented by a reversible
formation at (u>0). If a fourth KMS, modular, or reflected-path realization transports the same
source laws and their directed relative entropies faithfully, then its entropy-production
orientation must equal (FCRM.11). An involutive realization forces that orientation to vanish and
therefore selects (u=0).

This predicts a concrete audit test for any proposed reflected arithmetic completion: compute its
two directed formation costs. Equality off neutrality proves that the realization has forgotten
the literal source formation or is not information-faithful.

## 9. RH boundary

No RH statement follows from (FCRM.17) alone. An RH application would still need a pre-zero,
coefficient-faithful comparison which:

1. sends reflection-paired physical displacements to a generated gas-formation pair;
2. realizes functional-equation reflection as an involution exchanging their source laws;
3. preserves the directed information packet before divisor specialization.

Unlike bilateral summability or a postulated uniform work bound, these requirements are
transformation laws and can be attacked before asking where zeros lie. They are not constructed in
this card.

## 10. Gates

- [x] 0 -> 1: exact source, exact conjecture, internal audit, external parents, hostile loops.
- [ ] 1 -> 2: close the all-mode third-cumulant expansion, strict positivity, and involution proof.
- [ ] 2 -> 3: formalize the exact paper theorem with no additional hypothesis or project axiom.
- [ ] 3 -> 4: publication/priority audit and standalone exposition.

## Log

- 2026-08-11 -- automatic bounded conservation falsified by source properness; pivoted to directed
  formation chirality.
- 2026-08-11 -- extracted exact second/third-cumulant reconstruction identities and the proposed
  involutive-selection theorem.
