# Lower-triangular observer-clock transport, anomaly cocycle, and flat-square law

- **ID:** ULF-TAFM-21
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT REPRESENTATION LAW / EXACT COCYCLE / CLOSED-OBSERVER LIFT
- **Status:** `[PROVED HERE] [FORMALIZED] [DEPENDENCY-CLOSED] [PRE-ZERO] [UNCONDITIONAL] [NOT RH]`
- **Parents:** observer-clock transmutation groupoid; observer-clock multiplier descent and
  interaction anomaly; finite-quotient interaction cohomology
- **Statement:** Marginal recovery and anchored interaction split every joint observable into a
  two-level state. Every scale clock acts lower-triangularly on that state. Marginal and interaction
  diagonal blocks compose multiplicatively; the off-diagonal anomaly obeys an exact cocycle law.
  Commuting clock changes therefore satisfy a zero-curvature square identity. A recurrent marginal
  observer has a closed lifted history exactly when this anomaly vanishes.

## 1. The missing mechanism after ULF-TAFM-20

ULF-TAFM-20 proved that a nonconstant clock does not descend through the marginal quotient. That
alone does not explain how anomalies behave under several clock changes. Treating each failure of
descent independently would again reduce the field to a collection of obstructions.

The new law is compositional. Marginal information and interaction history form one triangular
state space. An anomaly created at one clock step is transported by every later interaction block;
new anomaly is simultaneously generated from the current marginal block. This is the exact law
behind closed observer recurrence with open lifted history.

## 2. Canonical recovery and interaction projections

Let `A` and `B` be anchored sets and

\[
 V=\mathbb C^{A\times B}.
\]

Define

\[
 (Pf)(a,b)=f(a,b_0)+f(a_0,b)-f(a_0,b_0),
\tag{21.1}
\]

and

\[
 (Qf)(a,b)=f(a,b)-f(a,b_0)-f(a_0,b)+f(a_0,b_0).
\tag{21.2}
\]

The marginal space is `M=im P`; the anchored interaction space is

\[
 H=\{q:q(a,b_0)=q(a_0,b)=0\}.
\tag{21.3}
\]

### Theorem 2.1 -- canonical two-level recovery

For every `f`,

\[
 \boxed{Pf+Qf=f.}
\tag{21.4}
\]

Moreover `Pq=0` and `Qq=q` for every `q in H`. Hence `P` and `Q` are complementary projections
and

\[
 V=M\oplus H.
\tag{21.5}
\]

#### Proof

Equation (21.4) is direct expansion. If `q` vanishes on the anchored row and column, every term in
(21.1) vanishes, so `Pq=0`; substituting in (21.4) gives `Qq=q`. The exact marginal criterion of
ULF-TAFM-20 gives `ker Q=M`, while `im Q=H`. QED.

## 3. Clock action is lower triangular

For a scale rate `lambda : A -> C`, let

\[
 (T_\lambda f)(a,b)=\lambda(a)f(a,b).
\tag{21.6}
\]

### Theorem 3.1 -- interaction-sector invariance

\[
 \boxed{T_\lambda H\subseteq H.}
\tag{21.7}
\]

Equivalently,

\[
 PT_\lambda Q=0,
 \qquad
 QT_\lambda Q=T_\lambda Q.
\tag{21.8}
\]

#### Proof

If `q(a,b0)=q(a0,b)=0`, multiplication by `lambda(a)` preserves both zero conditions. Apply
Theorem 2.1 inside `H`. QED.

Define the three blocks

\[
 A_\lambda=PT_\lambda|_M,
 \qquad
 H_\lambda=QT_\lambda|_M,
 \qquad
 D_\lambda=T_\lambda|_H.
\tag{21.9}
\]

Relative to `V=M direct-sum H`, Theorem 3.1 gives

\[
 \boxed{
 T_\lambda=
 \begin{pmatrix}
 A_\lambda&0\\
 H_\lambda&D_\lambda
 \end{pmatrix}.}
\tag{21.10}
\]

The upper-right zero is irreversible at observer level: interaction history never becomes a
marginal main effect under a scale-only clock, although new interaction can be created from a
marginal through the lower-left block.

## 4. Exact composition and anomaly cocycle

Pointwise multiplication of rates gives

\[
 T_{\lambda\mu}=T_\lambda T_\mu.
\tag{21.11}
\]

### Theorem 4.1 -- triangular clock representation

For all clock rates `lambda,mu`,

\[
 \boxed{A_{\lambda\mu}=A_\lambda A_\mu,}
\tag{21.12}
\]

\[
 \boxed{D_{\lambda\mu}=D_\lambda D_\mu,}
\tag{21.13}
\]

and

\[
 \boxed{
 H_{\lambda\mu}=H_\lambda A_\mu+D_\lambda H_\mu.}
\tag{21.14}
\]

#### Proof

Decompose `T_mu f` using (21.4):

\[
 T_\mu f=PT_\mu f+QT_\mu f.
\]

Apply `T_lambda`. Projection by `P` kills the transported second summand by (21.8), proving
(21.12). On an interaction input, both clock maps remain inside `H`, proving (21.13). Projection by
`Q` retains the anomaly newly created from `PT_mu f` and transports the already-created
`QT_mu f` diagonally, giving (21.14). QED.

Equation (21.14) is not a metaphorical curvature statement. It is an exact cocycle identity. It
specifies how local route/organ anomalies assemble into one global history under arbitrary clock
composition.

### Corollary 4.2 -- flat clock-square conservation

Because pointwise clock rates commute,

\[
 T_{\lambda\mu}=T_{\mu\lambda}.
\]

Therefore

\[
 \boxed{
 H_\lambda A_\mu+D_\lambda H_\mu
 =H_\mu A_\lambda+D_\mu H_\lambda.}
\tag{21.15}
\]

#### Proof

Apply (21.14) to `lambda*mu` and `mu*lambda`, then use commutativity. QED.

Thus every apparent two-clock order defect in newly generated anomaly is exactly cancelled by
transport of pre-existing interaction. A no-go which detects only one term is seeing a nonzero
shadow of a globally flat square.

## 5. Functional equation as diagonal gauge

If `lambda(a)=c` is constant, then `T_lambda=c Id`. Consequently

\[
 A_\lambda=c\,Id_M,
 \qquad H_\lambda=0,
 \qquad D_\lambda=c\,Id_H.
\tag{21.16}
\]

The functional-equation sign or constant phase therefore acts diagonally on the full recovered
state. It creates no off-diagonal information and is neutral under the common recovery kernel.
This is stronger than saying a positive receiver is invariant: the lifted oriented history itself
is transported without anomaly creation.

## 6. Closed observer and open lifted history

For arbitrary `f`, define observed and lifted outputs

\[
 O_\lambda(f)=PT_\lambda f,
 \qquad L_\lambda(f)=QT_\lambda f.
\tag{21.17}
\]

Equation (21.4) gives exact recovery

\[
 T_\lambda f=O_\lambda(f)+L_\lambda(f).
\tag{21.18}
\]

### Theorem 6.1 -- recurrence/lift separation

If the observer closes,

\[
 O_\lambda(f)=f,
\tag{21.19}
\]

then

\[
 \boxed{T_\lambda f=f\iff L_\lambda(f)=0.}
\tag{21.20}
\]

#### Proof

Substitute (21.19) into (21.18): `T_lambda f=f+L_lambda(f)`. Cancellation gives (21.20). QED.

This is the precise mechanism requested by the universal-field question. Recurrence is closure of
the projected observer state, while open history is nonzero cocycle in the invariant interaction
sector. No compact-space analogy is required.

## 7. Consequences for the RH architecture

The previous architecture treated route-local outputs as separate estimates. The triangular law
changes the object:

\[
 \text{state at scale }N=(\text{marginal recovery},\text{interaction history}).
\tag{21.21}
\]

Every route organ is a choice of marginal reporter. Every nonconstant physical clock injects an
off-diagonal cocycle. Functional equation is diagonal gauge. Positive formation may quotient
orientation only after the cocycle has been created. Recurrence can close the first coordinate
without closing the second.

The next RH producer is therefore not another bound on an isolated route statistic. It must be a
source law for the triangular transport itself: a signed conservation or admission theorem forcing
the literal arithmetic cocycle to lie in a bounded bilateral interaction chamber. The flat-square
identity (21.15) supplies a nontrivial compatibility equation which any such producer must obey.

## 8. Hostile audit

- **Not ULF-TAFM-20 restated.** ULF-TAFM-20 classifies one-step failure of descent. This theorem
  supplies the invariant interaction sector, full lower-triangular representation, composition
  cocycle, and flat-square identity.
- **Not generic matrix notation.** Each block is the canonical anchored recovery or interaction
  projection already realized in the corpus; the zero block and cocycle are proved from the actual
  pointwise clock action.
- **No RH smuggling.** No zero, zeta estimate, compactness assumption, arithmetic cancellation, or
  source bound occurs.
- **No novelty claim required.** Triangular representations and cocycles are classical structures.
  Their role here is a Frankenstein unification of observer clocks, finite interaction cohomology,
  functional-equation gauge, positivity loss, and recurrence/lift separation.
- **Remaining danger.** Flatness alone does not bound a cocycle. Calling (21.15) “curvature zero”
  without constructing the literal source admission law would be theatre.

## 9. Gates

- [x] canonical two-level recovery
- [x] invariant interaction sector
- [x] lower-triangular clock representation
- [x] exact anomaly cocycle
- [x] flat clock-square conservation
- [x] functional-equation information-neutral diagonal action
- [x] closed-observer/open-history equivalence
- [x] Lean formalization and umbrella wiring
- [ ] literal signed cocycle admission law
- [ ] RH selection

## Log

- 2026-08-31 -- Proved lower-triangular clock representation, anomaly cocycle, commuting-clock
  flat-square identity, and exact recurrence/lift separation. This is compositional upgrade of
  ULF-TAFM-20, not another route endpoint.
- 2026-08-31 -- Formalized canonical recovery, invariant interaction sector, triangular block
  composition, anomaly cocycle, flat clock square, and observer/lift closure criterion in Lean;
  wired leaf into universal-field umbrella without building umbrella.
- 2026-09-01 -- Made the exact image/complement and projection claims explicit, closed constant
  clock diagonal gauge law (21.16) on both sectors, added a zero-argument certificate for every
  stated theorem, passed scratch/direct elaboration and targeted leaf build, and audited new theorem
  axioms. Existing universal-field umbrella wiring was retained; no umbrella build was run.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.ObserverClockTriangularRepresentation`.
- `observerClockTriangularRepresentation_completion_certificate` packages canonical recovery,
  exact marginal/interaction images and complement, invariant interaction sector, triangular
  composition, anomaly cocycle, flat square, recurrence/lift separation, and constant-clock
  diagonal gauge.
- Targeted build: `lake build
  GaloisForLFunctions.HTGeometry.ObserverClockTriangularRepresentation` passed `8780/8780`.
- All twelve newly added theorem declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
