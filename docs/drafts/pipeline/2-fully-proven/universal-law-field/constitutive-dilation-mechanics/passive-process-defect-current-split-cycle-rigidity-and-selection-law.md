# Passive process defect current, split-cycle rigidity, and selection law

- **ID:** ULF-CDM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Constitutive Dilation Mechanics field programme
- **Statement:** Passive process defects compose additively; a passive split cycle has zero defect
  on every leg; any strict source detector therefore selects the neutral formation.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM FIRST]
  [SERIAL CONSERVATION] [SPLIT-CYCLE RIGIDITY] [SELECTION SCHEMA]
  [RECURRENCE/DISSIPATION SEPARATION] [LEAN TARGET] [NOT RH]

## 1. Heterogeneous work chart

Let $X,Y,Z$ be normed spaces over a common valued field.  No linearity is required for the
process maps.  For $f:X\to Y$, define its pointwise passive defect current by

\[
 \mathfrak J_f(x)=\|x\|-\|f(x)\|.
 \tag{PDC.1}
\]

The map is passive at $x$ when $\|f(x)\|\le\|x\|$, equivalently
$\mathfrak J_f(x)\ge0$.

The norm can be replaced throughout by arbitrary work functions
$W_X,W_Y,W_Z$ and
$\mathfrak J_f(x)=W_X(x)-W_Y(fx)$.  The normed formulation is used because it is the minimal
common chart for positive Gram, Hilbert compression, observer contraction, and passive process
realization.

## 2. Serial conservation

### Theorem 2.1 — exact defect-current composition

For maps $f:X\to Y$ and $g:Y\to Z$,

\[
 \boxed{
 \mathfrak J_{g\circ f}(x)
 =\mathfrak J_f(x)+\mathfrak J_g(fx).}
 \tag{PDC.2}
\]

#### Proof

Expand both sides:

\[
 \|x\|-\|g(fx)\|
 =\bigl(\|x\|-\|fx\|\bigr)
  +\bigl(\|fx\|-\|g(fx)\|\bigr).
\]

The middle norms cancel.  ∎

For a finite heterogeneous chain

\[
 X_0\xrightarrow{f_1}X_1\xrightarrow{f_2}\cdots
 \xrightarrow{f_n}X_n,
 \qquad x_k=f_k(x_{k-1}),
\]

induction gives the ledger conservation law

\[
 \boxed{
 \|x_0\|=\|x_n\|+
 \sum_{k=1}^n\mathfrak J_{f_k}(x_{k-1}).}
 \tag{PDC.3}
\]

Thus terminal visible work and the ordered hidden-current ledger jointly reconstruct initial work.
This is scalar work reconstruction, not state reconstruction.

## 3. Passive split-cycle rigidity

### Theorem 3.1 — two-leg split cycle

Let $q:X\to Y$, $r:Y\to X$, and $x\in X$.  Assume

\[
 \|q x\|\le\|x\|,
 \qquad
 \|r y\|\le\|y\|\quad(y\in Y),
 \qquad
 r(qx)=x.
 \tag{PDC.4}
\]

Then

\[
 \boxed{
 \|qx\|=\|x\|,\qquad
 \mathfrak J_q(x)=0,\qquad
 \mathfrak J_r(qx)=0.}
 \tag{PDC.5}
\]

#### Proof

Passivity of $r$ and the split equation give

\[
 \|x\|=\|r(qx)\|\le\|qx\|.
\]

Passivity of $q$ gives the reverse inequality.  Hence the norms are equal, and both differences
in `(PDC.5)` vanish.  ∎

The same argument is not valid if $r$ is expansive.  A set-theoretic or unbounded decoder can
reconstruct after strict positive loss.  Contractive reconstruction is load-bearing.

### Theorem 3.2 — three-leg cycle and current localization

Let

\[
 X\xrightarrow{f}Y\xrightarrow{g}Z\xrightarrow{h}X
\]

be passive on the trajectory $x,fx,gfx$, and assume $h(g(fx))=x$.  Then

\[
 \boxed{
 \mathfrak J_f(x)=
 \mathfrak J_g(fx)=
 \mathfrak J_h(gfx)=0.}
 \tag{PDC.6}
\]

#### Proof

By `(PDC.2)` twice and the return equation, the sum of the three defects is
$\|x\|-\|x\|=0$.  Passivity makes every summand nonnegative, so every summand is zero.  ∎

This theorem is heterogeneous: the three process organs need not share a carrier, dimension,
coordinates, or doctrine.  They need only transport one source-generated positive work passively.

## 4. Strict selection

### Corollary 4.1 — passive reconstruction selects a strict neutral locus

Let $\mathsf{Neutral}(x)$ be a source-defined predicate and suppose

\[
 \mathfrak J_q(x)=0\Longrightarrow\mathsf{Neutral}(x).
 \tag{PDC.7}
\]

Under the hypotheses of Theorem 3.1,

\[
 \boxed{\mathsf{Neutral}(x).}
 \tag{PDC.8}
\]

#### Proof

Theorem 3.1 gives $\\mathfrak J_q(x)=0$; apply `(PDC.7)`.  ∎

Equivalently, if every nonneutral source state suffers strict loss under $q$, no nonneutral state
can belong to a passive split cycle.

### Corollary 4.2 — no positive leg in a passive closed cycle

Under Theorem 3.2, none of the three defects is strictly positive.  Consequently a claimed model
with an exact return, one fixed positive work, passive legs, and positive hidden dissipation is
inconsistent.

This is the first withheld prediction of the mechanism.  Recurrent observation plus open lifted
history can still occur, but the lift must be conservative/phase-like, be unitized by the observer,
or live across a change of work doctrine or completion.  It cannot be the positive defect ledger of
the same closed passive cycle.

## 5. Fusion across unlike organs

The theorem does not identify distinct organs; it supplies one transport law they must obey.

| organ | passive work | defect current |
|---|---|---|
| information/observer | directed divergence or distinguishability | conditional/fibre loss |
| Hilbert/Gram compression | norm or norm square | compression/defect energy |
| process/history | passive storage function | dissipative memory ledger |
| completion/reconstruction | completed source work | work lost at a non-strict boundary |

The serial identity is the fusion law.  The completion prediction is the fourth organ: a recurrent
return with positive defect cannot be realized in one passive Hausdorff work completion.  A legal
realization must expose the missing quotient, singular domain, metric change, or conservative
dilation memory.

## 6. Relation to global formation properness

The existing formation-properness theorem uses unbounded work along a source scale orbit.  The
present law gives an orthogonal selection mechanism.  Properness says a nonneutral orbit cannot stay
inside bounded work.  Split-cycle rigidity says a nonneutral strict defect cannot occur even once
inside an exact passive return.

Together they suggest two source-level closure strategies:

\[
 \boxed{
 \text{bounded cofinal work}\Rightarrow\text{neutrality},
 \qquad
 \text{passive source reconstruction}\Rightarrow\text{neutrality}.}
 \tag{PDC.9}
\]

Neither conclusion follows from endpoint equality alone.

## 7. Exact RH-facing gate

The theorem is not an RH proof.  It types one new sufficient producer target.

Suppose the literal pre-zero source supplies:

1. a marked positive work space for the reflection-pair packet;
2. a passive compression $q$ whose defect is the already constructed positive Hodge/formation
   current;
3. a passive source-natural reconstruction $r$ with $r q=1$ on the source packet;
4. the existing strict radical theorem identifying zero current with horizontal neutrality.

Then Corollary 4.1 selects neutrality, and the corpus's receiver theorem supplies RH.  Items 1--3,
especially the contractive reconstruction, are open and may not be inferred from Xi-zero
specialization.  This is a producer specification, not a disguised endpoint criterion.

## 8. Hostile countermodels and scope

1. **Expansive decoder.** $q(x)=x/2$, $r(y)=2y$ has $rq=1$ but positive $q$-defect.
   Passivity of both legs is necessary.
2. **Endpoint norm only.** Equality (|rqx|=\|x\|) without passivity does not localize loss;
   one leg may contract and another expand.
3. **Zero defect, nonzero memory.** A unitary phase rotation has zero defect and nontrivial
   winding.  The theorem does not erase conservative history.
4. **Observer-created recurrence.** A quotient may send a positive-cost nonunit history to the
   identity.  That is not a closed passive cycle in the source work doctrine.
5. **Indefinite or signed work.** Nonnegative localization fails without passivity.  Krein and
   signed-current charts require a sourced positive majorant or a different theorem.
6. **No universal norm.** Different route organs may not admit one source-generated work.  Failure
   to construct it kills the proposed fusion rather than proving a scalar no-go.

## 9. Parent mathematics and significance boundary

The algebra is the elementary energy-balance core of contraction/dilation theory, passive systems,
and information data processing.  No priority claim is made.  Its field significance is the exact
separation between dissipative defect and conservative memory, and the replacement of another
endpoint receiver by one constructive source target: passive reconstruction.

## 10. Lean target

Formalize in
`GaloisForLFunctions.HTGeometry.ConstitutivePassiveCycleMechanics`:

1. pointwise defect and passivity equivalence;
2. heterogeneous serial conservation;
3. two-leg split-cycle rigidity;
4. three-leg cycle localization;
5. strict-neutral selection and positive-leg impossibility.

No theorem may use RH, a target zero-location premise, `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, or computation-based proof.

## Gates

- [x] source-independent statement
- [x] dependency-closed paper proof
- [x] expansive-decoder and conservative-memory boundaries
- [x] exact serial conservation and strict selection
- [ ] Lean module direct build
- [ ] universal-law-field umbrella build and axiom audit

## Log

- 2026-08-11 — paper proof closed as finite core of Constitutive Dilation Mechanics.
