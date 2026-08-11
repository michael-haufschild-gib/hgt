# Source-coherent synchronization mechanics — field laws

- **ID:** ULF-SCSM-FIELD
- **Stage:** 1-in-progress
- **Type:** FIELD CONSTITUTION / MECHANISM PROGRAMME
- **Status:** finite algebraic kernel proved and Lean-certified; source-specific infinite realization
  and RH selection gate open
- **Scope:** universal-law-field only

## 1. Higher pivot

The corpus should not be organized around a universal object, a preferred proof route, or a scalar
curvature.  Its recurrent phenomenon is a **formation problem**:

> one source intervention is realized in several mathematical organs; each organ admits a larger
> local gauge freedom than the source actually generated; fusing the organs before quotienting
> exposes the incompatibility among their locally optimal gauges.

The field studies laws governing this formation, relative response, fusion, reconstruction,
admission, and selection.  Differential geometry, sheaf theory, information geometry, operator
theory, homological algebra, recurrence, and hypertranscendence are available gauges of the
mechanism.  None is the definition of the field.

## 2. Primitive mechanism

Let `V` be a space of legal source interventions and let a finite family of structurally different
organs have response spaces `W_i` and source response maps

\[
  \rho_i:V\longrightarrow W_i.
\]

The **formation map** is

\[
  \Phi:V\longrightarrow \prod_i W_i,
  \qquad \Phi(x)=(\rho_i x)_i.                         \tag{SCSM.1}
\]

The product is the space of independently adjustable local responses.  The image of `Phi` is the
smaller set of response packets realizable by one source intervention.  This distinction is
load-bearing:

\[
  \text{source intervention} \neq \text{arbitrary tuple of routewise repairs}. \tag{SCSM.2}
\]

In the common scalar-gauge chart, `V=W_i=G` and every `rho_i=id`; `Phi` is the diagonal.  The
shared nuisance in quotient--fusion genesis is therefore not declared after inspecting an
endpoint.  It is the image of one source arrow.

## 3. Seven formation laws

### Law I — source coherence

One legal source intervention produces one simultaneous response packet `Phi(x)`.  Independent
local gauges form the larger product `prod_i W_i` and are admissible only if the source itself has
a corresponding product decomposition.  Routewise existence never implies source-coherent joint
existence.

### Law II — relative response

For an additive common-gauge packet `t=(t_i)`, define

\[
  \delta t(i,j)=t_j-t_i.                               \tag{SCSM.3}
\]

Then

\[
  \delta(t+\Delta u)=\delta t,
  \qquad
  \delta t(i,j)+\delta t(j,k)=\delta t(i,k).           \tag{SCSM.4}
\]

Thus relative response is invariant under the source diagonal and satisfies an exact edge/Čech
cocycle law.  It is not an analogy to curvature.

### Law III — joint reconstruction

One anchor `t_i0` and the relative packet reconstruct every local gauge:

\[
  t_i=t_{i_0}+\delta t(i_0,i).                         \tag{SCSM.5}
\]

Two local packets have the same complete relative response exactly when they differ by one global
source intervention:

\[
 \delta s=\delta t
 \iff
 \exists u,\quad t=s+\Delta u.                        \tag{SCSM.6}
\]

Hence the relative packet is a complete coordinate on the quotient of local gauges by global
source gauge.  Pairwise mismatch plus one anchor, not a scalar obstruction, is the reconstructive
state.

### Law IV — quotient--fusion genesis

Suppose organ `i` has positive gauge weight `c_i` and locally optimal scalar gauge `t_i`.  Local
quotienting allows every organ to use its own optimum.  Source-coherent fusion permits only one
global gauge.  The information created by imposing source coherence is

\[
 \mathfrak Q(c,t)
 =\sum_i c_i(t_i-\bar t)^2
 ={1\over C}\sum_{i<j}c_ic_j(t_i-t_j)^2,              \tag{SCSM.7}
\]

where `C=sum_i c_i` and `bar t=C^{-1}sum_i c_i t_i`.

This is **constraint-induced collective information**.  It can be positive even when every local
quotient residual is zero and even when the underlying source law is a product law.  It is not
statistical interaction.

### Law V — refinement conservation

For any partition into blocks `F_alpha`,

\[
 \mathfrak Q_F
 =\sum_\alpha \mathfrak Q_{F_\alpha}
  +\sum_\alpha C_\alpha(\bar t_\alpha-\bar t)^2.       \tag{SCSM.8}
\]

Information does not disappear under fusion refinement.  It migrates between within-block and
between-block incompatibility.  Iterating `(SCSM.8)` on a tree gives an exact multiscale
conservation ledger.

### Law VI — doctrine/admission phase

At infinite aperture, algebraic realizability, approximate realizability, and stable positive
distance are distinct:

\[
 z\in\operatorname{ran}\Phi,qquad
 z\in\overline{\operatorname{ran}\Phi}\setminus\operatorname{ran}\Phi,
 \qquad
 z\notin\overline{\operatorname{ran}\Phi}.             \tag{SCSM.9}
\]

This trichotomy is already formalized in the corpus.  It is not a new theorem of this programme.
Its role here is constitutive: a completion doctrine decides whether the relative response is
executable, merely approximable with open history, or separated by positive energy.

### Law VII — equalizer selection

Choose an anchor organ `i0`.  The synchronization kernel is

\[
 K_\rho=\bigcap_i\ker(\rho_i-\rho_{i_0}).              \tag{SCSM.10}
\]

If a source law forces all organ responses to synchronize and `K_rho={0}`, then the source
displacement is zero.  This is the selection mechanism:

\[
  \bigl(\forall i,\ \rho_i(x)=\rho_{i_0}(x)\bigr)
  \ \&\ K_\rho=0
  \quad\Longrightarrow\quad x=0.                     \tag{SCSM.11}
\]

It is not enough to discover routewise formulas that agree at the desired locus.  The source must
produce the common intervention and the synchronization equation before target specialization;
the response family must then separate nonzero displacement.

## 4. Full-frontier grammar

The earlier full-frontier grammar

\[
 \text{mark}\to\text{form}\to\text{ghost}\to\text{dualize}
 \to\text{admit}\to\text{saturate}\to\text{conserve}   \tag{SCSM.12}
\]

acquires a mechanism-level meaning:

| grammar verb | synchronization meaning |
|---|---|
| mark | declare source interventions and organ ports before endpoint evaluation |
| form | apply one source arrow through all response representations `rho_i` |
| ghost | retain local gauge product and the smaller globally realizable image |
| dualize | read relative response by functionals, Gram forms, phases, or currents |
| admit | choose algebraic, Hilbert, Tate, bornological, or derived execution doctrine |
| saturate | close under legal compositions, refinements, and prolongations |
| conserve | track the relative class as it migrates among energy, history, topology, and homology |

This grammar separates mechanisms that prior route work repeatedly conflated.

## 5. Why existing routes stall

Every mature route learns to optimize or quotient its own nuisance direction.  That makes the route
powerful locally and blind globally: local quotienting erases exactly the comparison needed to test
whether all local repairs came from one source law.  More work inside one route therefore tends to
stabilize at the same wall.

The higher move is:

1. retain locally optimal gauges rather than discarding them;
2. form the simultaneous source packet;
3. quotient only by interventions actually generated by the source;
4. measure/reconstruct the residual relative packet;
5. apply the equalizer selection law.

This explains why a source-native selector was repeatedly missing: the sought datum is not another
absolute source class.  It is the **compatibility law among several source images**.

## 6. Closed finite fusion already achieved

The existing Stage-2 and Lean-certified quotient--fusion theorem realizes Laws II--V on one literal
prime source:

1. Boolean parity--clock capacity;
2. Mass half-density current;
3. positive Hankel/moment geometry;
4. recurrent pure-state quantum Fisher information as the predicted fourth organ.

The marked packet `(c_p,t_p)` reconstructs prime logs, Gibbs weights, Mass amplitudes, and the Hankel
moments.  The partition law predicts

\[
 I_\perp(F)-\sum_\alpha I_\perp(F_\alpha)
 =4\pi^2\sum_\alpha C_\alpha(\gamma_\alpha-\gamma)^2.  \tag{SCSM.13}
\]

The new synchronization kernel proves why one shared gauge is legitimate whenever those organs are
simultaneous representations of one source intervention.

## 7. Hypertranscendence, positivity, recurrence, topology

These are consequences or doctrines, not foundations:

- **hypertranscendence** predicts nonstabilizing rank of source response/prolongation packets;
- **positivity** supplies a metric quotient and can erase orientation while retaining squared
  relative information;
- **recurrence** is return in a quotient response while the anchored/global lift may remain open;
- **topology** determines whether the formation image is exact, dense nonclosed, or stably separated;
- **homology** records whether a relative packet is a boundary after a doctrine enlargement;
- **inertia** records signed response not visible to positive metric formation.

No universal implication among these is asserted.  Their coupling must be proved through one
formation map.

## 8. RH selection programme — only after fusion

Let the transverse divisor displacement be

\[
  a(\rho)=\operatorname{Re}\rho-\tfrac12.              \tag{SCSM.14}
\]

A noncircular RH theorem now has an exact required form.

1. Construct, before Xi-zero specialization, one literal arithmetic intervention module `V`
   containing the displacement direction.
2. Construct at least two source response representations `rho_i` landing in structurally distinct
   organs.
3. Prove divisor admissibility forces their response packet to lie in the synchronized equalizer.
4. Prove the equalizer kernel on the displacement line is zero.

Then `(SCSM.11)` gives `a(rho)=0`; functional equation and conjugation give RH.

Existing routes mostly provide candidate response components, but not Step 3.  Equality imposed
only on Xi zeros is circular.  Equality derived from one pre-zero source intervention is the live
theorem.

## 9. Falsifiers

This field programme fails if any of the following occurs:

1. the alleged organs do not arise from one source intervention;
2. their shared gauge is chosen only after reading a target endpoint;
3. the relative packet does not reconstruct local gauges modulo the source action;
4. fusion conservation fails under refinement;
5. the infinite formation map changes with the proof route rather than with declared doctrine;
6. the synchronization kernel contains the entire radial displacement direction;
7. the supposed RH compatibility equation is only a restatement of critical-line symmetry.

## 10. Current status

- Laws II, III, and VII: paper-proved and Lean-certified in
  `HTGeometry.SourceCoherentInterventionSynchronization`.
- Laws IV and V plus three-organ fusion and fourth-organ QFI prediction: paper-proved and
  Lean-certified in `HTGeometry.SharedGaugeQuotientFusion` and
  `HTGeometry.PrimeBooleanMassHankelQuantumFusion`.
- Law VI: already formalized elsewhere in corpus; integrated, not duplicated.
- Law I for literal RH source and the pre-zero divisor compatibility theorem: open.

This is a mechanism programme, not a claim that generic quotient, Čech, ANOVA, or equalizer algebra
is individually new.

## 11. Parent mechanisms

The Frankenstein synthesis deliberately uses occupied mathematics:

- global-section obstructions and contextuality
  ([Abramsky--Brandenburger](https://arxiv.org/abs/1102.0264));
- preparation-side stochastic extension and source-context compatibility
  ([Williams--Doosti--Shahandeh](https://arxiv.org/abs/2605.00975));
- weighted ANOVA/Cochran heterogeneity and efficient-information Schur complements;
- synchronization/Hodge theory on graphs and group actions;
- quotient, descent, and equalizer constructions;
- closed-range and non-Hausdorff completion theory.

The field claim is the interpretation and coupling: source interventions are formation laws;
relative response is the reconstructive quotient state; fusion creates information by enforcing
source coherence; doctrine controls executability; and selection is an equalizer theorem.  A live
arithmetic realization must prove all transitions from one marked source rather than import them as
independent premises.
