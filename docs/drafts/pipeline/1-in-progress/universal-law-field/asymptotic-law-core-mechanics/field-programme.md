# Asymptotic Law-Core Mechanics -- field programme

- **ID:** ULF-ALCM-PROGRAMME-1
- **Stage:** 1-in-progress
- **Type:** ROUTE-INDEPENDENT FORMATION MECHANISM
- **Status:** `[FIELD PROGRAMME ACTIVE] [MECHANISM NOT OBJECT]`
  `[LAWS I/III/IV LEAN-PROVED] [LAW II PARTIAL] [LAW V OPEN] [NOT RH]`
- **Date:** 2026-08-14

## 1. Founding mechanism

Let `K` be a compact convex law space and let `(x_n)` be a legal formation history.  Define its
canonical tail-law core

\[
 \mathfrak F(x)
 =\bigcap_{N\ge0}\overline{\operatorname{co}}\{x_n:n\ge N\}.
 \tag{ALF.1}
\]

The proposed field primitive is not a chosen cluster point.  It is the operation sending an open
history to the complete compact convex family of laws that remain formable after every finite
prefix is discarded.  The word **core** is deliberate: this set need not be a face in the technical
convex-geometric sense.

This changes the question from “which missing carrier should be added?” to:

> Which identities become exact on the tail-law core, which reporters reconstruct that core, and
> when does properness force the core back into ordinary admitted laws rather than the corona?

## 2. Frozen law package

### Law I -- formation is tail fusion

`F(x)` is the surviving result of every cofinal finite convex formation.  It is nonempty, compact,
and convex.  It is history-generated and contains no selected ultrafilter, Banach limit, or fitted
boundary point.

### Law II -- reporter reconstruction

For every continuous affine real reporter `f`,

\[
 f(\mathfrak F(x))
 =\bigcap_N\overline{\operatorname{co}}\{f(x_n):n\ge N\}
 =[\liminf_n f(x_n),\limsup_n f(x_n)].
 \tag{ALF.2}
\]

Consequently the oscillation identity

\[
 \operatorname{osc}_{\mathfrak F(x)}f
 =\limsup_n f(x_n)-\liminf_n f(x_n)
 \tag{ALF.3}
\]

is exact.  All affine reporters jointly reconstruct the core by separation.

### Law III -- affine formation exchange

For every continuous affine map `T : K -> L`,

\[
 \mathfrak F(Tx)=T\mathfrak F(x).
 \tag{ALF.4}
\]

Thus observation, common recovery, functional-equation involution, and coefficient transport act on
formed laws without choosing cluster representatives.  If `R` has an affine left inverse, formation
through `R` is information-neutral.

### Law IV -- approximate execution exactifies

In a compact convex subset of a normed space, if `T` is affine and

\[
 \|Tx_n-x_n\|\longrightarrow0,
 \tag{ALF.5}
\]

then every `y in F(x)` is fixed by `T`.  More generally, if an affine constraint `A` satisfies
`A x_n -> 0`, then `A` vanishes on the whole tail-law core.  Approximation becomes an exact law only
after formation, not at a selected finite stage.

### Law V -- properness separates ordinary from corona law

For probability formations on a countable carrier, embed `ell^1` probabilities in the weak-star
compact state space of `ell^infinity`.  Then:

1. uniform tightness is equivalent to the entire tail-law core being countably additive;
2. complete finite-set escape is equivalent to every formed law annihilating `c_0`;
3. in the escape phase every proper nonnegative source cost diverges;
4. mixed histories produce a genuine normal/corona core rather than a false binary classification.

This is the proposed formation/properness law.  A corona law is not an additional object: it is the
exact cofinal product of a non-tight formation history.

## 3. Required fusion and prediction

The same theorem must couple at least these four organs:

1. positive convex formation;
2. recurrence or approximate invariance;
3. completion/corona admission;
4. observer reconstruction and information loss.

The withheld fourth-organ prediction is:

> Compact-observer extinction does not imply one undifferentiated corona point.  On any larger
> source-generated reporter algebra, the surviving corona core has reporter width exactly equal to
> the corresponding tail limsup--liminf.  Enlarging the reporter algebra splits the apparent point
> precisely when a noncompact reporter has nonzero asymptotic oscillation.

This predicts an exact corona-multiplicity invariant in operator, recurrence, and all-prime
completion charts.

## 4. Nonisomorphic test laboratories

1. **Compact scalar recurrence.**  For `x_n=(-1)^n` in `[-1,1]`, the tail-law core is the whole
   interval.  No singular completion occurs.
2. **Escaping atomic formation.**  For `x_n=delta_n` in the state space of `ell^infinity`, the
   tail-law core is the state space of the corona `ell^infinity/c_0`.  Every local reporter dies,
   while nonlocal reporters may have nonzero width.
3. **Asymptotically invariant Cesaro formation.**  Uniform measures on longer initial intervals
   escape, are asymptotically shift-invariant, and form an exact shift-invariant corona core.
4. **Operator defect formation.**  Escaping normal vector or trace-class states vanish on compact
   reporters but may retain a nontrivial core on a multiplier/Calkin reporter algebra.

The third and fourth laboratories are predictions until their full typed realizations are proved.

## 5. Hostile death gates

Retire this programme if any of the following occurs:

1. `(ALF.4)` fails without hidden openness or metrizability assumptions;
2. reporter ranges do not jointly determine the tail-law core;
3. the probability normal/corona classification is weaker than the existing coalitional
   attainment theorem and adds no core-level reconstruction;
4. all operator realizations collapse to the already-certified one-point unitized-compact corona;
5. formation requires a chosen ultrafilter or fitted invariant mean;
6. no source-generated reporter algebra makes corona multiplicity operational;
7. no dependency-closed Lean theorem certifies the formation and exchange laws.

## 6. Parent mathematics and scope

Banach--Alaoglu, Krein--Smulian compact convexity, Reiter amenability, invariant means, Choquet state
spaces, Yosida--Hewitt decomposition, concentration compactness, and C*-algebraic compactifications
are established parents.  No novelty claim is attached to those ingredients.  Candidate field
content is their interpretation as one history-generated exactification/reconstruction/properness
mechanism, plus cross-organ predictions.

The mechanism supplies no arithmetic source history, no RH selector, and no right to treat singular
global laws as coefficient-faithful.  Indeed, complete escape forces erasure of every `c_0`
reporter.  A successful arithmetic use must couple the corona core to an independent local
provenance/transgression law rather than pretending a positive invariant mean retains prime atoms.

## 7. Immediate proof programme

1. [x] Prove compact-convex nonemptiness and affine functoriality.
2. Prove exact reporter interval reconstruction and separation.
3. [x] Prove approximate-fixed and approximate-kernel exactification.
4. Prove countable probability tight/escape/properness classification.
5. Construct scalar, shift, and operator laboratories.
6. Hostile-audit current literature and full ULF corpus.
7. [x] Promote the dependency-closed formation/exchange/recovery/exactification survivor to Stage 2.
8. [x] Formalize that survivor scratch-first in `HTGeometry` and wire only the ULF umbrella.

## 8. Current exact frontier

The Stage-2/Lean theorem
`asymptotic-law-core-formation-affine-exchange-recovery-and-exactification-law.md` closes Laws I,
III, and IV. It also proves the functional-equation action and its information-neutral lift through
every common affine recovery pair.

This does not repeat the existing Markov-kernel KL theorem: the new carrier is the complete
compact-convex tail core of an open history. The remaining field-producing gate is stronger:

1. prove scalar reporter intervals and joint separation in Lean;
2. prove the normal/corona/properness classification for probability histories;
3. realize the same core in at least three nonisomorphic corpus organs;
4. use reporter width to predict and prove a fourth-organ multiplicity theorem;
5. only then ask whether source properness collapses the arithmetic core to the critical law.
