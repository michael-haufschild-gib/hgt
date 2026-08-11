# Observer gap-death filtration, strict composition, and no-revival law

- **ID:** ULF-SELM-8
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT EFFECTIVITY-HISTORY THEOREM
- **Status:** [PAPER-PROVED] [LEAN-CERTIFIED] [DEPENDENCY-CLOSED] [STRICT OBSERVER
  COMPOSITION] [GAP-DEATH FILTRATION] [NO REVIVAL] [NOT RH]
- **Parents:** ULF-SELM-1--7

## 1. Purpose

ULF-SELM-7 proves a one-step asymmetry: positive observation preserves both symbolic admission and
legal execution, but may erase a symbolic--execution gap.  This card proves the compositional law
that the one-step theorem forces.  Along every finite chain of positive observers applied to a
locally admitted source law, execution gaps form an initial segment.  Once an observer has erased
the gap, no later positive observer can make it reappear.

This is not a slogan about information loss.  It is an exact persistence theorem with strict
composition, a death-time invariant, and a falsification rule for proposed observer chains.

## 2. Strict observer composition

Let `X,Y,Z` be finite coordinate sets, let `f:X->Y`, `g:Y->Z`, and let `H` be a finite failure
family on `X`.  For a kernel `K` and nonnegative integral weight `a`, define

\[
 fK=\{f(x):x\in K\},\qquad
 fH=\{fK:K\in H\},\qquad
 (f_!a)(y)=\sum_{f(x)=y}a(x).
 \tag{GD.1}
\]

### Theorem 2.1 -- strict functoriality

The observer transports preserve identities and compose on the nose:

\[
 \boxed{
 (g\circ f)K=g(fK),\qquad
 (g\circ f)H=g(fH),\qquad
 (g\circ f)_!a=g_!(f_!a).}
 \tag{GD.2}
\]

### Proof

The kernel equality is the elementary identity `g[f[K]]=(g o f)[K]`.  Applying it to every member
of `H` gives the family equality, including repeated-image removal on both sides.  For each `z`,
finite Fubini rearrangement gives

\[
 \begin{aligned}
 (g_!f_!a)(z)
 &=\sum_{g(y)=z}\sum_{f(x)=y}a(x)\\
 &=\sum_{g(f(x))=z}a(x)
 =((g\circ f)_!a)(z).
 \end{aligned}
\]

Every source point contributes exactly once, at `y=f(x)`.  The identity laws follow by taking
`f=id`. ∎

Thus positive observers form an honest execution-transport category, not merely a collection of
unrelated quotients.

## 3. Backward persistence and forward death

Put

\[
 (H_0,a_0)=(H,a),\qquad
 (H_1,a_1)=(fH,f_!a),\qquad
 (H_2,a_2)=(gH_1,g_!a_1).
 \tag{GD.3}
\]

Assume `Local(H_0,m,a_0)`.  ULF-SELM-7 transports local admission and execution at every stage.

### Theorem 3.1 -- two-step backward persistence

\[
 \boxed{
 \operatorname{Gap}(H_2,m,a_2)
 \Longrightarrow
 \operatorname{Gap}(H_1,m,a_1)
 \Longrightarrow
 \operatorname{Gap}(H_0,m,a_0).}
 \tag{GD.4}
\]

### Proof

Local admission at stage zero transports to stage one.  Apply the one-step noncreation theorem to
`g` to obtain the first implication, and to `f` to obtain the second. ∎

### Corollary 3.2 -- no revival

\[
 \boxed{
 \neg\operatorname{Gap}(H_1,m,a_1)
 \Longrightarrow
 \neg\operatorname{Gap}(H_2,m,a_2).}
 \tag{GD.5}
\]

This is the contrapositive of the first implication in `(GD.4)`.  Notice what it says: a later
observer can destroy more distinctions, but it cannot reconstruct a symbolic--execution
obstruction already erased by an earlier positive observer.

### Corollary 3.3 -- finite gap-death filtration

For a finite composable observer chain

\[
 X_0\longrightarrow X_1\longrightarrow\cdots\longrightarrow X_N
 \tag{GD.6}
\]

issued from a locally admitted source law, write `G_i` for the proposition that the transported
law at stage `i` is a gap.  Then

\[
 j\ge i\ \wedge\ G_j\Longrightarrow G_i.
 \tag{GD.7}
\]

Hence `{i:G_i}` is an initial segment of `{0,...,N}`.  Equivalently, execution-gap death can occur
at most once.  If it occurs at stage `d`, every stage `i<d` is a gap and every stage `i>=d` is not.

### Proof

Iterate Theorem 3.1 backward from `j` to `i`.  Abstractly, any predicate `G:N->Prop` satisfying
`G(n+1)->G(n)` is downward closed by induction on `j-i`. ∎

The death stage depends on the marked observer chain.  The theorem does not declare it invariant
under arbitrary replacement of that chain.

## 4. Exact finite death witness

Take the triangle law from ULF-SELM-1:

\[
 H_\triangle=\{\{0,1\},\{1,2\},\{0,2\}\},\qquad a=(1,1,1),\qquad m=2.
\]

It is a source gap.  Collapse vertices `0,1` and retain vertex `2`.  ULF-SELM-7 proves that the
observed family and weight are

\[
 H_1=\{\{A\},\{A,B\}\},\qquad a_1=(2,1),
\]

and that two copies of `(1,0)` execute the target law.  Therefore the gap dies exactly at stage
one.  For every subsequent positive observer `g`, execution transports to `g_!a_1`; hence

\[
 \boxed{
 \operatorname{Gap}(H_\triangle,2,a),\qquad
 \neg\operatorname{Gap}(H_1,2,a_1),\qquad
 \neg\operatorname{Gap}(gH_1,2,g_!a_1).}
 \tag{GD.8}
\]

This is a nonvacuous death filtration: alive at stage zero, dead at stage one, permanently dead
afterward.

## 5. Constitutive law

### SELM Law VIII -- effectivity history is an irreversible filtration

For positive observer transport of a locally admitted law:

1. local admission and execution move forward;
2. an execution obstruction moves backward;
3. gap truth is hereditary toward the source;
4. gap death is hereditary toward coarser observers;
5. observer composition is strict, so the result is independent of parenthesization;
6. a proposed observer chain in which a dead gap later revives cannot be a chain of these positive
   transports.  At least one stage changes admission, uses signed cancellation, changes the law,
   loses functoriality, or is not represented by a comparison map.

The mechanism is closer to persistence theory than to curvature: source obstruction has a barcode
with one possible death and no finite rebirth.  Holonomy or recurrence may coexist with it, but are
not needed to define it.

## 6. Frontier leverage

The theorem imposes one common audit on all proof-route exits without identifying their native
objects:

1. a positive scalarization that makes an obstruction executable cannot later recover it through
   further positive scalarization;
2. a Hausdorff quotient that kills a dense-radical obstruction cannot have that obstruction
   reappear in another ordinary quotient without a changed admission doctrine;
3. a recurrent endpoint observer may hide open lifted execution history, but later endpoint-only
   observers cannot reconstruct it;
4. a route comparison claiming both positive functoriality and obstruction revival is false or
   missing a marked source leg;
5. parallel observers are not covered by the linear-chain theorem: jointly faithful probes may
   retain information that either leg separately kills.

This is route-independent leverage, not a claim that every route has already supplied its literal
observer functor.

## 7. Sharp boundaries

1. Nonnegative fibre aggregation is load-bearing.  Signed, oriented, or indefinite transport may
   create cancellations and requires another law.
2. Local admission at the initial stage is load-bearing for backward gap propagation.
3. The theorem concerns a serial chain.  Parallel observer families require joint reflection.
4. The death stage is observer-relative, not a source repair or a homology boundary.
5. Finite no-revival does not decide a pro-limit.  A gap may survive every finite stage yet disappear
   after a non-strict completion.  That is the next completion/exactification law.
6. No HT theorem, positivity theorem, recurrence theorem, physical identification, or RH statement
   is inferred from the abstract filtration alone.

## 8. Lean certification

Formalization target:

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveObserverGapPersistence.lean`

The module certifies without project axioms or computation proofs:

1. identity and strict composition for kernels, failure families, and fibre-sum weights;
2. two-step backward gap persistence and forward no-revival;
3. the abstract initial-segment theorem for hereditary obstruction predicates;
4. permanent triangle-gap death after every later positive observer;
5. one unconditional capstone wired into `HTGeometry.UniversalLawField`.

Direct foreground elaboration passes.  Final foreground umbrella build passes with 11,606 jobs.
Axiom inspection reports only `propext`, `Classical.choice`, and `Quot.sound`; the abstract
initial-segment theorem itself reports no axioms.  Repository lint reaches the new module with no
target error; its global nonzero exit is caused by unrelated unwired modules elsewhere in the
shared corpus.

## Log

- 2026-08-10 -- extracted from ULF-SELM-7 by closing observer composition instead of pursuing a
  route-specific source selector.  Full paper proof and Lean certification pass.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
