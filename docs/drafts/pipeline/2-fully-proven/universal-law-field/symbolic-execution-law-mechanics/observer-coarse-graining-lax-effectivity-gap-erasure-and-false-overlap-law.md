# Observer coarse-graining, lax effectivity, gap erasure, and false-overlap law

- **ID:** ULF-SELM-7
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT OBSERVER-TRANSPORT THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [LAX EFFECTIVITY]
  [EXACT GAP ERASURE WITNESS] [LEAN TARGET] [NOT RH]
- **Parents:** ULF-SELM-1--6; ULF-FKT-OD-1

## 1. Purpose

SELM now has a semantic quotient for static presentations.  The missing dynamic question is what an
observer does to symbolic admission and legal execution.  This card proves a strict direction:
positive coarse-graining transports both local laws and actual executions.  It therefore cannot
create a symbolic-execution obstruction from an executable source law.  But it can erase an
existing obstruction by identifying independent resources.

The same identification that erases the execution gap produces the positive false-overlap defect
of ULF-FKT-OD-1.  This is the first exact exchange law between failure-kernel mechanics and
symbolic-execution mechanics.

## 2. Positive observer transport

Let `X,Y` be finite coordinate sets and `f:X->Y`.  Define

\[
 fK=\{f(x):x\in K\},\qquad
 fH=\{fK:K\in H\},
 \tag{OC.1}
\]

and push a nonnegative weight by fibre summation:

\[
 (f_!a)(y)=\sum_{x:f(x)=y}a(x).
 \tag{OC.2}
\]

For every kernel `K`, positivity gives

\[
 \boxed{
 \sum_{x\in K}a(x)
 \leq
 \sum_{y\in fK}(f_!a)(y).}
 \tag{OC.3}
\]

Indeed, the right side sums `a(x)` over every source point whose image belongs to `fK`, a set
containing `K`.

## 3. Lax-effectivity theorem

### Theorem 3.1 -- local admission is covariant

\[
 \boxed{
 \operatorname{Local}_H(m,a)
 \Longrightarrow
 \operatorname{Local}_{fH}(m,f_!a).}
 \tag{OC.4}
\]

### Proof

Every target kernel is `fK` for some `K\in H`.  Apply source local admission followed by `(OC.3)`.
∎

### Theorem 3.2 -- execution is covariant

\[
 \boxed{
 \operatorname{Exec}_H(m,a)
 \Longrightarrow
 \operatorname{Exec}_{fH}(m,f_!a).}
 \tag{OC.5}
\]

### Proof

Push every grade-one execution piece by fibre summation.  Theorem 3.1 makes every pushed piece
locally admitted.  If the source pieces satisfy

\[
 \sum_j a_j(x)\leq a(x),
\]

then summing this inequality over `f^{-1}(y)` gives

\[
 \sum_j(f_!a_j)(y)\leq(f_!a)(y).
\]

Thus the pushed pieces form a target execution. ∎

### Corollary 3.3 -- observer noncreation of gaps

If the source state is locally admitted and its pushforward is a symbolic-execution gap, then the
source was already a symbolic-execution gap:

\[
 \boxed{
 \operatorname{Local}_H(m,a)\wedge
 \operatorname{Gap}_{fH}(m,f_!a)
 \Longrightarrow
 \operatorname{Gap}_H(m,a).}
 \tag{OC.6}
\]

The target nonexecution and `(OC.5)` imply source nonexecution by contraposition.

This is one-sided.  Nonexecution is not covariant.

## 4. Exact gap-erasure witness

Take source coordinates `X={0,1,2}` with the triangle failure family

\[
 H=\{\{0,1\},\{1,2\},\{0,2\}\}.
\]

At grade two, the weight `a=(1,1,1)` is locally admitted but nonexecutable by ULF-SELM-1.  Let

\[
 f(0)=f(1)=A,\qquad f(2)=B.
 \tag{OC.7}
\]

Then

\[
 fH=\{\{A\},\{A,B\}\},
 \qquad f_!a=(2,1).
 \tag{OC.8}
\]

The target law is executable: use two identical grade-one pieces `(1,0)`.  Each is locally
admitted because every inclusion-minimal target failure kernel contains `A`, and their sum fits
under `(2,1)`.  Hence

\[
 \boxed{
 \operatorname{Gap}_H(2,a)
 \quad\text{but}\quad
 \neg\operatorname{Gap}_{fH}(2,f_!a).}
 \tag{OC.9}
\]

The obstruction was not repaired at source.  It was erased by observer identification.

## 5. Exact false-overlap coupling

Let `u=delta_0` and `v=delta_1`.  Their source meet is zero, but

\[
 f_!u=f_!v=\delta_A.
\]

Therefore the ULF-FKT-OD-1 overlap defect is

\[
 \boxed{\Omega_f(u,v)=\delta_A.}
 \tag{OC.10}
\]

Thus one concrete identification simultaneously:

1. manufactures one unit of observed common repair;
2. turns the triangle primitive obstruction into two legal copies of that repair;
3. erases the symbolic-execution gap.

This does not assert that total overlap mass classifies all execution-gap loss.  It proves a typed,
exact common mechanism in the minimal witness.

## 6. Constitutive law

### SELM Law VII -- positive observation is lax for effectivity

Positive coarse-graining preserves symbolic admission and legal execution, but can turn an
indecomposable source obstruction into an ordinary target execution.  Consequently:

1. an obstruction seen after observation is inherited from source;
2. absence of an observed obstruction does not imply source effectivity;
3. source no-go classes can disappear without becoming boundaries or without changing the source
   law;
4. false overlap is one exact resource-collision mechanism for this disappearance;
5. bijective observers are the strict chamber, recovered by ULF-SELM-5.

This is mathematical leverage: any proof strategy that closes only after a noninjective positive
observer must separately prove source reflection.  Target execution alone is insufficient.

## 7. Sharp boundaries

1. Fibre summation and nonnegative weights are load-bearing.  Signed transports require oriented
   cancellation data.
2. Theorems 3.1--3.2 prove covariance, not reflection.
3. The triangle proves erasure can occur; it does not classify every erased primitive.
4. False-overlap mass is bounded under normalized positive observation and cannot itself be an
   unbounded history cost.
5. Completion, topology, phase, and infinite apertures require separate admitted transport laws.
6. No route is credited without a literal pre-endpoint observer map and source failure family.
7. No RH statement occurs.

## 8. Lean target

Formalize in

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveObserverExecutionGap.lean`

without project axioms, `sorry`, `admit`, `opaque`, `unsafe`, or computation proofs.  Certify:

1. finite kernel/family and natural-weight pushforward;
2. kernel-sum domination `(OC.3)`;
3. local and executable covariance;
4. gap noncreation;
5. explicit triangle-collapse gap erasure;
6. one unconditional capstone imported by `HTGeometry.UniversalLawField`.

## Log

- 2026-08-10 -- derived by composing SELM's symbolic/executable gap with the finite positive
  observer mechanics of ULF-FKT-OD-1.  General transport and exact triangle-erasure proofs are
  dependency-closed.  Lean certification pending.
