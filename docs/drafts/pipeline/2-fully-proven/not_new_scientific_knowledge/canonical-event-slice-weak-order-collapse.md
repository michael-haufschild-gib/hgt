# Canonical event-slice weak-order collapse

- **ID:** `canonical-event-slice-weak-order-collapse`
- **Stage:** 2-fully-proven
- **Type:** ORDER-THEORETIC NO-GO / POSITIVE CLASSIFICATION / SPACETIME BRIDGE
- **Status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/event-boundary-identity-spacetime-law.md`

## Exact statement

Let \((P,\leq)\) be a partially ordered set and write \(x<y\) for its strict order. Define
augmented incomparability

\[
  x\mathrel{\sim}y
  \quad\Longleftrightarrow\quad
  \neg(x<y)\ \wedge\ \neg(y<x).
\]

Thus \(x\sim y\) means that \(x=y\) or \(x\) and \(y\) are incomparable.

A subset \(A\subseteq P\) is an antichain when any two distinct elements of \(A\) are
incomparable. Call \(A\) a **greatest slice through \(x\)** when:

1. \(x\in A\);
2. \(A\) is an antichain; and
3. every antichain containing \(x\) is contained in \(A\).

The following are equivalent:

1. every \(x\in P\) has a greatest slice through it;
2. augmented incomparability \(\sim\) is transitive.

When these conditions hold:

1. \(\sim\) is an equivalence relation;
2. the unique greatest slice through \(x\) is exactly
   \[
     [x]_\sim=\{y\in P:x\sim y\};
   \]
3. the equivalence classes are antichains;
4. distinct equivalence classes are totally ordered by the order inherited from \(P\); and
5. \(P\) is therefore an ordinal stack of antichains, equivalently a strict weak order.

For a finite poset, these conditions are also equivalent to:

> every event lies in exactly one inclusion-maximal antichain.

## Dependency-closed paper proof

### Greatest slices imply transitive incomparability

Assume every \(y\in P\) has a greatest slice \(S_y\).

Take \(x,y,z\in P\) with \(x\sim y\) and \(y\sim z\). The two-element set
\(\{x,y\}\) is an antichain unless \(x=y\), in which case \(x\in S_y\) already. In either
case, the defining maximality of \(S_y\) gives \(x\in S_y\). Similarly \(z\in S_y\).
Because \(S_y\) is an antichain, either \(x=z\) or \(x\) and \(z\) are incomparable.
Hence \(x\sim z\). Thus \(\sim\) is transitive.

### Transitive incomparability constructs greatest slices

Assume \(\sim\) is transitive. It is reflexive because the strict order is irreflexive, and it is
symmetric by definition. Hence \(\sim\) is an equivalence relation.

For \(x\in P\), set

\[
  S_x=\{y\in P:x\sim y\}.
\]

Reflexivity gives \(x\in S_x\). If \(y,z\in S_x\), then \(y\sim x\) by symmetry and
\(x\sim z\); transitivity gives \(y\sim z\). Therefore distinct elements of \(S_x\) are
incomparable, so \(S_x\) is an antichain.

Let \(A\) be any antichain containing \(x\), and take \(y\in A\). If \(y=x\), then
\(y\in S_x\). If \(y\neq x\), the antichain property gives \(x\sim y\), so again
\(y\in S_x\). Therefore \(A\subseteq S_x\). Thus \(S_x\) is the greatest slice through
\(x\).

The same argument shows uniqueness: two greatest slices through \(x\) contain one another.

### The slices form a total stack

Because \(\sim\) is an equivalence relation, the sets \(S_x=[x]_\sim\) partition \(P\).
Each class is an antichain by the preceding proof.

Let \(C\neq D\) be two classes and choose \(x\in C\), \(y\in D\). Since \(x\not\sim y\),
either \(x<y\) or \(y<x\). Suppose \(x<y\). We show that every element of \(C\) lies below every
element of \(D\).

Take \(x'\in C\). Then \(x'\sim x\). The alternatives \(y<x'\) and \(y\sim x'\) are impossible:
the first would give \(x<y<x'\), contradicting \(x'\sim x\), while the second combined with
\(x'\sim x\) would give \(y\sim x\), contradicting \(C\neq D\). Hence \(x'<y\).

Now take \(y'\in D\), so \(y'\sim y\). The alternatives \(y'<x'\) and \(y'\sim x'\) are
impossible by the same argument. Hence \(x'<y'\). Therefore the direction of comparison is
independent of representatives and the quotient classes are totally ordered.

Thus \(P\) is an ordinal stack of antichains, which is exactly the standard strict-weak-order
classification.

### Finite unique-maximal-antichain formulation

Assume \(P\) is finite. Every antichain is contained in an inclusion-maximal antichain.

If every event has a greatest slice, that slice is inclusion-maximal and contains every other
antichain through the event. Hence it is the unique maximal antichain through that event.

Conversely, assume each event belongs to a unique maximal antichain. If \(x\sim y\) and
\(y\sim z\), extend \(\{x,y\}\) and \(\{y,z\}\) to maximal antichains \(A\) and \(B\).
Both contain \(y\), so uniqueness gives \(A=B\). Therefore \(x\) and \(z\) lie in one antichain,
and \(x\sim z\). Transitivity follows, and the preceding classification applies.

This closes every dependency.

## Hostile audit and priority

The mathematics is established order theory, not a new theorem. A poset whose augmented
incomparability is transitive is called a stratified poset or strict weak order; its
incomparability classes form a chain. The exact unique-maximal-antichain equivalence also appears
as a standard exercise in poset logic.

Relevant sources:

- *Theory of Relations*, section on stratified posets and weak orders:
  <https://www.sciencedirect.com/science/article/pii/S0049237X0080049X>.
- Cambridge logic exercises explicitly asking for axiomatizations of posets in which every
  element belongs to a unique maximal antichain:
  <https://www.dpmms.cam.ac.uk/~tef10/cam_only/logicandproofquestions.pdf>.
- Major, Rideout, and Surya identify antichains with discrete spatial hypersurfaces in causal-set
  cosmology:
  <https://arxiv.org/abs/gr-qc/0506133>.

**Verdict:** `REDISCOVERED`.

## Exact physical insight

The theorem kills a naive realization of the parent conjecture:

> Causal order alone cannot canonically assign one complete space to each event without collapsing
> causal structure to absolute, totally ordered simultaneity layers.

Generic relativistic causal structures must allow multiple inextendible antichains through an
event, or must contain additional physical data beyond order that selects a relational boundary.
This is already true in flat relativistic spacetime, so slice nonuniqueness is not gravitational
curvature.

The positive survivor is the exact classification:

> Unique canonical spatial completion from causality is possible precisely for weak-order
> spacetimes—ordinal stacks of antichains.

The parent event--boundary identity therefore cannot define a boundary as “the unique maximal set
of events incomparable with this event.” Its open core must use source-complete joint-variability
data richer than causal order and must separately explain why gravity is curvature of comparison,
not mere relativity of simultaneity.

## Lean target

Formalized in
`formal/GaloisForLFunctions/HTGeometry/CanonicalEventSlice.lean`.

The exact general equivalence without finiteness is:

```text
every event admits a greatest antichain through it
  iff
augmented incomparability is transitive.
```

The main declaration is
`orderGreatestCausalSlices_iff_augmentedIncomparable_transitive`. The module also proves that the
canonical slice is the augmented-incomparability class and that two events have the same canonical
slice exactly when they are augmented-incomparable.

No physical statement is claimed.

## Gates

- [x] exact statement and dependency-closed paper proof
- [x] hostile mathematical and physical interpretation audit
- [x] priority corrected to `[REDISCOVERED] [BRIDGE]`
- [x] exact unconditional Lean theorem
- [x] axiom and formal lint audit

## Log

- 2026-07-29 — extracted from hostile attack on the frozen event--boundary identity. The
  obstruction rules out a causality-only canonical slice while preserving the strict weak-order
  classification as positive content.
- 2026-07-29 — exact theorem formalized in `CanonicalEventSlice.lean`; direct Lean check and
  dedicated module build passed. Axiom report contains only standard logical quotient/extensionality
  principles.
