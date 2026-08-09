# Observer unitization, recurrence, open history, and cost nondescendence law

- **ID:** ULF-PRD-PUMP-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified) / FOUNDATIONAL EXCHANGE LAW
- **Source:** Polarized Realization Dynamics
- **Statement:** If an observer sends a positive-cost source history to the identity, its iterates
  give exact recurrent observation, injective open lifted history, linearly growing action, and a
  proof that action cannot descend through the observer.
- **Status:** [LEAN-CERTIFIED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [NO PROJECT AXIOMS] [NOT RH]

## 1. Setup

Let \(M,N\) be monoids, let \(Q:M\to N\) be a monoid homomorphism, and let

\[
 A:M\to\mathbb N
\]

satisfy

\[
 A(1)=0,\qquad A(xy)=A(x)+A(y).
\tag{UP.1}
\]

Fix a source history \(h\in M\) such that

\[
 Q(h)=1,\qquad A(h)>0.
\tag{UP.2}
\]

## 2. Observer-unitization pump theorem

For every \(n\in\mathbb N\),

\[
 Q(h^n)=1,
\qquad
 A(h^n)=nA(h).
\tag{UP.3}
\]

The map

\[
 \mathbb N\longrightarrow M,\qquad n\longmapsto h^n
\tag{UP.4}
\]

is injective. Thus the observer sees one stationary recurrent value while source history visits
infinitely many distinct states with unbounded linear action.

### Proof

The homomorphism law gives \(Q(h^n)=Q(h)^n=1\). Induction using (UP.1) gives
\(A(h^n)=nA(h)\). If \(h^m=h^n\), applying \(A\) gives
\(mA(h)=nA(h)\). Since \(A(h)>0\), cancellation in \(\mathbb N\) gives \(m=n\). QED.

## 3. Cost nondescendence

There is no additive observer cost \(B:N\to\mathbb N\) with

\[
 B(1)=0,
\qquad
 A=B\circ Q.
\tag{UP.5}
\]

Indeed, (UP.2) and (UP.5) would give

\[
 0<A(h)=B(Q(h))=B(1)=0.
\]

Therefore positive action is not merely hidden numerically; it provably fails to descend through
the recurrent observer.

## 4. Coordinate-free reading

The hypothesis \(Q(h)=1\) says an observer localization **unitizes** a nontrivial directed history.
One such event forces four shadows from one composition law:

1. closed/exact observer recurrence;
2. open lifted history;
3. positive action growth;
4. loss of action under observer descent.

No metric, connection, curvature, covering space, or route endpoint is assumed.

## 5. Sharp boundaries

1. If \(A(h)=0\), powers need not be distinct and no action growth follows.
2. If \(Q(h)\ne1\), observation need not recur.
3. If action is merely subadditive, linear equality in (UP.3) can fail.
4. The theorem does not source-select \(M,Q,A,h\); PRD acceptance requires one literal source to
   produce them before target specialization.
5. Exact identity observation is stronger than approximate recurrence. A topological successor
   needs properness/coercivity hypotheses.

## 6. Lean certificate

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveObserverUnitization`.

Closed declarations:

- exact observer return of all powers;
- exact linear action of all powers;
- injectivity of lifted power history;
- impossibility of additive cost descent;
- one bundled pump theorem.

Targeted source check and final module build passed. `#print axioms` reports no axioms for observer
return and cost nondescendence, and only `propext` for action, injectivity, and bundled theorem. No
project axiom or computation proof occurs.

## Log

- 2026-08-09 — observer-unitization exchange law proved on paper as first PRD theorem coupling
  recurrence, open history, positive action, and nondescendence from one source history.
- 2026-08-09 — all five declarations closed in Lean; targeted final build passed; promoted to
  Stage 3.
