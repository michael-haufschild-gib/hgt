# Alternating unary-law saturation horizon and finite-observer stabilization law

- **ID:** ULF-LSM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Source:** Law-Saturation Mechanics, first exact calibration
- **Statement:** Two explicit unary source laws induce noncommuting idempotent least-repair
  closures whose joint saturation has exact finite depth and closure ordinal \(\omega\), although
  every finite observer stabilizes.
- **Status:** [PROVED HERE] [DEPENDENCY CLOSED] [MECHANISM FIRST] [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [NOT RH]

## Goal

Exhibit one unconditional system in which operation admission itself forces observer loss, ordered
repair history, a directed depth geometry, and a finite/cofinal horizon. No route, RH endpoint,
curvature, topology, or physical analogy is used in the construction.

## 1. Source, observers, and laws

Let

\[
  X=\mathbb N\times\{0,1\}.
\]

For \(S\subseteq\mathbb N\), define an equivalence relation \(E_S\) on \(X\) by

\[
  (m,b)\ E_S\ (n,c)
  \quad\Longleftrightarrow\quad
  m=n\ \text{ and }\ (b=c\ \text{or}\ m\in S).
  \tag{1}
\]

Thus the observer forgets the bit exactly at the levels in \(S\).

Define two unary source laws:

\[
 e(n,b)=
 \begin{cases}
   (n+1,b),&n\text{ even},\\
   (n,b),&n\text{ odd},
 \end{cases}
 \qquad
 o(n,b)=
 \begin{cases}
   (n+1,b),&n\text{ odd},\\
   (n,b),&n\text{ even}.
 \end{cases}
 \tag{2}
\]

Their induced distinction-repair operations are

\[
 C_e(S)=S\cup\{n+1:n\in S,\ n\text{ even}\},
 \tag{3}
\]

\[
 C_o(S)=S\cup\{n+1:n\in S,\ n\text{ odd}\}.
 \tag{4}
\]

Write \(P_k=\{0,1,\ldots,k\}\).

## 2. The theorem

### Theorem 2.1 — executable descent and least repair

For every \(S\subseteq\mathbb N\):

1. \(E_S\) is an equivalence relation.
2. The law \(e\) descends through \(X/E_S\) iff \(C_e(S)=S\).
3. The law \(o\) descends through \(X/E_S\) iff \(C_o(S)=S\).
4. \(C_e(S)\) is the least superset \(T\supseteq S\) for which \(e\) descends through
   \(X/E_T\). The analogous statement holds for \(C_o\).
5. Both \(C_e\) and \(C_o\) are extensive, monotone, and idempotent closure operators.

### Theorem 2.2 — exact noncommuting saturation

Let \(\Phi=C_oC_e\). Then for every \(r\ge0\),

\[
  \Phi^r(P_0)=P_{2r}.
  \tag{5}
\]

More precisely,

\[
  C_e(P_{2r})=P_{2r+1},
  \qquad
  C_o(P_{2r+1})=P_{2r+2}.
  \tag{6}
\]

The closures do not commute:

\[
  C_oC_e(P_0)=P_2,
  \qquad
  C_eC_o(P_0)=P_1.
  \tag{7}
\]

No finite \(\Phi^r(P_0)\) is a common fixed point. The increasing union

\[
  P_\omega=\bigcup_{r<\omega}\Phi^r(P_0)=\mathbb N
  \tag{8}
\]

is the least common fixed point of \(C_e,C_o\) above \(P_0\). Hence the joint repair has closure
ordinal exactly \(\omega\).

### Theorem 2.3 — exact directed law depth

Let a repair word be a word in \(C_e,C_o\), and let \(w(P_0)\) denote its action. For every
\(j\in\mathbb N\), the least word length for which \(j\in w(P_0)\) is exactly \(j\).

Thus the propagation level is the directed law distance from the initial observer state:

\[
 d(P_0,\{S:j\in S\})=j.
 \tag{9}
\]

### Theorem 2.4 — finite observer stabilization with open global history

For each level \(j\), let \(\rho_j(S)=1\) if \(j\in S\) and \(0\) otherwise. Then

\[
  \rho_j(\Phi^r(P_0))=1
  \quad\Longleftrightarrow\quad
  j\le 2r.
  \tag{10}
\]

Consequently every finite reporter family \(\{\rho_j:j\in J\}\) is constant for all
\(r\ge\lceil\max(J)/2\rceil\), while the global source history
\(P_0\subsetneq P_2\subsetneq P_4\subsetneq\cdots\) never stabilizes at finite time.

In the product topology on \(\{0,1\}^{\mathbb N}\), the reporter vectors converge to the all-one
vector. Therefore open law history does not imply noncompact observer dynamics.

## 3. Proof

### Proof of Theorem 2.1

Reflexivity, symmetry, and transitivity of \(E_S\) follow directly from (1). At each fixed level
outside \(S\) its classes are the two singletons; at a level in \(S\) there is one two-point class.

A unary operation descends through a quotient exactly when it preserves the kernel equivalence.
Suppose first that \(e\) preserves \(E_S\). If \(n\in S\) is even, then

\[
 (n,0)\ E_S\ (n,1).
\]

Applying \(e\) gives \((n+1,0)\ E_S\ (n+1,1)\), so \(n+1\in S\). Hence
\(C_e(S)\subseteq S\), and extensivity gives equality.

Conversely assume \(C_e(S)=S\), and take \((n,b)E_S(n,c)\). If \(b=c\), their images under
\(e\) are equal. If \(b\ne c\), then \(n\in S\). When \(n\) is odd, \(e\) fixes both points,
so their images remain equivalent. When \(n\) is even, the closure equation implies
\(n+1\in S\), so their images are again equivalent. Thus \(e\) preserves \(E_S\).

The proof for \(o\) is identical with parity reversed.

By construction \(C_e(S)\supseteq S\). It is \(e\)-closed: any even element of \(C_e(S)\) must
already lie in \(S\), because every newly adjoined element is the odd successor of an even element.
Its successor is therefore already adjoined. If \(T\supseteq S\) is \(e\)-closed, it contains the
successor of every even element of \(S\), hence contains \(C_e(S)\). This proves leastness.

Extensivity and monotonicity are immediate from (3). The preceding parity observation gives
\(C_e(C_e(S))=C_e(S)\), so \(C_e\) is idempotent. The argument for \(C_o\) is the same. ∎

### Proof of Theorem 2.2

Every even element of \(P_{2r}\) has successor at most \(2r+1\), and the top element \(2r\)
forces \(2r+1\). Therefore \(C_e(P_{2r})=P_{2r+1}\). Every odd element of
\(P_{2r+1}\) has successor at most \(2r+2\), and the top element forces \(2r+2\), proving the
second identity in (6). Equation (5) follows by induction.

Since \(C_o(P_0)=P_0\), applying \(C_e\) next yields \(P_1\). The opposite order yields \(P_2\)
by (6), proving (7).

No \(P_{2r}\) is \(C_e\)-closed because it contains the even level \(2r\) but not its successor.
The union in (8) is all of \(\mathbb N\), hence fixed by both closures. If \(T\) is any common
fixed point containing \(0\), then \(e\)-closure forces \(1\), \(o\)-closure forces \(2\), and
induction alternately forces every natural number. Hence \(T=\mathbb N\). This proves leastness and
exact closure ordinal \(\omega\). ∎

### Proof of Theorem 2.3

One application of either closure can adjoin only successors of elements already present. Starting
from \(P_0\), after a word of length \(\ell\) no level greater than \(\ell\) can occur. Hence any
word reaching level \(j\) has length at least \(j\).

The alternating word

\[
 C_e,\ C_o,\ C_e,\ C_o,\ldots
\]

of length \(j\) produces \(P_j\) by the same parity calculation as (6), so it reaches level \(j\).
The lower and upper bounds agree. ∎

### Proof of Theorem 2.4

Equation (10) is immediate from (5). For finite nonempty \(J\), choose
\(r\ge\lceil\max(J)/2\rceil\); then every reporter in the family has value one forever after.
For \(J=\varnothing\), stabilization is vacuous. Strictness of the global chain follows because
\(2r+2\notin P_{2r}\).

Coordinatewise convergence to the all-one vector is exactly (10). Product-topology convergence is
coordinatewise convergence, and \(\{0,1\}^{\mathbb N}\) is compact by Tychonoff's theorem. ∎

## 4. Universal consequences

1. **Idempotent local repair does not imply shallow joint repair.** Each law is fully repaired in
   one step, but their interaction has unbounded depth.
2. **Finite verification does not imply global executability.** Every finite reporter family
   eventually certifies stability while one source law still fails at the next unseen level.
3. **History is generated by noncommuting law admission.** No connection or curvature is required.
4. **Nontermination is not noncompactness.** The complete observer history converges inside a compact
   product space.
5. **The geometry is operational.** Minimal repair-word length recovers propagation depth exactly.

## 5. Hostile scope

- The closure-semigroup component is classical. The exact contribution of this card is the explicit
  realization as least observer repairs for source operations and the combined finite/cofinal law.
- The theorem does not identify hypertranscendence with closure ordinal \(\omega\). It supplies only
  the mechanism that a differential realization would have to instantiate.
- The theorem does not make positivity a universal quotient. A positive realization must provide a
  literal kernel equivalence and source operations.
- Compact convergence here is not recurrence. Recurrence requires an additional periodic action or
  quotient.
- No RH implication, source selector, physical prediction, or whole-corpus universality is claimed.

## 6. Falsifiers for the field programme

This theorem fails to support Law-Saturation Mechanics as a new field if subsequent work cannot do
all of the following:

1. derive the repair closures from a literal pre-target source in at least three nonisomorphic corpus
   organs;
2. compute a forced observer loss not already explicit in those organs;
3. couple a positive quotient, a recurrence/history quotient, and a prolongation closure without
   supplying independent generators;
4. produce a withheld cross-organ prediction.

## 7. Lean certificate

Certified module: `GaloisForLFunctions.HTGeometry.ConstitutiveLawSaturation`.

Unconditional capstone: `lawSaturationMechanism_closed`.

The certificate includes equivalence of source-law preservation and repair fixedness, universal least repair, idempotence, noncommutation, the exact sweep-prefix law, absence of finite common fixed stages, the least common fixed point above level zero, reporter stabilization, and strict global history. Source check, module build, project lint, and axiom audit passed. Axiom audit reports only Lean/mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation certificate is used.

## 8. Original Lean target

Formalize the closed concrete theorem in
`GaloisForLFunctions.HTGeometry.ConstitutiveLawSaturation` and import it from
`GaloisForLFunctions.HTGeometry.UniversalLawField`. Required exported statements:

- idempotence and noncommutation of the two closures;
- exact \(r\)-sweep prefix law;
- no finite common fixed stage;
- coordinate reporter stabilization;
- strict global history.

## Log

- 2026-08-09 — paper proof completed; generic closure collision recorded.
- 2026-08-09 — Lean module, umbrella wiring, lint, build, and axiom audit passed; promoted to Stage 3.

