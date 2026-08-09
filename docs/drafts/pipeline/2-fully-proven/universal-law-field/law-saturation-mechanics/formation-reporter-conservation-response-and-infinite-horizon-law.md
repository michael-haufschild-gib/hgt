# Formation-reporter conservation, response, and infinite-horizon law

- **ID:** ULF-LSM-4
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [LEAN-PROVED] [REPORTER CONSERVATION] [RESPONSE EXISTENCE]
  [HORIZON CERTIFICATE] [NOT RH]

## 1. Setup

Let law formations act on distinction states as in ULF-LSM-3. A reporter $q$ is invariant under a
formation $C$ when

$$
q(C(S))=q(S)
$$

for every state $S$. A reporter coframe $\mathcal R$ separates states when

$$
(\forall q\in\mathcal R,\ q(S)=q(T))\Longrightarrow S=T.
$$

No linearity, topology, metric, positivity, or arithmetic structure is assumed.

## 2. Conservation theorem

### Theorem 2.1

Let $\mathcal F$ be a family of formations and let $q$ be invariant under every member of
$\mathcal F$. Then every finite formation word $w$ in $\mathcal F$ conserves $q$:

$$
q(w(S))=q(S).
$$

### Proof

Induct on word length. The empty word is the identity. If $w=Cv$, the induction hypothesis gives
$q(v(C(S)))=q(C(S))$, and invariance of $q$ under $C$ gives $q(C(S))=q(S)$. ∎

## 3. Horizon certificate

### Theorem 3.1

Let $J_{\mathcal F}(S)$ be joint repair. If

$$
q(J_{\mathcal F}(S))\ne q(S),
$$

then no finite word in $\mathcal F$ reaches joint repair from $S$.

### Proof

If $w(S)=J_{\mathcal F}(S)$ for a finite word, Theorem 2.1 gives
$q(J_{\mathcal F}(S))=q(w(S))=q(S)$, contradiction. ∎

Thus reporter change at saturation is an exact certificate of an infinite formation horizon or of a
failure in the claimed primitive reporter invariance. It is not automatically an anomaly class.

## 4. Response theorem

### Theorem 4.1

If a reporter coframe $\mathcal R$ separates states and $C(S)\ne S$, then some reporter has nonzero
response:

$$
\exists q\in\mathcal R,\qquad q(C(S))\ne q(S).
$$

Equivalently, if every reporter in a separating coframe is invariant under $C$, then $C$ is the
identity formation.

### Proof

If all reporter values agreed on $C(S)$ and $S$, separation would give $C(S)=S$. Contraposition
proves the first statement; the second is its pointwise form. ∎

## 5. Mechanism consequences

1. A conserved source reporter cannot be killed by any finite legal schedule.
2. A changed value at joint repair locates the failure: infinite horizon or broken reporter
   naturality.
3. A nontrivial formation cannot remain invisible to a complete reporter coframe.
4. Therefore “completion erased the obstruction” is incomplete unless it identifies which reporter
   stopped extending or which infinite limit was used.
5. Finite reporter conservation does not imply conservation at a topological or pro-limit; such a
   conclusion requires an independently proved continuity law.

## 6. Sharp scope

- Separating coframes may be very large and need not be physically admitted.
- A single nonseparating reporter may miss a nontrivial formation.
- Reporter change does not identify a unique repair schedule.
- The theorem does not claim all corpus charges share one codomain.
- Infinite-horizon conclusion assumes primitive invariance under every finite formation step.

## 7. Lean certificate

Module `GaloisForLFunctions.HTGeometry.ConstitutiveFormationReporter` certifies conservation along
words, changed-reporter horizon obstruction, separating-coframe identity rigidity,
nontrivial-response existence, and a closed capstone. Targeted foreground build passed. Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, placeholder, unsafe
declaration, or computation proof is used.

## Log

- 2026-08-09 — paper proof closed as general charge/response law for formation mechanics.
- 2026-08-09 — Lean formalization, targeted build, and axiom audit passed.
