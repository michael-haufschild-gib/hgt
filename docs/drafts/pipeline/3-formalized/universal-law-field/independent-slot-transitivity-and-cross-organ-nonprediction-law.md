# Independent-slot transitivity and cross-organ nonprediction law

- **ID:** ULF-SLOT-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** universal-law field anti-theatre audit
- **Statement:** A product of independently relabelable organ spaces has no nonconstant intrinsic invariant and no proper nonempty intrinsic phase.
- **Status:** [LEAN-FORMALIZED] [ANTI-THEATRE] [ROUTE-INDEPENDENT]
- **Formalized companion:** `formal/GaloisForLFunctions/HTGeometry/ConstitutiveIndependentSlotNoGo.lean`

## 1. Setup

Let \(X_1,\ldots,X_n\) be nonempty sets and put

\[
X=\prod_{i=1}^n X_i,
\qquad
G=\prod_{i=1}^n \operatorname{Sym}(X_i).
\]

The group \(G\) acts on \(X\) by independent coordinate relabelling:

\[
(g_1,\ldots,g_n)(x_1,\ldots,x_n)
=(g_1x_1,\ldots,g_nx_n).
\tag{1}
\]

Call a subset \(P\subseteq X\) intrinsic to the independent-slot structure when it is \(G\)-invariant.
Call a function \(I:X\to Y\) an intrinsic invariant when \(I(gx)=I(x)\) for every \(g\in G\).

## 2. Theorem

The action (1) is transitive. Consequently:

1. every intrinsic subset of \(X\) is either \(\varnothing\) or \(X\);
2. every intrinsic invariant \(I:X\to Y\) is constant;
3. no nontrivial relation between two or more coordinates is determined by the independent-slot
   product alone;
4. adding more independently relabelable slots cannot repair the failure.

### Proof

Take \(x=(x_i)\) and \(y=(y_i)\) in \(X\). For each \(i\), choose a permutation
\(g_i\in\operatorname{Sym}(X_i)\) with \(g_ix_i=y_i\). Such a permutation exists: if
\(x_i=y_i\), use the identity; otherwise exchange \(x_i\) and \(y_i\). Then
\(g=(g_i)\in G\) satisfies \(gx=y\). Thus the action is transitive.

If \(P\) is nonempty and invariant, choose \(x\in P\). Transitivity sends \(x\) to every
\(y\in X\), so every \(y\) lies in \(P\), hence \(P=X\). If \(I\) is invariant, transitivity gives
\(I(x)=I(y)\) for all \(x,y\), hence \(I\) is constant. The last two assertions restate these facts:
a cross-coordinate relation is a proper nonempty subset, and the same proof applies after adjoining
any further independent factors. QED.

## 3. Coordinate-free groupoid form

Let \(\mathcal G_i\) be nonempty connected groupoids. Then
\(\prod_i\mathcal G_i\) is connected. Therefore every equivalence-invariant functor

\[
\prod_i\mathcal G_i\longrightarrow Y_{\mathrm{disc}}
\]

to a discrete groupoid is constant on objects. Nontrivial discrete phases require either a
disconnected factor or structure coupling the factors before taking the invariant.

## 4. Field consequence

A proposed universal field whose primitive merely lists independent relation, positivity, topology,
history, cost, and observer coordinates predicts no relation among them. It is a classification
vocabulary, not dynamics. A nontrivial field must include at least one load-bearing coupling that
reduces the independent relabelling symmetry and yields a cross-organ invariant or response law.

This does not require the coupling to be geometric, local, binary, or curvature-like. It may be an
action, generating functional, composition law, fixed-point equation, common universal property,
or another single producer.

## 5. Sharp scope

- Existing structure inside an \(X_i\) can reduce \(\operatorname{Sym}(X_i)\); the theorem then says
  that this structure, not the bare slot, does the work.
- A chosen relation \(P\subset X\) trivially breaks transitivity, but then \(P\) is added constitutive
  data and must be derived independently before it can count as a prediction.
- The theorem does not select the correct coupling. It supplies a necessary anti-theatre gate.
- No claim of external novelty is made; the proof is elementary group-action theory.

## 6. Representation lesson

The next field candidate must begin with one producer whose shadows are the apparent organs. It may
not begin by storing those organs in separate boxes and later declaring their coexistence universal.

## Log

- 2026-08-09 — dependency-closed paper proof recorded after field ontology reset.
- 2026-08-09 — finite dependent slot products, transitivity, empty/full phase classification, and
  constant-invariant theorem formalized in Lean.
