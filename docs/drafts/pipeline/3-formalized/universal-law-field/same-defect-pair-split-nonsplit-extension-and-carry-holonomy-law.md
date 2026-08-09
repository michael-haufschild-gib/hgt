# Same defect pair, split/nonsplit extension, and carry holonomy law

- **ID:** ULF-DEFECT-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Source:** hostile attack on ordered-defect reconstruction
- **Statement:** Identical kernel and cokernel objects support split and nonsplit law events distinguished by carry and lifted recurrence holonomy.
- **Status:** [LEAN-CERTIFIED] [FALSIFIES PAIR COMPLETENESS] [EXTENSION SURVIVOR]
  [CLASSICAL EXT PARENT] [NO PROJECT AXIOMS]

## 1. Two events with identical endpoints

Let \(K=C=\mathbb Z/2\). Define the split event

\[
0\longrightarrow K
\xrightarrow{i_{\mathrm{sp}}}E_{\mathrm{sp}}=(\mathbb Z/2)^2
\xrightarrow{q_{\mathrm{sp}}}C
\longrightarrow0,
\tag{1}
\]

where \(i_{\mathrm{sp}}(a)=(a,0)\) and \(q_{\mathrm{sp}}(a,b)=b\). Define the nonsplit event

\[
0\longrightarrow K
\xrightarrow{i_{\mathrm{ns}}}E_{\mathrm{ns}}=\mathbb Z/4
\xrightarrow{q_{\mathrm{ns}}}C
\longrightarrow0,
\tag{2}
\]

where \(i_{\mathrm{ns}}(a)=2a\) and \(q_{\mathrm{ns}}(x)=x\bmod2\).

Both have the same ordered defect pair \((K,C)\), and both middle groups have cardinality four.

## 2. Theorem

1. Event (1) splits as a group extension.
2. Event (2) does not split.
3. With the canonical sections

   \[
   s_{\mathrm{sp}}(b)=(0,b),
   \qquad
   s_{\mathrm{ns}}(0)=0,
   \quad
   s_{\mathrm{ns}}(1)=1,
   \]

   the section carry

   \[
   \kappa(a,b)=i^{-1}\bigl(s(a)+s(b)-s(a+b)\bigr)
   \tag{3}
   \]

   is identically zero for (1), while for (2)

   \[
   \kappa_{\mathrm{ns}}(1,1)=1.
   \tag{4}
   \]

4. The base history \(b(n)=n\bmod2\) has period two in both events. Its canonical lift in the
   split event can close after two steps, while the lift \(a(n)=n\bmod4\) in the nonsplit event
   satisfies

   \[
   a(n+2)=a(n)+2,
   \tag{5}
   \]

   giving nonzero kernel holonomy after one base period and closure only after two base periods.

### Proof

The map \(s_{\mathrm{sp}}\) is a homomorphism and
\(q_{\mathrm{sp}}s_{\mathrm{sp}}=\operatorname{id}\), so (1) splits. If (2) split, the nonzero
element of \(\mathbb Z/2\), which has order two, would have a section lift of order dividing two.
Every odd element of \(\mathbb Z/4\) maps to the nonzero quotient element and has order four. This
is impossible, so (2) is nonsplit.

For the split section, additivity makes (3) zero. In the nonsplit event,

\[
s_{\mathrm{ns}}(1)+s_{\mathrm{ns}}(1)-s_{\mathrm{ns}}(0)=2=i_{\mathrm{ns}}(1),
\]

which proves (4). Periodicity of \(b\) is immediate. Equation (5) holds modulo four and its
increment \(2=i_{\mathrm{ns}}(1)\) is the nonzero kernel element. QED.

## 3. Killing theorem and positive survivor

**Killed conjecture:** ordered kernel--cokernel defect and positive size reconstruct the erased law
event.

**Exact why:** extension classes vary while endpoints and sizes remain fixed.

**Strongest survivor:** retain the full extension/Yoneda class, or equivalently a carry cocycle up to
coboundary, before taking endpoint pairs or stable differences. Lifted recurrence holonomy is a
direct observable of this extension class.

## 4. Relation to existing corpus and external mathematics

The finite mechanism is classical \(\operatorname{Ext}^1(\mathbb Z/2,\mathbb Z/2)\) and truncated
Witt carry. The HGT corpus already contains its ramification/Boolean realization in
`constraint-frame-relativity/ramification-witt-carry-boolean-hardcore-recurrence-law.md`.
The field-level delta is the exact placement in the failure chain

\[
\text{stable index}
\longleftarrow
\text{ordered defect pair}
\longleftarrow
\text{extension/carry law}.
\]

No external novelty claim is made.

## 5. Sharp scope

- An extension class still does not determine metric cost, analytic completion, or framed torsion.
- The canonical carry representative depends on section; its cohomology/extension class does not.
- Finite holonomy is not physical curvature or RH leverage by itself.

## 6. Lean certificate

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveExtensionCarry`.

The formalization proves, without theorem premises:

- injectivity, surjectivity, and pointwise exactness of both events;
- existence of the split additive section and nonexistence of any nonsplit additive section;
- equality of both middle cardinalities with four;
- zero split carry and nonzero canonical binary carry at `(1,1)`;
- period-two base and split histories;
- nonzero kernel increment after one period in the nonsplit lift and closure after two periods;
- one bundled same-defect/carry/holonomy theorem.

Targeted source check, module build, and universal-law umbrella build passed. `#print axioms` for the
exactness, nonsplitting, and bundled capstone reports only `propext`, `Classical.choice`, and
`Quot.sound`; no project axiom or unresolved proof premise is used.

## Log

- 2026-08-09 — ordered-pair completeness falsified; full extension survivor recorded.
- 2026-08-09 — exact split/nonsplit, carry, cardinality, and lifted-holonomy theorem closed in Lean;
  promoted to Stage 3.
