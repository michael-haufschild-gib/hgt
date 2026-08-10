# Completion homology and serial exactness mechanics

- **ID:** ULF-CHM-PROGRAM
- **Stage:** 1-in-progress
- **Type:** MECHANISM PROGRAMME
- **Statement:** Enlarging constitutive layers by completion creates two independent serial
  homology defects: extra source preimages and unattained target limits.

## Mechanism question

Given a serial law-producing mechanism

\[
K\xrightarrow{T}A
\]

with an inner discarded layer \(R\subseteq K\), a composite discarded layer
\(P\subseteq A\), and an outer discarded layer \(Q\subseteq A\), what laws determine whether
the algebraic primary--secondary exact sequence survives enlargement of those layers?

Required containments are

\[
R\subseteq T^{-1}P,\qquad P\subseteq Q,\qquad \operatorname{im}T\subseteq Q.
\]

They produce a canonical complex

\[
K/R\longrightarrow A/P\longrightarrow A/Q.
\]

The live hypothesis is that its failure is not one scalar defect. It has two different homology
organs.

## Candidate laws

1. **Source-preimage homology**

   \[
   H_{\mathrm{src}}=T^{-1}P/R.
   \]

   Nonzero classes were distinct before completion but are erased after composite transport.

2. **Target-attainment homology**

   \[
   H_{\mathrm{tgt}}=Q/(\operatorname{im}T+P).
   \]

   Nonzero classes are outer-limit residuals not attained by any actual carrier modulo the
   composite layer.

3. **Two-defect exactness law.** Serial exactness survives iff both homology groups vanish.

4. **Topological specialization.** For continuous composable carriers \(S,T\), set

   \[
   R=\overline{\operatorname{im}S+\ker T},\quad
   P=\overline{\operatorname{im}(TS)},\quad
   Q=\overline{\operatorname{im}T}.
   \]

   Exactness then becomes two independent closure-exchange identities.

## Why this matters

One-stage language such as “nonclosed range” conflates two mechanisms. A secondary class can die
because its image becomes approximable, or a new primary-kernel class can appear only at the
target closure. These have opposite variance and different repairs. First requires stricter source
admission; second requires completion of carrier attainment.

## Next gate

Classify sufficient hypotheses—strict morphisms, open maps onto closed range, quotient maps, bornological
exactness—forcing both homology groups to vanish. Then determine how the two groups compose over
three or more carrier stages.

## Log

- 2026-08-10 — opened as forced successor to ULF-PSB-1; route names excluded.
- 2026-08-10 — abstract two-defect theorem, topological specialization, converse, independence
  cells, and one genuine compact-dense target-defect realization closed as ULF-CHM-1.
