# An event involution canonically separates self-law from seam transfer

- **ID:** `involution-actuality-colligation-grading`
- **Stage:** 3-formalized
- **Type:** EXACT ALGEBRAIC BRIDGE / EVENT-SELECTED COLLIGATION GRADING
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [AXIOM-AUDITED]`
  `[REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/actuality-conservation-boundary-colligation-law.md`
- **Formal target:** `GaloisForLFunctions.HTGeometry.EventInvolutionComplement`

## Statement

Let \(V\) be a finite-dimensional complex carrier, let \(A\in\operatorname{End}(V)\) satisfy
\[
A^2=1,
\]
and define its continuation and record projections
\[
P=\frac{1+A}{2},\qquad Q=\frac{1-A}{2}.
\]
For every law \(T\in\operatorname{End}(V)\), define the actuality-even and actuality-odd parts
\[
T_{\mathrm{even}}=\frac{T+ATA}{2},\qquad
T_{\mathrm{odd}}=\frac{T-ATA}{2}.                       \tag{1}
\]
Then:

1. \(T=T_{\mathrm{even}}+T_{\mathrm{odd}}\);
2. \(AT_{\mathrm{even}}A=T_{\mathrm{even}}\);
3. \(AT_{\mathrm{odd}}A=-T_{\mathrm{odd}}\);
4. \(T_{\mathrm{odd}}=0\) if and only if \(TA=AT\);
5. the full event-selected block decomposition is
   \[
   T=PTP+PTQ+QTP+QTQ;                                   \tag{2}
   \]
6. the even part is exactly the two self-blocks
   \[
   T_{\mathrm{even}}=PTP+QTQ;                            \tag{3}
   \]
7. the odd part is exactly the reciprocal transfer blocks
   \[
   T_{\mathrm{odd}}=PTQ+QTP.                             \tag{4}
   \]

Thus a source-selected involution canonically determines the minimum colligation data of every
law on the carrier:

```text
continuation self-law PTP;
record self-law       QTQ;
outgoing transfer     PTQ;
incoming transfer     QTP.
```

No independently chosen direct-sum decomposition is needed after \(A\) is supplied.

## Proof

Since \(P+Q=1\),
\[
T=(P+Q)T(P+Q)=PTP+PTQ+QTP+QTQ,
\]
which proves `(2)`.

Direct expansion gives
\[
\begin{aligned}
PTP+QTQ
&=\frac14\bigl((1+A)T(1+A)+(1-A)T(1-A)\bigr)\\
&=\frac12(T+ATA)
=T_{\mathrm{even}},
\end{aligned}
\]
proving `(3)`. Likewise,
\[
\begin{aligned}
PTQ+QTP
&=\frac14\bigl((1+A)T(1-A)+(1-A)T(1+A)\bigr)\\
&=\frac12(T-ATA)
=T_{\mathrm{odd}},
\end{aligned}
\]
proving `(4)`. Adding the two formulas proves item 1.

Using \(A^2=1\),
\[
A T_{\mathrm{even}} A
=\frac12(ATA+A^2TA^2)
=T_{\mathrm{even}},
\]
and
\[
A T_{\mathrm{odd}} A
=\frac12(ATA-A^2TA^2)
=-T_{\mathrm{odd}},
\]
proving items 2 and 3.

If \(TA=AT\), then \(ATA=T A^2=T\), so \(T_{\mathrm{odd}}=0\). Conversely,
\(T_{\mathrm{odd}}=0\) gives \(T=ATA\); multiplying on the right by \(A\) yields \(TA=AT\).
This proves item 4.

## Scientific boundary

This is elementary \(\mathbb Z_2\)-graded linear algebra and not new mathematics. It does not prove:

- that a physical event supplies an involution;
- that \(Q\) is a spacetime boundary;
- that \(QTQ\) is matter;
- that \(PTQ+QTP\) is force;
- that variation of \(A\) is gravity; or
- that the trace-two ten-dimensional event model is realized in nature.

Its exact value is removal of one arbitrariness from the conjectural physics. Once a
source-selected event involution exists, “self” and “transfer” are no longer chosen block labels:
they are the canonical even and odd sectors of that event.

## Lean declarations and verification

`GaloisForLFunctions.HTGeometry.EventInvolutionComplement` now contains:

```text
involutionEvenPart
involutionOddPart
involutionEven_add_odd
involutionEven_conjugate
involutionOdd_conjugate
involutionOdd_eq_zero_iff_commute
involution_full_block_decomposition
involutionEven_eq_self_blocks
involutionOdd_eq_transfer_blocks
```

Verification:

- scratch proof against the pinned toolchain: passed;
- direct
  `lake env lean GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean`: passed;
- final
  `lake build GaloisForLFunctions.HTGeometry.EventInvolutionComplement`: passed
  (`2947/2947`);
- `scripts/formal_tools.py lint`: passed;
- axiom audit for all seven theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`;
- no stale Lean or Lake process remained.

## Gates

- [x] theorem dependency-closed
- [x] complete paper proof
- [x] scientific overclaim boundary stated
- [x] Lean formalization
- [x] direct Lean verification
- [x] module build
- [x] formal lint and axiom audit
