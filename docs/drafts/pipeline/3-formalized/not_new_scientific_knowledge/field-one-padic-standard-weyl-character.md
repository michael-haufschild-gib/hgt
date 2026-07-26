# Canonical all-depth standard Weyl character at every finite place

- **ID:** `field-one-padic-standard-weyl-character`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-spherical-weyl-multiplier-bridge`
- **Supersedes locally:** the noncanonical depth-one extension in
  `field-one-padic-weyl-character`
- **Statement:** for every prime \(p\), the compatible reductions on
  \(p^{-n}\mathbb Z_p\) assemble into the canonical standard additive character of
  \(\mathbb Q_p\), with kernel exactly \(\mathbb Z_p\), prescribed value at every
  \(p^{-n}\), and a locally constant Weyl-multiplier action.

## Goal

Remove the arbitrary injective-extension choice from the finite-place part of the
spherical-to-analytic bridge. No trace formula, positivity, zero data, or RH premise enters.

## Theorem

For \(n\ge0\), define
\[
  D_n=p^{-n}\mathbb Z_p
      =\{x\in\mathbb Q_p:\lVert p^n x\rVert_p\le1\}
\]
and
\[
  \psi_{p,n}(x)
    =\frac{(p^n x)\bmod p^n}{p^n}\pmod{\mathbb Z}
    \in\mathbb R/\mathbb Z.
\]

1. If \(m\le n\), then \(D_m\subseteq D_n\) and
   \(\psi_{p,n}|_{D_m}=\psi_{p,m}\).
2. Every \(x\in\mathbb Q_p\) belongs to some \(D_n\).
3. The compatible family therefore defines an additive character
   \[
     \psi_p:\mathbb Q_p\longrightarrow\mathbb R/\mathbb Z.
   \]
4. For every \(n\),
   \[
     \psi_p(p^{-n})=1/p^n\pmod{\mathbb Z}.
   \]
5. Its kernel is exactly \(\mathbb Z_p\). Hence it is locally constant and nontrivial.
6. After embedding \(\mathbb R/\mathbb Z\) in the complex unit circle, multiplication by
   \(x\mapsto\psi_p(rx)\) preserves compactly supported locally constant functions and obeys
   \(W_rW_s=W_{r+s}\).

## Proof

For \(m\le n\), multiplication by \(p^{n-m}\) identifies the reduction of \(p^n x\) modulo
\(p^n\) with the reduction of \(p^m x\) modulo \(p^m\). Dividing by the respective moduli in
\(\mathbb Q/\mathbb Z\) gives stage compatibility. The valuation of a nonzero \(p\)-adic
number supplies a finite \(n\) with \(p^n x\in\mathbb Z_p\); zero belongs to every stage.
Compatibility makes the chosen-stage value independent of the choice.

Additivity is checked after placing two inputs in a common maximum stage. At \(p^{-n}\), the
integral numerator is \(1\), giving the normalization. If \(\psi_p(x)=0\), write
\(u=p^n x\in\mathbb Z_p\). Vanishing of its reduction modulo \(p^n\) says
\(u\in p^n\mathbb Z_p\), so cancellation in \(\mathbb Q_p\) gives \(x\in\mathbb Z_p\).
The converse is the depth-zero case. Since the exact kernel is open, the character is locally
constant. The Weyl laws follow from additivity.

## Hostile audit and exact boundary

- **Choice audit:** a denominator depth is selected internally, but stage compatibility proves
  the output independent of that selection. No arbitrary extension of characters remains.
- **Conductor audit:** the theorem proves the exact kernel \(\mathbb Z_p\), not merely that the
  character vanishes there.
- **Normalization audit:** every principal depth \(p^{-n}\) is covered, not only \(p^{-1}\).
- **Still open:** assembly over the finite restricted product, compatibility with diagonal
  rationals and the archimedean factor, semilocal tensor faithfulness, and finite-place
  \(L^2\) unitarity.

## Gates

- [x] 0 → 1: denominator-stage and target types identified
- [x] 1 → 2: dependency-closed compatibility, kernel, and normalization proof
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration

## Lean certificate

- **Module:**
  `GaloisForLFunctions.RHTower.FieldOnePadicStandardWeylCharacter`
- **Core theorems:**
  `zmodPow_toAddCircle_mul_transition`,
  `fieldOnePadicDenominatorStageCharacter_transition`,
  `fieldOnePadic_exists_denominatorStage`,
  `fieldOnePadicStandardUnitAddCircleCharacter_inv_pow`,
  `fieldOnePadicStandardUnitAddCircleCharacter_eq_zero_iff`,
  `fieldOnePadicStandardUnitAddCircleCharacter_isLocallyConstant`,
  `fieldOnePadicStandardAddChar_ne_one`,
  `fieldOnePadicStandardWeylMultiplier_add`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` on all listed theorem
  families reports only `propext`, `Classical.choice`, and `Quot.sound`. Final targeted
  `lake build` remains reserved for final audit.

## Log

- 2026-07-26 — Replaced the noncanonical depth-one extension with the compatible all-depth
  standard character. Formalized symbolically, without computation or any RH premise.
