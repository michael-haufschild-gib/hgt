# Canonical standard character of the rational finite adeles

- **ID:** `field-one-finite-adele-weyl-character`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-spherical-weyl-multiplier-bridge`
- **Statement:** the standard local characters of all rational \(p\)-adic completions assemble
  canonically over the finite restricted product into a nontrivial locally constant additive
  character of \(\mathbb A_f\), and hence into a finite-adele Weyl-multiplier action.

## Goal

Close restricted-product character assembly without replacing the finite adeles by an
unrestricted product and without assuming a global product formula, trace formula, positivity,
zero data, or RH.

## Theorem

Let
\[
  \mathbb A_f=\prod_v'(\mathbb Q_v,\mathbb Z_v)
\]
and let \(\psi_v:\mathbb Q_v\to\mathbb R/\mathbb Z\) be the standard local character with
kernel \(\mathbb Z_v\). For \(x\in\mathbb A_f\), set
\[
  \psi_f(x)=\sum_v^{\mathrm{finite}}\psi_v(x_v).
\]

1. The family \(v\mapsto\psi_v(x_v)\) has finite support.
2. \(\psi_f:\mathbb A_f\to\mathbb R/\mathbb Z\) is an additive homomorphism.
3. It vanishes on the open subgroup \(\prod_v\mathbb Z_v\), hence is locally constant.
4. A one-place adele with coordinate \(p_v^{-1}\) has nonzero image, so \(\psi_f\) is
   nontrivial.
5. Its complex unit-circle embedding defines a nontrivial locally constant additive
   character.
6. Multiplication by \(x\mapsto\psi_f(rx)\) preserves compactly supported locally constant
   functions on \(\mathbb A_f\) and satisfies \(W_rW_s=W_{r+s}\).

## Proof

Restricted-product membership says \(x_v\in\mathbb Z_v\) for all but finitely many \(v\).
The exact local kernel therefore makes \(\psi_v(x_v)=0\) eventually, proving finite support.
Two adeles have finite local-character support; distributivity of `finsum` then proves
additivity. The all-integral restricted product is open because every local valuation subring
is open. It lies in the global kernel, so cosets give neighborhoods of constancy.

For nontriviality, choose any finite place \(v\), transport \(p_v^{-1}\) through the canonical
completion equivalence, and form the adele supported only at \(v\). Its global finite sum is
the single nonzero local value. The multiplier law is the generic locally constant character
law.

## Hostile audit and exact boundary

- **Restricted-product audit:** the sum is finite because of eventual integrality; no
  convergence claim or infinite-product rearrangement is hidden.
- **Canonicity audit:** local characters come from compatible denominator stages, and the
  global operation is `finsum`; no arbitrary extension remains.
- **Kernel audit:** the all-integral subgroup is proved to lie in the global kernel. Equality
  is neither true nor claimed, because values at distinct places can cancel.
- **Still open:** evaluation on the diagonal copy of \(\mathbb Q\), cancellation against the
  archimedean character, semilocal tensor assembly/faithfulness, and \(L^2\) unitarity.

## Gates

- [x] 0 → 1: restricted product, local character, and finite-sum types identified
- [x] 1 → 2: dependency-closed finite-support/additivity/local-constancy proof
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleWeylCharacter`
- **Core theorems:**
  `fieldOneFiniteAdeleLocalUnitCharacter_vanishes_on_integers`,
  `fieldOneFiniteAdeleLocalUnitCharacter_hasFiniteSupport`,
  `fieldOneFiniteAdeleStandardUnitAddCircleRaw_add`,
  `fieldOneFiniteAdeleIntegralAddSubgroup_isOpen`,
  `fieldOneFiniteAdeleStandardUnitAddCircleCharacter_isLocallyConstant`,
  `fieldOneFiniteAdeleStandardUnitAddCircleCharacter_single`,
  `fieldOneFiniteAdeleStandardUnitAddCircleCharacter_ne_zero`,
  `fieldOneFiniteAdeleStandardAddChar_ne_one`,
  `fieldOneFiniteAdeleStandardWeylMultiplier_add`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` on all listed theorem
  families reports only `propext`, `Classical.choice`, and `Quot.sound`. Final targeted
  `lake build` remains reserved for final audit.

## Log

- 2026-07-26 — Assembled all finite places through symbolic finite support and `finsum`.
  Formalized without computation and without any RH premise.
