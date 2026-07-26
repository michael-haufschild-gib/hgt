# Prime-local diagonal reciprocity for the finite-adele character

- **ID:** `field-one-finite-adele-diagonal-reciprocity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-spherical-weyl-multiplier-bridge`
- **Statement:** at every finite place \(v\), the canonical finite-adele character evaluates
  diagonal \(m/p_v^n\) as \(m/p_v^n\bmod\mathbb Z\); paired with the negative real character,
  it vanishes on the diagonal copy of \(\mathbb Z[1/p_v]\).

## Goal

Prove the diagonal product law actually required by each fixed-prime spherical perfection stage,
without importing the general adelic product formula as an assumption.

## Theorem

Let \(v\) be a height-one prime of \(\mathbb Z\), with associated rational prime \(p_v\). For
\(m\in\mathbb Z\) and \(n\ge0\), put \(q=m/p_v^n\). Then:

1. At \(v\), the local standard character sends \(q\) to \(q\bmod\mathbb Z\).
2. At every \(w\ne v\), \(q\) belongs to \(\mathbb Z_w\), so the local character vanishes.
3. Therefore
   \[
     \psi_f(\Delta_f q)=q\pmod{\mathbb Z}.
   \]
4. For
   \[
     \psi_S(x_\infty,x_f)=-x_\infty+\psi_f(x_f)\pmod{\mathbb Z},
   \]
   one has \(\psi_S(q,\Delta_f q)=0\).

## Proof

The all-depth local normalization gives
\(\psi_v(p_v^{-n})=1/p_v^n\); additivity gives the factor \(m\). If \(w\ne v\), the distinct
prime \(p_v\) has \(p_w\)-adic norm \(1\). Its inverse powers are therefore integral at \(w\),
as are integer numerators. Hence all off-\(v\) local terms vanish. The finite sum reduces to its
single \(v\)-term. The real term has the opposite sign, so cancellation is exact.

## Hostile audit and exact boundary

- **No product-formula assumption:** off-place integrality and the one-place normalization are
  proved directly.
- **Scope:** the theorem covers all \(m/p_v^n\), hence all of \(\mathbb Z[1/p_v]\), exactly the
  exponent group of a fixed-\(p\) perfection stage.
- **Still open:** one simultaneous theorem for arbitrary rational denominators, finite-real
  Bruhat tensor assembly, semilocal faithfulness, and \(L^2\) unitarity.

## Gates

- [x] 0 → 1: local, diagonal, and semilocal character types identified
- [x] 1 → 2: dependency-closed norm/integrality/single-support proof
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleDiagonalReciprocity`
- **Core theorems:**
  `fieldOnePadicStandardUnitAddCircleCharacter_int_div_pow`,
  `fieldOneFiniteAdeleLocalUnitCharacter_algebraMap_int_div_pow`,
  `fieldOnePadic_int_div_primePow_mem_integers_of_ne`,
  `fieldOneFiniteAdele_algebraMap_int_div_pow_mem_integers_of_ne`,
  `fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_int_div_pow`,
  `fieldOneSemilocalStandardUnitAddCircleCharacter_diagonal_int_div_pow`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` on every listed theorem
  reports only `propext`, `Classical.choice`, and `Quot.sound`. Final targeted `lake build`
  remains reserved for final audit.

## Log

- 2026-07-26 — Proved fixed-prime diagonal reciprocity directly from local normalization and
  distinct-prime integrality, without computation or any RH premise.
