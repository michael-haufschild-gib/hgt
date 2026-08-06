# Fraction-field transport, first half (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **46**.
Continues [[research/conductor_adjoin_top_2026_08_06]].

## `AdjoinFractionTransport.lean`

- **`map_mem_adjoin_of_mem_adjoin`** — `b ∈ Algebra.adjoin A {x}` ⟹
  `algebraMap B L b ∈ Algebra.adjoin K {algebraMap B L x}`.  By `Algebra.adjoin_induction`; the
  `algebraMap` case is `IsScalarTower.algebraMap_apply` twice (down through `B`, up through `K`).
- **`range_le_adjoin_of_adjoin_eq_top`** — hence the image of the whole ring is contained in the
  fraction-field adjoin.

## What remains for the full transport

`Algebra.adjoin K {x_L}` is a **field** (the generator is integral over `K`, so the subalgebra is a
finite-dimensional domain over a field).  A field containing the image of `B` contains
`Frac B = L`, so the adjoin is `⊤`.  Only this field step is missing.

## mathlib-version note (v4.32.2 in this repo)

**`Mathlib.FieldTheory.Adjoin` does not exist** — the module was split; the relevant material is
under `Mathlib/FieldTheory/IntermediateField/Adjoin/`.  Importing the old path fails at *link*
time with a bare "object file … does not exist", not at elaboration, which is easy to misread as a
stale build.

## Lean note

Calling a lemma whose `A`/`K` appear only in hypotheses leaves `IsScalarTower ?m K L` stuck; pass
`(A := A) (K := K)` explicitly.

## Remaining for Theorem A

1. Field step ⇒ full transport ⇒ `differentIdeal A B = (maximalIdeal B)^(e−1)`.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
