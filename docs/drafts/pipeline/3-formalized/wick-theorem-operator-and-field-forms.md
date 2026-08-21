# Wick's theorem: operator, field, and vacuum forms

- **ID:** wick-theorem
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** classical (Wick 1950); statement and induction as in the standard QFT presentation
- **Statement:** An ordered product of creation and annihilation operators, or of free fields, equals
  the normal-ordered product plus the sum over all partial contractions; the vacuum expectation
  keeps only the complete pairings.

## Goal

A Lean-certified, unconditional Wick's theorem usable wherever a quasi-free/Gaussian expansion is
needed. The corpus already contained the *scalar* Isserlis recursion
(`HTGeometry.QuasiFreeWickExpansion.wickMoment`) but nothing that derives it: no normal ordering, no
canonical commutation relations, no operator expansion. This card supplies the derivation and the
model in which the hypotheses are realised.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (the induction of the physics literature, made exact)
- [x] 3      formalized: Lean, `lake env lean` green on every module, axioms
      `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 → 4  publication-ready

## What is proved

Modules, in dependency order, all under `GaloisForLFunctions.HTGeometry`:

1. `ListPositionSum` — `positionSum l f = ∑ k, f l[k] (l.eraseIdx k)`; head/tail recursion,
   linearity, and the **exchange law** `positionSum_swap`: choosing a position, deleting it and
   choosing a second position gives a double sum symmetric in the two chosen entries. This is the
   combinatorial heart; the proof is an induction in which the two leading terms of the two sides
   are each other's second terms, so no bijection of ordered pairs is ever constructed.
2. `CompletePairing` — `completePairing c l`, the sum over the perfect matchings of a word.
3. `PairingExpansion` — `pairingExpand c φ l`, the sum over *partial* pairings, with linearity,
   transport along linear maps and along left multiplication, the exchange law
   `pairingExpand_positionSum`, and the collapse `pairingExpand_eq_completePairing` when `φ` is
   normalised on the empty word and vanishes elsewhere.
4. `WickNormalOrdering` — `WickSystem K A ι` (canonical commutation relations), modes,
   `nord` (normal ordering by filtering creations to the left), and the one-step law
   `op_mul_nord : op u * nord l = nord (u :: l) + ∑ₖ contract u l[k] • nord (l.eraseIdx k)`.
5. `WickTheorem` — `prod_op_eq_pairingExpand_nord`:
   `(l.map op).prod = pairingExpand contract nord l`.
6. `WickVacuumExpectation` — `WickVacuum`, and `vacuum_prod_op`:
   `ω ((l.map op).prod) = completePairing contract l`.
7. `WickFieldTheorem` — fields `φ x = cre x + ann x`, the two-term normal-ordering recursion
   `nordField (x :: l) = cre x * nordField l + nordField l * ann x`,
   `prod_field_eq_pairingExpand_nordField`, `ω_field_mul_field : ω (φ x φ y) = κ x y`, and
   `vacuum_prod_field : ω ((l.map field).prod) = completePairing κ l`.
8. `WickFockModel` — the polynomial Fock space `MvPolynomial ι K` with `cre i = Xᵢ ·`,
   `ann i = ∂ᵢ`, vacuum `T ↦ constantCoeff (T 1)`: a concrete `WickSystem` and `WickVacuum`, so the
   structures are not vacuous, plus the specialised statements
   `bosonicFock_vacuum_prod_op` and `bosonicFock_vacuum_prod_field`.

## Approach

The induction is the physics one. The only real content beyond bookkeeping is that the contraction
terms produced by pushing one operator through a normal-ordered word are indexed by *a partial
pairing together with a marked free letter*, while the recursion defining the expansion of the
longer word indexes them by *a letter together with a partial pairing of the rest*. Identifying
those two enumerations is the exchange law.

## Open continuations

- Identify `completePairing` with an explicit sum over fixed-point-free involutions.
- Bridge `completePairing` to the pre-existing `QuasiFreeWickExpansion.wickMoment`.
- The probabilistic form (Isserlis): moments of a Gaussian measure as a complete-pairing sum of
  covariances.
- The fermionic (CAR) form, with the sign of the sorting permutation.

## Log
- 2026-08-21 — created directly at stage 3; all eight modules compile, axiom audit clean.
