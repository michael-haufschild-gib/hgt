---
name: binomial-multiplicity-determinantal-step
---

# Critical binomial multiplicity: the TRUE frontier (corrected 2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/projective-horizon/projective-horizon-critical-binomial-multiplicity.md`

**An earlier version of this memory described a frontier the corpus had already passed, and led to
a duplicate module (`CriticalTailFibreCount.lean`, since deleted).  Read the modules below before
writing anything.**

## What the corpus already has — the card's whole Lean cluster

Dependency order:

- `ProjectiveHorizonPureTailFiber` — pure critical case: exact factorization, separability of the
  cyclic polynomial, binomial cardinality of the occupation labels.
- `MonomialTailFibreCount` — divisor counts (`nat_card_monic_divisors_X_pow_sub_C`,
  `nat_card_monic_divisors_monomialTail`), truncation vacuity at the critical degrees.
- `MonomialTailFibreEquiv` — `nat_card_criticalFibre_monomialTail`: the **fibre itself** is counted
  by the critical multiplicity at monomial tails.
- `TruncatedCompatibilityFibre` — the general fibre: `criticalFibre` (a Type), `criticalFibreSwap`,
  `criticalLowProduct_comm`, `coeff_zero_add_ne_zero_of_dvd`, `criticalLowProduct_right_unique`,
  `criticalFibre_fst_injective`, `dvd_criticalLowProduct_sub_one_iff_mul_sub_one`.
- `InverseJetNumerator` — `invNumerator`, its recursion, and `natDegree_invNumerator_le`.
- `OneDeepFibreBound` — depth one **completely done for arbitrary tails**:
  `oneDeepEquation`, `degree_oneDeepEquation`, `isRoot_oneDeepEquation`, `fibreOfRoot`,
  `nat_card_criticalFibre_one_eq`, `nat_card_criticalFibre_one_eq_horizon`,
  **`nat_card_criticalFibre_one_eq_multiplicity`** and its `snd` mirror.
  Plus the general-depth machinery: `fibre_eval_invNumerator`, `fibre_system`, `fibreOfSystem`,
  `dvd_invPoly_compat_general`, and
  **`nat_card_criticalFibre_eq_solutions`**.
- `CriticalHorizonRadicalRegime` — the radical-regime classification `(18)`.

## The actual frontier

`nat_card_criticalFibre_eq_solutions` reduces the card's `(2)` to a **count of solutions of an
explicit square polynomial system**.  With `a = (A+U).coeff 0` and `u i = (A+U).coeff i`, the
solutions are the `A` of degree `< m`, invertible at the origin, with

```text
a ^ (k+1) * V.coeff k = (invNumerator u k).eval a      for  n ≤ k < m + n.
```

That is `m` equations in the `m` unknown coefficients of `A`.  The card's claim is that a generic
observation has exactly `C(m+n, m)` solutions.  **This — and only this — is what remains.**

Depth one is the case `m = 1`, already done: one equation in one unknown, degree `1 + n`.

## What that means for the next attempt

The remaining statement is a Bezout-type count for the above system.  Two routes, both needing
infrastructure mathlib lacks:

1. multiprojective Bezout for `(1,1)` forms on `P^m x P^n` (the bihomogenised system);
2. the degree of the rank-drop locus of an `(m+n) x (n+1)` matrix of linear forms
   (Giambelli–Thom–Porteous).

The Chow-ring side of the number is already formalized as
`criticalHorizonMultiplicity_eq_chowCoefficient`.

## Process rule that would have prevented the duplication

Before starting a *direction* on this card, list the modules whose names contain the card's
vocabulary (`fibre`, `critical`, `tail`, `truncat`, `deep`, `multiplicit`) **and read their
docstrings**, not just grep for a lemma name at the moment of writing it.  The single command that
finds the cluster:

```
grep -rl "TruncatedCompatibilityFibre\|OneDeepFibreBound\|MonomialTailFibreCount" GaloisForLFunctions/HTGeometry/*.lean
```


## 2026-08-06 (later): the mathlib gap is now identified exactly

The remaining case is `m, n ≥ 2` with truncations strictly between the critical degrees and the
horizon.  Everything else on the card is proved:

- `m = 0`, `n = 0`: outright, arbitrary tails (`existsUnique_fibre_depth_zero` and its mirror in
  the deleted-then-rebuilt work; corpus has the fibre framework).
- `m = 1`, `n = 1`: arbitrary tails.  Corpus `nat_card_criticalFibre_one_eq_multiplicity` assumed a
  monomial reciprocal tail; `nat_card_criticalFibre_one_eq_multiplicity_of_tail` in
  `CriticalDegreeTailFibre.lean` removes that, since at depth one the system reads only `V.coeff n`.
- all `(m, n)`, truncated tails of exactly the critical degrees with separable target:
  `nat_card_criticalFibre_criticalTails`, and `nat_card_criticalFibre_of_truncation` for tails of
  any length.

### CORRECTION (same day): the criterion IS in mathlib

**`Polynomial.resultant_eq_zero_iff` exists** — `Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`
line 908:

```text
f.resultant g = 0 ↔ (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g       (over a field)
```

The corpus already uses it: `separable_of_resultant_ne` in `U0/U0PhiCard.lean`.  The paragraph
below claiming it absent was produced by a grep whose output was truncated at `head -20`, cutting
off everything past line ~344 of a 900-line file.  **Third truncation error of this kind — when
scanning an unfamiliar mathlib file for an API, grep for the concept
(`grep -rn "resultant_eq_zero" Mathlib/`), never list declarations with a head limit.**

So no resultant infrastructure needs building.  Steps 1–3 below are unnecessary.

### (superseded) What was thought to block the rest

- present: `Polynomial.sylvester f g m n` (a `Matrix (Fin (m+n)) (Fin (m+n)) R`),
  `Polynomial.resultant f g m n = (sylvester f g m n).det`, `resultant_map_map`,
  `resultant_comm`, and a family of small computations
  (`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`).
- **absent**: any statement of the form `resultant f g = 0 ↔ f and g have a common factor`, or
  the Sylvester map's meaning.

### The build, in order

1. `sylvester_mulVec` — the matrix–vector product of `sylvester f g m n` against the concatenated
   coefficient vectors of `u` (degree `< m`) and `v` (degree `< n`) is the coefficient vector of
   `u * g + v * f`.  This is the missing computational core; the column convention is
   `Fin.addCases`, first `m` columns carrying shifted `g`, last `n` carrying shifted `f`.
2. `resultant_eq_zero_iff_exists` — combine 1 with `Matrix.exists_mulVec_eq_zero_iff` (over a
   field): `resultant = 0` iff there are `(u, v) ≠ 0` with those degree bounds and `u g + v f = 0`.
3. Over an algebraically closed field, that is a common root.

Note `ker_ne_bot_iff_det_eq_zero` (a linear map between spaces of equal finite dimension is
degenerate iff its matrix determinant vanishes) was proved during this session and lost with the
deleted module; it is a two-line consequence of `Matrix.exists_mulVec_eq_zero_iff` and worth
rebuilding if step 2 needs it in map form rather than matrix form.
