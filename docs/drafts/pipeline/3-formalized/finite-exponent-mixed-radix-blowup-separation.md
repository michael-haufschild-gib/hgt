# Finite-exponent mixed-radix blow-up separation

- **ID:** finite-exponent-mixed-radix-blowup-separation
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean), `[BRIDGE]` / `[REDISCOVERED]`
- **Formalized companion:** `finite-exponent-mixed-radix-blowup-separation-formalized.md`
- **Source:** `prop-interface-discharge-audit` full-rank residue
- **Statement:** For every injective finite family
  `e : κ → (Fin n →₀ ℕ)`, there is `d : Fin n → ℕ` such that
  `a ↦ ∑ k, e a k * d k` is injective.

## Goal

Supply the missing connector between the finite monomial boxes in the five expanded-full-rank
interfaces and `MultiBlowUpData`: a finite exponent family can always be separated by one integral
blow-up-rate vector. Combined with the multi-blow-up sampling theorem, this gives an unconditional
full-rank realization for every injectively indexed finite monomial box.

## Gates

- [x] 0 → 1 in-progress: exact collision obstruction and survivor isolated
- [x] 1 → 2 fully-proven: dependency-closed mixed-radix proof below
- [x] 2 → 3 formalized: exact Lean theorem and axiom audit — see
  `finite-exponent-mixed-radix-blowup-separation-formalized.md`
- [ ] 3 → 4 publication-ready: not applicable; classical encoding bridge

## Frontier and hostile audit

- `[CORPUS]` `not_injective_mulVec_of_expandedMonomialFamily_eq` proves equal columns make every
  sampling packet singular. Thus arbitrary exponent families cannot satisfy a full-rank law.
- `[CORPUS]` `linearIndependent_restrict_expandedMonomialFamily_of_multiBlowUp` proves that an
  injective blow-up order makes the bounded expanded monomial box linearly independent.
- `[LITERATURE]` Wang--Yao, *Difference independence of the Euler gamma function*,
  arXiv:2303.02767, proves the sharp shifted-Gamma statement under pairwise nonintegral shift
  differences; integer-related shifts carry functional relations. This independently confirms
  that unrestricted shift packets cannot be the universal target.
- `[LITERATURE]` Bank--Kaufman, *An Extension of Hölder's Theorem Concerning the Gamma Function*,
  Funkcialaj Ekvacioj 19 (1976), 53--63, treats Gamma hypertranscendence over larger meromorphic
  coefficient fields, not the finite sampling connector here.
- `FALSE`: full rank for arbitrary exponent maps.
- `BRIDGE`: exact survivor above. The mixed-radix mechanism is classical and appears in the same
  form in Mathlib's Noether-normalization proof; no novelty claim.

## Complete paper proof

Let

`B = 2 + ∑ a : κ, ∑ k : Fin n, e a k`

and set `d k = B^k`. Every digit `e a k` is strictly below `B`, because it is bounded by the total
double sum. Define

`E(a) = ∑ k : Fin n, e a k B^k`.

This is the base-`B` value of the fixed-length digit list `(e a 0, …, e a (n-1))`. Fixed-length
base-`B` expansion is injective when every digit is below `B`, so `E(a)=E(b)` implies
`e a k=e b k` for every `k`. Hence `e a=e b`; injectivity of `e` gives `a=b`. Therefore the rate
vector `d` separates the exponent family.

The collision obstruction no longer applies: injectivity of `e` is necessary, while mixed-radix
weights prove it sufficient for separation by a nonnegative integral linear functional.

## Positive survivor

- **Exact killing mechanism:** duplicate exponent vectors produce identical expanded columns.
- **Strongest positive survivor:** injectivity is exactly sufficient for existence of a separating
  integral blow-up rate on a finite family.
- **New insight:** analytic full-rank construction splits into two independent obligations:
  combinatorial exponent separation (closed here) and carrier-specific realization of those pole
  rates.
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED]`.

## Log

- 2026-08-05 — internal corpus audit, current literature audit, hostile falsification, and complete
  mixed-radix proof recorded.
