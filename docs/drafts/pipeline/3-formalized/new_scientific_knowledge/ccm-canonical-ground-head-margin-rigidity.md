# CCM canonical-ground-head margin rigidity

- **ID:** CCM-O-HEAD-MARGIN-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route O canonical exact-ground Γ--Slepian heads
- **Statement:** Canonical-head Rayleigh margins converge to the exact ground margin; fixed positive cofinal head coercivity is equivalent to strict ground positivity and is impossible at zero-energy first contact.

## Goal

Determine whether Route O can target a fixed `δ > 0` in
`δ ‖h_n‖² ≤ Q_a(h_n)` on canonical actual Γ--Slepian heads. This is source-faithful: `h_n` is the
projection of exact restricted-Weil ground onto literal accuracy-selected Γ--Slepian head.

## Gates

- [x] 0 → 1: exact canonical heads and source quadratic already constructed
- [x] 1 → 2: dependency-closed proof below
- [x] 2 → 3: Lean module `CCMRestrictedWeilCanonicalGroundHeadEnergy`
- [ ] 3 → 4: standalone publication treatment

## Theorem and proof

Let `u_a` be nonzero canonical complete-form ground lift, `h_{a,n} → u_a` canonical finite heads,
`E_a` exact ground floor, and `A_a` physical form embedding. Continuity of source quadratic and
norm gives

```text
Q_a(h_{a,n}) / ‖h_{a,n}‖²
  → E_a ‖A_a u_a‖² / ‖u_a‖².
```

Both denominator masses are strictly positive: `u_a ≠ 0` follows from injectivity/its embedding
into nonzero attained ground eigenstate. Therefore:

```text
E_a > 0
↔ ∃ δ > 0, eventually δ ‖h_{a,n}‖² ≤ Q_a(h_{a,n}).
```

Forward direction chooses half limiting quotient. Reverse direction passes eventual lower bound to
limit and divides by two positive masses. If `E_a = 0`, quotient tends to zero, contradicting every
fixed positive eventual margin.

## No-go closure

- **Exact killing mechanism:** form-norm convergence plus quadratic continuity forces normalized head margin to zero at zero-energy first contact.
- **Strongest positive survivor:** exact limiting quotient and iff-classification above; shifted head defect remains nonnegative, equals omitted-tail defect, and has explicit vanishing rate.
- **New insight:** fixed positive `δ` is not equivalent to endpoint nonnegativity; it is equivalent to strict floor positivity. Lawful Route O producer must prove literal reverse-prime inequality with vanishing head error, preserving prime--polar--Γ cancellation.
- **Status:** paper proof dependency-closed; Lean source check and leaf build pass; standard foundational axioms only.

## Novelty audit

Corpus search before proof found head convergence, source-aligned finite reduction, and generic
Rayleigh excess bounds, but no normalized canonical-head limit, uniform-margin equivalence, or
first-contact no-go. CCM/Suzuki literature does not construct canonical actual Γ--Slepian ground
heads, so cannot contain this classification.

## Lean certificate

- `tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic_div_normSq`
- `tendsto_ccmRestrictedWeilCanonicalGroundHead_margin_zero_of_groundEnergy_eq_zero`
- `not_eventually_ccmRestrictedWeilCanonicalGroundHead_uniform_positive_margin_of_groundEnergy_eq_zero`
- `ccmRestrictedWeilGroundEnergy_pos_iff_exists_eventually_canonicalGroundHead_uniform_margin`

All in `formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilCanonicalGroundHeadEnergy.lean`.

## Log

- 2026-08-17 — conjectured fixed-margin target; corpus audit exposed first-contact conflict; proved exact limit, falsified target, extracted sharp survivor, formalized in Lean.
