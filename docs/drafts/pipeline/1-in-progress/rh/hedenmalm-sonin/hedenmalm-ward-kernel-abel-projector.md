# Hedenmalm Ward-kernel Abel projector

- **ID:** `P-G153`
- **Stage:** `1-in-progress`
- **Type:** CONJECTURE / SOURCE-RECOVERY TEST
- **Parent:** `P-G152`
- **Statement:** Recover P-G152's critical-line kernel projection as a cofinal Abel boundary value of the source-defined Ward energy.

## Goal

Test whether the missing critical-line projector is genuinely unavailable to source geometry, or
whether it is the boundary value of a regular family constructed before totalized Green
inversion. Required result is exact trace convergence, not a pointwise indicator repackaging.

## Heavy conjecture loop

1. `[CONJECTURE]` The projector is unrecoverable because source Ward energy vanishes on its kernel.
2. `[PIVOT CANDIDATE]` Ward mass stays strictly positive there. The source-only Abel quotient
   `2M(q)^2 / (2M(q)^2 + n E_W(q))` equals `1/(1+n y(q)^2)`, is regular for every finite `n`, and
   separates zero from nonzero transverse energy as `n -> infinity`.
3. `[OPEN]` Prove pointwise convergence to the critical-line indicator and pass the limit through
   the full critical-feature trace by a summable majorant.
4. `[OPEN]` Audit whether finite Abel traces admit a prime--Gamma evaluation or only a
   divisor-indexed mixed-moment representation. Pivot immediately if the latter is circular.

## Anti-theatre test

- Pointwise convergence alone is insufficient.
- Defining the indicator directly is insufficient.
- Progress requires source-only finite weights, exact dominated trace convergence, and a precise
  classification of arithmetic evaluability.

## Gates

- [x] 0 -> 1: source-pure quotient and attack identified
- [ ] exact source quotient law
- [ ] exact pointwise kernel limit
- [ ] summable finite currents
- [ ] exact critical-line trace limit
- [ ] arithmetic/source evaluation audit
- [ ] Lean module build and axiom audit
- [ ] unconditional RH

## Log

- 2026-08-13 -- opened after P-G152 identified totalized Green loss as one positive kernel atom.
