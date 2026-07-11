# Xi even-shift prime exposure

- **ID:** `xi-even-shift-prime-exposure`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[FORMALIZED] [UNCONDITIONAL] [BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiShiftPrimeExposure.lean`
- **Statement:** On `Re(s)>1`, the shift defect of the actual Riemann xi logarithmic
  derivative, after subtracting the exact rational archimedean/boundary difference, is the
  filtered von Mangoldt L-series with coefficient `Lambda(n)(1-n^(-2))`.

## Theorem

For `1 < Re(s)`, Lean proves

`logDeriv xi (s+2) - logDeriv xi s`

`  - (1/(s+2) + 1/(s+1) - 1/(s-1))`

`= LSeries (fun n => Lambda(n) * (1-n^(-2))) s`.

The capstone declaration is

`RHTower.xi_logDeriv_shift_two_exposes_prime_source`.

The proof is assembled from four separately exposed declarations:

1. `logDeriv_archFactor_closed`: the completed archimedean/boundary logarithmic
   derivative is `1/s + 1/(s-1) + gammaRealLogConnection s`;
2. `logDeriv_archFactor_shift_two`: the digamma recurrence collapses its `+2` shift
   defect to `1/(s+2)+1/(s+1)-1/(s-1)`;
3. `LSeries_shift_two`: translating an ordinary L-series by two multiplies coefficient
   `n` by `n^(-2)`;
4. `filtered_vonMangoldt_shift_two`: subtracting the shifted von Mangoldt series produces
   coefficient `Lambda(n)(1-n^(-2))`.

No zero location, RH, numerical verification, prime cutoff, or ordering of zeros is used.

## Exact scope

This card formalizes the source-exposure identity only.  The paper-level theorem that the
right side is hypertranscendental uses Ostrowski/Reich/Nagoshi theory for Dirichlet series,
which is not present in Lean.  Therefore this card does not claim a Lean proof that `xi`,
`xi'/xi`, or the filtered series is hypertranscendental.  That theorem remains in
`2-fully-proven/not_new_scientific_knowledge/completed-logderiv-augmentation-filter-exposure.md`
until its complete unconditional statement is formalized.

## Verification

- `lake build GaloisForLFunctions.RHTower.XiShiftPrimeExposure` passed.
- Scratch `#print axioms` for all five declarations reports only the project baseline
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced.

## Scientific status

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The identity is an exact and useful formal
connection between the completed carrier and the prime source, but it is obtained from the
classical digamma recurrence, the standard logarithmic derivative split, and L-series
linearity.  Its role is to remove an ambiguity in later research, not to claim scientific
novelty.

## Gates

- [x] 0 -> 1: exact analytic statement and proof architecture
- [x] 1 -> 2: complete unconditional paper proof
- [x] 2 -> 3: complete claim formalized in Lean; narrow build and axiom audit pass
- [ ] 3 -> 4: not a standalone publication target

## Log

- 2026-07-11 -- Formalized the closed archimedean logarithmic derivative, its rational
  even-shift defect, the coefficientwise L-series shift, the filtered von Mangoldt identity,
  and the actual-xi capstone.  Kept the unformalized Ostrowski hypertranscendence consequence
  outside stage 3.
