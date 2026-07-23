# Prime-boundary Wick critical-profile universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Theorem-first origin

- `PrimeBoundaryDickmanWick.primeBoundaryWickCumulant_ofReal` identifies real-axis finite Wick
  cumulant at `r` with prime-clock cutoff energy at `r/2`.
- `PrimeClockCriticalProfile.tendsto_primeClockCutoffEnergy_critical_profile` and its moving version
  give universal nonlinear energy crossover at `c/log N`.

## Universal law

Finite prime-boundary Wick cumulant evaluated at real coordinate `2c/log N` converges to
complexified universal prime-clock profile. Same limit holds for any moving `cN → c`.

## Novelty and verification

Corpus scan found axis identity and critical energy profile in separate terminal modules, with no
Wick-cumulant critical scaling theorem. External literature audit and exact Lean audit pending.
