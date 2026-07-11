# Nonautonomous ADE carriers should split coefficient and state frequency budgets

- **ID:** `nonautonomous-kolchin-frequency-budget-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED]`
- **Statement:** For a jointly almost-periodic coefficient/solution pair, the total rational
  frequency rank should split into the coefficient-hull rank plus the rank of the kernel fiber. If
  the solution is algebraic-differential over the fixed coefficient field, relative Kolchin jet
  capacity should bound that kernel rank.

## Exact target

For the joint hull projection `pi:X_(a,f)->X_a`, prove

```text
rank_Q dual(X_(a,f))
 =rank_Q dual(X_a)+rank_Q dual(ker pi),
rank_Q dual(ker pi)<=2 kappa_rel.                         (1)
```

Then a cutoff carrier retaining `V_N=span_Q{log p:p<=N}` must satisfy

```text
kappa_rel>=1/2(dim_Q V_N-rank_Q Gamma(a)).                (2)
```

The coefficient module is a positive carrier, not an exception hidden inside a nonautonomous
equation.

## Gates

- [x] exact conservation law identified
- [ ] relative jet-capacity theorem proved
- [ ] compact-group rank additivity proved
- [ ] arithmetic-complement bound proved
- [ ] degeneracy and coefficient-pole cases attacked
- [ ] parent-literature audit
- [ ] complete unconditional Lean formalization
