# Mixed-valuation stability changes at zero support

- **ID:** biscale-mixed-stability-strata-1810
- **Stage:** 1-in-progress
- **Parent:** [field programme](../../biscale-field-development-1810.md), item 5
- **Status:** exact obstruction and positive replacement identified; Lean audit open

## Failed uniform coefficient-metric formulation

Take the actual period-four atoms

`u(n)=2·1_(2|n)−1`,

`v(n)=4·1_(4|n)−2·1_(2|n)`.

They are the order-two and order-four Ramanujan rows, realized by divisor weights supported on `{1,2,4}`. At any cutoff at least four set `f_t=u+t v` and `g_t=−u+t v`. Their Selberg coordinate vectors on these orders are `(1,t)` and `(−1,t)`.

For `t≠0`, the candidate exact ambiguity from all translated observations is reversal of the highest active block only: `(a,b)↦(a,−b)`. The coefficient distance between the displayed vectors modulo this action is at least two. Yet as `t→0`, every fixed finite family of moment observations merges. At zero the lower block itself acquires a sign ambiguity, since `u(n+1)=−u(n)`.

More precisely, a zero-sum frequency tuple cannot contain exactly one order-four frequency; its maximal two-adic multiplicity must be even. Changing the order-two sign affects only terms with an odd number of order-two factors. Thus all even translated moments agree identically, and differences of any fixed odd-degree moments are divisible by `t²`. At zero lag the cubic difference is exactly `12t²`.

Therefore no global modulus of continuity, even without a power-law requirement, can reconstruct coefficients in the metric obtained by minimizing over only each nonzero support's highest-block sign action. The failure is a change of symmetry at a vanishing coordinate. It is not repaired by adding more finitely many moment degrees.

## Positive replacements to prove

1. On a fixed support stratum, impose explicit lower bounds on the coordinates that orient lower blocks. The quintic identity then gives quantitative bounds whose degeneration in these lower bounds must be tracked.
2. For a global quotient metric, allow all actual cyclic translations in the ambient signal space, even when a translated signal falls outside the order-constant coefficient family. Here `T₁f_t` and `g_t` differ by `t(T₁v−v)`; their mean-square signal distance is `4t²`. The discrepancy tends to zero, as it should in the translation quotient.

The cubic gap and this translation-distance scaling suggest a square-root boundary for this particular mixed pair; a complete sharp estimate in the ambient quotient remains open. Do not extend the prime-family's fixed common-sign stability theorem to mixed supports without resolving this change of symmetry.

## Required proof gates

- [ ] Exact Selberg profiles and literal translated moments for the displayed actual weights.
- [ ] Exact surviving ambiguity for nonzero `t`, including translation realization.
- [ ] Formal nonexistence of a global modulus in the stated coefficient metric.
- [ ] Actual ambient-translation distance and a sharp positive stability theorem.
- [ ] Corpus and external comparison before making any novelty claim.

This obstruction does not retire item 5; it determines which stability statement can be true.
