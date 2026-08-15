# Formalization certificate — `ccm-poisson-jensen-outer-defect-rh-law`

- **Card:** `ccm-poisson-jensen-outer-defect-rh-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMPoissonJensenOuterDefect.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 10 declarations
- **Hypotheses:** only the card's standing data conditions (`x > 0`, `a_ρ > 0`, positive
  multiplicities, zero-free outer factor); no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(10)` elementary Blaschke factor | `halfPlaneBlaschke`, `norm_sq_halfPlaneBlaschke` |
| `(11)` exact defect of one zero | `neg_log_norm_halfPlaneBlaschke`, `outerDefectTerm` |
| `(12)` positivity | `outerDefectTerm_nonneg`, `outerDefectTerm_pos` |
| `(13)` exact detection (finite form) | `sum_outerDefect_eq_zero_iff` |
| `(20)`–`(21)` dephasing | `log_norm_meanType_interior`, `log_norm_meanType_boundary` |
| `(15)`–`(18)` limit subtraction | `defect_limit_eq_zero` |

## Deliberately outside the Lean statement

- the Hardy inner–outer factorization `(4)` and absence of a singular inner factor;
- the Poisson representation `(9)` and the Poisson–Jensen integral `(5)`;
- the Blaschke convergence condition;
- the analytic zeta multiplier `(2)`–`(3)`.

The card's remaining open gates (proving the logarithmic-boundary convergence `(16)` from the CCM
finite source; RH) are route gates, not statements of this card.
