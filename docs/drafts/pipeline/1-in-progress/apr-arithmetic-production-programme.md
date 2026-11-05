# Arithmetic production at square-root precision (APR)

- **ID:** apr-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.7.2
- **Statement:** what unconditional statements can produce square-root precision; exact production limit of each classical tool.

## Goal
Build `formal/GaloisForLFunctions/ArithmeticProduction/` with umbrella and README. Answer the four questions of §2.7.2 and the mechanism question.

## Gates
- [x] 0 → 1  README first draft
- [x] modules proved, checked, wired (22 modules, umbrella `ArithmeticProduction.lean`, `MainTheorems.lean`)
- [x] README on established results

## Results
Foundational document: `formal/GaloisForLFunctions/ArithmeticProduction/README.md`, with the pillar table and Lean names.

- Q1, Q2 reduced to the second-moment law and the rate `K/log T`; both false at every fixed exponent (`necessary_length_uniform`); the rate needs `log N ≥ c log²T` (`log_length_ge_of_secondMomentRate`). Both questions remain open.
- Q3: floor `1 + 1/(8+6θ)` for `θ ≤ (log T)/24`, purity floor `c²/p`, linear defect bounded ⇒ RH. Upper side at growing `θ` open.
- Q4: class-wide self-improvement is `Θ = 1` on shifted products; one impure factor realizes any width.
- Q5: norm statements on sign-stable classes, Type I, prime polynomials are blind; twin test is pole parity (`poleCorrectedTwin`); entry tests are filters (`Proximity`); no finite convergent linear system decides; long integer polynomials see parity away from the pole (`eventually_not_uniform_liouville`).
- Floors: Gram floor on finite sets of off-line zeros; floors add up to interference.

## Open
Upper side of Q3; constant `1/θ`; the law beyond `θ = (log T)/24` and the exact constant of the rate; exactness of the Gram floor; non-tautological statements with stabilizer in `𝒬` beyond finite linear systems; self-improvement inside the Ramanujan class; growth in `N` of the Liouville polynomial.
