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
- [x] modules proved, checked, wired (21 modules, umbrella `ArithmeticProduction.lean`, `MainTheorems.lean`)
- [x] README on established results

## Results
Foundational document: `formal/GaloisForLFunctions/ArithmeticProduction/README.md`, with the pillar table and Lean names.

- Q1, Q2 reduced to the second-moment law and the rate `K/log T`; both false at every fixed exponent (`necessary_length`).
- Q3: floor `1 + 1/(8+6θ)`, purity floor `c²/p`, linear defect bounded ⇒ RH. Upper side at growing `θ` open.
- Q4: class-wide self-improvement is `Θ = 1` on shifted products; one impure factor realizes any width.
- Q5: norm statements on sign-stable classes, Type I, prime polynomials are blind; twin test is pole parity (`poleCorrectedTwin`); entry tests are filters (`Proximity`); no finite convergent linear system decides.
- Floors: Gram floor on finite sets of off-line zeros; floors add up to interference.

## Open
Upper side of Q3; constant `1/θ`; uniformity of `necessary_length` in `θ ≤ c log T`; exactness of the Gram floor; non-tautological statements with stabilizer in `𝒬` beyond finite linear systems; self-improvement inside the Ramanujan class; integer polynomials above the window.
