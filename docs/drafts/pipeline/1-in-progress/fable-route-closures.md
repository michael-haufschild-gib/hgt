# Closure tasks in the consolidated review

- **ID:** fable-route-closures
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/fable.md`, §12.3.
- **Goal:** Resolve all ten listed tasks with unconditional, dependency-audited Lean proofs. The cited section lists closures; §12.1 instead lists nine unfinished assemblies. Scope clarification is pending; the positivity ceiling belongs to both.

## Obligations

| Item | Required scope | Status |
|---|---|---|
| Calibrations of B13, Landing, DH | Exact scope of the three model theorems and joint rigidity | Audit pending |
| Arithmetic constituents | Wiener obstruction and the remaining bounded class | Bounded case `0 ≤ x < 1/2` remains open |
| First rung by sizes | Exact barrier and positive boundary theorem | Audit pending |
| Section rings of the square | Tower product formula and planar ideal equality | Audit pending |
| Covers and averaged families | Fixed-part and character-index laws, with rightmost-zero exception | Audit pending |
| S3 transfer | Exact implication and status of the transfer itself | Audit pending |
| Window and theta stages | Verification law and obstruction to unconditional induction | Audit pending |
| Scheduled sums and source completions | Exact criteria for all named routes | Audit pending |
| Positivity census | Decide 70% at every bandwidth | Open; existing spike only excludes 75% at `4/3` |
| Short mean values as detectors | Relocation invariance and positive density/census scope | Audit pending |

## Positivity question

The known model has excess mass `1/5` near frequency one. Its lower bound
`1/18 + 47/750` does not exceed the 70% target `7/45`.
A possible stronger model adds several nonnegative Fourier spikes. A periodic
majorant of `sinc²` supplies the positive pair density; a Fejér kernel redistributes
its unused constant coefficient into spikes. Neither the majorant nor the
all-bandwidth obstruction is proved yet. A single counterexample at `4/3` does
not settle the all-bandwidth question.

## Completion gates

Exact statements, paper proofs, direct `lake --old env lean` checks, transitive
`#print axioms`, umbrella imports, and positive survivors for every retired route.
No numerical optimization or assumed analytic inputs.
