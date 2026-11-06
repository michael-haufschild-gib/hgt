# Arithmetic Inner-Function Theory (AIF) programme

- **ID:** AIF
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.7 (also §1.10, §2.6.1, B14)
- **Statement:** why a function with an Euler product and a functional equation has trivial inner factor on the half-plane right of its symmetry line, while its critical passive system stays passive at zero slack.

## Goal
Develop the field: objects, language, mechanisms, questions, tools, test cases of §2.7, all in Lean under
`formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/` with umbrella `ArithmeticInnerFunctionTheory.lean`
and foundational `README.md`. Unconditional only; RH appears only inside equivalences.

## Work plan
- [x] A. Poisson–Jensen identity at every centre; inner field `I(w)`; no singular part; `N(ρ) = Π ϱ` exactly.
- [x] B. Helson–Lowdenslager form of Szegő; `exp(2I) = inf` of mollified Poisson second moments.
- [x] C. Function-field chain: inner mass = Mahler measure; Castelnuovo ⇔ Carathéodory ⇔ trivial inner factor; golden.
- [x] D. Euler columns: closed-form inner mass, mass at infinity = Mahler; fakes table in the README.
- [x] E. Prime insertion: Sato–Tate orthogonality, Hecke–Bessel, log-concavity wall, size floor, Kronecker locking, arithmetic Bernstein classification, `{2,3}` rung.
- [x] F. Anchor flow: `κ' = q − sinh 2κ`, coming down from infinity, energy identity, Darboux pair, kicks; Born medium at `½ log n`.
- [x] G. Frustrated forms at zero slack: outer predictor certificate, window RH, Allegretto–Piepenbrink as the sign-definite face.
- [x] H. Carleson/crowd geometry: shadows, balayage, exponential moment, large deviations of crowds.
- [x] I. Finite inner factors: zero–one law, datum as Szegő threshold, echo trains on independent reflectors, inverse scattering with prime data, no decoupling.
- [x] J. Questions of the field: `question_one` … `question_ten` in `TheQuestionsOfTheField`.
- [x] K. Near-extremal mollifiers: Hardy calculus of the disc, rigidity law, forced limit and coefficient; Abel mollifiers on a curve, Castelnuovo as the domination.
- [x] L. Forward map from primes to reflectors; potential past the Born regime.
- [x] M. Arithmetic Carleson measure and embedding; inner mass at infinity as depth density and Abel log-mean; `log log` bound at large width.
- [x] N. Restoring bound of the actual chain; passivity certified on arithmetic windows; causal certificate at one critical ratio.
- [x] O. Profile decomposition over Bohr space on the energy space, on-line configurations, RH iff at tests.
- [x] P. Calculus of signed Euler columns, Gamma base; correlated amplitudes; local onset field.

## Status
Questions Q1–Q10 answered by theorems, with RH-strength answers stated as equivalences; tools T1–T7 developed. Modules, pillars and open topics are in `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/README.md`. No sign for `ζ` is produced.

## Open core
The opposite sign (a mollifier family, or its dilation bound over `ℤ`), oscillation of the amplitude in `S(a, b)`, the zero–one law for `ζ`, depth density `o(T)`, the profile decomposition at atomic tests (B6), the height of alignment, the onset field at fixed `λ`.

## Do not redo
GWZ has Levinson, Szegő–Verblunsky, lattice anchor flow, curve flow, no slack, causality and single kicks. CSTW has the literal Weil flow. CompletedArithmeticForms has `eulerPartial`, `S = Π T_p A`, `thetaApertureAmplitude_not_laplaceMixture`. FADF has frustration of the Weil kernel in every sign gauge.

## Log
- 2026-11-06 — created; programme developed and formalized in 37 modules, wired into the umbrella and `MainTheorems`.
