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

## Work plan (each line is a module family; tick when it compiles and is wired)
- [x] A. Poisson–Jensen identity at every centre; inner field `I(w)`; no singular part; `N(ρ) = Π ϱ` exactly.
- [x] B. Helson–Lowdenslager form of Szegő; `exp(2I) = inf` of mollified Poisson second moments (second expression).
- [x] C. Function-field chain: inner mass = Mahler measure; Castelnuovo ⇔ Carathéodory ⇔ trivial inner factor; golden.
- [ ] D. Euler columns and fakes: closed-form inner mass; selectivity battery.
- [ ] E. Prime insertion: Chebyshev–Poisson kernel, Sato–Tate orthogonality, Hecke–Hankel cone, Kronecker locking, Laplace cone, Turán break, `S = Σ τ_b(N) A(N)`.
- [ ] F. Anchor flow: hyperbolic coordinate `κ' = q − sinh 2κ`, coming down from infinity, energy identity, Darboux pair, kicks, Szegő sum rule; literal `K` flow of the Weil chain.
- [ ] G. Frustrated forms at zero slack: causal certificate replacing Allegretto–Piepenbrink, slack = Schur product, Perron special case, deterministic orbits.
- [ ] H. Carleson/crowd geometry: shadows, balayage embedding, exponential moment of the inner field, big-cluster rate.
- [ ] I. Finite inner factors: almost-periodic zero–one law, classes table, datum (β,s) criticality via a.c. spectral density.
- [ ] J. Questions of the field: one theorem per question of §2.7.

## Log
- 2026-11-06 — created; read §2.7 and neighbours (FADF, CHT, CSTW, MZF, AKL, GWZ).
- 2026-11-06 — modules compile: ThePoissonJensenIdentity, TheInnerFieldOfZeta, TheSzegoInfimum, TheInnerMassIsAMollifierInfimum, TheDerivativeIsTheBlaschkeProduct, TheInsertionConeOfExponentiallyConvexAmplitudes, TheAnchorFlow, TheCurveChainOfTheInnerFactor. Uncheck: wire into umbrella at the end.
- Existing work not to redo: GWZ has Levinson, Szegő–Verblunsky, lattice anchor flow (`artanh` form), curve flow, no slack; CompletedArithmeticForms has `eulerPartial`, `S = Π T_p A`, `thetaApertureAmplitude_not_laplaceMixture`.
