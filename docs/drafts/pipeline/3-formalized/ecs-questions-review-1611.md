# Review 1611 — ECS Questions (E-Q5, E-Q4, E-Q3, E-Q2)

- **ID:** ecs-questions-1611
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1611/route-ecs.md §6
- **Statement:** Complete unconditional solutions, implications, and corollaries in Lean 4 for all questions posed in §6 of `route-ecs.md`, ordered from easiest to hardest.

## Summary of Verdicts & Lean Formalizations (Easiest → Hardest)

Note: **E-Q1** (`ZetaBeyondTheWallPrimeContinuation`: does $\Phi_F$ continue to $\operatorname{Re} p < 0$ for every $F \in \mathcal{H}$?) is labeled `fails T1: the target, not a door` in `route-ecs.md` §6 and is proved unconditionally equivalent to `RiemannHypothesis` in `ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean` (`zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis`, `zetaBeyondTheWallPrimeContinuation_iff_no_criticalState`).

| Order | Question | Final Answer | Lean Module (`ExclusionOfTheCriticalState/`) | Status |
|---|---|---|---|---|
| 1 | **E-Q5**: Subexponential $F(u)e^{-8u}$ along a thick set of $u \to -\infty \implies$ AAL? | **YES, unconditionally** (proved for local $L^1$ windows, a.e./pointwise `ThickLeft` sets, and `heatedState`) | `Decay/SubexponentialThickTailGivesTheAbscissaLaw.lean` | formalized |
| 2 | **E-Q4**: Does the weak equation on $(-\log 2, 0)$ constrain left zero values $\mathcal{L}F(z)$ beyond $(\star)$? | **NO — completely soft beyond $(\star)$** (left-normalised $(\star)$ implies the full smooth half-line weak equation, hence all collar tests; quantitative collar bound, collar uniqueness, and positive deep-tail mass proved) | `Collar/TheCollarWeakEquationIsSoftBeyondStar.lean` | formalized |
| 3 | **E-Q3**: Critical state of a curve configuration with non-unitary Frobenius root, and which ECS identities `curve_hodgeIndex_tfae` and `riemannHypothesis_cubicCharacter` violate? | **CONSTRUCTED & EXACTLY SEPARATED** (closed-form discrete Frobenius state + rational continuation + $(\star)$ + Parseval + seen outer/inner pair; Castelnuovo–Severi violates negative bare-energy $B_D(f, f) = -a W_8(f) < 0$; native Stepanov excludes outer roots via even-degree counts and forces Stage-5 beyond-the-wall continuation across $\{|z| < 1\}$ on `cubicKummerDatum`) | `Models/CurveCriticalStatesAndStepanovExclusion.lean` | formalized |
| 4 | **E-Q2**: Under a finite layer, do the $N$ critical states, Parseval identity, and "$F^+ =$ prime heads of $F$" force $N = 0$? | **NO at the soft / single-input model level; equivalent to B13 on $\zeta$** (refuted unconditionally on `hidingDatum M` and `overRegularZeta`; Beurling–Lévy rigidity pins joint $(\text{atomic }\Lambda_B \ge 0) \wedge (\Gamma_{\mathbb{R}}\text{ FE})$ uniquely to $\zeta$; full finite-layer Krein faithfulness, multiplicity-free bound $k \le \# Z_{\text{right}}$, single-pair pole isolation, and 6-way B13 `TFAE` proved) | `Index/FiniteLayerKreinStructureAndRigidity.lean` | formalized |

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (per question card)
- [x] 2 → 3  formalized (all 4 modules verified with `lake --old env lean`, standard axioms only, wired into `ExclusionOfTheCriticalState.lean`)
