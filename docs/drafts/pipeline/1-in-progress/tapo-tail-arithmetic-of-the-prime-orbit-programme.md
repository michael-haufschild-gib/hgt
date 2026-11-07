# Tail arithmetic of the prime orbit (TAPO)

- **ID:** tapo
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0711/obstacles-summary.md §2.8b
- **Statement:** the law of the tail phases `t log p`, `p > y`, at one height, conditionally on the head `p ≤ y`.

## Goal
Answer the six questions of §2.8b and build the six tools, in Lean, in
`formal/GaloisForLFunctions/TailArithmeticOfThePrimeOrbit/` (umbrella `TailArithmeticOfThePrimeOrbit.lean`,
wired into `MainTheorems.lean`). README is the foundational document.

## Module plan and status

| Module | Content | Answers | Status |
|---|---|---|---|
| TheFirstReturn | `firstReturn`, Dirichlet bound, group laws, corners | Q1 | open |
| TheFirstReturnIsAnExtremeValue | `log|ζ(1+1/log N+it)| = log log N − A_t(N) + O(1)`; weak return ⟺ spike | Q1 | open |
| ThePrecisionLawOfTheFirstReturn | PTT savings → lower bounds for `R(y, η)` | Q1 | open |
| ProportionalSavingIsAHeavyFirstReturn | B46 ⟺ no heavy return | T1 | open |
| TheTailDecouplesFromTheHead | smooth × rough mean value factorizes (MVT) | Q2, T3 | open |
| TheHeadIsFrozenAtItsResolution | `|(log E_y)'| ≤ Σ_{p≤y} log p/(p^σ − 1)` | Q2 | open |
| TheTailOfAReturnCarriesTheZero | bounded return ⇒ tail → `ζ/E_y` | Q5 | open |
| AReturnAtAZeroIsTailBad | `zetaReturnSet ⊆ tailBad` at every cut | Q5, T4 | open |
| TheFadeOfAReturn | forced fade, pole mimicry | objects | open |
| TheJetOfTheLogarithm | dilation equivariance, sweep, exotic isolation | Q3 | open |
| TheDepthAspect | exact `q`-differencing, `p`-adic integrality | Q4 | open |
| EulerCoordinatesStopAtTheAbscissa | divergence; head–tail certificate | Q6, T6 | open |
| TheCombOfAReturn | smooth numbers on the comb; level set density | T5, T2 | open |
| TheTestSystemsOfTheTail | rank one, corners, rounded tail | criteria | open |
| TheQuestionsOfTheField | six answers | all | open |

## Gates
- [x] 0 → 1  in-progress: README draft, module plan
- [ ] 1 → 2  paper proofs for each module (inline in module docstrings)
- [ ] 2 → 3  every module checked with `lake --old env lean`, wired into the umbrella

## Notes for continuation
- Reuse: RAC `primeReturnSet`, AAD `IsPhaseReturn`/`tendstoLocallyUniformlyOn`, RHTower `eulerHead`,
  `eulerDiscTailBadSet`, `zetaReturnSet`, twin-prime `primeSum_log_comparison`, PTT savings, `dirichlet_meanValue_dyadic`.
- VK upper bound `|ζ(1+it)| ≪ (log t)^{2/3}` not found in corpus; the VK side of Q1 is cited, not proved.

## Log
- 2026-11-07 — created in 1-in-progress
