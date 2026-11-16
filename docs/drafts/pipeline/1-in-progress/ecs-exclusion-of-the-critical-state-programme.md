# Exclusion of the critical state (ECS)

- **ID:** ecs
- **Stage:** 1-in-progress
- **Type:** programme card (goal loop)
- **Source:** docs/reports/review-1511/obstacles-summary.md §2.18 ("the most likely route to a proof, as a research programme")
- **Statement:** make every exact property of the critical half-line state a Lean theorem (stages 1–4: probe kernel, zero side, (★), continuation, sign/decay laws, index law) and attack stage 5 (no state for the zeros of ζ).

## Goal
README: `formal/GaloisForLFunctions/ExclusionOfTheCriticalState/README.md` (Q1–Q9). Lean in
`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/`, umbrella `ExclusionOfTheCriticalState.lean`.

## Gates
- [x] 0 → 1 in-progress: README draft, questions Q1–Q9
- [ ] 1 → 2 fully-proven: per conjecture below
- [ ] 2 → 3 formalized: per module

## Approach
Order: Q1 probe calculus (pole, prime, Gamma parts on `e_p`, Poisson integral of Re ψ) → probe kernel;
state's probe identity in prime coordinates; Q6 finite index law; Q2/Q3 zero side on the domain → (★);
Q5 sign law via Landau; Q4 decay law (divergent half). Stage 5 entry points: wall, collar, charges, difference equation.

## Conjecture ledger
- C1 (PROVED, Lean) probe kernel: `bareMixedEnergy_probe` = (D(p)+D(q))/(p+q), `probeSymbol_eq_logDeriv_xiCent`, zero side `bareMixedEnergy_probe_eq_zeroSide` (WeilsFormOnProbesIsTheCaratheodoryKernelOfXi). Q1 answered.
- C2 (PROVED, Lean) state equation on probes in prime coordinates: `criticalState_probeEquation` (TheStateEquationOnProbes).
- C3 (PROVED, Lean) holomorphic extension: `differentiableOn_laplace_of_sq`, `differentiableOn_stateGamma`, `differentiableOn_stateTail`, `stateEquation_ofReal_eq_zero`.
- C4 (PROVED, Lean) decay law, divergent half for zeros right of the line: `criticalState_not_integrable_of_zero`, `riemannHypothesis_or_criticalState_decay_ruler` (∫F²e^{-bu}<∞ ⇒ Re ρ ≤ (17-b)/2). Mechanism: cleared equation ζ(½+p)A(p)+LF(p)ζ'(½+p)=0 on Re p>max(0,8-b/2), Im p>0; residue of ζ'/ζ forces LF(ρ-½)=0, contradicting closed-RHP zero-freeness. No zero side, no explicit formula on the domain needed.
- Next: sign law (Landau + removable point p=½ + off-line zero from ¬RH); b ≤ 16 via on-line zeros (needs crossing Re p = 0); finite index law (Q6).

## Log
- 2026-11-16 — created; README draft written.
