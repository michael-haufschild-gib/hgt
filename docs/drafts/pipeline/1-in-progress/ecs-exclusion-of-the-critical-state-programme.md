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
- C5 (PROVED, Lean) sign law: `criticalState_changes_sign_on_every_ray`, `riemannHypothesis_or_criticalState_changes_sign` (TheStateChangesSignOnEveryRay). Mechanism: one-signed tail ⇒ Landau (corpus IsAbscissa + Cauchy estimates) ⇒ abscissa ≤ -8 because the remainder (with (s-1)ζ(s) and dslope at ½) is holomorphic near the real segment ⇒ LF holomorphic on Re w > -8 ⇒ decay law gives all zeros on Re ≤ ½. Uses: no real zeros of ζ in (½,1) (fails for some prime-two deformations: real factor zeros).
- C4' (PROVED, Lean) general form `zero_re_le_of_laplace_holomorphic`: LF holomorphic on Re w > κ (κ ≤ -7) ⇒ Re ρ ≤ κ + 17/2.
- Note: b ≤ 16 via on-line zeros is weaker than C4 off RH (state exists only off RH) — not pursued.
- C6 (PROVED, Lean) finite index at every ratio: `exists_bound_orthonormal_nonpositive` (TheConfinedFormHasFiniteIndexAtEveryRatio). Mechanism: Q_R = Q_{2R} + (a(R)/2)W₈ bounds W₈ on the nonpositive cone; corpus compactness `exists_domain_limit_of_smooth_energy_limit`; greedy 1/2-separated sequence (`exists_seq_of_forall_finset_exists`). Q6 for ζ answered.
- Assessment: stage 5 ⇔ (★) has no solution ⇔ no eigenvector of the Cauchy matrix 1/(8+z'-z) of the zeros with negative eigenvalue; holds for every configuration without right zeros and fails for prime-two deformations; decay exponent of the state = PNT error exponent (barrier with PNT cancellation is circular).
- Next: residue law (Q3a right half); exact index count (Q6 exact) via Pontryagin + translation; zero side on domain (Q2, heavy).

## Log
- 2026-11-16 — created; README draft written.
