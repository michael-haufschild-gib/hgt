# The pole-point budget of a Weil-positive weight system

- **ID:** weil-cone-pole-point-budget
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L101 (MUST-513, paper), L108/L109 (gap weights), L221 · STATUS MUST-598
- **Statement:** Every full-cone Weil-positive `lam` satisfies `limsup_x [Σ_{2≤n≤x} lam(n)/n − log x − (1/x) Σ_{2≤n≤x} lam(n)] ≤ −(γ + log 4π)/2`. `Λ` attains `−γ − 1`, a slack of `Σ_ρ 1/ρ = 0.0231`.

## Goal
Make the `s = 1` interior evaluation of the Herglotz function of a producer formal, without the density and Mertens hypotheses of L101. Then decide L108's gap-weight candidate.

## Gates
- [x] 0 → 1
- [x] 1 → 2: L101 paper proof (density-one form)
- [x] 2 → 3: `RHTower.PolePointBudget.eventually_polePointBudget_le`, `tendsto_polePointBudget_vonMangoldt`, `polePointBudgetConstant_eq` and `not_weilPositiveFull_primeGapWeight` (module `RHTower/WeilFullConePolePointBudget.lean`).
  - `lake env lean` is clean.
  - `#print axioms` gives propext, Classical.choice, Quot.sound.
  - The module is wired into the `RHTower` umbrella.
- [ ] 3 → 4

## Proof
1. Full-cone positivity reaches the literal pole vector `e^{x/2}1_{[−a,a]}` of the aperture-`a` restricted form (`ccmRestrictedWeilSourceQuadraticWith_nonneg_of_weilPositiveFull`).
2. A visible atom `n ≤ e^{2a}` pairs with the pole vector as `2(e^a/n − e^{−a})` (`ccmPrimeTransport_polar_self`). So the weighted entry equals `A(a) + 2e^a Σ(Λ−lam)(n)/n − 2e^{−a}Σ(Λ−lam)(n)` (`with_pole_eq`), where `A(a)` is the corpus's `Λ` entry.
3. Divide by `2e^a` and put `x = e^{2a}`. Then `B_lam(x) ≤ A(a)/(2e^a) + E_M(2a) − ψ(x)/x`.
4. The right side tends to `(2 + γ − log 4π)/2 − γ − 1 = −(γ + log 4π)/2`, by `tendsto_poleDiagonalExplicit_div_exp`, Mertens with Euler's constant, and the PNT.

## Gap-weight corollary
Take `lam(p) = p⁺ − p`.
- Telescoping gives `Σ_{p≤N} gap_p/p = log(p⁺(N)/2) + Σ(u_p − log(1+u_p))`, and `p = 2, 3, 5, 7` contribute `≥ 23/84 + 1/10`.
- Also `Σ_{p≤N} gap_p = p⁺(N) − 2`, and `p⁺ < 1.01x` eventually (PNTPlus `prime_between`).
- So `B ≥ −1.33` eventually, against the bound `≤ −1.433`.

## No-go closure
- **Killing mechanism:** positivity at the interior point `s = 1` of the producer's Herglotz function.
- **Strongest positive survivor:** the budget law itself, formal and hypothesis-free. Every producer matches `Λ`'s Mertens constant to within `Σ_ρ 1/ρ`.
- **New insight:** the budget sees net `1/n`-mass, including prime-supported reweightings that divisor resonance cannot see. It is the first rung of the Carathéodory–Toeplitz (generalized Li) tower of L101. Pole vectors `x^k e^{x/2}` should give the higher rungs.
- **Status:** Lean complete for the density-one form and the gap-weight exclusion.

## Log
- 2026-09-30 — created at stage 3
