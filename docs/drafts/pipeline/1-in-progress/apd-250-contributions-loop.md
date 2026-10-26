# APD conjecture loop (250 contributions)

- **ID:** apd-250-contributions-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop card)
- **Source:** `formal/GaloisForLFunctions/ArithmeticPositiveDuality/README.md` §8–§10
- **Statement:** Answer the open APD topics with unconditional Lean theorems, one conjecture at a
  time; log every success and failure in `logs/apd-250-2026-10-25.md`.

## Goal
Each item: positive side, spectral side, gap, integer; inserted or intrinsic charge; depth scaling;
battery behaviour (README §10).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  (per conjecture)
- [ ] 2 → 3  (per conjecture)

## Current conjecture
**C6–C8 (Fourier analysis on `ℚ_{>0}`, Kronecker dichotomy).**
- C6: `f` positive definite on `ℚ_{>0}` ⇔ `f(u) = ∫ χ_x(u) dμ(x)`, `μ` finite on the prime torus,
  unique. Proof: finite-rank Herglotz–Bochner on the primes below `k`, eventually constant
  coefficients, Fourier–Lévy on the prime torus.
- C7: `f(u) = F(log u)`, `F` continuous ⇒ `μ = ν ∘ z⁻¹`, `z_x = (x log p/2π)_p` (Kronecker line).
  Proof: `F` positive definite on `ℝ` by density of `log ℚ_{>0}`; Bochner on `ℝ`; uniqueness.
- C8: decay `f((N+b)/(N+a)) → 0` ⇒ `μ(line) = 0`; Gram form at `(N+j)/N`, `j < M`, is
  `f(1)/M + o(1)` and dominates `∫|M⁻¹Σ_j ((N+j)/N)^{ix}|² dν → ν(ℝ)`. Integer and Bost–Connes
  successors decay (height of `(N+b)/(N+a)` is `≥ N²/(a−b)²`), hence no nonzero archimedean
  positive-definite `g` with `f − g` positive definite.

## Done
- C1 `TheIntegerSuccessorForcesTheHeckeWeight` (P18); C2 `TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor` (P19);
  C3 `TheBostConnesTemperatureIsTheHeckeExponent` (P20); C4 `TheExtremalsOfTheHeckeLawAreTwistedHaarStates` (P21);
  C5 `AMautnerPhenomenonForTheAffineGroupOfQ`.

## Next
- Kronecker decomposition `f = f_arch + f_null` (unique); successors compatible with archimedean
  dilation parts (conjecture: continuous on `ℝ` plus `c·δ₀`).

## Log
- 2026-10-25 — created; C1 opened.
- 2026-10-26 — C1–C5 formalized; C6–C8 drafted.
