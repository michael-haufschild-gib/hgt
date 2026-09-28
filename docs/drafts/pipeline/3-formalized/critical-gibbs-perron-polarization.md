# The pole direction is the Perron vector of the von Mangoldt correspondence

- **ID:** critical-gibbs-perron
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** HF card L58 ("Lorentzian arithmetic"); facts HF-F55, HF-F56; STATUS MUST-499, CANNOT-476
- **Statement:** On `ℓ²([1,N])`, the form `c ↦ 2Σ_{n≥2}Λ(n)n^{−½}Re Σ_m c(nm)conj c(m)`:
  - has Rayleigh quotient `log N − γ + o(1)` at the critical Gibbs vector `m^{−½}`;
  - is at most `(log N + C)‖c‖²` for every `c`.

## Goal
This is the arithmetic seed of a spectral–algebraic–geometric dictionary:
- the ample class (pole direction of the Weil form) is the Perron vector of the prime correspondence;
- Euler's constant is the defect of its eigenvalue;
- the polar constraint deletes the top eigen-direction.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  `RHTower.CriticalGibbs.gibbs_perron_polarization`, `tendsto_gibbs_rayleigh`, `exists_vonMangoldt_toeplitz_le`; module `RHTower/CriticalGibbsPerronPolarization.lean`; `lake build` green; axioms propext, Classical.choice, Quot.sound.
- [ ] 3 → 4

## Proof
1. Divisor reindexing gives `P(N) = Σ_{nm≤N}Λ(n)/(nm) = Σ_{k≤N}(1/k)Σ_{d|k}Λ(d) = Σ_{k≤N} log k/k`.
2. Swapping sums gives `P(N) = Σ_{m≤N} S(⌊N/m⌋)/m`, with `S(x) = Σ_{n≤x}Λ(n)/n`.
3. So `2P − (log N − γ)H = Σ_m (1/m)[E(⌊N/m⌋) + (log m + log⌊N/m⌋ − log N)]`, where `E(k) = S(k) − log k + γ → 0` (Mertens with γ, corpus). The floor defect is at most `1/⌊N/m⌋`.
4. Cesàro lemma: a bounded `φ → 0` has `Σ_{m≤N}φ(⌊N/m⌋)/m = o(H(N))`.
5. Schur: use AM–GM with weight ratio `√n`. The row sums are `log k + S(⌊N/k⌋) ≤ log N + C`.

## No-go closure (the field's first local test)
- **Killing mechanism:** Lorentzian signature of the Metzler-extended Weil form fails for the archimedean-only form and for every single-prime form (the symbol is negative at `τ = 0`).
- **Positive survivor:** this theorem. On lattice tests the polar constraint removes the Perron direction, and positivity is a constant-level (Mertens) balance.
- **New insight:** Hodge signature for ζ is a property of the complete Euler product. It cannot come from local closure.
- **Status:** formalized.

## Log
- 2026-09-28: L58 created, proved, formalized and wired.
