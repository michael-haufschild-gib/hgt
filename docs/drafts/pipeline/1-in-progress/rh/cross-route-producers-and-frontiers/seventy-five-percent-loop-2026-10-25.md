# 75% critical-line loop, second campaign (2026-10-25)

- **ID:** g75-1025
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop
- **Source:** `seventy-five-percent-loop-2026-10-12.md` (cycles 1–148), `TransThresholdPairCorrelation/README.md`
- **Statement:** Unconditional Lean proof of `∀ ε > 0, ∀ᶠ T, (3/4 − ε)·N(T) ≤ N₀(T)`.

## Frontier entering this campaign (corpus only)
- Proved: `two_thirds_le_liminf_xiSimpleCriticalRatio` (Zeta23 Thm B); Montgomery–Taylor `0.6725` (Zeta23 Thm D).
- TTPC: `N₀*(T,2T) ≥ (29/36 − ε)N − coalescentSurplus` at bandwidth `4/3`; `3/4` ⟸ surplus `≤ (1/18 + o(1))N`.
- Walls recorded in g75-1012: Nyquist/length law (pair correlation beyond `α = 1`), continuity barrier
  (averaging proofs cannot separate on-line doubles from coalescing pairs, so 75% on-line ⟹ 75% simple-like,
  above the RH-conditional record), Jensen floor (Levinson/CGG), parity (sieves bound close pairs only by size).

## Conjecture ledger (this campaign)
- **C1 two-window sign trick** (two windows on `[T,2T]` whose coalescent kernels sum `≤ 0`, so one surplus is `≤ 0`):
  FALSE. Every window `Ω ≥ 0` on `[T,2T]` has `Ω̂ > 0` on `|θ| ≲ 1/T`; a sum of windows is a window.
- **C2 positive-definite height window** (`Ŵ ≥ 0` makes the pair sum monotone, so a sieve majorant bounds it):
  FALSE. `W` PD forces `W(0) = max`, so the window covers `τ ≈ 0`, where the pole makes the Poisson continuum `≍ X`;
  pole subtraction makes the coefficients `Λ − 1` signed. Same wall as the "spectral sieve `Υ = 2`" model.
- **C3 eighth-moment Chebyshev** (`#{μ ≤ 0} ≤ tr(Â₁ − I)⁸ ≤ N/8 ⟹ n₊ ≥ 7N/8 ⟹ 3/4`): reduction TRUE
  (Uniform[0,2] gives `N/9`); input is an 8-level statistic at support 8 with signed height phase. BLOCKED.
- **C4 low-rank prime modes** (`Â_λ` positive on a subspace of codimension `#primes ≤ X`): FALSE. A frequency mode
  compressed to a window of length `T` is a multiplication operator, not rank two.
- **C5 parity of interval counts** (`N₀ ≥ #{I : N(I) odd}`): REDISCOVERED. `(−1)^{N(t)} = −sgn Z(t)`, so parity
  statistics are sign statistics of `Z` (Selberg's method).
- **C6 complex-shifted bilinear/Hermitian Gram `C_η`**: order law again; a pair block's negative eigenvalue is `−Θ(β²)`.
- **C7 displaced product `ξ(s+δ)ξ(s−δ)`**: consistency identity only; the certificate needs bandwidth `2`.
- **C8 Speiser–Levinson–Montgomery form** (`3/4 ⟺ N⁻(ζ') ≤ N/8 + O(log T)`): TRUE (classical); no leverage.
- **C9 curvature control by the bilinear `ζ''M` moment**: a near pair's CGG cost is `δ²×` its (positive) bilinear
  `ζ''M`-contribution, so the `a → 0` corner dies once far pairs' signed `ζ''` terms are bounded. Far pairs need
  near-line density rate `> 2` (the Zeta23 isolated-pair slack has rate `2λ = 2` at `λ = 1`: borderline, couples
  excluded). REDISCOVERED (g75-1012 cycle 11 "control of Σκ through ∫|ζ''M|²").
- **C10 Hermitian discrete moment by subharmonicity + Hölder** (mollified fourth moment of `ζ'` × Selberg moments of
  local zero counts): gives `Σ_ρ|ζ'M(ρ)|² ≤ K·N` with a constant loss. The adversary puts that whole budget on the
  pairs; the certificate needs the asymptotic. FALSE as a route.
- **C11 decorated crystal is not admissible**: on a lattice the form factor is 1-periodic and even, which contradicts
  `F(α) = α` on `(0,1)` except at `α = 1/2`, so `P = I_r` is never exact. TRUE, but already priced: the
  positivity-LP optimum is Montgomery–Taylor `0.6725`.
- **C12 hardness of the `λ = 4/3` surplus**: an off-line pair enters the bilinear Frobenius with weight `cosh(2λa)`, so
  without interference `surplus ≤ N/18` would force `N(σ,T) ≪ T^{1−(8/3)(σ−½)}`, i.e. beyond the density hypothesis and
  a zero-free strip `σ > 7/8`. Interference (g75-1012 cycle 14) keeps this heuristic. Sharpens the TTPC hardness
  witness; no route.

## Survivors to formalize

## Log
- 2026-10-25 — created; corpus frontier re-read (Zeta23, TTPC, ACS, g75-1012).
