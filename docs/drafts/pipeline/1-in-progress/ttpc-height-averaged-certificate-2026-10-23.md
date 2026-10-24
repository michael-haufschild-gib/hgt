# TTPC: coalescent localization of the bandwidth-4/3 certificate

- **ID:** ttpc-hac
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, partial) + CONJECTURE (assembly)
- **Source:** formal/GaloisForLFunctions/TransThresholdPairCorrelation/README.md §7 open problems 1–3
- **Statement:** Unconditionally, for every `ε > 0`, `η > 0` and large `T`,
  `N₀*(T,2T) ≥ (29/36 − ε − c_coal(T)) N(T,2T)`, where `c_coal` is the normalized smooth-window
  prime-pair sum over the coalescent band `|log(n/m)| ≤ T^{-1+η}` (diagonal excluded).

## Goal
Open problem 2 done so that it actually reaches open problem 3's band. The seam is linear in
`frobSq` and holds for every grid weighting `|w_k| ≤ 1` (`RHTower.seamA_weighted`), so the whole
surplus can be read through a smooth window.

## Findings
- **Standard Jackson windows cannot reach the coalescent band.** `F_b²` has cubic tails, so the
  outer mass is `≍ L/(b³M²)` and the far-pair error `≍ XL³/(b³M²)`; against `L²Tl` this forces
  `b ≫ X^{1/3}/T` (`b ≫ T^{-5/9}` at `λ = 4/3`). The "close pairs" `|log(n/m)| < 4b` then include
  the band `T^{-1} ≪ |θ| ≪ T^{-5/9}` where the Jackson pair kernel is still `≍ L/|θ|` (sharp-window
  leakage, total `≍ X log X`). Pillar 4 does not localize to `h ≪ m/T`.
- **Height averaging at fixed λ fails**: the moving cutoff `X(T)` costs `≍ √ε X log²X`.
  At fixed `L` it works (module `HeightAveragedCoalescentLocalization`, done) but needs uniform-λ
  core estimates and an averaged end form.
- **Smooth compactly supported grid weights at fixed λ** avoid both: `W(τ_k) = 0` off the grid, so
  `K_W − W(τ)·LΦ = Σ_{k∈ℤ}(W(τ_k) − W(τ)) φ̂φ̂` exactly (no aliasing, no end form), with error
  `O(Lip W)` against a Lorentzian of width `T`; the smooth continuous form `∬W(τ)²Φ²νν'` has exact
  pair kernels `∫Φ(x)² Re[e^{ixy'} (W²)^(y − y')] dx`, decaying like `‖(W²)^{(k)}‖₁/|θ|^k`.

## Gates
- [x] 0 → 1
- [ ] 1 → 2
- [ ] 2 → 3

## Approach (modules, all in `TransThresholdPairCorrelation/`)
1. `HeightAveragedCoalescentLocalization` — oscillatory decay (done).
2. `FejerWeightedPrimeMeanSquare` — Fejér/Lorentz mean squares of `P_X` (done).
3. `SmoothGridWeightKernel` — grid kernel of a Lipschitz weight, two comparisons (done).
4. `SmoothWindowContinuousForm` — `Φ² ⋆ v` (slowly varying / decaying / prime polynomial),
   linear-growth Fubini, exact coalescent kernel and its diagonal/close/far/sum-frequency split,
   half-period shift, Lorentz mean square of `C_w` (done).
5. `SmoothWindowFrobeniusChannels` — bilinear expansion along `μ + Π_X + P_X`, nine channels,
   `smoothPair_nuX_le` (done).
6. `SmoothWindowGridComparison` — weighted Frobenius sum `= L²·smoothForm` up to explicit errors;
   Lorentz mean square of `ν_X`; lattice deficit `ρ` at distance `D` (done).
7. `SmoothWindowWeightedTrace` — summation by parts, Jordan bound, prime part at `λ = 4/3`,
   collar form of the trace (done).
8. Profile module + assembly through `seamA_weighted` at `params43` (in progress).

## Log
- 2026-10-23 — created; moving-cutoff obstruction; Jackson-tail obstruction; smooth-weight route.
