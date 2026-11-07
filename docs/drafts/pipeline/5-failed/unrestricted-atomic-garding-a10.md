# Unrestricted atomic Gårding (A10) at fixed critical ratio

- **ID:** unrestricted-atomic-garding-a10
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** docs/reports/review-0611/obstacles-summary.md · §3 (A10)
- **Statement rejected:** At a fixed critical ratio `R = c_N^8 / log N > 0`, there exist `B_R ≥ 0` and `a_R > 0` such that `weilQuad(U_N) + B_R ‖U_N‖_{L²}² ≥ a_R W₈(U_N)` holds eventually for all normalized centred atomic sources `U_N` (even when restricted to vectors in `(conductorSubspace 1 N)ᗮ`, under either `‖z_N‖_{ℓ²} = 1` or `‖U_N‖_{L²} = 1`).

## Obstruction

Take `z_N = (e₁ - √2 e₂) / √3 ∈ (conductorSubspace 1 N)ᗮ` at indices `n = 1, 2`, so `‖z_N‖_{ℓ²} = 1` and `z_{N,1}/√1 + z_{N,2}/√2 = 0`. When `N > 4 c_N`, the atoms of `centredAtomicTest φ z_N c_N N` centred at `-log N` and `log 2 - log N` of width `c_N / N < (log 2)/2` are disjoint, and by translation invariance (`weilQuad_centredAtomicTest`) `weilQuad` equals its value on the uncentred two-atom test supported in `[0, 2]`. Hence for `U_N = normalizedCentredAtomicTest φ z_N c_N N`:

- `‖U_N‖_{L²}² = (∫ φ²) / c_N`,
- `weilQuad(U_N) ≤ C (log N) / c_N`,
- `W₈(U_N) ≥ (e⁻⁸ ∫ φ² / (3 c_N)) N⁸`.

For the unit-`L²` source `Ũ_N = U_N / ‖U_N‖_{L²}`, `weilQuad(Ũ_N) + B_R ‖Ũ_N‖_{L²}² ≤ C' log N + B_R` while `W₈(Ũ_N) ≥ (e⁻⁸ / 3) N⁸`, refuting unrestricted atomic Gårding at every `R > 0`.

Reason for failure: in `U_N` for `n ≪ N / c_N`, individual atoms are separated (`c_N / n` width vs `1 / n` spacing), so the continuum `L²` form `weilQuad(U_N)` sees isolated bumps of cost `O(log N)` while `W₈(U_N)` grows as `(N / n)⁸`; the missing `(N / n)⁷` factor lives in the discrete high-frequency aliasing part of `completeWeilMatrix` (`poleDefect` / `aliasingEnergy`), which `weilQuad(U_N)` drops below the overlap collar.

## No-go closure

- **Exact killing theorem/mechanism:** Separated prefix atoms (`n = 1, 2`) have `weilQuad(Ũ_N) = O(log N)` by translation invariance onto `[0, 2]`, while recentred exponential mass satisfies `W₈(Ũ_N) ≳ N⁸`.
- **Strongest positive survivor:**
  1. **Unconditional Collar Atomic Gårding:** On the overlapping top collar `Ioc (N / linearDefectCutoff c_N) N` (with no conductor-orthogonality restriction), for every `R > 0` there exist `B_R ≥ 0` and `a_R > 0` such that eventually `weilQuad(U_y) + B_R ‖U_y‖_{L²}² ≥ a_R W₈(U_y)`.
  2. **All-Space Window-Localized Matrix Gårding:** On the full discrete space `EuclideanSpace ℝ (PrimeHorizonIndex N)` at critical ratio `R > 0`, there exist a logarithmic window cutoff `Λ_R` (`log Λ_R = O(log R + 1)`), `B_R ≥ 0`, and `a_R > 0` such that `(1 / c_N) ⟨B_N x, x⟩ + B_R ‖W_{win,N}‖_{L²}² ≥ a_R (W₈(W_N) + (1 / c_N) ∑_{m ≤ Q₁} E_m b_m² + b₁² / log N + (‖u₀‖² + ‖u₁‖²) / c_N)`.
- **New insight:** Replacing unrestricted continuum `weilQuad(U_N)` by collar-restricted `weilQuad(U_y)` plus discrete prefix/conductor reserves on `completeWeilMatrix` recovers the full `W₈` Gårding control at every fixed `R > 0`, confines every nonpositive direction to a terminal window of length `O(log R + 1)`, and implies `log R_c(ζ) ≳ a*(ζ)`.
- **Status:** Dependency-closed paper proof in `critical-ratio-window-confinement-and-threshold-law.md`; Lean formalization in `CriticalArithmeticCorrelationTheory/UnrestrictedAtomicGardingFailsAndCollarGardingHolds.lean` and `CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean`.

## Log
- 2026-11-07 — falsified with positive collar and window-localized Gårding survivors
