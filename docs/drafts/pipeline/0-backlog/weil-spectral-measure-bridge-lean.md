# Lean bridge: from Weil positivity to spectral measures (and the Ξ-positivity rigidity lemma)

- **ID:** MC-WEIL-SPECTRAL-BRIDGE
- **Stage:** 0-backlog
- **Type:** THEOREM (paper) → Lean infrastructure
- **Source:** MC conjecture loop, cycles 154–155 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`)
- **Statement (target lemma):** Let `W ≥ 0` be an even, translation-bounded measure on `ℝ` supported in `{|u| ≥ log 2}`, and let `K = Φ⋆Φ̃` be the autocorrelation of Riemann's kernel. If `K⋆W` is a positive-definite function, then `W = 0`.

## Why
- The lemma gives Theorem C downward (order rigidity for deletions) without RH and without a Herglotz representation. It is also the downward half of Theorem C′. Apply it to `W_d = Σ d(n)n^{−½}(δ_{log n} + δ_{−log n})`: positive definiteness of `K⋆W_d` is exactly full-cone Weil positivity of `Λ − d` on the near-null tests `Φ⋆q`.
- The same bridge from positive-definite functions and forms to measures is what the measure forms of L107 and L150–L153 need.

## Paper proof
1. `T = FT(W)` is positive-definite and tempered.
2. By Bochner, `Ξ²T = FT(K⋆W) ≥ 0`. So `T` is a positive measure off the real zeros `Z` of `Ξ`.
3. The positive-definite bound `|T⋆P_η(t)| ≤ T⋆P_η(0) = O(1/η)` makes `T` a signed measure with atoms `c_γ` at `Z` and no worse singularities, and gives `|c_γ| ≤ a₀ = T({0})`.
4. The Fejér kernel `F_b`, `b < log 2`, satisfies `∫F_b dT = 0`. Hence `0 ≥ a₀(F_b(0) − Σ_Z F_b(γ))`.
5. `Σ_Z F_b(γ) ≤ 0.39 F_b(0)` at `b = 0.69`, from `Σ_Z 1/(¼+γ²) ≤ 2 + γ_E − log 4π`, unconditionally. So `a₀ = 0`, then `T ≥ 0`, then `T = 0`.

## Lean inventory and plan
- **Present:**
  - `HTGeometry/SchwartzPositiveMeasureRepresentation.existsUnique_temperateSpectralRepresentation` (Bochner–Schwartz for continuous, momentum-symmetric, nonnegative Schwartz forms);
  - `HTGeometry/HerglotzRepresentationDisc.exists_herglotz_representation`;
  - Mathlib Prokhorov (`isCompact_closure_of_isTightMeasureSet`) and Lévy convergence;
  - corpus `PositiveDefiniteOnReal`.
- **Missing:**
  - (a) Bochner for continuous positive-definite functions on `ℝ`. Route: lattice Fejér densities on the circle, Prokhorov on the circle, pushforward to `ℝ`, lattice tightness via the Fejér kernel bound `F_K(θ) ≤ π²/((K+1)θ²)`, then Prokhorov on `ℝ`.
  - (b) The structure of `T = FT(W)` near `Z`: a signed measure with atoms. This is the heavy step. An alternative is to define atoms through Fejér means `(2π/λ)∫F_λ(·−γ)dT` and prove the Fejér inequality directly.
  - (c) The zero-sum bound `Σ_Z 1/(¼+γ²) ≤ 2 + γ_E − log 4π` in Lean. Check the corpus Hadamard modules.

## Log
- 2026-09-30: created from MC cycles 154–155.
- 2026-09-30: item (a) done. `HTGeometry/BochnerPositiveDefiniteReal.exists_charFun_eq_of_positiveDefinite` (continuous PD ⇒ `charFun` of a finite measure), axiom-clean and wired into `HTGeometry.lean`. Lattice-Fejér route: nonnegative lattice densities, lattice characteristic values `(#pairs/(N+1))φ(lh)`, Fejér tail bound, Prokhorov, Lévy, dyadic density. Items (b) and (c) remain.
