# Zeta density preserves the minimal-face counterexample

- **ID:** A83
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every `0<Θ≤1/2`, there is a tempered zero configuration with ordinate gap at least `4`, a logarithmic local count bound, zeta's leading ordinate density, and unattained top `1/2+Θ`. Its trace exceeds every fixed floor on arbitrarily late windows of a monotone radius tending to infinity and satisfying `R(T)/log T→0`.

## Proof

Project zeta's zeros horizontally to the critical line, adding multiplicities at equal ordinates. Every finite ordinate-window count is preserved exactly. The unchanged local count proves temperedness. Positivity on the critical line bounds the entire complex lag trace by its value at zero.

The off-line minimal-face tower contributes `o(T log T)` zeros: doubling bounds the sum of base ordinates through level `k` by twice the last ordinate; the prefix count is at most `64(k+1)T`, while `log Γ_k≥(Θ/7)k²`. Add the critical background to this sparse tower. Counts add exactly, the top remains unattained, and the extra trace changes every floor by only one fixed constant. The original growing sub-logarithmic windows therefore survive.

## Formalization

- `ZeroConfigurationGeometry/TheCriticalProjectionPreservesTheCounts.lean`: `criticalProjectionConfig_N`, `temperedConfig_criticalProjection_zeta`.
- `ZeroConfigurationGeometry/TheZetaDensityBackgroundHasBoundedTrace.lean`: `zetaDensityBackground_trace_bound`, `N_add_zetaDensityBackground`, `trace_sub_le_add_zetaDensityBackground`.
- `SurfaceOfSpecZ/ScaleLocality/TheMinimalFaceCounterexampleHasZeroRelativeDensity.lean`: `minimalFace_count_small_relative_to_T_log_T`.
- `ZeroConfigurationGeometry/TheMinimalFaceSurvivesZetaDensity.lean`: `exists_zetaDensity_subLog_counterexample`.
- All four modules passed Lean checks and are wired into their programme umbrellas. Axiom audits omitted as requested.

Projection alone preserves exact counts. Superposition with the sparse tower preserves leading density, with count difference `o(T log T)`.
