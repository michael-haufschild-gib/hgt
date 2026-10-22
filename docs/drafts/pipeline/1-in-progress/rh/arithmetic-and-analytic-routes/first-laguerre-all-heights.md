# First Laguerre inequality at every height

- **ID:** first-laguerre-all-heights
- **Stage:** 1-in-progress
- **Type:** OPEN TARGET (implied by RH; not known unconditionally)
- **Target.** `L₁(t) := Ξ'(t)² − Ξ(t)Ξ''(t) ≥ 0` for every real `t`. Up to a positive factor this is the order-`k = 1` slice coefficient `c₂(t)` of `ξ(½+x+it)ξ(½−x+it)` (route 3 window, `high-order-slice-positivity.md`).

## Phase 1 — corpus state (all [L])
- **Divisor identity** (`XiLaguerreZeroSumIdentity`, `XiLaguerreWindowPositivity`): for `Ξ(t) ≠ 0`,
  `L₁(t) = Ξ(t)² Σ_q ((t−γ_q)² − δ_q²)/((t−γ_q)² + δ_q²)²`, where `δ_q = Re ρ_q − ½`. Every on-line copy contributes `(t−γ_q)^{−2} > 0`. An off-line FE pair contributes `2((t−γ)²−δ²)/((t−γ)²+δ²)²`, which is negative exactly on the disk `|t−γ| < |δ|` and equals `−2/δ²` at `t = γ`.
- **Unconditional ranges:**
  - `L₁ > 0` for `|t| ≤ 4`, and `L₁ ≥ 0` for `|t| ≤ 58/5` (off-line copies have `|γ| > 12.1`);
  - `L₁ > 0` wherever the unit window around `t` contains only on-line copies.
- **Separation / companion law** (`XiLaguerreSeparation`): if `L₁(γ) ≥ 0` at the ordinate of a pair `(γ, δ)`, then `2/δ² ≤ 16(C + log(|γ|+4))(1 + d^{−2})`, with `d` the distance to the other copies. So an off-line pair closer to the line than `≈ d/√log γ` needs companions.
- **Reader** (`CompletedFluxLaguerreReader`): `L₁ = −Ξ²·(second completed-flux coefficient)`. The coefficient splits exactly into prime and archimedean parts.

## Phase 2 — literature (2026-09-26 web search)
- No unconditional proof of `L₁(Ξ)(t) ≥ 0` for all real `t` was found.
- Related results:
  - complex Laguerre positivity of `F` (`ξ(½+z)=F(z²)`) on `Re u ≥ −0.1613` (alphaXiv 2609). On the real line of `Ξ` (`u = −t²`) this covers only `|t| ≤ 0.4`;
  - Csordas–Dimitrov second-level concavity of the kernel Φ (arXiv 2608.19160), which concerns Φ, not Ξ;
  - Turán inequalities for the Maclaurin coefficients (Csordas–Norfolk–Varga).

## Phase 3/4 — analysis of the target (paper)
1. **Where `L₁` can fail.** Only inside the disk of an off-line pair, and only if that pair's negative mass (at most `2/δ²` in size) exceeds the positive background from all other copies at `t`.
2. **Far pairs are not the issue.** A pair with `δ ≈ 0.4` contributes at least `−12.5`. The background from on-line zeros at typical height has size `(log t)²` or more. So `L₁` failures at large height come from **near-line pairs** (`δ ≲ 1/log t`) that are **isolated** (no companion within about `δ`).
3. **`L₁ ∀t` does not imply RH in the analytic class.** Surgery on the Hadamard product that replaces a real quadruple at large height by an off-line quadruple with `δ = 0.4` keeps FE, order one and the growth, and keeps `L₁ ≥ 0` wherever the background exceeds `12.5`. The target is therefore strictly weaker than RH within that class. Any proof must still use the Euler product: surgery with `δ` tiny breaks `L₁` while keeping every analytic input (deformation-obstruction law).
4. **Reduction to one local configuration.** A failure point `t` requires `Z` (Hardy's function) to have, near `t`, a positive local minimum or a negative local maximum at scale `δ`. That is a "missing sign change" of size about `δ²`.
5. **Heat-flow identity** (paper, new here). For `H_λ(t) = ∫ e^{λu²}Φ(u)cos(tu) du` (so `∂_λH = −H''`):
   `L₁(H_λ)(t) = H'_λ(t)² + ½ ∂_λ[H_λ(t)²]`.
   So a Laguerre failure at `(t, λ)` forces `|H_λ(t)|` to decrease strictly in `λ` there, faster than `H'²/|H|`.

## Open core
Exclude isolated near-line off-line pairs: a pair with `|δ| ≲ d/√log γ` and no companion within about `δ`. In Hardy's function this is: `Z` has no positive local minimum (and no negative local maximum) whose depth is below the Laguerre background. No unconditional pointwise tool reaches this scale:
- local counts give only `O(log t)`;
- short-interval on-line zero results (Hardy–Littlewood, Karatsuba) work at scales `t^ε`, not `O(1/log t)`;
- zero-density results give density only (wall 3).

## Log
- 2026-09-26 — card opened at the user's direction. Phases 1–4 (paper) done: target open; failure set = isolated near-line pairs; not implied by analytic inputs; heat-flow identity.

## Phase 3/4 — mechanism candidates and verdicts
- **M1 (modulus monotonicity).** At a Laguerre failure `t*` with `Ξ'(t*) = 0`, harmonicity of `log|ξ|` gives `∂_σ² log|ξ| = −∂_t² log|Ξ| < 0` at `½+it*`, together with `∂_σ log|ξ| = 0` there by the FE. So `σ ↦ |ξ(σ+it*)|` has a local maximum on the line. Excluding this is the LA receiver "`|ξ|` nondecreasing in `σ ≥ ½`" (F0269, equivalent to RH). Verdict `CIRCULAR`.
- **M2 (Hadamard receiver trace).** `L₁/Ξ² = ∂_σ Re(ξ'/ξ)(σ+it)|_{σ=½}`. The Euler product controls `(ξ'/ξ)'` only for `σ ≥ 1+η`. Continuing inward to `σ = ½` requires the zeros of the strip; this is the saddle-in-strip wall of CANNOT-470. Verdict `CIRCULAR`.
- **M3 (heat flow).** `L₁(H_λ) = H'² + ½∂_λ(H²)`. A failure forces `|H_λ(t)|` to decrease in `λ` faster than `H'²/|H|`. That is correct but gives no sign at `λ = 0`. Verdict `INSIGNIFICANT` (identity only).
- **M4 (Pólya-approximation perturbation).** Pólya's `Ξ*` (the `n = 1` kernel term) has only real zeros, but `Ξ − Ξ*` has the same size as `Ξ` beyond small heights, since it carries the `ζ − 1` part. Verdict `FALSE` as an all-heights mechanism.
- **M5 (Turing / `S(t)` integrals).** An isolated off-line pair shifts `N − N₀` by 2. The unconditional bound `∫S = O(log T)` only forces compensation within `O(log T)`; it does not exclude the pair. Verdict `INSIGNIFICANT` (Turing's method verifies, it does not exclude).

## Status after the first cycle
The target is equivalent in difficulty to excluding isolated near-double zeros (near-line FE pairs without companions). That is an open problem adjacent to the simplicity of zeros: the known 67.25% simple-critical proportion (in Lean) is density-only. None of M1–M5 survives. The Euler product must enter pointwise on the line, where no tool reaches.
- **M6 (bad-extremum count).**
  - Between consecutive real zeros of Ξ, `Ξ'` changes sign `1 + 2·(bad extrema)` times; a bad extremum is a positive local minimum of `|Ξ|`.
  - The argument principle on `ξ'/ξ` (`N₁ − N = O(log T)`) gives `#bad(T) = (N_off(T) − N'_off(T))/2 + O(log T)`, where `N'_off` counts off-line zeros of `ξ'`.
  - An isolated near-line pair gives one bad extremum and no off-line zero of `ξ'`. A far pair gives off-line zeros of `ξ'` and no bad extremum.
  - So the count equals the number of isolated near-line pairs up to `O(log T)`: an exact restatement of the open core. Verdict `CIRCULAR`. A Levinson–Montgomery-type comparison `N'_off ≥ N_off − O(log T)` for `ξ'` would give `#bad = O(log T)`, but that comparison is itself the open core.
- 2026-09-26 — cycle 1 closed: M1–M6 give no mechanism. The open core is now stated exactly: isolated near-double zeros, equivalently bad extrema of `Z`.
