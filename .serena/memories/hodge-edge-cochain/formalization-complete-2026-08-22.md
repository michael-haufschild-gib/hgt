# arXiv:2608.19360 (Boudourides, Hodge coercivity / two-field edge cochains) — fully Lean-closed

Card: `docs/drafts/pipeline/3-formalized/hodge-coercivity-two-field-edge-cochain.md`
Modules: `formal/GaloisForLFunctions/HTGeometry/HodgeEdgeCochain/` (7 files, wired into
`GaloisForLFunctions.HTGeometry`). Axiom audit: 61 declarations, all
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

## Coverage
Every numbered item is proved: (1)–(21), Lemma 1/2/3, Proposition 1/2, Theorem 1/2/3/4/5,
Remark 1 (sharp form). §6 + Appendices A–D are the deterministic numerical study and are
excluded (computations; the paper says their residuals are not used as assumptions).

## Reusable infrastructure this built (search here before rebuilding)
- `exists_solution_of_bounded_lipschitz` — **globally bounded + globally Lipschitz
  time-independent vector field has a solution on every `[-T,T]`**, with no smallness restriction
  on `T`. Mathlib only has local Picard–Lindelöf; this is the missing global step. Built from
  `IsPicardLindelof.of_time_independent` with `a := L*T`, `r := 0`.
- `cutoff`, `truncField`, `norm_truncField_le`, `norm_truncField_sub_le` — the continuation device.
  **Key trick:** cut the *whole* field off by a scalar `χ_R(‖x‖) ∈ [0,1]`. A scalar multiple of the
  entire field preserves the exact energy-cancellation identity, so the a priori bound applies to
  the truncated system *directly* — no first-exit-time argument. Then pick `R` above the a priori
  bound on `[0,T]` so `χ = 1` along the trajectory.
- `exists_pos_forall_mem_smul_norm_sq_le` / `exists_attained_forall_mem_smul_norm_sq_le` —
  continuous 2-homogeneous function positive off `0` on a submodule of a f.d. space dominates
  `λ‖·‖²`, with the sharp constant attained. This is the compactness step behind any coercivity
  criterion; corpus previously had only matrix-specific (`posDef_coercive`) and Hermite-specific
  versions.
- `bilinearCLM` — in finite dimension every bilinear map is a continuous bilinear map
  (`E →ₗ E →ₗ E` → `E →L E →L E`).
- `le_gronwallBound_of_hasDerivAt` — mathlib's `le_gronwallBound_of_liminf_deriv_right_le` fed by
  a genuine `HasDerivAt` (via `HasDerivWithinAt.liminf_right_slope_le`).
- `AdmissibleSystem` + `orbit`/`flow`/`orbit_add`/`continuous_flow` — a forward semiflow from an
  ODE by choice + uniqueness, and its continuity in the initial state from a Grönwall difference
  estimate. Attractor facts come from mathlib `omegaLimit` (`Mathlib/Dynamics/OmegaLimit.lean`).

## Traps hit
- `Norm (↥W →L[ℝ] ↥W →L[ℝ] ↥W)` for a **submodule** `↥W` fails to synthesize with the default
  `maxSynthPendingDepth 1`. Fix: `set_option maxSynthPendingDepth 3` at file level. It works fine
  for an abstract `E`; only the submodule instance chain trips.
- `le_or_lt` does not exist in this toolchain — use `le_or_gt`.
- `Submodule.starProjection_apply_eq_zero_iff` has `K` **explicit**, so `.mpr` dot-notation fails;
  write `(Submodule.starProjection_apply_eq_zero_iff K).mpr`.
- `open scoped RealInnerProductSpace` gives `⟪x, y⟫` (no subscript); for `⟪x, y⟫_ℝ` use
  `open scoped InnerProductSpace`.
- `WithLp` is a structure: build `EuclideanSpace` elements with `WithLp.toLp 2 f`; coordinates are
  `x i = x.ofLp i`; pointwise simp lemmas are `PiLp.add_apply` / `PiLp.smul_apply`.
- `mathlib`'s `omegaLimit` invariance theorem is stated for a bundled `Flow` (needs *joint*
  continuity). Avoid that by replaying its proof with `mapsTo_omegaLimit` +
  `omegaLimit_subset_of_tendsto`, which only need `Continuous (ϕ t)` per `t` and the semigroup law.

## Design note worth reusing
Coercivity is carried through the whole energy layer as a **set parameter** `W`
(`hcoe : ∀ v ∈ W, lam * ‖v‖^2 ≤ ⟪A v, v⟫`) plus trajectory membership. `W = univ` gives the
coercive whole-space theorems; `W = Set.range P₀` gives the harmonic-fibre theorems on `V₀`
without duplicating a single proof.
