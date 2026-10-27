# Positive coupled rigidity and the critical transfer law

- **ID:** bgg-c6
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `(F, Λ) ∈ HeightCoupledSystem 2 1 1 γ` with `−F'/F + ζ_γ'/ζ_γ = 𝓛ν + E`, `ν ≥ 0`,
  `E` holomorphic on `Re s > σ_E`, `σ_E < 1/2`, and suppose `ξ` has no off-critical zero at ordinate `γ`.
  1. (Gram law) `r(t) = ord_{1/2+it} Λ_γ − ord_{1/2+it} Λ` is even positive definite; hence
     `|r(t)| ≤ r(0)` (critical transfer bounded by the central drop).
  2. (Rigidity, `E = 0`) If `r(0) ≤ 0` then `ν(0,∞) = 0` and `F = K ζ_γ`, `Λ = K Λ_γ`, `K ∈ ℝ^×`.
  3. (Classification) `PositiveCoupledRigid γ ⟺ ξ(x + iγ) ≠ 0 ∀ x`; `PositiveChiral γ ⟺` no
     off-critical zero at `γ`; `RH ⟺ ∀ γ, PositiveChiral γ`.

## Paper proof
1. Perturbed positive-deformation theorem: abscissa `c ≤ 1/2`; on `Re z > 1/2` away from zeros,
   `Λ_γ'/Λ_γ − Λ'/Λ = 𝓛ν + E`. Along `σ + it`, `σ ↓ 1/2`, multiply by `σ − 1/2`: LHS → `r(t)`,
   `(σ − 1/2)E → 0`. So `r(t) = lim (σ − 1/2) Re 𝓛ν(σ + it) = lim (σ − 1/2) ∫ e^{−σu} cos(tu) dν`;
   each approximant is even positive definite (`Σ cᵢcⱼ cos((xᵢ − xⱼ)u) = |Σ cᵢ e^{ixᵢu}|²`), and
   pointwise limits of such functions are.
2. With `r(0) ≤ 0`: `r ≡ 0`, and off the line orders agree (positive off-line rigidity), so `Λ` and
   `Λ_γ` have the same divisor. Both are entire of order one; the entire quotient is zero-free of order
   one, so `Λ = K e^{Bs} Λ_γ`. Cancelling the common archimedean factor, `F = K e^{Bs} ζ_γ` on
   `Re s > 1`, hence `𝓛ν(σ) = −B` for all large `σ`. Two equal values of a Laplace transform of a
   nonnegative measure force `ν(0,∞) = 0`; then `B = 0`, and `K` is real by conjugation symmetry at `s = 2`.
3. `⇐`: no zero on the line gives `hoff` and `Λ_γ(1/2) ≠ 0`, so `r(0) ≤ 0` automatically. `⇒`: a
   critical zero `1/2 + iγ` admits the outward split `ζ_γ W_β`, which is rational, hence positive by the
   lattice sieve (Post–Widder weight `≥ 0`), and not proportional to `ζ_γ`; an off-critical zero gives
   the quartet contraction raising the central order by 4. Chirality: same two constructions plus 2.

## Lean
`PositiveCoupledRigidityAndTheCriticalTransferLaw.lean`: `criticalSplitMultiplier_eq_rationalMultiplier`,
`isPositiveMassDeformation_of_rational`, `exists_nontrivial_positiveDeformation_of_xi_critical_zero`,
`norm_complexLaplace_le`, `tendsto_abel_complexLaplace`, `abs_criticalTransfer_le_centralDrop`,
`isEvenPosDef_laplace_cos`, `criticalJump_isEvenPosDef`, `exists_eq_const_mul_exp_mul_of_orders_eq`,
`measure_Ioi_eq_zero_of_laplaceReal_eq`, `positiveDeformation_trivial_of_central_le`,
`PositiveCoupledRigid`, `PositiveChiral`, `positiveCoupledRigid_iff`, `positiveCoupledRigid_zero`,
`exists_gt_not_positiveCoupledRigid`, `positiveChiral_iff`, `riemannHypothesis_iff_forall_positiveChiral`.
Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
