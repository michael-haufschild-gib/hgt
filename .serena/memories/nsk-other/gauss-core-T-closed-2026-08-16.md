# Gauss card: the named open core (T) is proved

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/gauss-component-quasi-inner-residue-hierarchy.md`
(passes 43 and 44 at the end of the card record everything below).

## What is new in the tree (all unconditional, axiom-clean, umbrella-wired)

- `HTGeometry/LatticeTailSums.lean` — six elementary `ℤ`-lattice weights in `ℝ≥0∞`:
  quadratic tail `≤ 4/(1+J)`, harmonic band `≤ 2(1+log(J+2))`, punctured power band
  `≤ 2N^(1-t)/(1-t)`, counting band `≤ 2N`, punctured harmonic band `≤ 2(1+log N)`.
  Built on mathlib `sum_Ioo_inv_sq_le` and corpus `HTGeometry.sum_rpow_sub_one_le`.
- `RHTower/GaussShiftRatioWeight.lean` — `gaussShiftRatio`, the ratio-weighted Parseval identity
  `‖S̃v‖² = Σ ρ_l²‖v̂(l)‖²`, and the two regime bounds
  (`ρ² ≤ 1+2K` off the spike; `ρ² ≤ 1 + (Kn/|n+l|)^(1/2)` for `m ≥ 2`).
- `RHTower/GaussSpikeBandSum.lean` — `Σ_(2|n+l|<n) ρ_l² ≤ (2+4K^(1/2))·n`.
- `RHTower/GaussDefectHighModeTail.lean` —
  `Σ_(|j|>J) (A/(1+|j|))²‖defect_j‖² ≤ 16A²(1+K)/(1+J) + 16KA²(1+log n)/n`.
- `RHTower/GaussLowModeKernelBound.lean` — separation of spike from low band, the kernel bound on
  a truncation, `‖defect_j‖ ≤ 5+3K` on the low band, and the `ℓ¹` log bound.
- `RHTower/GaussSpikeDefectVanishing.lean` — the assembly and **(T)**:
  `tendsto_norm_gaussShiftedBlockDiag_invSq_defect_zero`.

## The key simplification

Carry the exponent `1/2`, not `1/m`.  For `m ≥ 2`, `ρ⁴ ≤ ρ^(2m) ≤ Kn/|n+l|` gives
`ρ² ≤ 1 + (Kn/|n+l|)^(1/2)` and every estimate closes at that one exponent, uniformly in `m`.
Also: split at the operator level (`S̃(B⁻²w) = S̃(B⁻²w') + S̃(B⁻²w'')`) so the two regimes are never
recombined inside one sum.  And `‖defect‖ ≤ 1 + ‖defect‖²` avoids all square roots on the low band.

## What remains on the card

1. Restate (T) with `B^(-2)` replaced by an arbitrary member of the piecewise-exponential algebra
   (the proof uses only `|ĉ(k)| ≤ C/(1+|k|)`, which `norm_fourierCoeff_of_isExpPiecewise` gives).
2. Run the `m`-fold telescope of pass 30 in the *relative* form, using (T) plus the already-proved
   `tendsto_norm_gaussShiftedBlockDiag_sub_rotationInv_family` for the second bracket of
   `R̃ f - a_δ f`.
Then `gaussPrincipalDiagonalTerm_logResidue` and `gaussLocalFactorWeight_mul_principalResidue`
(already general in `m`) finish the card.
