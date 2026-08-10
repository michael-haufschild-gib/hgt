# Squarefree Euler modular-corona colligation — promoted to stage 3 (2026-08-09)

Card `squarefree-euler-modular-corona-curvature-colligation.md` moved from `2-fully-proven` to
`3-formalized` with companion card `...-formalized.md`.

## New Lean modules (all unconditional, axioms = propext/Classical.choice/Quot.sound)

- `HTGeometry/ExteriorOrderedProduct.lean` — reusable: `orderedWedge` (increasing wedge over a
  `Finset` in a `LinearOrder` index), `orderedWedge_eq_basis` (agrees with mathlib's
  `Module.Basis.ExteriorAlgebra`), `orderedWedge_insert` (adjoining a max multiplies on the right —
  no permutation sign), `orderedPluckerProduct_eq_sum` (Plücker expansion).
  Key trick: `sort_insert_of_forall_lt` proves `(insert a T).sort = T.sort ++ [a]` via
  `Perm.eq_of_pairwise'`, so `permOfDisjoint` signs are never needed.
- `RHTower/SquarefreeExteriorHorizonLift.lean` — occupation configs ≃ squarefree subsets, the
  exterior-horizon identification, source coefficient = Plücker coordinate, source = ordered
  exterior product. Needs a `local instance LinearOrder Nat.Primes` (mathlib has none; same
  pattern as `RouteEProductTruncatedReservoirMass`).
- `RHTower/SquarefreeCriticalFockEscape.lean` — vacuum overlap `Z(σ)⁻¹`, weak nullity, no strong
  `ℓ²` limit, four-unit tangent residue survives.
- `RHTower/SquarefreeCoronaPrimeCurrentField.lean` — `j(s)_p = (log p)p^{-s}/(1+p^{-s})` is a
  holomorphic `ℓ²(Primes)`-valued field on `Re s > 1/2`. The series is NOT absolutely convergent in
  `ℓ²` norm, so `Complex.differentiableOn_tsum_of_summable_norm` does not apply: holomorphy comes
  from `TendstoLocallyUniformlyOn.differentiableOn` with the tail bound
  `‖field − section_T‖² = ∑_{p∉T}‖coeff‖² ≤ ∑_{p∉T} u_p → 0` (`tendsto_tsum_compl_atTop_zero`).
- `RHTower/SquarefreeCoronaCodiagonal.lean` — `∑_{p,k}(log p)(p^{-s})^{k+1} = −ζ'/ζ` (prime-power
  Laplace channel), codiagonal `∑_p j(s)_p = A(s) − 2A(2s)` via the alternating expansion with the
  even part reindexed to `A(2s)`, and the no-go `not_exists_bounded_coronaCodiagonal` (normalized
  indicator of N coordinates has sum `√N`).
- `RHTower/SquarefreeCarlemanDeterminant.lean` — `A_s` Hilbert–Schmidt (via
  `HTGeometry.isHilbertSchmidt_ellTwoDiagonal_iff`), `I+A_s` boundedly invertible (uniform
  acyclicity), `D₂ = exp(∑ log(1+p^{-s}) − p^{-s})` nonvanishing + holomorphic, Weierstrass
  product, and `Z = D₂ exp(P)` on `Re s>1` (reuses `squarefree_eulerProduct_tprod`).
- `RHTower/SquarefreeCarlemanLogExpansion.lean` — `log D₂ = ∑_{k≥2}(−1)^{k+1}P(ks)/k` (reuses
  `HilbertSchmidt.hasSum_peri` from `FredholmDeterminantZeta`), `−P' = ∑_p (log p)p^{-s}`, and
  `J_sq = −D₂'/D₂ − P'`.
- `RHTower/SquarefreeDeterminantLineChernMetric.lean` — Chern coefficient of `h_S = Z_S(Re s)⁻¹`
  equals `V_S/4` (plane Laplacian of a potential depending only on `Re s`).

## Reused, do not rebuild

`tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq` (four-unit law), `squarefreeFixedCurrent`
and `neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent`, `squarefree_eulerProduct_tprod`,
`natCast_pow_cpow` (MFreeLadder), `summable_abs_log_natCast_pow_mul_rpow_neg` (EulerFisherCurvature),
`eulerPrimePowerNat_injective`, `vonMangoldtLSeriesTerm_support_primePower`,
`HTGeometry.ellTwoDiagonal` layer, `HilbertSchmidt.lpBasis`/`memℓp_of_sq`/`lp_norm_sq_eq`.

## Repo state note

`lake build GaloisForLFunctions.RHTower` is green. `lake build GaloisForLFunctions.HTGeometry`
fails on `HTGeometry/MatrixSemicircleAnalyticLaw.lean`, an untracked in-progress module from a
concurrent session (unrelated to this work); the lint gate also reports four unreachable modules
owned by other sessions.
