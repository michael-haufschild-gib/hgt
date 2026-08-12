# Mass-shifted projective Gauss-root renewal

- **ID:** `mass-shifted-projective-gauss-root-renewal`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Retained adaptive mixed/completed projective work is exactly current Gauss-root
  spread plus terminal trace mismatch plus current Christoffel edge; hard-edge root spread has
  exact weight four under `z=2yX-1`.

## Gates

- [x] 0 → 1: hostile alternatives and exact invariant isolated
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: direct Lean check, targeted build, forbidden-declaration scan, axiom audit
- [ ] 3 → 4: publication-ready

## Conjecture / proof-or-fail loop

1. Adjacent scalar projective clocks order automatically. **Failed:** exact numerator has
   uncontrolled terminal diagonal shape.
2. Newborn Christoffel edge carries a uniform work fraction. **Failed:** generic positive Jacobi
   data permit arbitrarily small edge ratios.
3. Retained Jacobi inventory is actual admission-root spread. **Proved exactly:** Vieta plus the
   coefficient-jet energy law identify accumulated alpha dispersion and beta inventory with the
   centered quadratic spread of all roots of the current monic admission.
4. Hard-edge scaling obscures that spread. **Falsified:** affine transport multiplies it by exactly
   `4y²`, so normalized collapse is literal hard-edge root concentration.
5. Root concentration alone contradicts a nonzero Paley--Wiener limit. **Not yet proved:** raw
   real-rootedness lacks an interval bound pre-RH, and a rigorous concentration-to-angular-energy
   bridge must control a sublinear outlier set. No such claim is smuggled into Lean.

## Exact law

For roots `r_(n,k)` of current monic admission, put

```text
G_n = sum_k r_(n,k)^2 - (sum_k r_(n,k))^2 / n.
```

Finite positive-block Vieta and coefficient-jet identities give

```text
sum_k r_(n,k)   = sum_(j<n) alpha_j,
sum_k r_(n,k)^2 = sum_(j<n) alpha_j^2 + 2 sum_(j<n) beta_j,
G_n = lower-alpha dispersion + 2 sum_(j<n) beta_j > 0.
```

Hence retained inventory is exactly

```text
R_n = 2(2n+1) G_n
      + (2/n)(sum_(j<n) alpha_j - n alpha_n)^2
      + 2(2n+1)(n+1) beta_n.
```

Together with next-admission renewal,

```text
h_n mathfrak S_n = 2(2n+1)(n+1) h_(n+1) + h_n R_n.
```

If `z=2yX-1`, centered root spread obeys `G_n^hard=4y²G_n` exactly.

## Higher universal principle

Projective arithmetic work is a four-account conservation law: newborn edge capital, empirical
hard-edge root spread, terminal trace mismatch, and current edge reserve. Scalar-clock failure was
loss of this internal decomposition. Effective cofinal collapse is no longer an unspecified lack
of uniformity; it is simultaneous hard-edge point concentration and boundary-edge collapse.

## Honest residual

Completed-source compactness gives nonzero strong `L²` Paley--Wiener limits at parabolic first
contact. Closing route requires proving such tight finite-type packets cannot arise when empirical
hard-edge root spread and both boundary accounts collapse. Standard Bernstein inequalities give
only degree ceiling; audited restricted-zero variants do not supply this moving-root concentration
incompatibility. This is not yet RH.

## Lean

Module:
`GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal`

Key declarations:

- `HTGeometry.multisetQuadraticSpread_map_affine`;
- `HTGeometry.monicOrtho_roots_sum_eq_sum_alpha_below`;
- `HTGeometry.monicOrtho_roots_sum_sq_eq_jacobiEnergy_below`;
- `projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory`;
- `projectiveGaussRootSpread_pos`;
- `projectiveHardEdgeGaussRootSpread_eq_four_mul_mass_sq_mul`;
- `projectiveJacobiRetainedInventory_eq_rootSpread_add_mismatch_add_edge`;
- `xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_edges_add_rootSpread_add_mismatch`;
- `xiShiftedAdaptiveMixedCompletedArithmeticSource_projectiveWork_eq_nextNorm_add_rootSpread`.

Targeted module build passed. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.
