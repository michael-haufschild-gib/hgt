# Card `projective-ht-horizon-symmetric-space-boundary`: boundary layer + isometric action

Fourteen modules now carry this card, all in the `HTGeometry` umbrella, axioms
`[propext, Classical.choice, Quot.sound]`, `lake build GaloisForLFunctions.HTGeometry` green
(15102 jobs).

## Layers
1. **Metric** — `MatrixCompound`, `TopSumMajorization`, `CompoundKyFan`,
   `ObserverTriangleInequality`, `ObserverDistanceSymmetry`, `ObserverMetricSpaceStructure`:
   `observerDist` is a `MetricSpace` (see `mem:research/observer_metric_space_complete_2026_08_06`).
2. **Flats and rays** — `FlatGeodesicIsometry`.
3. **Analytic core** — `LieTrotterProduct`, `GoldenThompsonNorm`, `ExponentialMetricIncreasing`
   (see `mem:research/emi_program_next_step_2026_08_06`).
4. **Boundary** — `ObserverBoundaryAtInfinity`, `ObserverBoundaryBuilding`,
   `ObserverBoundaryEquivariance`.
5. **Isometric action** — `ObserverCongruenceIsometry`:
   `congrOp g P = g* P g`, and **`observerDist_congrOp`**:
   `observerDist (g* P g) (g* Q g) = observerDist P Q` for an arbitrary `g : E ≃ₗ[ℂ] E`.

The congruence proof avoids eigenvalue-uniqueness: `X = (g* P g)^(-1/2) g* P^(1/2)` preserves inner
products and carries the eigenframe of `relOp P Q` onto one of `relOp (g*Pg) (g*Qg)` with the same
weights.  Reusable by-products: `invSqrtOp_comp_invSqrtOp`, `apply_invSqrtOp`, `isSymmetric_congrOp`,
`inner_congrOp_pos`.

## What is left on the card
Only the **basepoint-change theorem**: every geodesic ray is asymptotic to exactly one ray from any
prescribed point.  That is the CAT(0) statement; with it, the isometric action of the whole observer
group (now proved) descends to the boundary, and `(3)` is fully `PGL`-equivariant.  A concrete route:
by polar decomposition it suffices to treat `g` positive definite, i.e. to show `t ↦ p exp(tT) p` is
asymptotic to a ray from the identity; the candidate direction is read off the flag of `T` moved by
`p`, and the estimate is the remaining work.

Also open: the Tits metric *between different apartments* (inside one apartment it is the chordal
formula `|t| √(2−2⟪w,w'⟫)`, proved in `ObserverBoundaryAtInfinity`).

## Lean traps hit in this layer
- `(g : E →ₗ[ℂ] E) v` and `g v` are defeq but not syntactically equal; normalise with
  `simp only [LinearEquiv.coe_coe]` before `rw`, and use `LinearEquiv.apply_symm_apply` via `simp`
  rather than `rw [show … from g.apply_symm_apply _]`.
- `rw [← h]` where the rewritten variable occurs on both sides of the goal rewrites both; use
  `conv_lhs => rw [h]`.
