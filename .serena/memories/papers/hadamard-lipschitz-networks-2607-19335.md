# 1-Lipschitz networks on Hadamard manifolds (arXiv:2607.19335) — CLOSED at stage 3

Card: `docs/drafts/pipeline/3-formalized/murari-2607-19335-one-lipschitz-hadamard-networks.md`
Lean: `formal/GaloisForLFunctions/HTGeometry/HadamardLipschitz/` (17 modules, all wired into
`GaloisForLFunctions.HTGeometry`, 52 audited decls on `propext/Classical.choice/Quot.sound` only).

## The one idea that replaced Jacobi fields

`BusemannFlow.dist_flow_sq_le`:  `d(Φ_h x, y)² ≤ d(x,y)² − 2h(b(x)−b(y)) + h²` for `h ≥ 0`.

Proof: apply the NPC (Bruhat–Tits) inequality on the geodesic `[x, Φ_H x]` at parameter `h/H`,
then let `H → ∞` using the *defining* Busemann property `d(Φ_H x, y) − H → b(y) − b(x)`.
Everything else (flow nonexpansiveness, Theorem 4.1, Theorem 4.4) is 3 lines from the two-point
corollary `dist_flow_flow_sq_le`.  Sharp: identity in a Hilbert space with `b = ⟪u,·⟫`.

**Consequence**: the source's Riemannian hypotheses (`C^{1,1}` activation, Lipschitz `a`, a.e.
chain rule, Hadamard *manifold*) are all removable.  Results hold on any NPC metric space with
only `a ≥ 0` and `r ↦ r − a(r)` nonexpansive.

## Reusable assets built here (were mathlib gaps)

- `NPCSpace` class (Bruhat–Tits inequality) + geodesic uniqueness (`eq_gd_of_dist`),
  betweenness NPC (`dist_sq_le_of_between`), convexity of `d(·,z)` (`dist_gd_le`);
  global instance: every real inner-product space.
- `BusemannFlow` structure + `GeodesicRay.busemann` (existence/1-Lipschitz/convexity of
  Busemann functions in any metric / NPC space).
- **Multivariate convex analysis**: `inner_gradient_le` (first-order convexity),
  `descent_lemma` (sharp `L/2`, proved by antitonicity on `[0,1]`, no integrals),
  `baillon_haddad`, `gradientStep_nonexpansive` (`τ ∈ [0,2/L]`).  Mathlib has none of these.
- `frobSq` (squared Frobenius norm) `= tr(AᵀA)`, orthogonal-congruence invariant, diagonal
  value; spectral matrix log `hermLog` with `exp (hermLog H) = H`.
- Congruence invariance of the affine-invariant matrix exponential (`spdExp_congr`).
- `artanh_sub`: `artanh a − artanh b = artanh((a−b)/(1−ab))`.
- Activations: softplus (`φ''≤1/4`), squared ReLU (`HasDerivAt` **including the kink at 0**),
  `¬ DifferentiableAt ℝ relu 0`.

## What is deliberately NOT formalised

Riemannian-only statements: `C²` regularity of Busemann functions on Hadamard manifolds, the
Jacobi-field proof, the Hessian identity in Lemma 3.2, "`S⁺⁺(n)`/`Dⁿ` are Hadamard manifolds",
and the two *cited* gradient formulas.  Mathlib has **no** Riemannian metric-connection theory
(no Levi-Civita connection, geodesics, exponential map, Hessian, Jacobi fields), so these cannot
be stated at all.  They are not needed: the metric proofs are complete and strictly stronger.

## Traps hit (worth remembering)

- `PiLp p α` has metric instances for *general* metric spaces (`PiLp.dist_eq_sum`), but
  `PiLp.dist_eq_of_L2` needs `SeminormedAddCommGroup`.
- `HasFDerivAt.sub` on real-valued functions yields the `Pi.sub` form with `RCLike`-routed
  instances: `simpa` fails, plain `exact` succeeds (defeq).
- `Matrix.exp` does not exist; it is `NormedSpace.exp` (`Matrix.exp_conj`, `exp_diagonal`,
  `exp_transpose`, `exp_add_of_commute`).  `Real.exp_eq_exp_ℝ`, `Pi.exp_def` bridge to `Real.exp`.
- Mathlib has `Real.artanh` (`Mathlib/Analysis/SpecialFunctions/Artanh.lean`) — do not redefine.
- `hasStrictFDerivAt_norm_sq` / `HasFDerivAt.norm_sq` exist in `InnerProductSpace/Calculus`.
- No Cholesky and no `Matrix.sqrt` in mathlib; the corpus has `CFC.sqrt` wrappers in
  `HTGeometry/ConstitutivePositiveConeMidpointRecovery.lean` — reuse those.
