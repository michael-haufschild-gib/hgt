# 1-Lipschitz neural networks on Hadamard manifolds (arXiv:2607.19335)

- **ID:** hadamard-lipschitz
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Murari, Ghirardelli, Adcock, Celledoni, Owren, Schönlieb, *1-Lipschitz Neural
  Networks on Hadamard Manifolds*, arXiv:2607.19335 (math.NA / cs.LG)
- **Statement:** Every theorem, lemma, corollary and provable remark of the paper is
  unconditionally Lean-proved, in the strictly larger generality of **NPC (Hadamard) metric
  spaces** rather than Hadamard manifolds, and with weaker regularity hypotheses.

## Goal

The paper builds 1-Lipschitz manifold-valued network layers out of gradient steps of Busemann
potentials.  Its proofs are Riemannian (Jacobi fields, Hessians, `C^{1,1}` activations), and
mathlib has no Riemannian geometry at all: no Levi-Civita connection, no exponential map, no
Jacobi fields.  The formalisation therefore *replaces* the Riemannian argument by a metric one
which is both complete and strictly stronger.

## What replaced the Jacobi-field argument

The single new inequality is `BusemannFlow.dist_flow_sq_le`:

```
d(Φ_h x, y)^2 ≤ d(x,y)^2 - 2h (b(x) - b(y)) + h^2 ,   h ≥ 0 ,
```

derived from the NPC (Bruhat–Tits) inequality alone by comparing on the geodesic `[x, Φ_H x]`
and letting `H → ∞`, using the *defining* Busemann property `d(Φ_H x, y) - H → b(y) - b(x)`.
On a Hilbert space with `b = ⟪u,·⟫` it is an identity, so it is sharp.  From it:

* nonexpansiveness of the flow (`flow_nonexpansive`) — no longer an axiom;
* the two-point estimate `dist_flow_flow_sq_le`, from which Theorem 4.1 and Theorem 4.4 are
  three lines each, with **no** regularity assumption on the time reparametrisation `a`.

## Coverage map (paper item → Lean name, module `GaloisForLFunctions.HTGeometry.HadamardLipschitz.*`)

| Paper | Lean |
|---|---|
| Def. 2.1 | `QuasiFirmAt`, `QuasiFirmlyNonexpansive` (`QuasiFirm`) |
| Thm. 2.2 | `tendsto_iterate_of_quasiFirmAt`, `tendsto_iterate_of_quasiFirmlyNonexpansive` (`FixedPointIteration`) |
| Prop. 2.3 | `quasiFirmAt_comp`, `alpha_comp_eq` (`QuasiFirm`) |
| Thm. 2.4 | `quasiFirmAt_gd`, `gd_fixedPoint_iff` (`QuasiFirm`) |
| Thm. 2.5 | `quasiFirmAt_of_geodesicFamily` (`QuasiFirm`), `busemannStep_quasiFirmAt` (`BusemannLayerQuasiFirm`) |
| Lem. 3.1 | `GeodesicRay.tendsto_busemann`, `busemann_lipschitz`, `busemann_convex` (`BusemannRay`) |
| Lem. 3.2 | `BusemannFlow.fn_flow`, `dist_flow_flow_line`, `gd_flow` (`BusemannFlow`) |
| Eq. (4)–(6) | `layer` (`BusemannLayer`), `busemannStep` (`BusemannLayerQuasiFirm`) |
| **Thm. 4.1** | `layer_nonexpansive`, `activation_layer_nonexpansive` (`BusemannLayer`) |
| Fig. 1 / App. B | `flowline_layer_dist_eq`, `squaredRelu_layer_not_nonexpansive` (`BusemannSharpness`); `poincare_tightness` (`PoincareDiameter`) |
| Rem. 4.3 | `layer_comp_nonexpansive` (`BusemannLayer`) |
| **Thm. 4.4** | `productLayer_sum_sq_le`, `productLayer_dist_le` (`BusemannLayer`) |
| Rem. 4.5 | `scalarAdmissible_iff_product`, `scalarAdmissible_of_monotone` (`BusemannLayer`) |
| **Cor. 4.6** | `productLayer_gradient_sum_sq_le` (`ProductGradientLayer`), via `gradientStep_nonexpansive` (`CocoerciveGradientStep`) |
| §5.1.1 `b(x) = uᵀx` | `busemann_linear` (`BusemannRay`), `linearBusemannFlow` (`LinearBusemannFlow`) |
| §5.1.1 Eq. (11) | `linearLayer_eq`, `linearLayer_of_direction` (`LinearBusemannFlow`) |
| §5.1.1 ResNet layer | `resnetLayer_nonexpansive` (`EuclideanResNetLayer`) |
| Rem. 5.1 | `resnetLayer_nonexpansive` needs no sign condition on `φ'` |
| §5.1.2 Eq. (12), `∇b`, `grad b` | `hasGradientAt_poincareBusemann`, `poincareBusemannGrad_eq` (`PoincareBusemann`) |
| §5.1.3 Eq. (13) | `spdExp_congr`, `spd_split_update`, `spd_basepoint`, `spd_direction` (`SPDBusemannStep`) |
| §5.1.3 `d_AI` eigenvalue form | `frobSq_hermLog`, `exp_hermLog` (`SPDAffineInvariantDistance`) |
| §5.1.3 `b_{U,d}` | `spdBusemannOfFactor` (`SPDBusemannStep`) |
| §5.2 softplus | `hasDerivAt_softplus`, `softplusDeriv_lipschitz` (`M₂ = 1/4`), `softplus_layer_nonexpansive` (`τλ² ≤ 8`) |
| §5.2 squared ReLU | `hasDerivAt_squaredRelu` (incl. the kink at 0), `relu_lipschitz`, `squaredRelu_layer_nonexpansive` (`τλ² ≤ 2`) |
| Rem. 5.2 | `not_differentiableAt_relu_zero`, `deriv_squaredRelu` (`Activation`) |

Supporting mathlib gaps closed on the way:

* `NPCSpace` (Bruhat–Tits inequality) with geodesic uniqueness and convexity of `d(·,z)`
  (`NPCSpace.eq_gd_of_dist`, `dist_sq_le_of_between`, `dist_gd_le`);
* the multivariate convex-analysis chain `inner_gradient_le` → `descent_lemma` →
  `baillon_haddad` → `gradientStep_nonexpansive` (mathlib has none of these);
* congruence invariance of the affine-invariant matrix exponential (`spdExp_congr`);
* the `artanh` subtraction formula `artanh a - artanh b = artanh((a-b)/(1-ab))` (`artanh_sub`);
* the squared Frobenius norm as `tr(AᵀA)`, its orthogonal-congruence invariance and its value
  on diagonal matrices (`frobSq_eq_trace`, `frobSq_conj`, `frobSq_diagonal`), and the spectral
  matrix logarithm `hermLog` with `exp (hermLog H) = H`.

## Strengthenings over the source

1. **No manifold.** Everything holds on any NPC/Hadamard metric space (trees, Hilbert spaces,
   singular Hadamard spaces included).
2. **No regularity.** Theorem 4.1 needs only `a ≥ 0` and `r ↦ r - a(r)` 1-Lipschitz; Theorem 4.4
   needs only `a ≥ 0` componentwise and `z ↦ z - a(z)` nonexpansive.  The source assumes `a`
   Lipschitz and `φ ∈ C^{1,1}` and uses an a.e. chain rule.
3. **No curvature in Theorem 2.2.** Convergence of the iterates needs only a *proper* metric
   space; the finite-dimensional-Hadamard-manifold hypothesis is not used.
4. **Sharpness in general.** Appendix B's `D²` computation is a special case of
   `flowline_layer_dist_eq`, which shows the ratio `|1-τ|` on any Busemann flow line.
5. `Theorem 2.5` is proved without the redundant hypothesis `τ < τ̄` (it follows from `α < 1`).

## Non-vacuity

`InnerProductSpace.toNPCSpace` makes every real inner-product space an `NPCSpace` (with the NPC
inequality holding as an identity), and `linearBusemannFlow u hu` is a `BusemannFlow` on it for
every unit vector `u`.  `squaredRelu_layer_not_nonexpansive` exhibits explicit points of `ℝ`.
So none of the hypotheses is vacuous.

## Deliberately not formalised (and why)

* **`C²` regularity of Busemann functions on Hadamard manifolds** (second half of Lemma 3.1),
  the Jacobi-field proof of Theorem 4.1 (version 2), and the Hessian identity in Lemma 3.2.
  These are statements *about Riemannian manifolds*; mathlib currently has no Riemannian
  metric-connection theory (no Levi-Civita connection, geodesics, exponential map, Hessian or
  Jacobi fields), so they cannot even be stated.  They are also not needed: the metric proofs
  above are complete and strictly more general, and the regularity is exactly what the metric
  route removes.
* **`S⁺⁺(n)` and `Dⁿ` are Hadamard manifolds**, and the two cited gradient formulas
  (`grad b_{U,d} = -U L D Lᵀ Uᵀ`, source citations [30, 55]).  Same reason: they are Riemannian
  facts about specific metrics, not statements mathlib can express.  Everything *derived* from
  them — Eq. (13), the eigenvalue form of `d_AI`, the Poincaré gradient — is formalised.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  17 modules, all `lake build` green, wired into `GaloisForLFunctions.HTGeometry`;
      52 audited declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
- [ ] 3 → 4

## Log
- 2026-08-22 — created directly at stage 3; 17 Lean modules under
  `formal/GaloisForLFunctions/HTGeometry/HadamardLipschitz/`.
