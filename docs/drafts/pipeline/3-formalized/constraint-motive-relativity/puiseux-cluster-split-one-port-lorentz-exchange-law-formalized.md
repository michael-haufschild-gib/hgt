# Puiseux cluster-split one-port Lorentz exchange law — Lean certificate

- **ID:** `cmr-puiseux-cluster-split-one-port-lorentz-exchange-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `puiseux-cluster-split-one-port-lorentz-exchange-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PuiseuxClusterExchange.lean`,
imported by the area umbrella `GaloisForLFunctions.HTGeometry`.
Namespace: `HTGeometry.ConstraintMotiveRelativity`.

## Formal statement chain

### §2 — the exact cluster-split exchange

1. `contactPairing`, `cartanForm`, `clusterSum`, `clusterSum_add_compl` — `(3)`: the coefficient
   coarea form as a base term minus the contact pairing, and the rank port
   `M(x) = X_U + X_V`.
2. **`cartanForm_sub`** — Theorem 2.1, `(4)`: if every cross contact rises by `Δ` and every
   within-cluster contact is unchanged, then
   `Q₁(x) - Q₀(x) = -2Δ X_U X_V`.  Proved by splitting the double sum over `U` and `Uᶜ`.
3. **`cartanForm_sub_lorentz`** — the Lorentzian reading
   `Q₁ - Q₀ = (Δ/2)((X_U - X_V)² - M(x)²)`: exactly `Δ/2` units of quadratic coupling move from
   the common rank port into the centered cluster contrast.
4. **`cartanForm_sub_on_ker`** — on `M(x) = 0` the change is the positive square `2Δ X_U²`, hence
   nonnegative for `Δ ≥ 0`.

### §3 — the sharp two-branch wall

5. `branchForm`, **`branchForm_diag`** — `(10)`:
   `Q_j = 2x₁² + 2x₂² + 2(1-j)x₁x₂ = ((1+j)/2)(x₁-x₂)² + ((3-j)/2)(x₁+x₂)²`.
6. `branchGap`, `branchDet`, `branchDet_eq` — `(11)`: `Ω_j = (3-j)/2`, `det C_j = (1+j)(3-j)`.
7. **`branchForm_pos`** (positive definite for `-1 < j < 3`), **`branchForm_at_three`** and
   `branchForm_three_null` (semidefinite with a one-dimensional radical at the wall `j = 3`),
   **`branchForm_neg_above`** (a negative direction for `j > 3`) — the inertia jump.
8. **`branch_endpoints`** — `(13)`–`(14)`: `Ω = 1, det C = 4` at `j = 1` and
   `Ω = -1/2, det C = -5` at `j = 4`.

### §4 — smooth phase versus constructible law event

9. `polarCurve`, `hasDerivAt_polarCurve`, **`logDeriv_polarCurve`** — `(17)`: along a
   differentiable nonvanishing path the logarithmic derivative splits as
   `u̇/u = (ṙ/r) + i θ̇`, so its imaginary part is the phase (wall-angle) rate and its real part
   is the logarithmic rate of the modulus.
10. `rotPath`, `spiralPath`, `hasDerivAt_rotPath`, `hasDerivAt_spiralPath`, `norm_rotPath`,
    `norm_spiralPath` — the pure rotation `e^{it}` and the spiral `e^{(1+i)t}` have the same phase
    rate `1` at the origin and modulus rates `0` and `1`.
11. **`no_universal_phase_response`** — consequently no function `Φ` of the phase rate can predict
    the response of a rotation-invariant receiver: `Φ(1)` would have to be both `0` and `1`.

### §5 — the general rank-one crossing form

12. `rankOneCL`, `crossQ`, `crossQ_apply` — `(18)`: `Q = P - λ r rᵀ`.
13. `crossQ_apply_inv`, **`crossQ_inv_eq_zero`** and **`crossQ_ker_le`** — `(19)`: with
    `c = ⟪r, P⁻¹r⟫`, `u = P⁻¹r`, `Ω = c⁻¹ - λ`, the gap condition `Ω = 0` puts `u` in the kernel,
    and every kernel vector is a multiple of `u`; so `ker Q₀ = ℝ u₀`.
14. **`crossQ_quadratic`** and **`crossQ_quadratic_gap`** — `(21)`:
    `uᵀQu = c - λc² = c²Ω`.
15. **`crossing_form`** — Theorem `(20)`: for a differentiable family with symmetric `Q₀`,
    `Q₀u₀ = 0` and `Ω₀ = 0`, the terms containing `u̇₀` and `2c₀ċ₀Ω₀` drop out and
    `u₀ᵀQ̇₀u₀ = c₀² Ω̇₀`.
16. **`crossing_sign`** — the local spectral-flow orientation `(22)`: at a simple crossing the
    value of the family on the fixed kernel line changes sign through zero with the sign of `Ω̇₀`.

### §6 — the common central twist

17. **`cartanForm_central_shift`** — a common central shift of *every* contact by `δ` changes the
    coefficient Cartan form by `-δ M(x)²`, a pure rank-port term with no cluster contrast.
18. **`central_twist_no_crossing`** — `(24)`: on the rank-port kernel `M(x) = 0` the common central
    twist changes nothing, so it can create no inertia crossing there.
19. `detHolonomy`, **`detHolonomy_nonconstant`** — `(25)`: the determinant holonomy `δ^{M(x)}` does
    move with the central parameter as soon as `M(x) ≠ 0`.
20. **`central_vs_cluster`** — the decisive separation on `M(x) = 0`: the cluster split moves the
    form by the positive square `2Δ`, the common central twist moves it not at all, and yet the
    central twist moves the determinant holonomy.

### §7 — the projective score and its failure

21. `partitionZ`, `gibbsWeight`, `projectiveScore`, `partitionZ_pos` — `(26)`–`(27)`.
22. **`projectiveScore_nonneg`** — `(28)`: `J = D_KL(q‖p) ≥ 0`, by Jensen for `exp` on the
    simplex.
23. **`gibbs_hessian_identity`** — `(29)`: `vᵀ(diag p - p pᵀ)v = ½ ∑_{i,j} p_i p_j (v_i - v_j)²`,
    the difference-Laplacian form of the Hessian.
24. **`projectiveScore_const`** — for a common central twist all relative coordinates `a_i - a_j`
    vanish, so `p = q` and `J ≡ 0`: projectivization kills exactly the arithmetic central port.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PuiseuxClusterExchange.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PuiseuxClusterExchange
```

Green with no warnings.  `#print axioms` on `cartanForm_sub`, `cartanForm_sub_lorentz`,
`cartanForm_sub_on_ker`, `branchForm_diag`, `branchForm_pos`, `branchForm_at_three`,
`branchForm_neg_above`, `branch_endpoints`, `projectiveScore_nonneg`, `gibbs_hessian_identity`,
`projectiveScore_const`, `logDeriv_polarCurve`, `no_universal_phase_response`,
`crossQ_inv_eq_zero`, `crossQ_ker_le`, `crossQ_quadratic_gap`, `crossing_form`, `crossing_sign`,
`cartanForm_central_shift`, `central_twist_no_crossing` and `central_vs_cluster` reports only
`propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The Puiseux data of §1 enter the proofs only through the contact function `a, b ↦ contact a b` and
the dimension vector `x`; the Lean development therefore states §2 for an arbitrary finite index
set with an arbitrary base term, which is strictly more general than the card's unramified
spectrum and makes Theorem 2.1 a literal identity rather than a computation with Puiseux
expansions.

`(16)`, the explicit wall angles `θ_{r,ε} = (arg γ - τ_ε)/k + 2πr/k`, is a normalization of the
argument lift; the content of §4 that the card uses is `(17)` and the resulting non-existence of a
phase-to-inertia response law, both of which are formalized.  The factor `1/k` is a fixed positive
constant and is omitted from `logDeriv_polarCurve`.

`(22)` is stated in the form the crossing form actually licenses: the sign change of the quadratic
form on the fixed kernel line.  Converting that into an integer spectral-flow count requires a
continuity-of-eigenvalue argument that adds nothing to the card's conclusion — the card's own point
is that the correctly typed signed response is the crossing form `(20)`, not a derivative of an
integer.

§8 records programme consequences and claims no new theorem.
