# Metric-phase exactness, cost, winding, cofinal strictness — Lean certification

- **ID:** ULF-MPE-1
- **Paper card:**
  `metric-phase-exactness-cost-winding-and-cofinal-strictness-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveMetricPhaseExactness`,
  `GaloisForLFunctions.HTGeometry.HilbertBlockOperator` (new reusable layer)
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## New corpus infrastructure

The corpus carried only a **scalar** block diagonal on a Hilbert direct sum (multiplication by a
real scalar in each block).  `HilbertBlockOperator` supplies the **operator-valued** version:

- `blockOperator_memℓp`, `blockOperator`, `norm_blockOperator_le` — a uniformly bounded family
  `T i : K i →L[𝕜] K i` acts blockwise on `lp K 2` and is bounded by the same constant;
- `blockOperator_injective` — blockwise injectivity is injectivity;
- `blockOperator_single`, `denseRange_blockOperator` — blockwise surjectivity gives dense range,
  because the range contains every `lp.single` and those sum to an arbitrary vector;
- `not_surjective_blockOperator`, `range_blockOperator_ne_top`,
  `not_isClosed_range_blockOperator` — blocks that are not uniformly bounded below make the
  operator non-invertible, so the dense range is proper and therefore not closed.

## Certified declarations

### Theorem 1 — metric and phase invisible to the derived endpoint

- `det_metricPhaseLaw` — `det T(α,φ) = e^{iφ} sin α`;
- `conjTranspose_mul_self` — `TᴴT = !![1, cos α; cos α, 1]`, independent of `φ`;
- `det_gramLaw` — its determinant is `sin²α`;
- `gramLaw_mulVec_low`, `gramLaw_mulVec_high` — `(1,−1)` and `(1,1)` are Gram eigenvectors of
  eigenvalues `1 ∓ cos α`: the squared singular values of (3);
- `det_metricPhaseLaw_ne_zero` — acyclicity for `0 < α ≤ π/2`;
- `gram_phase_erasure` and `det_phase_separates` — positive Gram data determine `α` and erase `φ`,
  while the determinant separates `φ = 0` from `φ = π`;
- `apertureBlock_filling_energy` — the worst unit-target filling energy is exactly `(1 − cos α)⁻¹`:
  every filling obeys `‖x‖² ≤ (1 − cos α)⁻¹‖y‖²`, and the bound is attained at the least-stretch
  unit vector.  This is (4) without an appeal to an operator-norm-of-a-matrix layer.

The metric core is `apertureBlock_norm_sq`, `apertureBlock_norm_sq_le` (stretch `≤ 2`, so
`‖T‖ ≤ √2`) and `apertureBlock_norm_sq_ge` (stretch `≥ 1 − cos α`), proved from the reverse and
forward triangle inequalities on the two coordinates.

### Theorem 2 — closed observation, open determinant history

`metricPhaseLaw_periodic` (exact `2π`-periodicity of the observed law and hence of the Gram law),
`exp_detLogLift` (the lift lifts the determinant), `detLogLift_period` (advance `2πi` per observed
period) and `detLogLift_winding` (winding `N` after `N` periods).

### Theorem 3 — the cofinal exactness wall

`cofinalLaw α hc` is the Hilbert direct sum `⨁ₙ T(αₙ,0)` on `lp (fun _ : ℕ => ℂ²) 2`.  For
`0 < αₙ ≤ π/2` with `αₙ → 0`, `cofinal_exactness_wall` certifies in one statement:

- `‖𝒯‖ ≤ √2` — bounded;
- injective;
- dense range;
- **not** surjective — the least singular values `√(1 − cos αₙ)` tend to zero, realized by the
  explicit unit vector `lowUnit`, so `𝒯` is not bounded below and cannot be invertible;
- range **not closed** — a closed dense subspace would be everything;
- `(1 − cos αₙ)⁻¹ → ∞` — the divergence (9);
- `−∑_{n<N} log sin αₙ → ∞` — the determinant free energy (10), via non-summability of a
  nonnegative sequence tending to infinity.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/HilbertBlockOperator.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveMetricPhaseExactness.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on the Gram identity, the winding, the
lower stretch bound, the filling energy, the cofinal wall, and both block-operator range statements
reports only `propext`, `Classical.choice`, and `Quot.sound`.  No project axiom, placeholder,
hypothesis interface, or unresolved theorem premise is used.

## Exact field consequence

Four decategorifications are logically independent on one family: the algebraic endpoint (derived
zero) retains nothing metric or phased; the positive law `TᴴT` retains the aperture but erases the
determinant phase and its winding; the determinant retains the phase; and cofinal strictness —
closed range, uniform inverse — is not determined by exactness of every finite aperture.  A
universal field must keep these four layers apart rather than rename them all "curvature".
