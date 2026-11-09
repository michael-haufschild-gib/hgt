# The canonical defect boundary is the strong Hardy boundary

- **ID:** euler-fe-hardy-laplace-transport
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Euler–FE transport theory; defect calculus.
- **Statement:** The actual vertical traces of every finite-energy Hamburger defect
  converge strongly to its canonical boundary `B`. The map `√π B` is unitary onto the
  Hardy boundary space, and every `L²` test passes to the boundary.

## Proof

Let `ψ_g` be the explicit Mellin source already identified with the actual defect:
`J_g(z)=∫₀∞ψ_g(u)e^(-zu)du`. Let `E` extend half-line data by zero, `F` be the unitary
Fourier transform with phase `exp(-2πiuξ)`, and `D_a f(y)=√a f(ay)`. The actual vertical
trace has `L²` class

    V_σ g = √(2π) D_(1/(2π)) F E(e^(-σu)ψ_g(u)),      σ>0.

Dominated convergence of `|e^(-σu)-1|²|ψ_g(u)|²` proves strong convergence to

    Cg = √(2π) D_(1/(2π)) F Eψ_g.

This is a continuous complex-linear operator in `g`. For integrable finite-energy
defects, the existing kernel theorem gives pointwise convergence to the original
boundary away from zero. A subsequence of the strong limit converges almost everywhere,
so `Cg` agrees with that original boundary. Density of `L¹∩L²` and uniqueness of its
continuous extension give `C=B` on all `L²`.

Pairing strong convergence with any `k∈L²` gives

    ∫ℝ conj(k(y))J_g(σ+iy)dy → ∫ℝ conj(k(y))(Bg)(y)dy.

Fourier dilation gives `F D_(2π)=D_(1/(2π))F`. Thus `C` is `√(2π)` times the
Paley–Wiener unitary applied to `ψ_g`. The Mellin source is onto `L²(0,∞)`, so the
boundary range is precisely `F(L²([0,∞)))`. This is the corpus's `hardyL2ᗮ`, with the
orientation induced by `z=σ+iy`. The already-proved identity `‖Bg‖²=π⁻¹‖g‖²` makes
`√π B` unitary onto that space.

## Formalization

`EulerFETransportTheory/FiniteEnergyDefectsConvergeToTheirBoundary.lean` implements
the actual vertical classes, strong limit, weak `L²` pairing, and exact Hardy range.
The terminal declarations are `tendsto_defectVerticalL2`,
`tendsto_integral_defectLaplace_L2_boundary`, `range_defectBoundaryL2`, and
`normalizedDefectBoundaryHardyUnitary`. Direct `lake --old env lean` verification
passes; all four axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

The arithmetic tent identity and complete finite-energy Beurling rigidity are
formalized in `euler-fe-finite-energy-rigidity.md`.
This boundary theorem supplies no height-replication law.
