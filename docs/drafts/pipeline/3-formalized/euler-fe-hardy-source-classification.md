# The finite-energy defect transform is onto the Hardy class

- **ID:** euler-fe-hardy-source-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Euler–FE transport theory; defect calculus.
- **Statement:** The actual Hamburger transform of every `g ∈ L²(ℝ)` is the Laplace
  transform of a unique scaled-unitary Mellin source. Its range is the right-half-plane
  Hardy class, and its limiting vertical energy is `π⁻¹‖g‖²`.

## Proof

Put `s(t)=½+2it` and

    A(t)=2^s(t) Γ(s(t)/2)/(√π Γ((1-s(t))/2)).

Conjugation gives `|A(t)|=√(2/π)`. Duplication at `(1-s)/2` and reflection at `s/2` give

    A(t)Γ(1-s(t))=1/sin(πs(t)/2).

Let `M : L²(0,∞) → L²(ℝ)` be the unitary Mellin transform with frequency
`½−2πiξ`. Define `ψ_g` by

    (Mψ_g)(ξ)=½g(-πξ)A(-πξ).

Multiplication by `√(π/2)A`, reflection, dilation, and inverse Mellin synthesis are
unitary. Thus `g ↦ ψ_g` is bijective and

    ‖ψ_g‖²=(2π²)⁻¹‖g‖².

For `Re z>0`, the exponential `e_z(u)=exp(-conj(z)u)` is in `L²(0,∞)`. The complex-rate
Gamma integral computes its Mellin transform. With `t=-πξ`,

    conj((Me_z)(ξ))=Γ(1-s(t))z^(s(t)-1).

Mellin–Plancherel and the substitution `t=-πξ` therefore give

    ∫₀∞ ψ_g(u)e^(-zu)du
      = ⟨e_z,ψ_g⟩
      = (1/(2π))∫ℝ g(t)A(t)Γ(1-s(t))z^(s(t)-1)dt
      = (1/(2π))∫ℝ g(t)z^(s(t)-1)/sin(πs(t)/2)dt
      = J_g(z).

The pairing is absolutely integrable by Cauchy–Schwarz. This proves the actual
Hamburger identity without assuming `g ∈ L¹` or a boundary representation.

Half-line Laplace–Plancherel now gives holomorphy and

    ∫ℝ |J_g(σ+iy)|²dy = 2π∫₀∞ e^(-2σu)|ψ_g(u)|²du.

Dominated convergence gives limiting energy `π⁻¹‖g‖²` as `σ↓0`.
Conversely, Paley–Wiener represents every right-half-plane Hardy function as a half-line
Laplace transform. Surjectivity of `g ↦ ψ_g` supplies its defect source.

## Formalization

`EulerFETransportTheory/TheDefectHasAUnitaryMellinSource.lean` proves
`mellin_defectMellinSource`, `norm_sq_defectMellinSource`, and
`defectMellinSource_bijective`.
`FiniteEnergyDefectsAreLaplaceTransforms.lean` proves
`defectLaplace_eq_laplaceRay`, `isHalfPlaneHardy_defectLaplace`,
`tendsto_vertical_energy_defectLaplace`, and `exists_defectLaplace_eq_of_hardy`.
Both modules pass direct `lake --old env lean` checks.
The transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

`euler-fe-hardy-laplace-transport.md` proves the canonical-boundary identification,
strong convergence, and weak `L²` test pairings. The arithmetic tent identity and
complete finite-energy rigidity are formalized in `euler-fe-finite-energy-rigidity.md`.
Hardy surjectivity alone supplies neither Euler rigidity nor height transport.
