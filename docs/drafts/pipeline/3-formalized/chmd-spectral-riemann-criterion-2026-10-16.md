# CHMD: the spectral Riemann criterion — RH ⟺ no primitive bound state of the arithmetic resolvent above 1/2

- **ID:** chmd-spectral-riemann-criterion-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional equivalence
- **Source:** CHMD route; closes the dictionary promised by the lane (chmd-polar-transfer-arithmetic-resolvent, chmd-far-field-energy-localization, chmd-no-weyl-above-threshold, chmd-pure-point-above-threshold); corpus input: `riemannHypothesis_iff_forall_phiDoobCoshMass_zero_dirichlet_poincare`
- **Statement:** With `R` the arithmetic resolvent on `L²(Θcosh(x/2)dx)` and `1` the constant ground state:
  `RH ⟺ ∀ w ⊥ 1, ⟪Rw, w⟫ ≤ ½‖w‖² ⟺ ∀ μ > 1/2, ∀ w ⊥ 1, Rw = μw → w = 0`, and
  `¬RH ⟺ ∃ μ > 1/2, ∃ w ≠ 0, w ⊥ 1, Rw = μw`.
- **Status:** STATUS MUST-1552. One leaf (`CHMDSpectralRiemannCriterion`, 21 declarations), axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audit clean; `lake build --old` green; wired; index refreshed; global lint clean of proof debt (remaining errors are other agents' unwired modules).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `riemannHypothesis_iff_resolventHalfBound`, `riemannHypothesis_iff_no_primitive_bound_state`, `not_riemannHypothesis_iff_exists_primitive_bound_state`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
The CHMD lane had the dictionary "RH ⟺ E ≥ 0 on even/primitive tests" only at the level of compact
test functions and quadratic forms. The operator-level statement "RH ⟺ no spectrum of the arithmetic
resolvent above 1/2 on the primitive sector" required (a) density of primitive compact tests in the
primitive hyperplane of the completed graph, (b) the conversion `E ≥ 0 ⟺ R ≤ ½` through `R = SS*`,
and (c) the passage from the numerical range to actual eigenvectors, which is where the discreteness
theorems enter. All three are now in Lean. The result is an exact spectral criterion: RH fails iff the
arithmetic resolvent has a bound state in the primitive sector above its essential threshold. Together
with MUST-1551 such bound states are isolated, finitely degenerate and finitely many above `1/2 + ε`.

## Paper proof
*Density.* Let `ℓ(q) = ⟪q.fst, 1⟫_μ` (continuous on the graph) and `q₀` a compact test with `ℓ(q₀) > 0`
(the window bump). `Φ(q) = q − (ℓ(q)/ℓ(q₀)) q₀` is continuous, maps compact tests to primitive compact
tests, and fixes primitive vectors. For primitive `p`: `p = Φ(p) ∈ closure Φ(compactTests) ⊆ {E ≥ 0}`
(RH gives `E ≥ 0` on primitive compact tests by the corpus criterion; `E` is continuous).

*Energy ⟺ resolvent bound.* `E(p) = ‖p‖² − 2‖Sp‖²`. For `w ⊥ 1`, `Riesz(w)` is primitive
(`⟪Rw, 1⟫ = ⟪w, R1⟫ = ⟪w, 1⟫ = 0`), `‖Riesz w‖² = ⟪w, Rw⟫`, `(Riesz w).fst = Rw`. If `E ≥ 0` on
primitives then `‖Rw‖² ≤ ½‖Riesz w‖²` and `‖Riesz w‖² = ⟪w,Rw⟫ ≤ ‖w‖‖Rw‖`, whence
`‖Riesz w‖² ≤ ½‖w‖²`. Conversely if `⟪Rw,w⟫ ≤ ½‖w‖²` on `1^⊥` and `p` is primitive with `w = Sp`:
`‖w‖² = ⟪Riesz w, p⟫ ≤ ‖Riesz w‖‖p‖` and `‖Riesz w‖² ≤ ½‖w‖²` give `‖Sp‖² ≤ ½‖p‖²`, i.e. `E(p) ≥ 0`.

*Resolvent bound ⟺ no bound state.* An eigenvector `w ⊥ 1` with `Rw = μw`, `μ > 1/2`, has
`⟪Rw,w⟫ = μ‖w‖² > ½‖w‖²`. Conversely, if the bound fails let `M = sup{⟪Rw,w⟫ : w ⊥ 1, ‖w‖ = 1} > 1/2`.
Cauchy–Schwarz for the positive form, `⟪Rx,y⟫² ≤ ⟪Rx,x⟫⟪Ry,y⟫`, with `y = Rw` and the bound
`⟪R(Rw), Rw⟫ ≤ M‖Rw‖²` (`Rw ⊥ 1`) gives `‖Rw‖² ≤ M⟪Rw,w⟫` on `1^⊥`; for unit `w_n ⊥ 1` with
`⟪Rw_n,w_n⟫ > M − 1/(n+1)`: `‖(R−M)w_n‖² = ‖Rw_n‖² − 2M⟪Rw_n,w_n⟫ + M² ≤ M(M − ⟪Rw_n,w_n⟫) → 0`.
By weak compactness and MUST-1548 a subsequence converges weakly to a nonzero eigenvector at `M`, which
is primitive (weak limits preserve `⟪·,1⟫ = 0`).

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDSpectralRiemannCriterion.lean` — `PrimitiveGraph`, `inner_compactLift_oneL`,
`primitiveGraph_compactLift_iff`, `sourceEnergy_compactLift_nonneg_of_rh`,
`riemannHypothesis_of_primitive_energy`, `exists_compactTest_mass_pos`, `sourceEnergy_nonneg_of_rh`,
`ResolventHalfBound`, `sq_le_half_sq`, `primitiveGraph_rieszLift`, `resolventHalfBound_of_energy`,
`sourceEnergy_eq_graph_sub`, `energy_nonneg_of_resolventHalfBound`,
`riemannHypothesis_iff_resolventHalfBound`, `eq_zero_of_primitive_eigenvector_of_resolventHalfBound`,
`exists_primitive_eigenvector_of_approx_eigen_above_half`, `inner_resolvent_sq_le`,
`resolventHalfBound_of_no_primitive_bound_state`, `riemannHypothesis_iff_no_primitive_bound_state`,
`not_riemannHypothesis_iff_exists_primitive_bound_state`, `mem_spectrum_of_primitive_bound_state`.

## Big picture
- The CHMD route now has an exact operator-theoretic statement of RH with the full structure of the
  obstruction: `σ_ess(R) ⊆ [0,1/2]` (MUST-1548), `1/2 ∈ σ_ess` (MUST-1544/1546), `σ(R) ∩ (1/2,1]`
  pure point and locally finite (MUST-1551), and RH ⟺ this point spectrum is empty on the primitive
  sector (this card). RH is a statement about finitely many bound states at a time.
- Nothing here is conditional; the only ζ-input is the corpus primitive Dirichlet–Poincaré criterion.
- Walls catalogue: this is a receiver (an equivalence), but a structural one: it turns RH into the
  absence of a discrete spectrum above an explicit essential threshold of an explicit arithmetic
  operator, which is the form in which perturbative/variational tools (min–max, Birman–Schwinger)
  apply.

## Next conjectures
1. Birman–Schwinger: the number of primitive bound states above `1/2` (with multiplicity) equals the
   number of nonreal Xi zero orbits; a bound state's level `μ` is an explicit function of the zero's
   distance from the critical line.
2. Perturbative stability: the top primitive eigenvalue is a Lipschitz function of bounded
   perturbations of `R` (min–max), giving quantitative "almost-RH" statements.
3. The even/odd splitting of the primitive bound states.
