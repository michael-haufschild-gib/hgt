# Ritt affine-tower residual: Lie-algebraic rigidity of scale-invariant jet equations

- **ID:** ritt-scale-invariant-residual-lie-rigidity
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper + Lean programme)
- **Consumers:** `2-fully-proven/04-rg-stochastic-quantum-fields/{exact-rational-rg-generation-dichotomy,
  gadc-tree-population-rg-clock-hypertranscendence, noisy-binary-tree-channel-rg-clock-hypertranscendence}.md`
  (their recorded remaining step: "the same bookkeeping for general n").

## Statement

Let `K` be a characteristic-zero differential field with shift `ψ`, chain-rule factor `ρ`,
`b₀ = −dρ/ρ²`, `b₁ = ρ⁻¹ d b₀`.  Suppose `F ∈ K[x₀,…,x_{n−1}]` is weighted homogeneous of weight
`n+1` (`w(x_j) = j+1`), has `ψ`-fixed coefficients, and satisfies the collapse identity of the affine
logarithmic tower `F ∘ A = ρ^{−(n+1)}F + δ_n`.  If `b₀ ≠ 0` (map not affine) and `b₁ ≠ b₀²/2`
(Schwarzian nonzero: map not Möbius), this is impossible.

## Proof (paper)

Put `Φ = x_n − F(x_0,…,x_{n−1})`.  Rescaling by weights turns the collapse into `Φ ∘ M_ν = Φ` for
every `ν ≠ 0`, where `M_ν` is the unipotent affine family with entries `ν^{j−i}ρ^{i+1}a_{j,i}` and
constants `ν^{j+1}b_j`.  Its `ν`- and `ν²`-coefficients give derivations `D₁`, `D₂ − ½D₁²` killing
`Φ`; explicitly `D₁ = b₀·ξ₁`, `D₂ − ½D₁² = (b₁ − ½b₀²)·ξ₂`, where `ξ_k` is the infinitesimal action
of `z^{k+1}∂` on connection jets: `ξ_k(x_j) = C(j+1,k+1)x_{j−k} + [j = k−1]`.  These satisfy
`[ξ₁, ξ_k] = ((1−k)(k+2)/2)·ξ_{k+1}`, so `ξ_kΦ = 0` for all `k ≥ 1`; but `ξ_{n+1} = ∂/∂x_n` and
`∂Φ/∂x_n = 1`.

## Lean plan
1. `HTGeometry/ConnectionJetGenerators.lean` — generators, bracket law, `ξ_{n+1} = pderiv last`,
   no nonzero-`∂_n` polynomial is killed by `ξ₁, ξ₂`.
2. `HTGeometry/PolynomialFamilyDerivations.lean` — first and second coefficients of an invariant
   polynomial substitution family are derivations killing the invariant.
3. `HTGeometry/RittLogTowerScaleInvariantRigidity.lean` — subdiagonal formulas, the family `M_ν`,
   invariance from the collapse, identification of the two derivations, contradiction.

## Caveat found (2026-09-29)
`RittLogTowerDescent.TowerObstruction` is satisfiable for every frame with `ρ ≠ 1`
(`w = 1`, `h = 1 − ρ`), so `obstruction_or_weightedHomogeneous_of_collapse` carries no
information on its obstruction side.  Closing the residual removes the second disjunct; the
obstruction side must be restated with the actual inhomogeneities before it can feed the cards.

## Progress
- 2026-09-29: **Residual closed in Lean**, unconditional, axioms `propext, Classical.choice,
  Quot.sound`.  `HTGeometry/ConnectionJetGenerators.lean` (`connectionGen`, bracket law
  `connectionGen_bracket_one`, `connectionGen_top = pderiv last`,
  `not_connectionGen_invariant_graph`), `HTGeometry/PolynomialFamilyDerivations.lean`
  (`familyDerivOne`, `familyDerivTwo = D₂ − ½D₁²`, `familySubst_eq_C_of_infinite`,
  `familyDeriv_eq_zero_of_eq_C`), `HTGeometry/RittLogTowerScaleInvariantRigidity.lean`
  (subdiagonal formulas in seed coordinates, `towerFamily`, `familyDerivOne_towerFamily = b₀•ξ₁`,
  `familyDerivTwo_towerFamily = (b₁ − b₀²/2)•ξ₂`, `towerFamily_invariant`, capstone
  `RittFrame.false_of_scaleInvariant_collapse`).  Wired into `GaloisForLFunctions.HTGeometry`.
- Next (layer structure below weight `n+1`): the same `ν`-expansion applied to a collapse with
  arbitrary lower layers gives, layer by layer, base equations `ψ f = ρ^{−k} f + h_k` with `h_k` a
  constant-coefficient weight-`k` polynomial in `b₀, b₁, …` plus higher-layer terms.  Layer 1:
  `h = κ·b₀` — an invariant rational 1-form (`κ = 0`) or an invariant rational affine connection
  (`κ ≠ 0`), both already refuted in the corpus for the channel maps.  Layers `k ≥ 2` need
  per-map pole counting (invariant rational projective / higher jet structures).
