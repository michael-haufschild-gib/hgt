# The Hecke-equivariant completion of the window tower (review-0311 §2.5.2)

- **ID:** R0311-25-2
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/obstacles-summary.md` §2.5.2
- **Statement:** One bounded real-linear map from window tests into the completed PM resonant space
  under which Weil's window energy is the Krein form exactly, reflection is the twisted conjugate Krein
  reflection, and the source Hecke operators minus the identity are the Mellin translations, for every
  prime.

## Answer

1. **Completion.** `𝒦 = ℓ²(upper Mayer resonances)`, `[x, y] = Σ_s x_s conj(y_{s♯})`, `s♯ = ½ − s̄`;
   `[x, y] = ⟨Jy, x⟩` with the unitary involution `J`. PM's core space embeds densely, carrying PM's
   Krein form to `[·,·]`; each core is a basis vector.
2. **Window map.** `𝓦_A H = (√m_{2s} Φ_H(s, 1))_s`, real-linear, bounded:
   `‖𝓦_A H‖² ≤ 20 e^A T ‖H‖²_{W^{2,1}}`, `T = Σ_ρ m_ρ/(1 + |γ_ρ|²)`. Finite core packets are its
   truncations.
3. **Exact Krein identity.** `Q(H) = 2 Re [𝓦_A H, 𝓦_A H]` (no limit).
4. **Reflection.** `𝓦(σ_A H)_s = e^{−A(2s−½)} conj(𝓦 H_{s♯})`.
5. **Hecke, every prime `p`.** `T_{p,s}f(a) = Σ_{M ∈ X_p} (γa + δ)^{−2s} f((αa + β)/(γa + δ))`,
   `X_p = {ad − bc = p, 0 ≤ c < a, 0 ≤ b < d}`. Then `(T_{p,s} − Id)ψ_s = p^{1−2s}ψ_s` at every
   resonance and across the strip, and `F_pH = √p H(· + log p)` acts on `𝒦` by the same multiplier:
   `𝓦_{A+log p}(F_pH) = D_p 𝓦_A H`, `(D_p x)_s = p^{1−2s}x_s`, `[D_p x, D_p y] = p[x, y]`,
   `‖D_p‖ ≤ p`; on completed periods `T_{p,s}Φ_H − Φ_H = Φ_{F_pH}`.

## Proof

1–4: `Q(H) = 2 Re Σ_s (zero coordinate)·conj(reflected coordinate)` (`weilQuad_eq_twice_upperMayer_sum`);
the coordinates are square-summable by `|Ĥ(γ)| ≤ e^{A/2}·4‖H‖_{W^{2,1}}/(1 + |Re γ|)²` and the tempered
zero sum.

5, cones: the cones `{m u₁ + k u₂ : m ≥ 1, k ≥ 0}` of `X_p` tile the quadrant — a vector lies in one
cone, or in `p + 1` when it is divisible by `p` (uniqueness: change-of-basis inequalities force the
identity; existence: the Euclid chain `(u₂, ⌈a/c⌉u₂ − u₁)`; count: index-`p` lattices = lines of `𝔽_p²`).
Weighting each lattice vector by its half-open cones writes every boundary Barnes period as one lattice
sum, so `Σ_{X_p} P_w(M(a,b)) = P_w(a,b) + pP_w(pa,pb)` and `T_{p,w/2}P_w(·,1) = (1 + p^{1−w})P_w(·,1)`
for `Re w > 2`. Determinant-one cones give the Farey splitting, inversion and the Lewis equation of
`P_w`.

5, continuation: `E_w = period w 1 (−ζ(w)) (state w)` satisfies the Lewis equation and inversion on
`Re a > 0` and equals the Mayer disc value on `(½, 7/2)`; propagation along the positive line makes
`w ↦ E_w(a)` holomorphic on `U = {Re w > 0} ∖ {1, 2}` for every `a > 0` and gives `E_w = P_w(·,1)` for
`Re w > 2`. The Hecke defect is holomorphic on the connected `U` and vanishes near `w = 3`.

## Lean

`formal/GaloisForLFunctions/RenormalizedIntersectionTheory/MayerScattering/`:

- `TheHeckeEquivariantCompletion`: `completedKreinForm_eq_inner`, `completedKreinForm_coreEmbedding`,
  `denseRange_coreEmbedding`, `windowResonanceMap`, `norm_windowResonanceMap_sq_le`,
  `weilQuad_eq_completedKreinForm`, `windowResonanceMap_heckePull`,
  `completedKreinForm_heckeMultiplier`, `norm_heckeMultiplier_le`,
  `windowResonanceMap_windowInvolution`.
- `TheHeckeConesTileTheQuadrant`: `heckeBasis_eq_of_inCone`, `exists_inCone_of_basis`,
  `heckeConeCount_eq`.
- `TheBarnesPeriodIsAHeckeEigenfunctionForEveryPrime`: `barnesBoundaryPeriod_eq_coneSum`,
  `barnesBoundaryPeriod_hecke_prime`, `barnesBoundaryPeriod_lewisHecke`, `barnesBoundaryPeriod_farey`,
  `barnesBoundaryPeriod_three_term`.
- `TheEisensteinPeriodIsAHeckeEigenfunctionForEveryPrime`: `differentiableAt_eisensteinPeriod`,
  `eisensteinPeriod_eq_barnes`, `eisensteinPeriod_lewisHecke`, `eisensteinLewisPeriod_lewisHecke`,
  `resonantLewisPeriod_lewisHecke`.
- `TheSourceHeckeOperatorsAreMellinTranslations`: `lewisHeckeOperator_windowMellinPeriod`,
  `windowResonanceMap_heckePull_intertwines`.

## Gates
- [x] 0 → 1  statement
- [x] 1 → 2  paper proof
- [ ] 2 → 3  every module passes `lake --old env lean`
