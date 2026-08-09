# Spectral terminal-horizon model — formalized

- **ID:** `spectral-terminal-horizon-model-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `spectral-terminal-horizon-model.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `.../InterfinityGeometry/SpectralHorizonCocycle.lean` | the source cochain, its weighted square integrability, the coboundary criterion, the death cut |
| `.../InterfinityGeometry/SpectralFinitePart.lean` | chart functions and the integrability of the finite-part integrands |
| `.../InterfinityGeometry/SpectralPrimitiveIdentity.lean` | the finite part `η_a` and the primitive identity; forward annihilation above the cut |
| `.../InterfinityGeometry/SpectralCutObstruction.lean` | divergence of the cut integral below the cut, and the no-stable-primitive obstruction |
| `.../InterfinityGeometry/HadamardDivision.lean` | **Hadamard's lemma for `C^∞` functions of one real variable** — absent from mathlib |
| `.../InterfinityGeometry/SpectralFixedSubspace.lean` | the common fixed subspace of the multiplication semigroup is `ℝ δ₀` |
| `.../InterfinityGeometry/SpectralGammaIntegral.lean` | the regularized Gamma integral `∫₀^∞ (e^{-t}−1)t^{a-1} = Γ(a)` for `−1 < a < 0` |
| `.../InterfinityGeometry/SpectralGammaScaling.lean` | the scaling identities and the scaled Gamma tail |
| `.../InterfinityGeometry/SpectralDeficientAsymptotics.lean` | the deficient projective limit `V^a η_a(e^{-V·}h) → cΓ(a)h(0)` |
| `.../InterfinityGeometry/SpectralLogarithmicHorizon.lean` | the logarithmic contact law at the cut |
| `.../InterfinityGeometry/SpectralComplexGamma.lean` | **the rotated Gamma integrals `∫₀^∞ (e^{-wt}−1)t^{a-1} = Γ(a)w^{-a}` and `∫₀^∞ e^{-wt}t^{a-1} = Γ(a)w^{-a}` for `Re w > 0`** |
| `.../InterfinityGeometry/SpectralComplexDeficient.lean` | the sectorial projective limit and the angular phase slope |
| `.../InterfinityGeometry/SpectralEulerConstant.lean` | **`∫₀¹(e^{-t}−1)/t + ∫₁^∞ e^{-t}/t = −γ`** |
| `.../InterfinityGeometry/SpectralComplexLogConstant.lean` | the sharp real log law and `∫₀¹(e^{-wt}−1)/t + ∫₁^∞ e^{-wt}/t = −γ − Log w` |
| `.../InterfinityGeometry/SpectralComplexLogHorizon.lean` | the sectorial logarithmic law `η₀(e^{-z·}h) = −c h(0)(Log z + γ) + o(1)` |

## Audited declarations

Namespace `GaloisForLFunctions.HTGeometry.Interfinity`.

Item 1 — `integrableOn_laplaceCochain_sq` (finite exactly for `β > −2`), `laplaceCochain_add`
(the cocycle law), `isCoboundary_iff` (a primitive in `H_β` exists exactly for `β > 0`),
`deathCut_add`, `mem_stableRegion_iff`, `deathCut_eq_iff`.

Item 2/3 — `finitePart_transport_sub` (the finite part is a primitive at every admissible
observer), `tendsto_transported_finitePart` (forward annihilation for `a > 0`),
`tendsto_cutIntegral_atBot` and `not_tendsto_finitePart_of_nonpos` (no stable primitive for
`a ≤ 0`), `mem_observerLine_iff`, `stableRegion_subset_observerLine`.

Item 4 — `hadamard_eq` and `laplace_defect_factor` (`e^{-Vs}−1 = s·E_V(s)` with `E_V` smooth and
nowhere zero), `fixed_eq_smul_deltaZero` and `deltaZero_fixed` (the fixed subspace is exactly
`ℝ δ₀`), `integral_gammaDefect`, `tendsto_regularizedCut`, `tendsto_transportedFinitePart`
(`V^a η_a(e^{-V·}h) → c Γ(a) h(0)`), `tendsto_cutIntegral_zero_div_log` and
`tendsto_transportedFinitePart_log` (the `a = 0` law).

Item 5 — `cgammaIntegral_eq`, `cgammaOrdIntegral_eq` (the rotation law, by holomorphy on the right
half-plane plus the identity theorem), `tendsto_ctransportedFinitePart` and
`tendsto_ctransportedFinitePart_ray` (`R^a T_z η_a → c Γ(a) e^{-iaθ} δ₀`),
`cpow_exp_mul_I`, `hasDerivAt_terminal_phase` (`∂_θ arg = −a`),
`phase_slope_eq_deathCut_sub` (`−a = 𝔡_β − ρ`), `gammaHead_add_gammaTail`,
`tendsto_cutIntegral_zero_add_log`, `tendsto_transportedFinitePart_log_sharp`,
`clogHead_add_clogTail`, `tendsto_ccutIntegral_zero_add_log`,
`tendsto_ctransportedFinitePart_log` (`T_z η_0 = −c(Log z + γ)δ₀ + o(1)`).

Every listed declaration is unconditional: `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry.InterfinityGeometry
```

## Boundary

Two inputs the card's handoff notes call hard dependencies were built here from scratch because
mathlib has neither: Hadamard's lemma for `C^∞` functions, and the rotated (incomplete) Gamma
integrals on the right half-plane.  The distributional statements are formalized on the concrete
transported smooth-chart model the card fixes, which is the model in which every displayed formula
of the card is stated.
