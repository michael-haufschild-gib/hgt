# Neutral Gamma-ratio full differential boundary depth law — formalized

- **ID:** `neutral-gamma-ratio-full-differential-boundary-depth-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `neutral-gamma-ratio-full-differential-boundary-depth-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/GammaPhaseCompletion.lean` | `HasPolynomialFunctionalProjectiveBoundary`, `neutralGammaRatio_twoStageBoundary` |
| `formal/GaloisForLFunctions/HTGeometry/PolynomialOnePointRecession.lean` | pointwise one-point recession of a nonzero polynomial tuple |
| `formal/GaloisForLFunctions/HTGeometry/PolynomialRecessionLocallyUniform.lean` | locally uniform upgrade `q(z+iT)/(iT)^d → q_d` |
| `formal/GaloisForLFunctions/HTGeometry/ConstantProjectiveBoundaryWitness.lean` | constant-class witness of the interface |
| `formal/GaloisForLFunctions/HTGeometry/PolynomialProjectiveBoundaryWitness.lean` | polynomial-class witness, antitonicity, nowhere-zero-factor absorption |
| `formal/GaloisForLFunctions/HTGeometry/NeutralGammaRatioProjectiveBoundary.lean` | **the Gamma-ratio class realization** with mathlib `Complex.Gamma` |
| `formal/GaloisForLFunctions/HTGeometry/KolchinFrequencyBudgetPhase.lean` | frequency split, prime-complement budget, Gamma-coefficient capacity floor |

## Formal theorem chain

1. **The interface.**  `HasPolynomialFunctionalProjectiveBoundary K`: every finite nonzero tuple
   from `K`, translated along every upper-height sequence, has after a subsequence one common
   normalization under which it converges locally uniformly to a nonzero polynomial tuple.

2. **The Gamma-ratio class.**  `neutralGammaRatio θ s = Γ(s + iθ)/Γ(s)` (mathlib `Complex.Gamma`),
   `neutralGammaRatioRationalClass θ = {G_θ · p/q : q ≠ 0}`.
   `neutralGammaRatio_ne_zero`: the ratio has no zeros in the open upper half-plane.

3. **The realization.**  `hasPolynomialFunctionalProjectiveBoundary_neutralGammaRatioRationalClass`
   (for every `θ ≥ 0`): the common normalization
   `(iT)^{-d} · G_θ(z+iT)^{-1} · ∏_l q_l(z+iT)` — the cleared common denominator restored as one
   meromorphic functional normalization — turns each member into the scaled vertical translate of
   its cleared numerator `p_j · ∏_{l≠j} q_l`; above a compact-dependent height the Gamma ratio and
   the denominators cannot vanish (`exists_norm_gt_eval_ne_zero` escape radius, the two Gamma pole
   lines are horizontal), and `poly_scaled_translate_tendstoLocallyUniformly` yields the nonzero
   polynomial limit at the common degree bound
   (`tendstoLocallyUniformly_congr_eventually_local` transfers the convergence).

4. **The two-stage boundary.**  `neutralGammaRatio_twoStageBoundary_rationalClass`: the boundary
   carrier chain `K_θ-class → ℂ[z] → ℂ` of length two, unconditional — polynomial projective
   limits, then one-point recession onto the nonzero leading-coefficient vector.

5. **Frequency and arithmetic-complement consequences.**  `nonautonomous_frequencyRank_exactSplit`,
   `nonautonomous_primeComplement_budget`, `nonautonomous_gammaCoefficient_capacity_floor`
   (`KolchinFrequencyBudgetPhase.lean`) formalize the recurrent finite-carrier split, the
   `π(N) − 2m(n+1)` complement bound, and the Gamma-only capacity floor at their exact reusable
   interfaces.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/NeutralGammaRatioProjectiveBoundary.lean
lake build GaloisForLFunctions.HTGeometry.NeutralGammaRatioProjectiveBoundary
```

`#print axioms` on `neutralGammaRatio_ne_zero`, `exists_norm_gt_eval_ne_zero`,
`tendstoLocallyUniformly_congr_eventually_local`, `gamma_clearing_identity`,
`hasPolynomialFunctionalProjectiveBoundary_neutralGammaRatioRationalClass`,
`neutralGammaRatio_twoStageBoundary_rationalClass` reports exactly `propext`, `Classical.choice`,
`Quot.sound`.

## Boundary

The realized coefficient class is the single-`G_θ`-power rational stratum `G_θ · ℂ(s)` of the paper
field `K_θ = ℂ(s)⟨G_θ⟩`, with genuine `Complex.Gamma` data, moving poles, and every polynomial
degree.  A literal inclusion `K_θ ⊆ g·ℂ[z]` is impossible for any Γ-bearing class (the encoded
pole lattice gives `G_θ` infinitely many zeros), so the direct realization above is the correct
form of the card's last obligation.  Higher strata (mixed `G_θ`-powers, `Ψ`-jets) would need the
vertical Tricomi–Erdélyi asymptotics; they carry none of the card's stated Lean obligations, which
are all discharged.  The card's remaining open gate is the parent-literature/novelty audit, which
is not a formalization obligation.
