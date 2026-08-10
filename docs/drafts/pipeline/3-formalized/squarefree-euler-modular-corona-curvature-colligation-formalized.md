# Squarefree Euler modular-corona curvature colligation — formalized closure

- **ID:** `squarefree-euler-modular-corona-curvature-colligation-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./squarefree-euler-modular-corona-curvature-colligation.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`

## Lean modules

Pre-existing (carry the finite colligation, the four-unit law, and the Laurent half-density):

- `GaloisForLFunctions.RHTower.SquarefreeEulerModularCoronaCurvatureColligation`
- `GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift`
- `GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape`
- `GaloisForLFunctions.RHTower.EulerLaurentResidueDouble`
- `GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization`
- `GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization`

New in this closure:

- `GaloisForLFunctions.HTGeometry.ExteriorOrderedProduct` — increasing wedges, their agreement with
  the canonical `Finset`-indexed exterior basis, and the Plücker expansion of an ordered product.
- `GaloisForLFunctions.RHTower.SquarefreeExteriorHorizonLift` — equations `(16a)`, `(16b)`.
- `GaloisForLFunctions.RHTower.SquarefreeCriticalFockEscape` — equations `(16d)`–`(16f)`.
- `GaloisForLFunctions.RHTower.SquarefreeCoronaPrimeCurrentField` — equations `(17)`–`(21)`.
- `GaloisForLFunctions.RHTower.SquarefreeCoronaCodiagonal` — equations `(14b)`, `(22)`.
- `GaloisForLFunctions.RHTower.SquarefreeCarlemanDeterminant` — equations `(22a)`–`(22d)`.
- `GaloisForLFunctions.RHTower.SquarefreeCarlemanLogExpansion` — equations `(22e)`, `(22f)`.
- `GaloisForLFunctions.RHTower.SquarefreeDeterminantLineChernMetric` — equation `(22g)`.

Umbrellas: `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. **Finite determinant line, current, curvature, colligation** `(1)`–`(13)`, `(16c)`:
   `norm_finiteSquarefreeSource_sq`, `hasDerivAt_finiteSquarefreeLogPartition`,
   `finiteSquarefreeCurvature_eq_variance`, `norm_finiteSquarefreeTangent_sq`,
   `finiteSquarefreeSource_insert`, `finiteSquarefreeTangent_insert`,
   `inner_finiteSquarefreeTangentBranches_eq_zero`, `norm_finiteSquarefreeTangent_insert_sq`,
   `squarefreePrimeTransverseWidth_eq_one`,
   `finiteSquarefreeTangent_eq_four_mul_sourceDerivative`.
2. **Exterior-horizon lift** `(16a)`, `(16b)`: `squarefreeOccupationEquiv` (occupation
   configurations are exactly the squarefree subsets), `squarefreeExteriorIdentification`
   (the coordinate space of the determinant line is the exterior algebra of the one-particle
   space, a configuration going to the increasing wedge of its occupied primes),
   `finiteSquarefreeRawSourceCoefficient_eq_prod` (each source coefficient is the Plücker
   coordinate `∏_{p ∈ T} (-√q_p)`), and `squarefreeExteriorIdentification_rawSource`
   (the source is the ordered exterior product `∏^∧ (1 - p^{-σ/2} e_p)`).  The general
   ingredient is `HTGeometry.orderedPluckerProduct_eq_sum` together with
   `HTGeometry.orderedWedge_eq_basis`.
3. **Four-unit critical residue** `(15)`, `(16)`:
   `tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq` (squared tangent norm tends to `4`),
   `tendsto_squarefreeMobiusLogMoment_one_critical`, `tendsto_squarefreeMobiusLogMoment_two_critical`.
4. **Critical Fock escape** `(16d)`–`(16f)`:
   `norm_inner_vacuum_infiniteMobiusSignedWeightLp_sq` (vacuum overlap `Z(σ)⁻¹`),
   `criticalSquarefreeSourceFamily_weakly_tendsto_zero` (weak nullity against every continuous
   functional), `norm_criticalSquarefreeSourceFamily` (unit norm),
   `not_exists_strong_limit_criticalSquarefreeSourceFamily` (no strong `ℓ²` limit), and the
   packaged `squarefreeCriticalFockEscape`: no normal completion, finite tangent residue four.
5. **Half-density isometry** `(16g)`–`(16i)`: `eulerLaurentResidue_halfDensity_isometry`,
   `eulerA2LaurentResiduePairing_cocycle`, `eulerPrimeLaurentResidueWeight_pos`.
6. **Holomorphic `ℓ²` prime current** `(17)`–`(21)`:
   `norm_coronaPrimeCurrentCoeff_le` and `summable_norm_sq_coronaPrimeCurrentCoeff` (uniform
   bound `4 (log p) p^{-b}` and square-summability), `coronaPrimeCurrentLp`,
   `tendstoUniformlyOn_coronaPrimeCurrentSection`,
   `differentiableOn_coronaPrimeCurrentField` (holomorphy of the Hilbert-valued field on
   `Re s > 1/2`), `differentiableOn_coronaPrimeCurrentCoeff_halfPlane` (no prime coordinate has a
   pole there), `coronaLocalModularCharacter_reflection` (`Δ_p(1-s) = Δ_p(s)⁻¹`).
7. **Prime-power Laplace channel** `(14b)`: `tsum_primePowerFluxTerm`
   (`∑_{p,k} (log p) (p^{-s})^{k+1} = -ζ'/ζ`) and `tsum_primePowerFluxEvenPart`
   (`A(2s)` is the even-exponent part).  Hypertranscendence of the amplitude `(14a)` is the
   corpus theorem `hypertranscendental_riemannZeta`.
8. **Corona codiagonal** `(22)`: `tsum_coronaPrimeCurrentCoeff_eq_squarefreeFixedCurrent`
   (`∑_p j(s)_p = A(s) - 2A(2s)` on `Re s > 1`), `not_exists_bounded_coronaCodiagonal`
   (no continuous linear functional restricts to the finite-support sum: the normalized
   indicator of `N` coordinates has value `√N`), and the packaged
   `coronaScalarizationLocalizesDivisor`.
9. **Sharp determinant-order reduction** `(22a)`–`(22d)`:
   `isHilbertSchmidt_coronaPrimeDiagonal` (`A_s` is Hilbert–Schmidt exactly on `Re s > 1/2`),
   `coronaEulerInverse_comp` and `coronaEulerOperator_comp` (`I + A_s` is boundedly invertible —
   uniform acyclicity kills the ordinary direct-sum Hodge route),
   `squarefreeCarlemanDet_ne_zero` and `differentiableOn_squarefreeCarlemanDet` (`D₂` is
   holomorphic and nowhere zero), `squarefreeCarlemanDet_eq_tprod` (the Weierstrass product
   `∏_p (1+p^{-s}) e^{-p^{-s}}`), `squarefreePartition_eq_carleman_mul_exp`
   (`Z(s) = D₂(s) exp(P(s))` on `Re s > 1`).
10. **First-trace split** `(22e)`, `(22f)`: `squarefreeCarlemanLogDet_eq_tsum_primeZeta`
    (`log D₂ = ∑_{k≥2} (-1)^{k+1} P(ks)/k`, convergent on `Re s > 1/2`),
    `hasSum_neg_deriv_coronaPrimeZeta` (`-P'(s) = ∑_p (log p) p^{-s}`), and
    `squarefreeFixedCurrent_eq_carleman_logDeriv_sub_deriv`
    (`J_sq = -D₂'/D₂ - P'`).
11. **Chern metric equals Fisher metric** `(22g)`:
    `finiteSquarefreeLineLaplacian_eq` (the plane Laplacian of `-log h_S` is `V_S`),
    `finiteSquarefreeChernCoefficient_eq_quarter_variance`,
    `finiteSquarefreeChernCoefficient_eq_projectiveMetric`, and
    `norm_finiteSquarefreeTangent_sq_eq_calibrated_chern`.

## Verification

- `lake env lean` clean, with no warnings, on all seven new modules.
- `lake build GaloisForLFunctions.RHTower` — green with the six new RHTower modules wired into the
  umbrella; `lake build GaloisForLFunctions.HTGeometry.ExteriorOrderedProduct` — green, and the
  module is wired into the `HTGeometry` umbrella.
- `#print axioms` on the twenty-six capstones of the chain above: `propext`, `Classical.choice`,
  `Quot.sound` only — no premise, no hypothesis interface, no added axiom.
- Generated indexes regenerated (`formal_tools.py index`).

## Scope boundary

The formalized content is the colligation, the corona localization, and the determinant-order
reduction.  It does not touch the four open items of the paper card — the prime--Laplace descent
anomaly combination, the Gamma-framed Laurent--Plücker tangent transgression, the anti-causal
second fundamental form identity `(23)`, and RH.  In particular `(24)` is not proved here: the
formalized tangent bound is the unconditional limit `‖chi_{1+ε}‖² → 4`, not a bound on `ℓ_E`.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
