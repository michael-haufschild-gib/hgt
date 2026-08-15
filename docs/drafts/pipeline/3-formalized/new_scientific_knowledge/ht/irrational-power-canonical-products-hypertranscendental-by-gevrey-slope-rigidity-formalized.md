# Irrational-power canonical products are hypertranscendental — formalized

- **ID:** `irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity.md`
- **Type:** FORMALIZATION CERTIFICATE

## Headline

```text
RHTower.hypertranscendental_powerCanonicalProduct_irrational :
  ∀ {s : ℝ}, 0 < s → Irrational s → Hypertranscendental (powerCanonicalProduct s)

#print axioms → [propext, Classical.choice, Quot.sound]
```

`Hypertranscendental f := ¬ DifferentiallyAlgebraic f`, and `DifferentiallyAlgebraic f` is the
existence of `n` and a nonzero `P ∈ MvPolynomial (Fin (n+2)) ℂ` with
`P(z, f, f', …, f^{(n)}) = 0` for every `z`.  So the theorem says: for every positive irrational `s`
the canonical product `W_s(z) = ∏_{n≥1} E_{⌊1/s⌋}(-z/n^s)` satisfies **no** algebraic differential
equation over `ℂ(z)`.

## Lean modules added for this card

```text
formal/GaloisForLFunctions/HTGeometry/RegularFactorialProfile.lean
formal/GaloisForLFunctions/HTGeometry/FactorialProfileShiftRatio.lean
formal/GaloisForLFunctions/HTGeometry/ShiftPolynomialDegreeBound.lean
formal/GaloisForLFunctions/HTGeometry/NewtonIrrationalUniformGap.lean
formal/GaloisForLFunctions/HTGeometry/ShiftTermPowerBound.lean
formal/GaloisForLFunctions/HTGeometry/ShiftTermFactorialBound.lean
formal/GaloisForLFunctions/HTGeometry/ShiftTermUnifiedBound.lean
formal/GaloisForLFunctions/HTGeometry/ShiftSumLimits.lean
formal/GaloisForLFunctions/HTGeometry/ShiftSumDominance.lean
formal/GaloisForLFunctions/HTGeometry/BarnesTailLinearObstruction.lean
formal/GaloisForLFunctions/HTGeometry/GammaConvolutionBound.lean
formal/GaloisForLFunctions/HTGeometry/GammaProfileProduct.lean
formal/GaloisForLFunctions/HTGeometry/ProfileBoundedSeries.lean
formal/GaloisForLFunctions/HTGeometry/TaylorDefectProfileBound.lean
formal/GaloisForLFunctions/HTGeometry/TaylorDefectUniformExponent.lean
formal/GaloisForLFunctions/HTGeometry/ProfileRatioLimits.lean
formal/GaloisForLFunctions/HTGeometry/BarnesTailNonlinearObstruction.lean
formal/GaloisForLFunctions/HTGeometry/AsymptoticPolynomialCoefficients.lean
formal/GaloisForLFunctions/HTGeometry/MvPolynomialLinearSubstitution.lean
formal/GaloisForLFunctions/HTGeometry/EulerOrdinaryJetChange.lean
formal/GaloisForLFunctions/HTGeometry/PowerCanonicalProductRightHalfPlane.lean
formal/GaloisForLFunctions/RHTower/BarnesTailAsymptoticExpansion.lean
formal/GaloisForLFunctions/RHTower/PowerCanonicalProductHypertranscendence.lean
formal/GaloisForLFunctions/RHTower/EulerJetRealRestriction.lean
formal/GaloisForLFunctions/RHTower/BarnesEulerRemainderStep.lean
formal/GaloisForLFunctions/RHTower/BarnesRemainderComplex.lean
formal/GaloisForLFunctions/RHTower/BarnesRemainderJetBridge.lean
formal/GaloisForLFunctions/RHTower/BarnesRemainderMeroTransfer.lean
formal/GaloisForLFunctions/RHTower/PowerCanonicalProductHypertranscendental.lean
```

Earlier layers of the card (the Mellin/Barnes representation at every genus, the exact Gevrey order
of the zeta tail, the DA closure properties, the asymptotic-to-formal transfer, Maillet in the
linear and nonlinear cases) were formalized in previous sessions and are listed in the card's own
progress log.

## Formal theorem chain

```text
 1  barnesTailSeries s                         R̂_s(t) = ∑_{k≥1} (-1)^k ζ(-sk) t^k
 2  zetaTailProfile, abs_zetaTailModulus_le_profile,
    infinite_setOf_profile_le_abs_zetaTailModulus
                                               the two-sided profile: |b_k| ≤ Θ(k) always, and
                                               ≥ δΘ(k) infinitely often (irrationality of s)
 3  IsRegularFactorialProfile, block_lower/upper
                                               the abstract profile axioms
 4  tendsto_shiftTail_div_leading              every shift but the leading Newton vertex is
                                               negligible in the coefficient recursion
 5  not_eulerLinearOp_barnesTail_eq            R̂_s solves no LINEAR analytic equation
 6  HasProfileBoundExp, hasProfileBoundExp_zero_of_isGevreySeries_zero
                                               a convergent series needs no polynomial factor
 7  exists_uniform_norm_coeff_taylorDefect_le  the Taylor defect exponent is fixed BEFORE the
                                               truncation order — the quantifier order is the point
 8  tendsto_shiftedProfile_div_leading         Θ(N+1)Θ(n−N−1) loses to (n+1)^{deg Φ_ν}Θ(n−ν)
 9  not_isFormalEulerADESolution_barnesTail    **R̂_s solves no analytic ADE at all** (nonlinear;
                                               nondegeneracy discharged by a minimal annihilator)
10  barnesEulerRemainder, barnesEulerJet       the Barnes remainder and its Euler jets in t = 1/x
11  isAsymptoticExpansion_barnesEulerJet       (6): those jets have the Euler jets of R̂_s as
                                               Poincaré expansions at 0⁺
12  eval₂_powerSeries_eq_zero_of_eventually    (14) ⟹ (15) with ℂ[t] coefficients
13  not_polynomial_relation_barnesEulerJet     the remainder satisfies no ADE over ℂ(1/x)
14  weightedJet_eq_sum                         z^m f^{(m)} = ∑_{k≤m} d(m,k) θ^k f, unitriangular
15  eulerDeriv_iterate_ofReal                  real Euler jets = complex Euler jets restricted
16  barnesEulerRemainder_eq_iterate            the weighted remainders are Euler jets of one function
17  powerCanonicalProduct_ne_zero_of_re_pos    W_s has no zero with Re z > 0
18  analyticOnNhd_barnesRemainderC             the remainder is analytic on the right half-plane
19  eulerEigen_barnesLeadingTermC              z u' = (1/s) u in meroField of the half-plane
20  differentialAlgebraicOver_barnesRemainderC §4.1–4.4 instantiated: W_s DA ⟹ remainder DA
21  matrixSubst_injective, reversedRelation_ne_zero
                                               the jet change and the z ↦ 1/t reversal keep the
                                               relation nonzero
22  hypertranscendental_powerCanonicalProduct_irrational
                                               **the card's theorem**
```

## What the formalization does NOT use

The card's §5 cited the **sharp** half of the Sibuya--Ramis exact Gevrey-order theorem.  It is not
used, and no part of the Lean proof depends on it.  What §5 was needed for is a single implication
about a single series whose coefficients are pinned on both sides; for such a series the leading
Newton vertex dominates the whole coefficient recursion directly.  Steps 6–9 above prove that.

Three facts make the nonlinear reduction unconditional, and all three are about quantifier order:

* the polynomial exponent in the defect estimate is attached to the equation, so it is chosen
  before the truncation order;
* the linearization along the truncation agrees with the linearization along the solution up to the
  truncation order, so the leading vertex sits below a ceiling `⌈m/s⌉ + v` that does not move;
* the truncation order is then free to be taken past both.

## Audit

```text
lake build GaloisForLFunctions.RHTower.PowerCanonicalProductHypertranscendental   ✓
#print axioms RHTower.hypertranscendental_powerCanonicalProduct_irrational
  → [propext, Classical.choice, Quot.sound]
scripts/formal_tools.py lint --check-generated                                     ✓ (exit 0)
```

All new modules are wired into `GaloisForLFunctions/HTGeometry.lean` and
`GaloisForLFunctions/RHTower.lean`.
