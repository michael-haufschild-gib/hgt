# Finite consequences of the certified arithmetic inputs

- **ID:** review-1411-finite-work-obstacles
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Obstacles summary, §2.1](../../../reports/review-1411/obstacles-summary.md).

## Results and Lean endpoints

| Task | Exact scope | Lean |
|---|---|---|
| A1 | Jensen real-rootedness for every degree at most `31922`, from width `3/8` and verified height `67`. | [Jensen rung](../../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean) |
| A2 | Common certified floor interfaces for smaller apertures, real/complex tests, step packets, charge-free neutral forms and dressed middles; constants and cutoff ranges explicit. | [Floor certificates](../../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheCertifiedFloorInRealComplexAndWindowForms.lean) |
| A3 | Exact rational ladder milestones and decomposition of `levelAt 2 4` into its three remaining nonnegative excesses. | [Three-excess budget](../../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheThreeRemainingExcessesOfTheRatioThreeLadder.lean) |
| A4 | Actual pole/Gamma/jump/root-number terms in WL, CHMD, SZ, HAT-C and PM transfers. | [WL/CHMD](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/TheSevenEighthsStripControlsTheCompletedWaves.lean), [SZ](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/TheAlignedSuzukiEnergyRetainsThePoleAndGammaIntegral.lean), [HAT-C](../../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheCertifiedApertureHasTheCorrectedScatteringFloor.lean), [PM](../../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/TheEisensteinFamilyRetainsItsCompletionAndScatteringBounds.lean) |
| A5 | The `2^ρ/3^ρ` trace equation, two/three reflection discriminants, realized central sheet exchange and contact ideals at degrees `1,2,3,4,9`. | [Trace/reflection](../../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeTwoThreeTraceEquationAndReflectionRelation.lean), [collisions](../../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheDoubleCollisionHasTheExplicitTwoSheetPermutation.lean), [contacts](../../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFirstTwoPrimeContactIdeals.lean) |
| A6 | Primitive completion, simple pole, reflection and scattering for `CyclotomicField 3 ℚ`. | [Eisenstein family](../../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/TheEisensteinFamilyRetainsItsCompletionAndScatteringBounds.lean) |
| A7 | Three-even-moment Gram certificate with exact margin `1/1000000`, and strictness exactly for nonzero moment triples. | [Exact Gram certificate](../../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheFirstThreeEvenMomentsArePaidAtAperture1881Over5000.lean) |

## Mathematical reductions

- `jensenNonrealCount_eq_zero_of_le_31922` uses
  `SquareRootThreshold.zetaZeroWidth_le_three_eighths` and verification through height `67`.
  The sector budget is `(d−1)·9/64≤4489`; `31922` satisfies it and `31923` does not.
- `levelAt_four_eq_three_excesses` removes the zero first overlap loss.
  Monotonicity and nonnegativity of `levelAt` give `levelAt_four_eq_zero_iff_three_excesses`:
  `levelAt Q 4=0` equivalent to three zero-level excesses at ratios
  `10609/5000`, `112550881/50000000`, and `103^8/(100^8/2)`, for `Q≥2`.
- `firstStep_continuum_certificate`, `firstStep_window_certificate` and
  `firstStep_dressed_certificate` use support inclusion to preserve the real and complex floor `1/50000` below
  `1881/5000`. The packet dictionary carries it to windows with
  `5000(R+J)≤10609R`, `R≥1`, `Q≥2`; the dressed-middle ranges are
  `100a≤3R` and `50b≤3(R+a)`.
- `primeTwoThreeRatioEquation_map` substitutes `e₂−e₃` into the monic trace equation.
  Additivity of prime monomials gives the factors `X−2^ρ/3^ρ`, with every analytic-multiplicity
  copy retained. `primeTwoThreeRatioEquation_rootSet` identifies exactly those roots.
- `primeTwoThreeReflectionSquareRoot_sq` places the product of the two reflection differences
  in the zero's pair field.
  Its square is `(T₂²−8)(T₃²−12)`. The two differences cannot both vanish,
  by injectivity of the two prime exponent coordinates and nonrealness of every ξ zero.
- `graphIdeal_first_two_primes` and `graphIdeal_first_prime_squares` specialize the prime-power
  contact formulas: `J(1,2)=(2)`, `J(1,3)=(3)`, `J(2,4)=(4)`, `J(3,9)=(9)`.
  Distinct prime valuations give `graphIdeal_two_three`: `J(2,3)=ℤ`.
- `exists_forward_doubleCollision_transposition` applies `exists_isCollision_center_two`
  and the local sheet identities. At central double collisions with arbitrarily large real
  parts of complex time, the labels `√2` and `−√2` are interchanged by `s↦−s` and remain
  distinct on a punctured neighborhood.
- `scatteringWeilEnergy_full_floor_firstOverlap` transfers the certified floor with jump tail,
  Robin mass correction and omitted prime contacts all retained.
- `completedWeilLag_primeSide_bound` and `chmdPrimeWave_completed_three_eighths`
  transfer width `3/8` to the literal completed waves at exponent `3/8`.
- `eventually_suzukiAlignedEnergy_literal_bounds` retains the integral of
  `2cosh(t/2)−ccmGammaTranslationDensity(t)` in amplitude `A_N`.
  Aligned energy satisfies `A_N²≤E_N≤1889568(log 4+4)² A_N²` eventually.
- `chi3D_primitive_rootNumber` and `gammaFactor_chi3D` give root number `+1` and `Γℝ(s+1)`.
  The Bianchi phase at the removable origin is `−1`; the completed quotient
  on the punctured spectral axis retains the polar factor;
  `bianchiScatteringPhase_eq_explicit_gamma_factors` gives its literal Gamma quotient.
- `thirdCyclotomic_primitive_hecke_completion` and `thirdCyclotomic_hecke_source_and_pole`
  identify the primitive trivial Hecke source with `ζL(χ₋₃)` off `1`, retaining pole order `−1`
  at `1`. `thirdCyclotomic_hecke_reflection` keeps the actual Gauss/parity phase.
  The proved Hecke strip feeds `eisenstein_scattering_certificate` at `δ=1/16`, hence pulse
  decay at `1/16−ε` for every `ε>0` and compact smooth pulse.
- `firstOverlapEvenMomentCapacity_certificate` uses the exact reflected-pair polynomial
  integrals, positive principal minors and inverse mixed charge form. Two square completions
  give margin `10⁻⁶(u²+v²+w²)`. Positivity of the sum of squares gives
  `firstOverlapEvenMomentCapacity_lt_iff`, with strictness exactly for nonzero triples.

## Boundaries

No all-aperture positivity, vanishing of the remaining overlap excesses, prescribed off-centre
collision, Artin holomorphy, infinite square-class classification or improved scattering rate
is asserted.
Test and window restrictions are explicit domain conditions. No unproved analytic premise
is introduced. All twelve changed theorem modules passed direct `lake --old env lean` checks.
Transitive axiom audits contain only `propext`, `Classical.choice` and `Quot.sound`;
the owning umbrellas import every endpoint module.
