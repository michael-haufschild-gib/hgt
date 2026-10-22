# ACCE — contributions 10–24 of 2026-10-22 (continuation of acce/contributions-2026-10-22)

All modules in `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy`, compiled with
fresh oleans, wired into the umbrella.

10. `TheSecondDampingTangentAndConvexity` — `dampedVonMangoldtSecond`, `dampedReadoutSecond` (from
    `ζ''`), the second tangent `dampedChebyshevSecond`, `hasDerivAt_signedDampingWork`
    (`W' = ‖E_ε‖² + ⟪A_ε,F_ε⟫`), `riemannHypothesis_of_second_tangent_pairing_ge` — constant-free.
11. `HorizonAveragesAndSparseHorizons` — dyadic horizons and Cesàro means suffice (`Admits.of_cesaro`,
    `admits_iff_cesaro`); horizon monotonicity does the work.
12. `TheApertureFloorTransportFromTheCertifiedEndpoint` — derivative-free multiplicative floor
    transport; instantiated on `ccmRestrictedWeilGroundEnergy` from the certified endpoint `3/10`
    (`μ ≥ 1/5000`): `riemannHypothesis_of_groundEnergy_relative_step` (open problem 7's endpoint).
13. `TheTangentIsADilationAverageOfTheSource` — hyperbola rearrangement;
    `dampedVonMangoldt_eq_dilation_convolution`; `dampedChebyshevError_eq_dilation`;
    the work is the dilation numerical range (`signedDampingWork_eq_dilationForm_add_correction`).
14. `TheQuotientIncidenceKernelIsIndefinite` — κ_ε has zero diagonal (`Λ(1)=0`), `κ_ε(2,1) = log2·2^{-ε}`,
    `exists_row_rowDilationForm_neg`: no form-positivity route; the sign must use the source.
15. `TheDilationInversionLawOfTheSource` — `dampedTwist` is a ring hom of the Dirichlet ring;
    `Σ_{j≤n} j^{-ε} A^raw(⌊n/j⌋) = n` and the centred version (`sum_rpow_mul_centeredPrefix_eq`).
16. `TheDilationCalculusOnIntegerPrefixes` — `prefixDilation_comp` (`D^f∘D^g = D^{f*g}` exact),
    `Λ_ε * ζ_ε = (log)_ε`, the log-dilation law of the source.
17. `TheCutoffParameterCostsNothingBeyondAdmission` — open problem 6 closed: the accumulated
    physical shell cost is bounded given admission (`exists_bound_sum_ramanujanPhysicalShellEnergy_of_admits`).
18. `TheSelfImprovingEnergyIdentity` — `E_T = ⟪A,ρ_ε⟫ − ⟪A, D^{ζ,≥2}A⟫` with `ρ_ε(n)=n−m₀Φ_ε(n)`;
    `admits_of_sublinear_pairings` gives admission at a SINGLE damping (no transport).
19. `TheInversionDefectIsPositive` — `(density).re = 1/realZetaSeries(1+ε)`; `0 ≤ ρ_ε(n) ≤ n`;
    only the positive part of the source feeds the explicit term; one-sided criterion.
20. `ThePronicDilationContractionAndItsThreshold` — `‖v(⌊·/j⌋)‖_T ≤ √(2/j)‖v‖_T`; the off-diagonal
    term-by-term cost is `√2 Σ_{j≥2} j^{-(ε+1/2)} · E_T`; that series converges iff ε > 1/2
    (`summable_dilationSeries_of_half_lt`, `not_summable_dilationSeries_of_le_half`);
    `admits_of_linear_pairing_of_dilationSeries_lt_one`.
21. `TheTangentObeysAnExplicitDilationLaw` — the damped unit dilation of the tangent is Möbius-free.
22. `TheWorkIntegralIsTheEnergyDrop` — `∫_a^c 2W_T = E_T(c) − E_T(a)`; additive dictionary;
    `exists_signedDampingWork_lt_of_not_admits` (visibility witness).
23. `TheDilationSelfSimilarityOfThePronicMeasure` — a dilation fibre carries exactly `1/j` of the
    level's pronic mass (`sum_Icc_pronic_dilation_fibre`), hence the sharp `1/√j` contraction;
    every finite head of the dilation scales is paid.
24. `TheMajorantSourceIsNeverAdmitted` — the majorant row `d^{-ε}` dominates `|μ(d)d^{-ε}|` and its
    pronic energy diverges for every `ε ≤ 1/2` (`not_admits_majorantEnergy`): the named
    unconditional selectivity certificate against sign-blind estimates.

## State of the obligation after these
The damping obligation is: control the signed anti-correlation `⟪A_ε, D^{ζ_ε,≥2} A_ε⟫` (equivalently
the negative part of the signed work), knowing that (a) the explicit linear part is a positive-weight
pairing, (b) finite heads of the dilation scales are paid, (c) term-by-term majorants die exactly at
ε = 1/2, (d) sign-blind estimates are refuted by the majorant source.

## Lean notes added
- `div_le_div_of_nonneg_right`/`div_le_div_of_nonneg_left`, `Finset.sum_fiberwise_of_maps_to`,
  `Finset.card_nsmul_le_sum`, `Real.rpow_le_rpow_of_nonpos`, `not_summable_iff_tendsto_nat_atTop_of_nonneg`,
  `ArithmeticFunction.abs_moebius_le_one`, `Real.sqrt_div`, `Real.summable_nat_rpow`,
  `ofReal_realZetaSeries`/`realZetaSeries_pos` (RHTower.BoseMellinCoordinate) all used.
- `field_simp` often closes goals that then make a trailing `ring` an error ("no goals").
- `Finset.range_subset.mpr` can mis-elaborate inside `sum_le_sum_of_subset_of_nonneg`; give the
  subset proof pointwise instead.
