# Joint payment of the entire square source and full pole

- **ID:** acs-joint-whole-square-polar-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Pay the coarse even-prime-power source from the retained coarse
  Gamma share in the proved full-polar nonfirst source, retaining positive
  coarse and detail reserves and recording two original scalar costs.

## Source and target

Let g be the original average profile, h the Haar detail, F=g+h, D the
logarithmic detail mass, and κ=fullDetailPrimeGap>0. Let R denote
fullPolarNonfirstSourceForm and S₂ the source over every even prime exponent.
The new source is exactly U=R−S₂(g).

Target: there exist c>0 and A≥1, independent of profiles and horizon, such
that details vanishing below A satisfy

`c Γg+(γ_E/2)∫g²+(κ/8)D+∫h²+2 coshHalfMoment(F)²
 ≤ U+2 sinhHalfMoment(F)²+(1/2)(∫F)²`.

The source decomposition must exhibit S₂(F) exactly once. Its remaining
detail prime term is haarPrimeEnergy−S₂(h); its remaining mixed prime term
is the odd-exponent source above one. No auxiliary polar or mean correction
is added to U. The two adverse scalar costs remain explicit.

## Proof [PROVED HERE]

The compact-BV square theorem retains δΓg+(γ_E/2)∫g² in
Γg−S₂(g)+(1/2)(∫g)² for one fixed δ>0. Apply the full-polar joint theorem
with ε=δ/2. Adding inequalities leaves c=δ/2 of coarse Gamma. Haar details
have zero integral, so ∫g=∫F. The kernel of the finite detail head and the
two original moments is nonnegative; any strictly negative finite-family
subspace therefore has dimension at most A+2.

More explicitly, the two proved estimates give

`R+2 sinhHalfMoment(F)² ≥ (1−δ/2)Γg+(κ/8)D+∫h²+2 coshHalfMoment(F)²`,

`−S₂(g)+(1/2)(∫g)² ≥ (δ−1)Γg+(γ_E/2)∫g²`.

Their sum is exactly the target. All constants and the head are independent
of q,d,X. Applying it to the literal tail gives the unrestricted tail
version. Unfolding the mixed square source gives the exact identity

`U=ΓF+2 gammaHardyPhaseRate(0)∫h²−(haarPrimeEnergy−S₂(h))
   −S₂(F)−oddHigherPrimePowerMixedSource+P(F)`.

For a finite family, send coefficients to the first A detail coordinates,
the complete-profile sinh moment, and the complete-profile ordinary mean.
Both moments are linear by integrability of compact BV profiles. On the
kernel both scalar costs vanish. Every term on the left is nonnegative:
Gamma and square mass are nonnegative, c>0, γ_E>0, and κ>0. Thus U≥0 there.
A strictly negative subspace has zero intersection with the kernel, so
the readout restricts injectively to that subspace. Its dimension is bounded
by the target dimension A+2.

No analytic premise remains in this proof. Its exact Lean formalization is
TheEntireSquareSourceSharesTheFullDetailReserve.lean.

## Lean validation

Direct check passed without diagnostics:

`lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheEntireSquareSourceSharesTheFullDetailReserve.lean`

- `fullSquarePolarSourceForm_eq_source_parts`: the entire original even
  source occurs exactly once.
- `exists_fullSquarePolar_coarse_detail_reserve`: simultaneous coarse
  Gamma, coarse mass, logarithmic detail mass, detail mass and cosh reserves.
- `exists_fullSquarePolar_uniform_tail`: the same estimate on literal tails.
- `exists_uniform_fullSquarePolar_negative_dimension`: uniform bound A+2
  for every finite original profile family and strictly negative subspace.

Imported by the AID umbrella; umbrella not compiled. The previously checked
full-polar dependency's missing olean was built for this import. Existing
dependency oleans were preserved.

## Dependencies and scope

- TheFullPolarNonfirstSourceHasUniformFiniteIndex.lean: direct check passed.
- TheSquarePrimeEstimateHoldsOnCompleteProfiles.lean: existing compact-BV
  retained-Gamma estimate; existing compiled dependency.
- HaarCellProfiles.lean: exact zero integral of details.

This pays a previously absent coarse source block without spending the
complete Gamma energy twice. Coarse first-prime and odd-higher sources,
coarse archimedean mass, first-prime mixing, finite head and scalar costs
remain. No full-Weil index or RH conclusion is asserted.

No web search, novelty checks, numerical computations or axiom checks.
