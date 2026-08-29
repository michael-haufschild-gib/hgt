# JAS Gamma-theta separate-normalization wall

Status: FAILED/RETIRED — obstruction and positive survivor formalized in Lean
Route: JAS separate-gauge completion subroute
Date: 2026-08-29
Labels: `[PROVED IN LEAN]` `[CORPUS-NOVEL NO-GO]` `[POSITIVE SURVIVOR FORMALIZED]` `[TARGETED EXTERNAL NO-MATCH]` `[GLOBAL NOVELTY UNVERIFIED]`

## Retired claim

The existing finite-packet cross-aperture identity cannot be promoted to the needed infinite
reflection transport by separately normalizing forward and reflected synchronized-lcm Gamma
tensor legs against their common prime-boundary constant.

At every actual Xi divisor, those two separate local-defect families cannot both be summable.
This kills only separate absolute completion.  It does not kill a relative construction that
cancels the common divergent part before either leg is completed.

Formal module:
`formal/GaloisForLFunctions/RHTower/JointAncestryGammaThetaSeparateNormalizationWall.lean`

## Corpus origin

Mandatory `scripts/formal_tools.py research` searches identified:

- the local aperture factor inside `gammaSewnSynchronizedLcmWeight`;
- `gammaSewnMobiusValuationContractionMultiplier_pow_four`;
- the cross-aperture packet gauge `jasGammaThetaCreation_crossAperture_packet_gauge`;
- the exact prime square-summability wall
  `summable_normSq_primePoissonParameter_zero_iff`;
- the new JAS reflection-Cauchy RH endpoint.

No corpus theorem computed this renormalized local defect or its reflection incompatibility.

## Positive survivor

Write `q=p^{-x}` and `c_x(p)` for the Gamma-sewn valuation contraction.  Lean proves the exact
first-order cancellation

`8 * (c_x(p) * (1-q))^4 = (1-q^2)^4 / (1+q^4)`.

The resulting defect is

`D_x(p)=q^2*(4-5q^2+4q^4-q^6)/(1+q^4)`

and satisfies, for every `x>0`,

`q^2 <= D_x(p) <= 4*q^2`.

Consequently

`Summable D_x ↔ 1/2 < x`.

This is the sharp square-tangency law exposed by the failed strategy: Gamma sewing cancels the
linear aperture drift, but not the critical prime-Hilbert wall.

Capstones:

- `jasGammaThetaLocalRenormalizedFourthFactor_eq`
- `jasGammaThetaLocalRenormalizedDefect_eq`
- `summable_jasGammaThetaLocalRenormalizedDefect_iff`
- `xiDivisorSupport_not_summable_jasGammaThetaLocalRenormalizedDefect_both`

## RH-chain consequence

Retired chain:

1. separately complete forward/reflected Gamma support gauges — impossible by this theorem;
2. preserve prime-Haar prefix Cauchy status;
3. use `xiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff` to force `Re rho=1/2`;
4. conclude RH from the Xi-divisor endpoint.

Surviving chain begins with one genuinely relative infinite-support Gamma-theta polarization.  It
must cancel the common divergent factor before completion, produce Cauchy coherence directly, and
then feed steps 3--4.  Finite-packet or separately completed diagonal gauges are now excluded.

## Novelty audit

Classical infinite-product and Kakutani theory are prior art and not claimed novel.  Targeted
search found no external statement of this corpus-specific Gamma-sewn square-tangency formula,
sharp prime wall, or Xi-reflection no-go.  Connes--Consani independently emphasize that semi-local
normalizations cannot replace the global Poisson normalization in RH operator routes, consistent
with this obstruction:

- https://arxiv.org/abs/1910.14368
- https://arxiv.org/abs/1611.10289
- https://arxiv.org/abs/1309.3455

## Audit

- Direct `lake env lean` check passed with no diagnostics.
- Exact leaf build passed: `12199/12199`.
- `#print axioms` on four capstones: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint found no forbidden declaration in this module; repository-wide failure consists of
  pre-existing unrelated reachability errors and large-file warnings.
- Module wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.
