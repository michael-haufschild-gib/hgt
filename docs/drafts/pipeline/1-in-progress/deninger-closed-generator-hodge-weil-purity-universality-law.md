# Deninger closed-generator/Hodge/Weil purity universality law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.DeningerClosedGeneratorHodgeWeilPurityUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

Whole-corpus terminal-module pairing placed these mechanisms in one dependency component:

- `DeningerDivisorClosedGenerator`: maximal closed dense divisor multiplication generator and
  multiplicity-exact eigenvectors;
- `DeningerArithmeticLocalHodgeObstruction`: each source-local positive Hodge form commutes with
  Frobenius exactly when its centered Xi support point is real;
- `DeningerArithmeticFiniteHodgePackets`: positive finite Hodge packets have no cancellation, and
  invariance along the geometric exhaustion forces RH;
- `XiWeilPositivityCriterion`: positivity of the full square-summable Weil polarization is
  equivalent to RH.

No corpus theorem identifies the local source Hodge test, every positive finite-packet exhaustion,
and full Weil positivity as the same purity law carried by the closed divisor generator.

## Statement

Define:

1. `DeningerLocalJetHodgeFrobeniusInvariant`: every canonical source-local rank-one Hodge form
   intertwines ordinary and compact-support Frobenius;
2. `DeningerFiniteJetHodgeExhaustionFrobeniusInvariant`: for every strictly positive support
   weight, every geometric finite Hodge packet in the closed-ball exhaustion intertwines
   Frobenius;
3. `XiWeilSquareConeNonnegative`: the complete Xi Weil polarization is nonnegative on every
   square-summable test function.

Then the canonical divisor generator is closed, has dense domain, has every multiplicity copy as
an eigenvector, and

`local Hodge invariance ↔ finite-packet invariance ↔ Weil positivity ↔ RH`.

## Dependency-closed proof

1. Closedness, density, and the coordinate eigenvector equation are exactly
   `deningerDivisorClosedTheta_isClosed`, `deningerDivisorClosedTheta_dense`, and
   `deningerDivisorClosedTheta_eigenvector`.
2. Under RH, for each support point `rho`, choose its zeroth multiplicity copy
   `⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩`. Spectral reality of that copy makes
   `xiSpectralPointSupport rho` real.
3. `deningerCompactOpenLocalJetHodge_theta_commutes_iff` converts this reality into local Hodge
   invariance. Conversely,
   `riemannHypothesis_of_deningerCompactOpenLocalJetHodge_theta_commutes` converts global local
   invariance into RH.
4. Under RH, each local summand in every finite Hodge packet commutes. Linearity of
   `deningerCompactOpenThetaCompact` and the packet sum gives every positive-weight finite-packet
   invariance.
5. Conversely, instantiate the universal finite-packet predicate with constant weight `1`.
   `riemannHypothesis_of_deningerFiniteJetHodge_exhaustion_commutes` yields RH.
6. `riemannHypothesis_iff_xiWeilPolarization_nonneg` identifies RH with the full Weil cone.
7. Transitivity gives all displayed equivalences.

No conjectural Hodge star, prime-orbit space, hidden positivity axiom, or computation enters.

## Novelty audit

Corpus audit: no declaration combines these three tests or proves their pairwise equivalence.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Core equivalence proof passed:
  `lake env lean /private/tmp/law477_core_scratch.lean`.
- Existing closed-generator dependency passed independently:
  `lake env lean GaloisForLFunctions/RHTower/DeningerDivisorClosedGenerator.lean`.
- Direct source elaboration is deferred to final module audit because this checkout has no cached
  `DeningerDivisorClosedGenerator.olean`; Lean stops before elaborating the new file.
- Wired into `GaloisForLFunctions.RHTower`.
