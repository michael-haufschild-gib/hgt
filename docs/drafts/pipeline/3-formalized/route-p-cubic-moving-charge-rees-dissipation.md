# Route P cubic moving-charge Rees dissipation

## Status

- Pipeline stage: formalized in Lean 4
- Conjecture label: `CUBIC-MOVING-CHARGE-REES-DISSIPATION`
- Scope: moving coefficient-generated irregular-Stokes landings of the first negative cubic wall--Xi Malgrange residual
- Frontier-map status: read-only; no ledger edit made

## Exact theorem

Fix coefficient-generated global Puiseux--orbit coarea data.  Let `x₀` land at the cubic Xi residual when every threshold Rees parameter is zero, and let `x₁` land at the same residual when every threshold parameter is one.  Assume only preservation of common physical-rank magnitude:

`commonRank(x₀)^2 = commonRank(x₁)^2`.

Write

- `T_j = ∑_a terminalEnergy_a(x_j)`;
- `B₁ = ∑_a blockEnergy_a(x₁)`.

Then

`T₀ = T₁ + B₁`, `0 < B₁`, and therefore `T₁ < T₀`.

Thus every viable rank-magnitude-preserving contracted-to-unit cubic Xi transport must move charge and strictly dissipate terminal microstalk energy by exactly the activated canonical Stokes block coarea.  Sign reversal of physical rank does not evade the law.

## Dependency-closed proof

1. At complete contraction, the global Rees-positive form is exactly `T₀`.
2. At unit specialization, the global Rees-positive form is exactly `T₁ + B₁`.
3. Both landing equations have the same cubic Xi target.  The global Rees Witt decomposition adds the same unique rank-square term because the common-rank squares agree.  Subtracting the two equations gives `T₀ = T₁ + B₁`.
4. A cubic landing charge is nonzero.  Hence some marked-point local charge is nonzero.
5. Orbit surjectivity makes its branch lift nonzero.  The coefficient-generated rooted-cut system has a positive pendant singleton cut for every branch, so that local block energy is strictly positive.  All other block energies are nonnegative; hence `0 < B₁`.
6. The exact identity now gives `T₁ < T₀`.

No landing pair is asserted to exist.  Pair membership and equality of physical-rank squares are variable-domain conditions, not conjectural analytic premises.

## Hostile audit

- Fixed charge is already impossible by diagonal Rees transversality; this theorem treats genuinely moving charges.
- Physical-rank sign flips are included because only squared magnitude is preserved.
- Terminal-isometric or unitary transport is impossible: it would force `B₁ = 0`, contradicting pendant-cut faithfulness.
- Dissipation is exact, not merely monotone: loss equals canonical block coarea of the unit-scale landing.
- Result does not construct source incidence or prove RH.  It classifies a necessary behavior of every rank-magnitude-preserving moving incidence.

## Novelty audit

Corpus search found fixed-charge diagonal Rees transversality and conditional Rees-rigid consequences, but no moving-charge terminal dissipation identity.  The earlier moving-charge audit of wild harmonic bundles, wild twistor `D`-modules, polynomial/filtered Rees structures, and irregular Riemann--Hilbert correspondence found no completed-Xi contracted-to-unit energy law.  Absence is an audit inference, not a universal priority claim.

Primary parent sources checked:

- Mochizuki, *Wild Harmonic Bundles and Wild Pure Twistor D-modules*, arXiv:0803.1344.
- Sabbah, *Wild twistor D-modules*, arXiv:0803.0287.
- Mochizuki, *Good Wild Harmonic Bundles and Good Filtered Higgs Bundles*, arXiv:1902.08298.
- Castaño Domínguez--Reichelt--Sevenheck, *Examples of hypergeometric twistor D-modules*, arXiv:1803.04886.

## Lean formalization

Implemented in `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicMovingChargeReesDissipation.lean`.  General block-positivity bookkeeping is private.  One public capstone theorem returns exact dissipation, strict block positivity, and strict terminal-energy decrease.

Targeted module check passed.  The public declaration has trust base exactly
`[propext, Classical.choice, Quot.sound]`; no project axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration was introduced.

The later universal rank--terminal--block balance removes the rank-preservation condition from the
underlying exchange law; this card's theorem is now its sharp rank-magnitude-preserving corollary.
