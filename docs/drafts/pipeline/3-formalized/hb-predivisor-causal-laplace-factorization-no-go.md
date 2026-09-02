# HB pre-divisor causal Laplace factorization no-go

- **ID:** HB-PREDIV-LAPLACE-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** No signed nonnegative-rate causal spectrum with finite exponential variation at any physical anchor realizes exact HB pre-divisor susceptibility on the remaining tail interval.

## Proof chain killed

`causal spectral two-leg factorization -> radiative ++ compensation -> full causal-cut extinction -> unit clock covariance -> RH`.

For `0 ≤ a < 1/2`, exponential tilting gives finite positive measures `mu, nu`. Their Laplace difference `L` is holomorphic on `Re z>0`. Equality with exact susceptibility on `a<x<1/2` forces, by identity theorem,

`D(z+a)L(z)=N(z+a)`.

At `z=1-a`, corpus polynomials satisfy `D(1)=0` and `N(1)=864`, contradiction.

## Novelty audit

Corpus search found finite-energy, late-time finite-variation, and open-complex-set holomorphy no-gos, but not this real-interval pole-clearing obstruction. Primary literature through 2026-08 covers topological-black-hole QNMs, AIME, Teukolsky sources, branch cuts, and general Laplace/strip representations; no exact HB susceptibility theorem of this form was found.

## Lean

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingHBPreDivisorCausalLaplaceFactorizationNoGo`
- Capstone: `d4HBPreDivisorExponentiallyFiniteVariationCausalLaplaceRouteKilled`
- Direct `lake env lean`: PASS
- Targeted build: `12471/12471` PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Global lint: stopped only by unrelated shared-tree umbrella-reachability failures; this module is reachable and no lint error names it

## No-go closure

- **Exact obstruction:** positive continuation pole conflicts with half-plane holomorphy of every exponentially finite-variation causal Laplace spectrum.
- **Positive survivor:** any spectral realization must fail finite exponential variation at every physical anchor, use negative/growing rates, change support/sheet, or land distributionally outside ordinary Laplace transforms.
- **New insight:** hard-edge infinite energy is insufficient; every locally exponentially temperable infinite-energy spectrum is excluded.
- **Status:** paper- and Lean-proved; novelty candidate pending external expert review.
