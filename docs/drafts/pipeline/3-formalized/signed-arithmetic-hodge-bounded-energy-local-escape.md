# Bounded prime energy escapes fixed integer windows

## Statement

Let E_N(x)=log(N)*norm(x)^2-inner(P_N*x,x) be the actual renormalized prime
energy, and let mass_L(x) be the sum of squares of the first L coordinates,
using the zero extension outside horizon N.

For every real T, natural L and epsilon>0, all sufficiently large N satisfy

norm(x)=1 and E_N(x)<=T imply mass_L(x)<=epsilon,

uniformly over every vector in that sublevel. The comparison uses the explicit
inequality mass_L(x)<=2*norm(x-v)^2+2*mass_L(v) for L<=N.

## Proof

Actual bounded prime-energy sets admit approximation in squared norm by a fixed
finite Ramanujan span with any prescribed error. Choose error
eta=min(epsilon/4,1). The approximant v has norm at most two. Uniform local
capture for that finite span makes mass_L(v)<=epsilon*norm(v)^2/16<=epsilon/4
at sufficiently large horizons. The comparison inequality gives the result.
The finite positive conductor set is transported explicitly from naturals to
positive naturals, preserving its actual horizon vectors and sums.

## Lean

Module:
formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/BoundedPrimeEnergyEscapesEveryFixedIntegerWindow.lean

Declarations:

- primeHorizonWindowMass_le_approximation_cost
- eventually_primeHorizonWindowMass_le_of_energy_le

The final individual no-olean check passes. Both capstones depend only on
propext, Classical.choice and Quot.sound. The module is wired into its umbrella.

## Scope

The statement concerns actual prime matrices and literal integer-coordinate
mass. Finite approximation remains compatible with escape because its modal
vectors depend on the horizon. The theorem does not determine continuous Gamma,
both polar moments or the full Weil sign, and does not prohibit source transfer
with separately proved moving coordinates and norm comparisons.
