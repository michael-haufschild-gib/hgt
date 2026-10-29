# Growing Ramanujan families have a square-root horizon

## Formalized theorem

For every Q>=2, N>=0 and real coefficient family c_m, the actual pole-profile
packet F(n)=sum_{1<=m<=Q} c_m*ramanujanPoleProfile(m,n) satisfies

 (H_N-H_{Q(Q-1)}) sum c_m^2 <= sum_{1<=n<=N} F(n)^2,
 (log(N+1)-log(Q(Q-1)+1)) sum c_m^2 <= sum_{1<=n<=N} F(n)^2.

Thus log(N+1)-2logQ is a lower frame constant. The exact logarithmic constant
is positive once N>Q(Q-1). All coefficients and all conductors up toQ are
controlled at the same horizon, with no fixed-conductor limiting argument.

## Mechanism

Resolve normalized Ramanujan sums into primitive roots. Distinct exact orders
are disjoint, and the root coefficient square mass is sum c_m^2. The existing
sharp two-sided large sieve gives ordinary packet mass at least
(N-Q(Q-1))*sum c_m^2. Nonnegativity gives its positive part. Abel summation
compares this with constant mass delayed toQ(Q-1), so harmonic weighting loses
only H_{Q(Q-1)}. Monotonicity of H_n-log(n+1) supplies the logarithmic bound
without an extra constant loss.

## Novelty and boundary

The prior whole-family Gram estimate has error proportional to sum m^2. This
new lower bound retains cross-conductor arithmetic cancellation and permits
cutoffs near the square-root integer horizon. It supplies neither a matching
upper bound nor a small prime residual at that cutoff, and it does not prove
complete-Weil positivity.

The alternative finite-part-locality idea remains unproved: conductor Gram
finite parts may vanish unless one conductor quotient is a prime power.
It was not used in this theorem and is not a formalized claim.

## Lean declarations and validation

HarmonicMassFollowsDelayedCounting.lean:
 harmonic_mass_ge_of_delayed_prefix; logarithmic_mass_ge_of_delayed_prefix.
GrowingRamanujanFamiliesHaveASquareRootHorizon.lean:
 abs_ramanujanPacket_window_discrepancy_le;
 ramanujanPoleProfile_family_harmonic_lower;
 ramanujanPoleProfile_family_logarithmic_lower;
 ramanujanPoleProfile_family_squareRoot_lower.

Both modules passed final individual `lake --old env lean` checks. Capstones
report propext, Classical.choice, Quot.sound only. Wired into own umbrella;
no full or umbrella build. Only the imported helper's olean was produced.
