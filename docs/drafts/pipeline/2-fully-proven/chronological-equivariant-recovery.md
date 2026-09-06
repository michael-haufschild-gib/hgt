# The sharp cost of preserving the physical flow during recovery

**Status:** four final leaf builds and all 38 declaration audits passed. Weight separation, exact constants, physical coordinate bounds, sharp witnesses, global minimax bound, uniqueness, and the intrinsic actual-observation formulation are formal. Follows the formal uniform-recovery obstruction. Candidate result is the exact approximation problem selected by the chronological physical section and its retraction. Polynomial weight separation and constrained approximation are classical; priority remains unestablished.

## The selected approximation problem

The missing middle gap c obeys T_q c=q c. Require a polynomial recovery P∈A=ℝ[u,c²,c³] to obey the same law. It is enough to require T_(1/2)P=P/2. Comparing every coefficient of u^i c^j forces i+j=1 whenever that coefficient is nonzero: distinct natural powers of 1/2 are distinct. The coefficient of c is forbidden in A. Thus every such recovery is precisely P=αu, α∈ℝ. Conversely each αu satisfies every scaling law.

On the physical section, put c=g₂. The proved mode identity gives

`u=c(1−(a−e)²)/4`.

Here 0≤c≤1, a,e≥0, and a+e≤1−c. Consequently

`L(c)=c²/2−c³/4 ≤ u ≤ c/4`.

For every c∈[0,1], the lower endpoint is attained by the physical probe (1−c,0,c,0,0), and the upper endpoint by ((1−c)/2,0,c,0,(1−c)/2). No optimization over unrealized coordinate values is used.

## Exact minimax solution

Define

`t=(√17−3)/4`, `α*=4/[t(4−3t)]`, `δ=α*/4−1`.

Then 0<t<1/3, 2t²+3t−1=0, α*>4, and δ>0. Equivalently,

`α*=(126+34√17)/59`, `δ=(17√17−55)/118`.

The exact minimum of sup_physical |c−αu| over all α∈ℝ is δ, uniquely attained at α*. Two physical probes attain opposite signs: c=1, u=1/4 gives −δ, and c=t, u=L(t) gives +δ.

Proof of the upper bound: write f(c)=c−α*L(c). The defining quadratic for t gives

`f(t)=δ`, `1−α*t+3α*t²/4=0`,

`f(t)−f(c)=(α*/4)(c−t)²(2−2t−c)≥0` for 0≤c≤1.

Since u≥L(c), c−α*u≤f(c)≤δ. Since u≤c/4,

`c−α*u≥c(1−α*/4)=−cδ≥−δ`.

For the lower bound at arbitrary α, if α≤α*, the probe c=t,u=L(t)>0 has c−αu≥δ. If α≥α*, the probe c=1,u=1/4 has αu−c≥δ. Strict inequality holds in the corresponding witness whenever α≠α*, proving uniqueness.

## Meaning and next obligations

Unrestricted polynomials in A recover c to arbitrary uniform accuracy, by the formal iteration in [uniform recovery](chronological-observation-recovery.md). Requiring exact compatibility with the physical retraction changes the minimum error from zero to the explicit positive δ. Thus the dynamics supply a positive obstruction that ordinary uniform completion erases.

CubicEquivariantAlgebra separates every total weight under half-scaling. CubicRecoveryConstants supplies the exact identities and arc bound. CubicRecoveryGeometry proves the physical bounds and unique minimax solution. CubicEquivariantRecovery defines admissibility directly in the actual observation algebra through physical pullback and proves attainment and uniqueness there. The next [homogeneous-boundary reduction](chronological-homogeneous-boundary.md) is paper-only. Higher-weight sharp constants and any canonical Hilbert completion remain open.

## Existing comparisons

The corpus already has `ClockHomogeneousScaling.lean`, proving polynomial weights under a concrete jet dilation; the general separation-of-weights idea is not new. [Salova et al. (2019), §III](https://csc.ucdavis.edu/~cmg/papers/koiasws.pdf) use symmetry components to constrain Koopman operators and their approximations. [Peitz et al. (2024), abstract](https://doi.org/10.3934/jcd.2024035) study equivariance and partial observations for PDE Koopman models. Our calculation concerns an exact scalar scaling law on this specific physical observation algebra, not a new general symmetry or Koopman principle. Neither comparison establishes priority for the displayed chronological minimax constant.
