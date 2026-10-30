# The pole conductor is the unique completed ground state

- **ID:** the-pole-conductor-is-the-unique-completed-ground-state
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

For a nonzero compact `C²` unit profile, put `M=∫φ²`,
`T(x)=∫_(t>x)|φ̂(2πt)|² dt`, and let `E_m(c)` be the completed conductor energy.
For every `c>0` and `m≥1`,

`E_m(c) ≥ E_1(c) + 2(m−1)T(c)/(Mϕ(m))`.

For the explicit tilted spline, `T(c)>0`. Thus conductor one is the unique
minimizer at every fixed overlap; every `m≥2` lies at least `2T(c)/M` above it.
The bottom of the actual complete Weil spectrum tends to `E_1(c)`, and exactly
one eigenvalue eventually lies below `E_1(c)+T(c)/M`. Its eigenline captures
the normalized pole vector in Euclidean norm.

## Proof [PROVED HERE]

The proved repayment series is

`E_m(c)=(2/M) Σ_(a≥1,(a,m)=1) [m/(ϕ(m)a)] T(ac/m)`.

Group positive integers into blocks `jm+r`, `1≤r≤m`. Each block has exactly
`ϕ(m)` coprime residues. For each such residue, `jm+r≤(j+1)m`, while `T` is
nonnegative and decreasing. Its summand is therefore at least

`2T((j+1)c)/(Mϕ(m)(j+1))`.

Summing a whole block gives the corresponding summand of `E_1(c)`.
In the first block, residue `r=1` gives the stronger lower bound
`2mT(c)/(Mϕ(m))`; retain its surplus `2(m−1)T(c)/(Mϕ(m))`.
Apply the block inequality to finite prefixes, bound each by the nonnegative
convergent repayment series, and pass to the limit. This proves the display
without rearranging a conditionally convergent sum.

For `m≥2`, `ϕ(m)≤m−1`, so the surplus is at least `2T(c)/M`. The explicit
spline's Fourier transform has no real zeros; the existing tail-positivity
theorem gives a strict gap. The complete norm quasimodes and defect reserve
are already unconditional. The existing exact spectral-count theorem, with
threshold halfway across this gap, gives count one. Its bottom theorem and
the newly identified minimum give convergence of the lowest eigenvalue.
Outside that ground window every eigenvalue is at least `T(c)/M` above the
pole energy. The existing spectral projection inequality bounds the squared
pole-vector projection error by its squared norm residual divided by this
fixed gap squared, hence by a quantity tending to zero.

## Novelty and boundary

The corpus had an unspecified attained minimum and a common positive tail
floor. The block comparison identifies the minimizing conductor and excludes
all nonpolar conductor crossings, with a uniform gap. This is an ordering
law for the actual completed energies, not a new assumed spectral receiver.
It makes no prescribed growing-overlap claim.

## Lean status

The comparison is formalized in
`RenormalizedArithmeticPotentialTheory/ThePoleConductorMinimizesTheCompletedEnergy.lean`:
`completedConductorEnergy_ge_pole_add_gap`,
`completedConductorEnergy_nonpolar_gap`, and
`tiltedUnitSpline_completedConductorEnergy_eq_ground_iff`.
Final direct check passed without warnings; all three audits report standard
logical axioms only. The RAPT umbrella is wired.

`CriticalArithmeticCorrelationTheory/TheCompleteWeilGroundStateIsThePole.lean`
discharges the actual spectral-count, ground-limit and eigenline consequences:

- `completedEnergyFloor_eq_conductor_one`;
- `eventually_tiltedUnitSpline_completeWeil_spectral_count_eq`;
- `eventually_tiltedUnitSpline_completeWeil_ground_count_one`;
- `eventually_tiltedUnitSpline_completeWeil_ground_near_pole`;
- `tendsto_tiltedUnitSpline_groundProjection_error_sq`.

Its final direct no-olean check passed without warnings. All five transitive
axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
CACT umbrella wired. The comparison and actual ground-state consequences
count together as one contribution.
