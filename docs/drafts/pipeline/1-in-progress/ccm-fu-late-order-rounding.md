# CCM-FU: removing late-prime order from the quadratic existence problem

- Type: derived global schedule transformation; PE4 and RH unchanged.
- Status: dependency-closed paper argument being formalized.
- Chain: actual source → exhaustive quadratic raw-energy order → O(M)
  Abel bound → CCM-FU → RH. Frontier map read only.

## Arithmetic question

The exact two-step admissibility window leaves a discrete supply problem
if each middle merger must be paired with one specially chosen late prime.
That restriction is unnecessary for a uniform quadratic ceiling: replace
late subsets by prefixes of one fixed late-prime order, rounding consumed
mass upward by at most one coefficient. The allowance below concerns the
quadratic existence target; it does not preserve the factor-one PE4 ceiling.

## Paper argument

Let U be the actual active late-prime set. Write b_p=-C_p>=0,
T=sum_U b_p, E=sum_U b_p^2, and D an upper bound on individual b_p.
Fix any enumeration of U, once for the whole order. Its prefix masses
increase from zero to T in jumps at most D. For every t in [0,T], choose
the first prefix with mass at least t. Its mass lies in [t,t+D], and
the selected prefix is nested as t increases. Equal target masses select
the same prefix. Zero-mass terms omitted at the terminal target can be
appended without changing energy.

For a middle-prime core P and two unused late subsets R,L, put
t=sum_R b_p, u=sum_L b_p and f=F_empty(P union R). Exact late-block laws give

    Q(P union L)-Q(P union R)
      = -2 f (u-t)+(u-t)^2+sum_R b_p^2-sum_L b_p^2.

If 0<=u-t<=D and Q(P union R)<=B, then

    Q(P union L) <= B+2 sqrt(B) D+D^2+E.

This is a pointwise bound, not a sum of per-step errors. It applies
simultaneously to every state of a successful original schedule. Replace
the old consumed late subset at each state by the canonical prefix of
the fixed enumeration. On a middle-prime step the old consumed mass is
unchanged, so the replacement late prefix is unchanged. On a late step
the core is unchanged; any additional replacement primes form a late
block. Every internal state of that block lies below the maximum of its
two endpoint energies by the existing exact late-block ceiling law.
Thus no intermediate single-prime state is dropped from the argument.

The corpus gives D<=sqrt(M), E<=722 M^2 and Q_empty<=722 M^2.
Consequently a successful uniform quadratic order can be transformed to
one with any prescribed relative order of late primes, with another
uniform quadratic constant. A descending-amplitude order can improve
the diagonal comparison, but is not required for this existence reduction.

This does not prove a successful original schedule exists. It removes
late-prime permutation as an essential degree of freedom at quadratic
scale; the changing middle-core field and a compatible consumed-mass
trajectory remain the arithmetic problem.

## Corpus and proof audit

Broad OR searches (`--any`) covered prescribed streams, reserves,
interleaving, discrepancy, rearrangement, scheduling, monotone corridors,
majorization, thresholds, rounding, and prefix quantization. Relevant
source leaves are `MobiusDivisorNonemptyEnergy`, `MobiusDivisorLatePrimeBlocks`,
`MobiusDivisorLatePrimeInterleavingCapacity`, `MobiusDivisorHeadNeutralization`,
and `MobiusDivisorLatePairMinimax`. `PhaseTailMajorization` has a related
cardinality-threshold comparison, but not the mass-rounding source law.
No computation is needed: the stated transformation follows from exact
source identities and bounded prefix increments.
