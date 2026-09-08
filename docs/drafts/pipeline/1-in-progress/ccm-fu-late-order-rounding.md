# CCM-FU: removing late-prime order from the quadratic existence problem

- Type: derived global schedule transformation; PE4 and RH unchanged.
- Status: source comparison, fixed-order history, and actual-chain
  transformation kernel checked; targeted final build passed. RH remains unproved.
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
uniform quadratic constant: for M>=1, `C M^2` becomes
`(C+2 sqrt(C)+723) M^2`. A descending-amplitude order can improve
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

## Formal certificate

[MobiusDivisorLateOrderRounding](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorLateOrderRounding.lean)
contains twelve public theorems. The scalar prefix selector is monotone,
starts at zero, and rounds every attainable nonnegative mass upward by
at most one coefficient. `mobiusDivisorSelectionEnergy_late_mass_difference`
is the exact actual-source displacement identity;
`mobiusDivisorSelectionEnergy_late_mass_rounding_le` is its pointwise bound;
`mobiusDivisorSelectionEnergy_late_rounding_quadratic` supplies the displayed
uniform constant. `mobiusDivisorSelectionEnergy_between_late_subsets_le`
controls every subset between bounded late endpoints.

The two capstones close the whole-history compatibility requirement.
`exists_mobiusDivisor_fixed_late_order_history` selects nested prefixes for
every state of a monotone late-subset history and includes internal block
states, equal-mass compatibility, empty start, and final completion.
`exists_mobiusDivisor_fixed_late_order_chain` applies this to an actual
monotone processed-prime chain by splitting each processed set into its
late intersection and complementary core. A middle-prime step remains
the literal same prime insertion; a late-prime step keeps the core fixed
and is replaced by a controlled block in the prescribed enumeration.
The terminal block includes any zero-mass terms not selected by first
crossing. No sampled state or intermediate one-prime stage is omitted.

The theorem transforms a bounded source chain; it does not supply that
chain's unresolved middle-prime control. At uniform quadratic scale,
late-prime permutation can now be fixed in advance. Exact factor-one
ceilings and optimal local pair policies remain separate, stronger targets.

Scratch and installed-source `lake env lean` checks passed. Only the new
leaf's required olean was emitted. An external scratch file audited all
twelve new public theorems once: only `propext`, `Classical.choice`, and
`Quot.sound`. No old theorem was re-audited. The leaf is imported by RHTower.
No computation or numerical certificate was used.

The final exact-module `lake build` compiled the byte-identical leaf in
8.3 seconds in an isolated temporary package with the repository toolchain
and existing dependency oleans. Only the new leaf compiled. No umbrella,
full, or dependency-source build ran. The source emitted no warnings or
tactic diagnostics; missing temporary cache-package manifest messages
concerned packaging only. Final source equality and emitted audit olean
were checked before deleting the temporary package.

Indexes were regenerated. The global lint check reported unrelated
unwired modules `SelbergCompactTestApproximation`,
`SelbergMaassContinuousCurvature`, and `SelbergUpperHalfPlaneCompactTests`,
plus stale API/overview files after concurrent source additions. A passing
global gate is not claimed; the generated files were refreshed after that
finding. Own proof-debt, single umbrella import,
whitespace, and card-link checks passed. Owned scratch and audit files
were removed; no owned Lean process remains. The frontier map was read only.
