# TG-C9: retain the literal radial jet through Fourier completion

- **ID:** TG-C9-20261001-01a0
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `PrimeBurnolFourierPair`, `PrimeBurnolFourierCompletion`,
  `PrimeBurnolConfluentMomentGram`, `HTGeometry.MaximalRealL2Multiplication`,
  `ArchimedeanMellinFourier`, `Mathlib.Analysis.Fourier.FourierTransformDeriv`.

## Learned obstruction and hard target

C8 gives finite source/Fourier independence but a dense coordinate core with completed kernel
`x=-J y`. The neutral coordinate does not descend, and the canonical diagonal section compresses
it to half the identity. Another bounded inversion or silent quotient loses required data.

Next candidate retains a source-derived unbounded observable before completion. Let M be
multiplication by r² on its actual maximal L2 domain, restricted to even physical L2; J is the
actual Fourier involution. The added column `M e_i` is precisely the even extension of the
already formalized radial jet of order 2. No target zero or arbitrarily chosen finite matrix
enters this construction.

## Exact next conjecture

The two-output source operator

`E(f,g) = (f + J g, M f + J M g)`

is injective on `D(M) × D(M)` of the even physical carrier. Establish the appropriate closed
extension and its literal prime-depth graph core separately; injectivity alone will not establish
either. The hard operator problem is to rule out a nonzero y with

`y in D(M), J y in D(M), M J y = J M y`.

The Fourier differentiation formulas suggest the weak equation `y'' + 4 pi² r² y = 0`.
Prove the weak-to-strong/domain passage and exclusion of L2 solutions; do not substitute the
ordinary positive oscillator theorem, whose sign is different. A potential proof is the exact
windowed dilation/virial identity with every boundary term justified by the maximal domain.
No decay assumption, boundary vanishing hypothesis, or numerical evidence may be added.

## Provenance and remaining TG gaps

Before using this as a Gamma seam, establish the actual completed Mellin reflection identity
for these literal columns. Existing `soninMellinEvaluation_fourier` has explicit L1 and weighted
Mellin-integrability premises; discharge them from the exact source and Fourier formula rather
than relabel the Fourier involution as a completed Xi comparison.

Even success leaves joint arithmetic cancellation, Hardy-index transfer, and the sub-unit
source action open. The next work attacks the missing physical operator theorem, not a revised
constant or an RH-equivalent hypothesis wrapper.

## Corpus audit

- Deep search `Fourier multiplication square commutator kernel oscillator`: partial due to
  semantic deadline. Returned Fourier and commutator ingredients were inspected; no absence
  claim is based on this search.
- `MaximalRealL2Multiplication` supplies the exact maximal multiplication domain, AE action,
  self-adjointness and bounded domain cutoffs; use it without the Xi-divisor-specific
  specializations in `BurnolHedenmalmCompletionDomain`.
- Read `OscillatorSpectralRigidity`, `OscillatorEnergyVanishing` and `OscillatorVirialWindow`.
  These treat the opposite-sign ordinary oscillator; their existing spectral theorem does
  not prove the proposed kernel exclusion. Their domain/boundary methods are available.
- C9.1 now passes scratch, production and separate axiom audits: the actual two-output map is injective on the
  maximal multiplication domain, and every literal source column is admitted with its exact
  order-two jet. All four public theorems use only the standard three foundations; the
  exact record is `../../../3-formalized/tg-fourier-radial-jet-kernel.md`. The stronger
  closed-graph assertion is C9.2, on `tg-fourier-jet-weak-kernel.md`. No analytic premise has
  been added to the TG goal.

## C9.1 revised paper proof: finite dilation identity

The same maximal-domain kernel problem admits a direct proof without a weak-ODE regularity
detour. The existing corpus proves strong continuity of physical dilation U_r and exact
Fourier covariance F U_r = U_(1/r) F. Prove from actual representatives that maximal position
square multiplication M preserves the dilation domain and obeys M U_r = r^-2 U_r M.

For y and F y in D(M), suppose M F y=F M y. Put u=M y. Formal symmetry and covariance give

`<u,U_r y> = r^-2 <y,U_r u>`.

Applying the actual Fourier unitary to both entries, then using the same identity at 1/r,
also gives

`<u,U_r y> = r^2 <y,U_r u>`.

For every r>1, these imply `<y,U_r u>=0`. Strong continuity as r decreases to 1 gives
`<y,M y>=0`. Its exact integral is the nonnegative position energy; since r² vanishes only
on a null singleton, y=0. This argument works on the full physical L2 carrier, so its even
restriction gives C9.1. No derivative-domain, decay or boundary condition is assumed.

The final leaf audit verifies maximal-domain covariance, the energy identity and the resulting
literal source operator injectivity. Production leaf: `PrimeBurnolFourierJetKernel.lean`.
The later C9.2 audit in `../../../3-formalized/tg-fourier-jet-closed-graph.md` proves injectivity
of both projections of the actual graph closure. C9.3 excludes bounded ambient recovery
of the first input coordinate on the full maximal-domain model; its positive survivor is
that closed, injective source graph. C9.4 now identifies the literal even prime graph core;
C9.5 supplies the independent even parity argument and excludes bounded recovery on each
finite prime core. C9.6 now settles the stronger input-and-output norm: the original neutral is closed,
unbounded, and has the original admitted graph as its exact proper dense domain. Its
range and kernel are closed disjoint channels with nonclosed sum; failure already holds
on each literal prime core. See `../../../3-formalized/tg-fourier-jet-closed-neutral-domain.md`
and `../../../5-failed/tg-fourier-jet-neutral-graph.md`. Next attack:
`tg-fourier-jet-theta-cubic-domain.md`, testing actual cubic cancellation rather than
inferring it from unbounded generators.
Gamma–Xi/Hardy/sub-unit gaps remain separate and open.
