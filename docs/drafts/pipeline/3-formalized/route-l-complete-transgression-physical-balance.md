# Route L: complete transgression and physical balance

- **ID:** L-C32
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; exact cancellation class and parity separation
- **Depends on:** [C31](../3-formalized/route-l-native-wold-cyclic-readout.md)
- **RH status:** unproved

The chain remains complete original source → agreement of cyclic and
fixed physical readers → conormal vanishing → RH. C31 supplies native
cyclic-swap invariance of nonlinear physical recovery, but the actual
commutator retains the same boundary scalar. A new cancellation must
come from the original source, not subtraction of equal decoded values.

## Candidate actual source term

The existing `DeningerAdiabaticTransgression` module proves a finite
collar integral identity, both endpoints, and the cofinal weak integral
of the actual Euler flux. Its final relation is

`MobiusBoundary(h) = GammaBoundary(h) - Transgression(h)`.

The transgression is defined as the endpoint difference, and the earlier
theorems identify that definition with the actual integrated source
flux. Thus it is an available source term, but the final rearrangement
alone says nothing about its physical value. A proposed cancellation
requires identifying both physical readings, with the original source
point and multiplicity retained.

First conjecture: the literal source collar exchange identifies the
Gamma and integrated-flux readings at the same physical anchor. Test
the exact exchange operation and its Fourier/physical pairing before
attempting a proof. Involution or transport to a reflected source is
not itself equality at one unchanged divisor.

The two-prime source-normal secondary transgression memory identifies
the same unresolved issue as inverse duality versus Hodge adjunction
on the original oriented boundary. Its physical reporter already reads
`g_2(s)-g_3(s)`, zero exactly on the critical line. That equality cannot
be used as an input. Complete-positive and canonical Krein primitive
budget compensation were previously excluded; a fixed rescaling of a
summable current does not supply the required new source channel.

## Work and proof discipline

Search the whole corpus for actual boundary cancellation and source
incidence methods, then test applicability against the precise source
definitions. Broad arXiv probes start with transgression and gluing.
No new Lean code is warranted until a new dependency-closed paper
argument is obtained. Preserve the existing distinction between weak
distributional source decomposition and fixed physical reader agreement.

## Paper attack: exact cancellation class and surviving parity

Write `M(h)` for the literal Möbius–Fourier boundary, `G(h)` for the
Gamma endpoint and `T(h)` for the integrated Euler flux. The cofinal
transgression identity and the already proved exact kernel give

`G(h) = T(h) ↔ M(h) = 0 ↔ h is a literal Poisson source`.

The actual weighted collar involution satisfies `M(Jh) = -Fourier(M(h))`.
Consequently a fixed source produces an anti-Fourier boundary; it need
not produce a zero boundary. Test this on the existing reflected log
Gaussian `g(t) = exp(-t/2) gaussReal(t)`. Its strong logarithmic decay
places it in the concrete exponential Schwartz source, and hence in
the Meyer source with its existing topology. The pointwise collar
formula transports the previously proved `Jg = g` to this actual source.

This Gaussian cannot be a Poisson source. If it were, the existing
pointwise agreement between the concrete Poisson source and the strong
logarithmic Poisson map would make its cohomology class zero. Its
zeroth evaluation at every actual Xi divisor is already proved nonzero;
existence of an actual divisor therefore gives a contradiction. No
off-line divisor or simplicity assumption is used.

Thus this fixed actual source has a nonzero anti-Fourier boundary and
unequal Gamma and flux distributions. The stronger conjecture that
collar fixedness forces full distributional cancellation fails. Its
positive survivor is cancellation on every Fourier-fixed Schwartz
test: evaluating `M(g) = -Fourier(M(g))` on such a test gives a scalar
equal to its negative. Some other Schwartz test detects the surviving
boundary. More sharply, for any detecting test `u`, the test
`u - Fourier(u) + Fourier²(u) - Fourier³(u)` is anti-Fourier and its
boundary value is four times that of `u`. This follows from Fourier's
fourth-power identity and the boundary's anti-Fourier covariance. Thus
the surviving component has a detecting test in its own parity sector.
These dependency-closed paper statements are now verified in Lean.

The literal Gamma endpoint definition sharpens this survivor: for the
fixed Gaussian, its Gamma distributional boundary is itself
`Fourier(GammaDistribution(g)) - GammaDistribution(g)`. Its value on
every Fourier-fixed test is zero separately. The equal transgression
value is therefore also zero. This is annihilation of the symmetry
sector, not compensation between two nonzero readings. The Lean audit
includes this stronger positive statement.

This Meyer Gaussian and C31's moving Wold product family are distinct
existing source realizations. No identification between them is asserted.
Nor does this argument identify the fixed physical reader with a
Fourier-fixed test. That incidence, with the original divisor and jet
retained, remains the hard obstacle in the RH chain.

## Search evidence

Two deep/method queries tested actual Green-source cancellation and
Fourier/Sonin physical incidence. All 20 candidate lemmas and 20 source
arguments from each response were inspected. Both were partial at index
generation 823361 (semantic coverage 2196271/2337495); refresh and deadline
work remained unfinished. The suggested Sonin-eigenspace/Arakelov-boundary
ingredient set requires a Fourier-invariance premise and an additional
compensating boundary coordinate. It supplies no actual physical incidence.
Other returned adjunction and reciprocity results retain balance premises.

Broad transgression, gluing, sewing and duality searches led to primary
August 2026 abstracts: [subgradient-flow error identities](https://arxiv.org/abs/2608.17845),
[operator systems in duality](https://arxiv.org/abs/2608.16395), and
[quantum-channel spacetime duality](https://arxiv.org/abs/2608.26266).
The first paper's introduction and formulas (1.8)–(1.12) were subsequently
read in its primary HTML version; only abstracts of the other two were
read. Their respective mechanisms require an actual
convex flow/optimality law, specified conic pairings, or a channel with
the relevant symmetry incidence. None supplies those structures for
the present source. No external theorem is used in the paper argument.

The concrete physical-reader check found that the Burnol conormal uses
ratios of multiplicity-exact Mellin jets and a reflected squared-norm
difference. The existing sub-window source theorem intertwines Fourier
transform with the reciprocal-window source, not with the unchanged
window. Neither fact supplies membership of the original physical
reader in the Fourier-fixed test sector.

A third deep/method query specifically tested physical conormal/Schwartz
Fourier-test incidence. All 20 candidates and 20 source arguments were
inspected; generation and coverage were unchanged, with deadline,
filter/judging and source refresh unfinished. The actual Fourier-fixed
prime probe was checked in
`DeningerRationalWittPoissonBoundarySamplingObstruction`: it is the
endpoint-cancelled Hermite combination `h4 - h4(0)h0`. Its proved prime
Poisson values are nonzero, and the module proves that raw prime
sampling fails to descend through the Meyer quotient. This is a real
fixed test, but it is not the missing conormal reader. Other hits gave
Fourier pairing identities, cofinal transport with its graph-scale
premise, or physical excess zero exactly on the critical line. No
unconditional physical annihilator was found.

The next window comparison must retain more than reflection invariants.
The checked existing `BurnolCoPoissonConormalReflectionCover` proves that
the orbit sum, orbit product and squared character difference all
descend under reflection; the orbit product has unit norm. Nevertheless
the squared difference is zero exactly on the critical line. Thus
passing to invariant window data or proving a unit-norm orbit product
does not merge the two physical characters. A new argument must act
on the original conormal difference, rather than assume that merger.

## Formal audit

All nine theorems passed scratch verification without errors or
warnings, including the anti-Fourier detecting test and separate
vanishing of Gamma and transgression on fixed tests. The repository
module `GaloisForLFunctions.RHTower.DeningerAdiabaticGaussianBoundaryParity`
contains exactly those checked bodies and one source definition, and
is wired into `RHTower`.

The final targeted build passed: only this leaf compiled (96 seconds),
with its existing dependencies served from cache. Cached dependency
warnings were replayed; the new module emitted none. All nine theorem
names were audited exactly once via a `/tmp` file. Every theorem depends
only on `propext`, `Classical.choice`, and `Quot.sound`. No added axioms,
proof placeholders, numerical experiments or full/umbrella builds were
used. All owned Lean processes exited.

Index regeneration passed. Global lint was run twice, with a shared-tree
wiring change between runs. The last run failed only on other unwired
modules `ChronologicalTailProfiles` and `Sieve.MenonHarmonicBlockHuxley`.
The earlier `ChronologicalTailMellin` wiring error had disappeared.
No C32 error was reported. Global lint is therefore not claimed clean;
these other modules were not edited or certified by this work.

Logs: `/tmp/route_l_adiabatic_gaussian_parity.log`,
`/tmp/route_l_adiabatic_gaussian_build.log`,
`/tmp/route_l_adiabatic_gaussian_axioms.log`, and
`/tmp/route_l_adiabatic_gaussian_lint_final.log`.

The failed full-cancellation candidate has a formally audited positive
survivor: exact Poisson classification, actual retained nonzero Gaussian
boundary, separate zero readings on fixed tests, and an anti-Fourier
detecting test. Route L remains open at the original physical-reader
comparison. No RH proof is claimed.
