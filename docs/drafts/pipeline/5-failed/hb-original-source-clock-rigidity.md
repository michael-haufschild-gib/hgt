# Linear packet matching and the original quartic clock

Target: full temporal/metric/QNM matching. The complete canonical action is
already the Laplace integral of the original finite-part source profile.
Its actual time-translation law, rather than a fitted spectral value, is the
object to match.

Candidate: retaining all original onset and boundary terms makes this
profile a single-frequency clock orbit after onset. The original formula
instead gives `K(u)=exp(2su)(A+uB)` for `u≥1`, with
`A=−mu*C*((mu−2)*X+Y)` and `B=mu*C*(mu−2)*M`. These are the original
angular coefficient and complete radial, tortoise, and forcing moments.

[BRIDGE] Positive candidate: the exact clock acts on the pair
`(K(u),exp(2su)B)` by
`(k,b) ↦ exp(2sT)*(k+T*b,b)`.
This is a source-derived first-order frequency jet; its nonzero second
coordinate prevents reduction to a single clock character.

Discriminator: prove
`K(u)*K(u+2T)−K(u+T)^2 = −T^2*B^2*exp(4s(u+T))`.
If `B≠0` and `T>0`, no scalar multiplier can advance both consecutive
steps. A surviving original Green pole implies `C*M≠0`, hence `B≠0`
at actual Xi copies because the physical factors `mu` and `mu−2` are
nonzero there. No numerical Xi zero is selected.

Whole-route consequence to test: scalar clock matching would erase a
source moment that the complete metric/QNM action retains. The exact
two-component clock is a positive replacement for that temporal law,
not yet a physical Peierls pairing, an extinction theorem, or RH.
The source profile must not be identified with the full retarded field.

## Finite clock mixtures

The obstruction extends to arbitrary finite packet encodings and arbitrary
time-independent complex-linear readouts of the unchanged physical clock.
Every such readout is a finite sum `Σ c_j exp(beta_j*u)`. Repeated
frequencies are allowed. A finite exponential sum equal to `A+uB` on a
real interval must have `B=0`: extend the equality by the entire identity
theorem and induct on the number of summands. If the last frequency is
zero, subtract its constant. Otherwise apply `D−beta_last`; the last
summand disappears and the affine slope becomes `−beta_last*B`, so the
induction hypothesis again forces `B=0`.

Apply this after multiplying the actual source profile by `exp(−2su)`.
Its nonzero `B` therefore excludes every finite mixture, not just the
original one-copy carrier. This proof does not depend on erased source
amplitudes, positivity, continuity of the linear readout, or distinct modes.

The positive temporal coordinates are observable directly:
`exp(2su)*B=(exp(−2sT)*K(u+T)−K(u))/T` for `T>0` and `u≥1`.
Both source coordinates vanish exactly when the profile is eventually
zero; in that case it is identically zero. There is no nonzero profile
which becomes exactly zero after a finite time.

## Positive matching with the original clock

The actual centered frequency is `omega(q)=−i*(rho−1/2)/2`. Put
`q_br=reflect(q)` for the true source branch and `q_br=q` for the false
branch. The original source rates satisfy the exact identity

`2s = −3 + 4*(−i*omega(q_br))`.

For the original physical time `u`, let `h(u)` be the `q_br` coordinate
of the original centered-clock evolution of the unit packet at `q_br`.
Consequently, for all real times, including the original onset,

`K(u) = chi(u)*exp(−3u)*h(u)^4*(A+uB)`.

This is an explicit source-derived nonlinear observation of the unchanged
clock evaluated at the original source-time coordinate. It retains the
original angular/radial/forcing moments and the first source-time moment.
No rescaling of that coordinate or fitting of a new frequency is used.
Inserting this expression in the already admitted source Laplace integral
represents the complete canonical temporal/metric/QNM value as its
convergent quartic-clock moment.

**Whole-route effect:** the linear finite-packet matching candidate fails,
while the original source supplies an exact quartic, time-dependent
observation. These results are compatible. The two-component translation
law belongs to the source observable; it does not assert a defective
physical Green pole or multiple arithmetic zero. An independent physical
Peierls pairing and an extinction/selection law for the complete retained
observation remain unproved. This identity is not a conjugacy of the full
PDE evolution with the packet clock. The original static time in the source
cutoff remains `u−tortoise(z)`; it has not been replaced by `u` inside the
field equations. No RH conclusion follows.

## Corpus and literature discrimination

Broad/deep searches covered transgression, extinction, boundary matching,
Jordan translation and semisimple recurrence. The source formulas and
clock definitions supplied the actual objects. `ConnesJordanTriangular`
supplied the triangular-translation comparison;
`ComplexExponentialPolynomial` supplied the eliminate-one-frequency
proof mechanism; `CompactFourierEntire` supplied interval-to-entire
uniqueness. These comparisons do not identify the source jet with an
arithmetic multiplicity. Search results had snapshot coverage but mostly
pending compiler metadata; boundary/Jordan/recurrence requests were
partial. Applicability is checked in the new Lean proof.

Broad arXiv searches for transgression, memory, hereditary, intertwining,
jet and confluence did not supply a missing HB identity. The retrieved
[conserved Kerr-current paper](https://arxiv.org/abs/2210.15935) distinguishes
a renormalized mode pairing from bare radial data; it is not a proof for
the HB source. Recent jet and cyclic-rewriting papers supplied no
applicable ingredient.

## Lean certificate

[OriginalSourceClockRigidity](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalSourceClockRigidity.lean)
proves the original two-coordinate translation and recovery laws,
`sourceClock_scalar_realization_iff`, `sourceClock_eventual_zero_iff`,
`sourceClockSlope_eq_zero_of_finite_exponentials`,
`not_exists_sourceClock_finitePacket_realization`, and the unconditional
actual-critical witness `exists_critical_finitePacket_clock_obstruction`.
Its positive endpoint is `canonicalCausalSourceProfile_physicalClock`
and `canonicalQNMValue_physicalClock_integral` for every actual Xi copy,
both source branches, both fundamental QNMs and every amplitude.

Status: dependency-closed paper proof and Lean proof completed. Scratch
check passed in 82.10 seconds; isolated exact-module audit passed in
93.83 seconds, two jobs. The leaf is imported by `RHTower`; no umbrella
build was run. No numerical certificate, added axiom, or raised heartbeat
limit occurs in the new source. Only finite-packet linear matching is
retired; the full HB route and RH remain open.
Global lint reports the separate unwired module
`ThetaCuspHawkingBMOnsetTransgressionHorizon`; it reports no error in this leaf.
