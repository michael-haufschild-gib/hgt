# SZ: direct joint phase credit on canonical heads

- **ID:** SZ-JOINT-PHASE-CREDIT
- **Stage:** 1-in-progress
- **Type:** OPEN hard arithmetic target; no new proof claimed
- **Source:** actual coherent Gamma phase square, canonical head energy,
  SZ-SHIFT-EDGE and SZ-ACTUAL-DEFECT-QUASIMODE.

## Exact target

For each actual positive aperture a, set

    u_n = ccmRestrictedWeilCanonicalGroundHead a n,
    f_n = ccmArchimedeanFormToAperture a u_n,
    N = floor(exp(2*a))+1.

Prove eventually in n:

    ccmActualHeadGammaHigherBinetModeEnergy f_n
      + ccmActualHeadCoherentQuantileGammaChiSquare (2*a) N f_n
    <= ccmActualHeadCoherentQuantileGammaPhaseSquare (2*a) N f_n
      + (2*gammaHardyPhaseRate 0+4)*norm(f_n)^2.

The exact source equivalence is already in
`CCMActualHeadCoherentQuantileGammaPhaseSquare` lines190-201. Do not add
another equivalence or use this inequality as an input hypothesis. The
task is to establish its arithmetic sign for the actual canonical heads.

## What the completed source research supplies, and what it does not

Every admissible fixed-source Xi schedule must approach the relative
spectral floor. Its actual amplified defect is eventually nonzero and a
relative normalized-covariance quasimode. These are audited restrictions
on a proposed identifying family. They do not construct such a family,
identify its defect with a canonical head, or prove the phase credit here.

## Constraints learned from existing failures

- Separate chi-square payment by the central scalar is already disproved:
  that scalar is negative. Keep the exact joint phase square and cross term.
- Ground stationarity is invariant under a scalar shift of the operator;
  it alone cannot decide the required absolute arithmetic sign.
- Relative covariance residual tending to zero gives no uniform spectral
  gap or closeness to a single ground eigenspace. Do not insert either.
- The proved limiting-logarithmic ground simplicity concerns a different
  operator. Its modulus argument does not automatically control the
  actual polar term.

## Current proof investigation

The phase square retains the actual Gamma-weighted translation increment
and the complete coherent prime--polar field. Investigate a joint
logarithmic uncertainty/phase-credit argument for those fields evaluated
on the actual head, preserving finite-cell cross terms and the terminal
polar current. The missing result is that these correlations pay the
displayed negative correction. No claimed norm estimate supplies it.

Search1191371 returned actual source identities, canonical Birman--Schwinger
fixed-point identities and the existing ground-plus-tail formulas; its
suggested ingredient set did not prove the sign. Search1191399 (older
coverage1191398) returned finite prime-log phase recurrence and arithmetic
phase source identities. The recurrence statement is an UPPER bound on
a return time; it is not a lower bound on the Gamma cost of coherence.
Neither search certifies completeness or novelty; both were partial and
source-only. Existing recurrence must be used with its actual direction.

## Log

- 2026-10-02: direct hard target recorded after actual-defect quasimode
  closure. No paper proof or Lean theorem for the phase credit is claimed.
  RH remains unresolved. Continue at this sign problem, not at another
  packaging of its equivalent RH receiver.

### Concrete phase-preserving ingredient to investigate next

Current source inspection of
`CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracTwoShear` (intro,
lines245-315) displays a two-shear representation retaining real and
imaginary components of the actual oriented prime-power phase symbol.
Its joint crossing energy is exactly
`4*gauge^4*normSq(orientedSymbol)` and positive away from the spectral
center. The source explicitly leaves transport to the global scalar
receiver open. This is a candidate for a phase-preserving decomposition
of the displayed canonical-head gap; it is not itself scalar positivity.
Next attempt must carry its orientation through the actual coherent
quantile/Gamma transport with every cross term retained. A positive norm
of the oriented symbol cannot be substituted for a signed real pairing.
No new Lean audit of that candidate module was run in this turn.

### 2026-10-03: signed transport attempts and exact entropy debit

The attempted inference from the two-shear carrier to scalar positivity
fails at an already-proved source obstruction: the literal oriented prime
reporter takes both signs. The self-polarized shear squares that reporter;
it does not preserve its signed scalar readout. Existing midpoint odd/even
and exterior-moment gauges preserve the complete action, so cancelling
another moment supplies no missing phase credit. These are uses of
existing corpus results, not new no-go theorems.

Ground modulation was considered next. Normalized variational comparisons
are invariant under adding a scalar multiple of physical mass. Without an
independent arithmetic normalization law they still cannot determine the
absolute floor. No receiver lemma was added for this observation.

The source-normalized next attempt uses the literal Suzuki checkpoint
reservoir and its cumulative prime load. An actual new paper mechanism is
recorded in `../3-formalized/sz-quantile-entropy-debit.md`: the exact outgoing quantile
cell-centroid debit is summable over the full arithmetic exhaustion. It
separates a finite positive nonlinear price from the signed node current.
Lean verification passed, including all12 public axiom queries. This is not the full Gamma reservoir's
Legendre-debit theorem, and neither version would by itself prove the
remaining signed-current floor. Keep the canonical-head gap as the target.

### Signed Selberg attempt after entropy-debit closure

Search1215522 and search1215533 were partial/source-only. The literal
identity `vonMangoldt_pmul_log_add_mul_self` reads
`Lambda*log + Lambda convolution Lambda = log^2 convolution mu`.
Solving for the logarithmic moment SUBTRACTS the positive convolution;
discarding it therefore gives the wrong inequality for the required
lower floor. The exact factorial reduction likewise retains a terminal
Chebyshev remainder (`CCMFUSuzukiFactorialChebyshevEndpoint`).

The retrieved `PMSelbergPowerInputBoundary` already proves that both
coarse Selberg inequalities admit an explicit3/4-power comparison error
with divergent variance. That theorem concerns a comparison error, not
actual primes, but rules out using those coarse inequalities alone.
No new theorem or RH progress is claimed from these source inspections.
The remaining attack must retain the signed convolution, exact forcing,
Gamma normalization, and terminal arithmetic error together.

### Physical prime-phase cost: normalization check

Search1215559 returned finite Dirichlet-density prime-correlation and
logarithmic frequency-cost laws. Source reads verify those statements,
but their carrier is a coefficient family indexed by integers, not the
canonical physical head. Multiplying all indices by a common positive
integer preserves its prime coefficient correlations while multiplying
its raw frequency cost. Thus that raw cost is not an identified Gamma
form. A sampling or torus transfer cannot be inserted as an assumption.

Search1215577 (partial, complete inventory but mostly pending/stale
compiler coverage) and1215595 (partial/source-only) supplied no verified
physical-to-density transfer. No absence claim follows. A serious next
phase-cost attempt must work with the actual Fourier spectral measure of
the head, retain prime-power phase correlations and the polar contribution,
and derive its Gamma budget in that same carrier. The canonical-head
inequality at the top of this card remains unproved.

### Actual physical phase law: exact transfer obstruction

The next conjecture concerns an exact transfer, not finite-correlation
approximation. The two fractional prime phases of the physical Fourier
frequency lie in a countable union of affine lines, null for the product
of two independent uniform phases. The actual normalized ground puts mass
one there. Hence its law cannot have an independent-phase density.

The positive survivor is stronger than a mass identity: irrationality of
log(3)/log(2) makes the same phase pair a Borel injection. Its measurable
inverse recovers the entire physical spectral measure and every
nonnegative cost, including the exact shifted Gamma weight. This retains
the original signed problem without substituting Dirichlet degree cost.
P3:sz-physical-two-prime-phase-law records the proof. Final25304 and all19
public axiom queries6552 passed; P5:sz-exact-independent-phase-density-transfer
records the narrow rejected mechanism and its survivor. No hard sign or RH
conclusion is claimed.

Direct sign attempts preceding this construction supplied no new bound:
the ground-frequency budget still depends on the unknown energy; the
boundary forcing divides a signed source functional by a positive Gram
factor; the finite parity-matrix theorem assumes positivity/simplicity;
the pole-compression sign is an existing RH-equivalent criterion.
None can be inserted as an unconditional producer. A first-negative
Suzuki minimum still requires the complete signed history, which local
convexity does not control. These failures are not new Lean theorems.

### Next direct sign test: exterior correction with the full cost retained

Search1215808 (partial/source-only) and source reads recover the exact
aperture autocorrelation zero law and existing Selberg/Krein completion.
The completion preserves every visible Mangoldt weight; its freedom is
outside the aperture, while every prime remains exact. No positive
completed symbol is supplied by that identity.

The existing exterior-cosine dual mass wall also prevents treating
approximation on a bounded frequency interval as a completed proof:
uniform constant approximation on growing windows requires faster than
every fixed polynomial growth of the signed measure mass. The logarithmic
Gamma tail cannot be declared to pay that uncontrolled mass. That wall
does not forbid a more selective correction adapted to the actual negative
set of the full symbol. The next candidate must construct such a correction
and control its complete tail; no new conditional receiver should be added.

### Literal exterior constant lift: actual energy obstruction

The literal packet (8*pi*a,4*pi*a,2) locally reproduces one while its
actual ground-weighted integral is zero. New audited leaf
`CCMExteriorPacketNegativeEnergyEscape` proves the exact signed tail limit
and at least one unit in the eventual lower-limit sense of negative energy
escaping beyond every fixed window. Even degrees do not repair the known
odd-degree pointwise obstruction. This rules out eventual global positivity
for that construction. It does not decide the actual Weil energy's sign.

Paper and Lean status: P3:sz-exterior-negative-energy-escape; narrow failed
construction: P5:sz-exterior-constant-lift-positivity. The remaining hard
task is still the displayed full canonical-head phase credit. Further
constant-lift mass estimates cannot solve it; any selective exterior
construction must account for its actual signed energy, not only compact
approximation and coefficient bounds.
