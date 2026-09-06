# Finite zeta prefixes and off-line Helson divisors

- **ID:** HELSON-PREFIX-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); research audit complete, parent RH search active
- **Scientific status:** NOT NEW SCIENTIFIC KNOWLEDGE; not an RH architecture
- **Statement:** For every finite coefficient cutoff, a completely multiplicative unimodular ordinary Dirichlet series matches zeta through that cutoff and has a meromorphic continuation with one prescribed simple off-line zero in the positive half-plane.

## Exact target

For every natural number `N`, construct `a : ℕ →*₀ ℂ` and `Z : ℂ → ℂ` with
`a(n)=1` for `1≤n≤N`, `|a(n)|=1` for every positive integer, and meromorphic
`Z` on the plane. For `Re(s)>1`, its absolutely convergent ordinary Dirichlet
series must equal `Z(s)`. For `Re(s)>0`, its meromorphic divisor must be one at
`3/4+i` and zero elsewhere. No functional equation is imposed. Values at
removable singularities are not independently prescribed.

## Closed paper construction

1. Use the corpus's existing prescribed-divisor Helson theorem to obtain a
   prime phase family `u` and continuation with singleton divisor at `3/4+i`.
2. Set `v(p)=1` for primes `p≤N`, and leave all other prime phases unchanged.
   Extend `v` completely multiplicatively. Unique factorization gives every
   required initial coefficient exactly.
3. Multiply the original continuation by the finite product
   `∏_(p≤N) (1-u(p)p^(-s))/(1-p^(-s))`.
   Each factor is meromorphic on the plane and analytic and nonzero for
   `Re(s)>0`. Thus the divisor in that half-plane is unchanged.
4. The existing finite Euler-gauge identity identifies this continuation with
   the new ordinary series for `Re(s)>1`.

This combines published divisor realization with a finite Euler modification.
The premise-free theorem
`RHTower.HelsonFinitePrefixDivisor.finite_prefix_singleton_divisor` passes the
scratch and production-source Lean checks. Its scratch axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`. The final leaf build and
import audit also pass, as recorded below.

## Research consequence

An argument using only finitely many exact zeta coefficients, together with
global complete multiplicativity, unit coefficient norms, and meromorphic
continuation, still cannot exclude an off-line zero in this class. A proof
using finite data needs a further justified constraint on the unseen
coefficients or on their analytic effect. This does not refute proofs using
the full literal coefficient sequence, a verified tail bound, or additional
global arithmetic structure.

## Source evidence

- `RHTower.exists_continuable_phase_with_prescribed_locallyFinite_divisor`
  in `LocallyFiniteDivisorPresentation`.
- `LSeries_phaseChar_eq_mul_finiteEulerGaugeRatio_of_eq_off_finset`
  in `HTGeometry.HelsonFiniteEulerGauge`.
- `finiteEulerGaugeRatio_ne_zero` and
  `differentiableOn_finiteEulerGaugeRatio_positiveHalfPlane`
  in `HTGeometry.FiniteGaugeTailCharge`.
- Actual coefficient definition and factorization proof in
  `HTGeometry.HelsonCharacterLSeries`.

These were retrieved with `research` and inspected with `rg` and source reads.
The nearby `FiniteDivisorHeadTailShadowUniversalityLaw` constructs a carrier in
an abstract finite-Euler class; its inspected theorem does not identify an
ordinary Dirichlet series with completely multiplicative coefficients. That
distinction is the reason for checking the present exact witness separately.
The preceding rational-Hurwitz refinement lead already has extensive corpus
development and supplied no new candidate. Broad ranked queries are discovery
evidence, not an exhaustive proof-body audit or a novelty certificate.

## Literature and second pass

Andersson's [*Mittag-Leffler type theorems for Helson zeta-functions*](https://arxiv.org/pdf/2408.15713),
Theorem 5, supplies the published prescribed-divisor mechanism. Seip's
[*Universality and distribution of zeros and poles of some zeta functions*](https://arxiv.org/pdf/1812.11729),
opening section, already notes preservation of the relevant positive-half-plane
analytic properties by finite Euler modifications. The prefix conclusion here
is a direct consequence of these mechanisms and unique factorization; it is
not an absence-from-literature claim.

The second pass distinguishes three possible escapes:

- Exact agreement on a larger but finite set remains covered: choose a larger
  cutoff, so every prime dividing any tested integer is fixed.
- One function agreeing at all positive integers would have the literal zeta
  coefficients. The quantified theorem constructs a potentially different
  function for each cutoff and does not supply such a function.
- A functional equation, a joint analytic tail bound, or another constraint
  on all coefficients is additional information. None is asserted for these
  witnesses or excluded as a possible ingredient of a future proof.

The constructive survivor is this known finite-modification consequence, now
formalized exactly. **NO POSITIVE SALVAGE FOUND** that qualifies as a new RH
mechanism. No candidate for the full literal zeta sequence is retired here.

## Validation

- Scratch directory: `/tmp/hgt-helson-prefix-lApoE8`.
- `Names.lean` and `FinitePrefix.lean`: passed after resolving universe
  arguments and opening topology notation. Final scratch axiom audit: standard
  three axioms only.
- Production source `HelsonFinitePrefixDivisor.lean`: passed `lake env lean`.
- Umbrella import added; no umbrella build requested.
- A plain targeted Lake build, then an `--old` attempt, began rebuilding
  transitive artifacts and were terminated. All removed required oleans and
  missing associated artifacts were regenerated using sequential foreground
  `lake env lean` calls. No dependency source was changed.
- Final targeted audit passed:
  `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.HelsonFinitePrefixDivisor`.
  The new leaf took four seconds; the 11,253 reported jobs include cached
  transitive dependencies. The final build used existing dependency artifacts
  and checked further required stale dependencies sequentially. This is not a
  full or umbrella build, nor a fresh audit of every dependency's source.
- `lake env lean /tmp/hgt-helson-prefix-lApoE8/Audit.lean` imports the built
  module and reports the premise-free theorem type and only the standard three
  axioms. An earlier import attempt, before the leaf existed, failed and is
  superseded by this successful check.
- `python3 scripts/formal_tools.py lint`: passed with existing size warnings.
  Final build and lint logs are in the scratch directory. The research index
  retrieves the new theorem with its accurate published-mathematics scope.
- No mathematical experiment or computed proof certificate was used.

## Formal artifact

[Lean source](../../../../../formal/GaloisForLFunctions/RHTower/HelsonFinitePrefixDivisor.lean)
contains the complete proof and is imported by `RHTower.lean`. No extra axiom,
assumed RH condition, placeholder, or computed certificate occurs in the proof.
