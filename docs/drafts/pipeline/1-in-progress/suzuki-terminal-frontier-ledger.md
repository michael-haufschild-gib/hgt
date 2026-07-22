# Suzuki terminal frontier ledger

- **ID:** `suzuki-terminal-frontier-ledger`
- **Status:** active research control file; read before any Suzuki work
- **Terminal objective:** prove RH, disprove RH, or prove a source-complete no-go for Suzuki's
  operator mechanism.
- **Current terminal result:** none.

## Rule

No new Suzuki card or Lean module is allowed unless it advances the single live edge below or
falsifies it. Coordinate changes, equivalent RH criteria, generic Grams, scalar capacity laws,
and finite-support coefficient reconstructions do not count as progress.

## Already closed — do not reopen

1. **Finite source identification.** The semilocal place connection is exactly the finite
   von-Mangoldt source, coefficient by coefficient (`semilocal-dual-pair-euler-connection-source-law`).
2. **Logarithmic commutator carrier.** The prime shift is the exact logarithmic-position
   commutator and its orthogonal compression splits into internal trace defect plus polarized
   leakage cross (`critical-euler-position-commutator-carrier-law`).
3. **Compact-support cyclic descent.** Physical logarithmic phase and dilation give the exact Weyl
   character; every finite prime-power test descends through the canonical Sonin cyclic probe
   (`SoninSemilocalCyclicWeylDescent.lean`).
4. **Fixed-probe all-prime assembly is impossible.** Critical prime tangent coefficients are not
   absolutely summable, and any fixed nonzero Hilbert--Schmidt central cyclic probe preserves that
   failure in trace norm (`not_summable_traceNorm_soninSemilocalCyclicPrimeTangentCarrier`).
5. **Scalar transport/capacity lane is dead.** Common-displacement splicing pays exactly its own
   seam, and atomless width-two capacity plus untouched decreasing-flank surplus still permits a
   completed-lag violation (`SuzukiBicausalNoFreeSplice.lean`,
   `SuzukiCriticalApexVacuumCapacityNoGo.lean`).
6. **Endpoint weakening is exhausted.** A finite lower floor for the completed prime--Gamma flux
   on Gaussian-rational left-half-strip points is already Lean-equivalent to RH
   (`PrimeArchSourceUpperBoundGate.lean`). Producing more equivalent endpoints is forbidden.
7. **Gamma Schur covariance exists.** The actual valuation tower supplies coherent cross-prime
   covariance, and Gamma Schur elimination is exact valuation translation
   (`XiTransverseGammaValuationCoherence.lean`). Do not search for another abstract covariance.
8. **Coherent causal field exists but bounded recovery fails.** All-prime causal rays fuse before
   squaring (`SuzukiCoherentCausalDepthFusion.lean`), but their gain relative to exact moving-wall
   source is at most `C_h/(p+1)`. No finite uniform inverse exists
   (`SuzukiCoherentResponseGainNoGo.lean`).
9. **Exact principal-relative shell descent is already formalized.**
   `SoninPrincipalRelativeIdeal.lean` proves the actual Gram corner equals its canonical shell
   representative modulo the retained projection/time-band ideal, proves principal multiplication
   closure, and proves finite-prime principal/residual uniqueness. `CCMSoninFiniteWordFaithfulness.lean`
   proves the stronger faithful zero/live normal form and associativity. Do not reopen these gates.
10. **Principal cyclic trace and finite-place source value are closed.**
    `SoninPrincipalShellCyclicTrace.lean` constructs the canonical identity-displacement
    logarithmic trace on faithful Sonin normal states, proves cyclicity and Calkin invariance,
    diagonalizes genuine CCM Gram factors, and returns the exact unsquared von--Mangoldt
    coefficient. Do not reconstruct shell length or crossed-product cyclicity again.
11. **Ordinary all-prime Hilbert recovery is impossible, even with an unbounded graph.**
    The depth-zero sharp-wall amplitude is exactly the already formalized critical rooted-Bianchi
    amplitude, whose squared prime norm diverges. `SuzukiCoherentSharpSourceDomainNoGo.lean`
    proves the connector and excludes every nonzero prime-independent scalar renormalization.
    Do not propose a global `ell^2` sharp-source target; only cutoff-renormalized or semifinite
    recovery remains.
12. **Positive cofinal finite-part extension is impossible, even algebraically.**
    `SuzukiCofinalPositiveFinitePartNoGo.lean` proves that a nonnegative nonsummable finite-cutoff
    weight has no finite-valued positive linear extension. More strongly, on any linear domain
    containing the order unit and every finite coordinate indicator, every exact extension is
    unbounded below on the nonnegative cone. No continuity, topology, regulator, or trace estimate
    is assumed. Applied to the exact depth-zero Suzuki sharp mass, finite-cutoff Gram positivity
    cannot descend to a global linear finite part with any finite lower floor. A survivor must be
    genuinely semifinite/nonunital, and its lower floor must be restricted to the completed
    resolvent test family rather than inherited from the prime Gram cone.
13. **Removing the unit does not rescue any completed Mellin profile.**
    `SuzukiCompletedMellinPositiveDomainNoGo.lean` strengthens item 12 from the cofinal unit to an
    arbitrary positive profile.  If a linear domain contains a nonnegative profile `f` and all
    finite truncations `f|_F`, positivity gives
    `sum_F w_p f_p <= Phi(f)`; hence finite-valued extension forces `sum_p w_p f_p < infinity`.
    For the exact critical Suzuki mass and actual Mellin abscissa `sigma`, the transported mass is
    identically `Lambda(p) exp(-sigma log p)` and is summable exactly when `1 < sigma`.  Therefore
    no positive finite part on any domain—unital or not—can contain even one Gaussian-rational
    left-half profile while preserving its finite Suzuki values.  Every exact extension containing
    such a profile is unbounded below on its full nonnegative cone.
14. **Fixed-aperture signed principal-relative finite part is closed.**
    `SoninPrincipalRelativeTraceSplitting.lean` proves directness of principal shell plus exact
    Schatten-1 relative ideal, constructs the unique signed finite part, and identifies the actual
    Gram value with principal logarithmic trace plus one ordinary trace anomaly.  Do not reopen
    trace construction or representative independence at fixed aperture.
15. **That finite-part class is not aperture closed at any strict step.**
    `SoninApertureRestrictionDefect.lean` proves exact nested-carrier defect
    `G_b-Q_bG_aQ_b=X*X`, compact distance at least one for `0<a<b<r*a`, and noncompactness of the
    positive defect. `SoninPrincipalRelativeApertureNoGo.lean` upgrades this to genuine primes:
    every `0<a<b` has a prime `p` for which the defect is outside the exact relative ideal.  Thus
    no strict aperture enlargement preserves all prime corners modulo Schatten-1.  A cofinal
    carrier must add aperture layers to the principal algebra; treating them as trace-class error
    is formally impossible.
16. **The enlarged principal aperture channel is closed and mass-conserving.**
    `SoninApertureRestrictionDefect.lean` identifies every strict-crossing diagonal defect with an
    existing scale-one live shell, proves exact compressed cocycle and quotient additivity, and
    isolates all remaining curvature in Schatten-1. `SoninApertureCyclicMassConservation.lean`
    proves the exact retained/lost operator split and
    `tau(retained)+tau(lost)=log r=tau(total)`. Do not search for another aperture-layer algebra,
    cyclic reader, or principal Burnol cancellation. Only the ordinary trace of the explicit
    Schatten-1 curvature remains on the aperture side.
17. **Aperture curvature is an exact negative square with canonical Ward cancellation.**
    `SoninApertureCurvatureTrace.lean` proves
    `Re Tr Kappa=-||L_(a,b)D_rL_(b,c)||_HS^2` and proves scalar faithfulness:
    `Re Tr Kappa=0 iff Kappa=0 iff L_(a,b)D_rL_(b,c)=0`.
    `SoninApertureWardCurvature.lean` proves the exact transgression
    `2 Re Tr Kappa+||[Z+Z^*,L_(a,b)]||_HS^2=0`. Do not recompute the curvature trace, seek its
    sign, or invent a different positive aperture counterterm.
18. **Scalar aperture curvature is globally exact, and invariant trace cannot read RH orientation.**
    `SoninApertureWardPotential.lean` proves the operator Bianchi identity, exact four-aperture
    energy conservation, an explicit base-aperture Ward potential, and exact base-gauge change.
    Hence `Re Tr Kappa` has zero cohomology class on every ordered chamber.
    `SoninApertureFourierParityNoGo.lean` proves that `Z` and `Z+Z^*` are Fourier-even while the
    forward-minus-inverse bilateral holonomy `H_(a,r)` is Fourier-odd. Every Fourier-invariant
    complex-linear reader annihilates `H_(a,r)`, and it equals the positive Ward energy iff
    `Z=0 iff Kappa=0`. This kills the proposed invariant relative-trace/Ward identification as an
    RH mechanism. Do not ask a global cyclic trace to recover same-fibre horizontal orientation;
    only a fibre-pointed reflection-covariant reader can survive.

## Single live edge

`SUZUKI-COPOISSON-FIBRE-ORIENTATION`

Let `E_b` be orthogonal projection onto Burnol's source-defined co-Poisson quotient and let
`k_w^b` be continuous completed-Mellin evaluation kernel. For bilateral aperture holonomy
`H_(a,r)`, define fibre-pointed Berezin value

```text
h_(a,r)(w)=<E_b k_w^b,H_(a,r) E_b k_w^b>.
```

Construct from explicit co-Poisson source sums, without selecting a zeta zero or assuming a Weil
sign, a source law forcing

```text
h_(a,r)(w)<=0
```

at every right-half co-Poisson annihilator character. Existing exact fibre identity is

```text
h_(a,r)(w)
 =2 sinh(2 log(r)(Re(w)-1/2)) ||k_w^a||^2
```

on that annihilator. Therefore requested source law rules out every right-half off-critical
annihilator character and proves RH. This is now sole RH-bearing Suzuki arrow. A global relative
trace cannot provide it by item 18; reader must remain fibre-pointed, with Fourier reflection
exchanging `w` and `1-conj(w)` rather than averaging them.

## Current falsifiable conjecture — only surviving form

`SUZUKI-COPOISSON-KREIN-CONTRACTION`:

The co-Poisson quotient evaluation-kernel colligation for forward/inverse normalized dilation has
a source-defined Krein contractivity law on the right-half annihilator character cone. Its
diagonal is exactly

```text
||epsilon^-_(a,r,w)||^2-||epsilon^+_(a,r,w)||^2<=0,
```

or equivalently `h_(a,r)(w)<=0`. The conjecture must be proved from compactly supported
co-Poisson seed relations before imposing annihilator condition; restating sign only on zeta-zero
fibres is not a producer.

Conjecture is false for a proposed source colligation if its exact diagonal contains an
uncontrolled positive boundary term on the annihilator, if its invariant part is the whole reader
(item 18 forces zero), or if physical/Fourier defect comparison has opposite orientation. A
successful exact time-band/Calkin lift of compactly supported co-Poisson divided differences is an
alternative realization of this same fibre orientation, not a second frontier.

## Immediate experiment — symbolic, not numerical

Do not compare invariant relative trace with Ward energy: item 18 proves equality only in flat
case. Work directly with projected co-Poisson evaluation kernel and exact bilateral defects.
Factor the quotient dilation colligation into Fourier parity blocks and test whether explicit
co-Poisson seed map supplies a Krein contractive identity before annihilator specialization:

```text
B_+(w)B_+(w)^*-B_-(w)B_-(w)^*
 = -S(w)^*S(w) + terms divisible by Lambda_b(w).
```

At an annihilator character `Lambda_b(w)=0`, such factorization gives required sign. Outcomes:

- exact negative-square-plus-co-Poisson-ideal factorization: proves source sign, then RH;
- unavoidable positive square on annihilator: kills this co-Poisson contraction and sends route to
  time-band lift/no-go audit;
- reflection averaging, global trace zero, or sign asserted only on zeros: no progress.

## Anti-loop checkpoint

Before each new action, answer in this file's log:

1. Which exact unresolved arrow above changes?
2. Which prior theorem prevents this from being a rediscovery?
3. What observation would falsify the conjecture?
4. Does the result prove a source bound, or merely restate RH?

## Log

- **2026-07-22 reset.** `SUZUKI-SOURCE-COMMUTATOR-GRAM` retired as an invalid frontier label:
  corpus already proves the source commutator/Gram and compact-support cyclic descent. Sole live
  edge narrowed to joint cutoff-dependent prime--Burnol completion and a uniform lower floor.
- **2026-07-22 gain hostile test.** Corpus already contained Gamma coherent covariance and exact
  valuation Schur translation, so another square was rejected as rediscovery. Exact causal
  formulas instead prove response/sharp-source gain `<=C_h/(p+1)` and no uniform inverse. This is a
  source theorem, not RH restatement. Live edge is now forced unbounded graph closability plus
  completed finite-part lower floor.
- **2026-07-22 stale-gate audit.** `sonin-log-shell-cyclic-finite-part-descent.md` still listed
  exact shell congruence, algebra closure, and uniqueness as open, but
  `SoninPrincipalRelativeIdeal.lean` and `CCMSoninFiniteWordFaithfulness.lean` already prove them.
  Those gates are closed here to prevent another rediscovery. First unresolved arrow is now the
  cyclic logarithmic functional on the faithful Sonin normal-state semigroup and its exact
  `log(p^m)` diagonal source value. Falsifier: the proposed identity-displacement shell length is
  not cyclic under the exact state product. This is a source theorem, not an RH restatement.
- **2026-07-22 principal trace advance.** Falsifier failed: reverse identity-displacement overlap
  is exactly the forward overlap dilated by the first scale, so logarithmic width is invariant.
  `SoninPrincipalShellCyclicTrace.lean` proves the resulting normal-state trace cyclic,
  Calkin-invariant, diagonal on genuine CCM Gram factors, and equal to the exact prime-power flux
  after the Euler coefficient. First unresolved arrow is now extension through the retained
  relative ideal and Burnol finite-part compatibility. The theorem produces source data; it does
  not restate RH.
- **2026-07-22 terminal-criterion reset and domain no-go.** Novelty and publication value are not
  success criteria: only RH, not-RH, or a class-complete Suzuki no-go counts. Corpus connector
  audit identifies the coherent sharp-wall coordinate exactly with the critical rooted-Bianchi
  coordinate. Its squared prime norm diverges, so the proposed global unbounded recovery graph
  cannot land in ordinary all-prime `ell^2`; nonzero scalar renormalization also fails. The only
  surviving coherent weld is finite-cutoff plus genuinely joint semifinite renormalization. First
  unresolved arrow is finite-part compatibility on that cutoff system and its uniform completed
  lower floor.
- **2026-07-22 positive finite-part no-go.** The remaining renormalization cannot preserve the
  finite-cutoff positive-trace order. A universal algebraic theorem proves that every finite-valued
  linear extension of the exact nonsummable sharp-source masses is unbounded below on the
  nonnegative cone; the same holds on every unital linear subdomain containing all finite prime
  indicators. This kills positive/unital cofinal finite parts. The sole survivor is a proper
  nonunital semifinite domain with a signed finite part and a lower floor proved only on the
  completed Burnol-resolvent test family. Next terminal falsifier is domain saturation: prove that
  this required test family forces the cofinal unit into the finite domain, killing the survivor,
  or construct the proper domain and prove its RH-equivalent floor.
- **2026-07-22 completed-profile no-go.** Unit saturation was the wrong hostile test.  A universal
  profile theorem shows that positivity at one nonnegative profile already bounds all of its finite
  weighted truncations.  Exact critical Suzuki transport identifies those truncations with the
  first-prime Euler mass `Lambda(p)p^(-sigma)`, whose ordinary sum is finite exactly for
  `sigma>1`.  Hence every Gaussian-rational left-half profile is excluded from every positive
  finite domain, even a proper nonunital one; every exact linear extension containing it is
  globally unbounded below on positive observables.  This is a source-domain theorem, not an RH
  restatement.  Positive-semifinite Suzuki completion is now class-completely dead.  Sole survivor
  is a signed canonical Burnol anomaly with a floor only on the normalized (non-conic) profile
  family; next terminal test is whether actual Sonin/Burnol cyclicity canonically fixes that signed
  anomaly and supplies any coercivity not equivalent to assuming its RH-bearing floor.
- **2026-07-22 aperture-closure no-go.** Fixed-aperture trace construction is closed, but its
  proposed cofinal relative compatibility is false.  Exact nesting gives a positive lost-layer
  Gram defect; shell sequences prove compact distance at least one and noncompactness.  For every
  strict positive aperture pair, Archimedean selection plus Euclid supplies a genuine prime in the
  crossing chamber, so the defect lies outside the exact Schatten-1 relative ideal.  This is a
  source-closure theorem, not RH restatement.
- **2026-07-22 aperture-anomaly closure correction.** The prior conclusion was too strong. Exact
  relative reduction identifies every strict-crossing diagonal defect with the existing scale-one
  live shell `S(ra,rb)`; canonical zero/live multiplication already closes modulo the concrete
  relative ideal. Its cyclic value is `log(b/a)`, and diagonal defects form an additive principal
  cocycle. The exact compressed cocycle shows all failure of ordinary additivity is a Schatten-1
  curvature. This closes the enlarged-reader gate without restating RH. Sole aperture-side
  frontier is now the computable scalar `Tr Kappa` and its exact Burnol cancellation.
- **2026-07-22 aperture mass conservation.** Exact live-window telescoping proves that retained
  mass plus lost mass equals the original `log r`; the aperture cocycle is internal transfer, not
  an archimedean anomaly. Burnol can only cancel the ordinary trace of the Schatten-1 curvature.
- **2026-07-22 aperture Ward transgression.** The remaining curvature trace is now exact:
  `Re Tr Kappa=-||L_(a,b)D_rL_(b,c)||_HS^2`. Trace zero is faithful, and symmetrizing the
  successive-layer transition gives a canonical Ward channel satisfying
  `2 Re Tr Kappa+WardEnergy=0`. This is a source-side theorem, not RH restatement. The aperture
  scalar is no longer open; sole connector is equality between this forced relative Ward energy
  and the relative finite part of Suzuki's concrete Burnol conductor, followed by the completed
  co-Poisson source floor.
- **2026-07-22 Ward cohomology and parity no-go.** The proposed connector in prior entry is false
  for every Fourier-invariant complex-linear reader. Aperture curvature obeys exact operator
  Bianchi; its energy integrates to an explicit Ward potential, and base changes are vertex
  gauges. More decisively, symmetric Ward channel is Fourier-even while bilateral RH-orientation
  holonomy is Fourier-odd. Lean proves every invariant linear reader kills holonomy, and equality
  with Ward energy holds iff aperture curvature is literally zero. This is a class-complete no-go
  for invariant relative-trace Suzuki welds, not RH and not a whole-lane no-go. Sole survivor is
  fibre-pointed co-Poisson Berezin orientation (or equivalent time-band lift) that reflection
  transports between distinct character fibres instead of averaging.
