# Suzuki terminal frontier ledger

- **ID:** `suzuki-terminal-frontier-ledger`
- **Status:** active research control file; read before any Suzuki work
- **Terminal objective:** prove RH, disprove RH, or prove a source-complete no-go for Suzuki's
  operator mechanism.
- **Current terminal result:** none. One-angle holomorphic-gauge, BV/co-Poisson, and regular
  finite-Rees post-fusion reflected-sewing subclasses are closed. Exact Xi identification now
  forces a strict first-defect/parity cone and persistent ground leakage, but source admission into
  that cone is open; two-angle meromorphic Livšic/Hermite--Biehler producer remains live.
- **Knowledge control:** `suzuki-source-realization-knowledge-ledger.md` classifies every attempted
  mechanism as parent theory, corpus-known, formal closure, failed class, or live source theorem.
  Read it before changing this file.

## Rule

No new card may reopen the one-angle subclass by changing source, aperture, shift, extension angle,
or finite holomorphic exponential normalization: `SR-51` quantifies over all of them. Coordinate
changes, equivalent RH criteria, generic Grams, scalar capacity laws, and finite-support coefficient
reconstructions do not count as progress. Advance must construct or class-completely refute the
source-selected two-angle meromorphic producer.

## Closed one-angle classification

`SuzukiHolomorphicGaugeCharacteristicLimitWall` formalizes the full analytic category displayed in
Suzuki's Corollary 1.6: eventually entire real-zero characteristics `W_n`, eventually entire
exponents `Phi_n`, and compact-open convergence on all of `C` of `exp(Phi_n) W_n` to
`z^2 XiC/XiC'`. The exponential is entire and nowhere zero, so it preserves real zeros; Weierstrass
forces the target to be entire. The existing unconditional consecutive-zero/Rolle theorem instead
produces a genuine nonzero real pole of that target. Lean proves
`not_suzukiHolomorphicGaugeCharacteristicLimitWall` with standard axioms only.

This is source-complete only for Suzuki's stated one-angle interface: no source-coefficient,
chord-mass, Pick/Ward, aperture, or normalization choice can alter that target type. Fixed-aperture
Hermite--Biehler structure survives. Its sharp positive survivor is the two-angle meromorphic
quotient, in which common gauges cancel and poles remain; that survivor is the live Route-G core.

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
   seam.  Beyond every prescribed aperture threshold, atomless width-two capacity with exact
   capacity-one exterior flanks still permits a completed-lag violation.  Lean formalizes the
   whole eventual information class as `SuzukiCriticalCapacityFlankTailProducer` and proves its
   negation (`SuzukiBicausalNoFreeSplice.lean`,
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
19. **Resolved Euler mixing requires cofinally unbounded Ward capacity.**
    `ResolvedChannelWardLaw.lean` proves that commuting with every resolved channel projection is
    exactly diagonal action and that total projection-commutator energy equals twice off-diagonal
    Frobenius energy. `PrimeMellinJetResolvedChannelNoGo.lean` composes this with positive-log prime
    divergence: a fully resolved channel-preserving incidence cannot realize a summable Mellin jet.
    More strongly, off-diagonal Cauchy--Schwarz and existing Gamma Schur-capacity theorem force
    `E_comm>=2(S/B-1)^2` for accumulated Gamma cost `S` and fixed scalar capacity `B`; cofinally
    `E_comm` exceeds every bound. Do not propose a uniformly Ward-bounded mixer or fixed finite
    Gamma boundary. Sole survivor is singular/growing-capacity principal-relative connection fixed
    from source before fibre evaluation.
20. **Growing reflection-even Gamma/Jacobi capacity is class-completely dead.**
    `ParityProtectedSchurFloor.lean` proves a capacity-independent law: arbitrary corrections in
    the even sector of a self-adjoint parity leave the entire odd packet Gram as an exact
    Pythagorean residual. `GammaEvenBoundaryParityNoGo.lean` identifies that protected Gram for the
    actual normalized Gamma source as `(phi(t-u)-phi(t+u))/2`, proves a uniform positive diagonal at
    every prime logarithm, and shows that weighting by the actual Gamma conductor Schur costs is
    nonsummable and cofinally unbounded. Do not propose more even Jacobi modes as the
    growing-capacity repair. Only a source-derived odd/parity-mixing boundary or signed
    principal-relative finite part survives.
21. **Actual odd Gamma-Jacobi capacity exists and is coherently summable.**
    `GammaOddJacobiCapacity.lean` proves the literal odd Jacobi sine coefficients, the exact Mercer
    expansion of the protected Gamma kernel, its finite-rank tail law, and a least source rank at
    each prime whose Gamma-conductor-weighted residual is bounded by `p^-2` and hence summable.
    `GammaOddJacobiCoherentCapacity.lean` zero-pads those prime-dependent cutoffs in the common
    absolute Jacobi coordinate, proving one positive cross-prime kernel on every finite packet with
    exactly that summable weighted diagonal. Do not reopen parity capacity, seek a common rank, or
    mistake generic Gram positivity for novelty. Sole source-realization gap is placement of this
    fixed boundary kernel in an actual singular/local Green--Schur incidence preserving completed
    Euler multiplication; a signed principal-relative alternative remains possible.
22. **Finite successor--Bianchi placement is solved; additive Hankel boundary is dead.**
    `ConservativeHankelRigidity.lean` proves any Hankel-balanced kernel with zero unit row is zero.
    `VonMangoldtAdditiveLogJetHankelCurvature.lean` strengthens the prior zero-row observation to an
    exact all-order source law: every adjacent successor curvature is a strictly negative
    summable von Mangoldt edge density. Therefore no additive ordinary Hankel boundary can repair
    successor carrier. `VonMangoldtSuccessorBianchiHankelWeld.lean` supplies positive survivor:
    actual pointed Bianchi tail feature shares same finite prime coordinate as successor edge;
    `difference + tail = head` exactly. Forced mixed block has exact opposite positive curvature,
    and coupled Gram is positive shifted moment-Hankel matrix at every finite aperture and jet
    size. Do not reopen finite cross-term placement or take orthogonal direct sum. Sole remaining
    source-realization gap is cofinal singular/principal-relative completion retaining forced mixed
    block while incorporating coherent odd Gamma--Jacobi residual and completed Euler trace.
23. **Signed principal-relative cofinal Hankel current is solved.**
    `VonMangoldtSuccessorPrincipalRelativeHankel.lean` proves every source-relative log moment is
    absolutely summable and that pointed-tail subtraction retains exactly successor plus forced
    mixed block. Whole fixed jet matrix converges cofinally to universal Hankel kernel
    `R(r,s)=rho_(r+s+2)`. Mixed block cancels successor Hankel-shift defect at every finite order.
    Do not reopen matrix-entry renormalization or claim divergent diagonal Grams prevent signed
    limit.
24. **The signed current has exact, unbounded negative index.**
    `VonMangoldtSuccessorTransportInertia.lean` factors every full aperture section as a
    square Vandermonde congruence of the endpoint-divergence masses and counts all positive,
    negative, and null directions exactly. The left endpoint is always negative. Every prime
    `p>3`, `p=3 mod 4`, contributes another negative direction because `p-1` is not a prime
    power; Dirichlet's theorem makes negative index unbounded. Therefore no positive completion
    and no fixed-index Pontryagin completion can contain all jet compressions. Do not propose
    Hilbert or finite-index repair. Only genuinely infinite-index Krein coupling survives.
    Remaining obstruction is object type: `R` is jet kernel after prime contraction, while
    coherent odd Gamma--Jacobi residual is prime kernel after Jacobi contraction. Separate direct
    sum is no source connector. Remaining producer problem is source-canonical, inclusion-compatible
    infinite-index bivariate prime--jet completion realizing both marginals and completed Euler
    trace.
25. **Ordinary bivariate partial trace is impossible at every Krein index.**
    `BivariateMarginalTraceLock.lean` proves both coordinate partial traces of an arbitrary finite
    product kernel have equal total trace, without positivity or symmetry.
    `VonMangoldtBivariateMarginalTraceLock.lean` proves the exact source law
    `tr R_(M,N+1)=tr R_(M,N)+rho_M(2N+2)` and `rho_M(2N+2)>0` for every nonempty aperture.
    Consequently no fixed source marginal, including the actual coherent odd Gamma--Jacobi
    marginal, can coexist with two consecutive `SR-40` jet sections through coordinate partial
    traces. Mixed entries and infinite negative index do not change this obstruction. Surviving
    connector must use a singular, weighted/renormalized, non-trace-preserving cyclic reader that
    carries the explicit positive opening flux.
26. **Compact-test operator phase selection is class-completely dead.**
    Under RH, global Weil translations form strongly continuous unitary group and compact smooth
    tests are dense and translation invariant. Invariant-core theorem makes compact-test derivative
    essentially self-adjoint, so its graph closure has deficiency zero. Hence finite deficiency
    projections vanish strongly and every contractive extension-angle schedule has same generalized
    strong-resolvent limit. `NestedExhaustionPhaseUniversality.lean` and
    `SuzukiCompactCorePhaseUniversality.lean` formalize exact unconditional rank-drop Cayley and
    resolvent consequences. Do not use stable-deficiency phase locking as Suzuki source mechanism.
    Positive survivor is narrower scalar moving-boundary limit; strong graph convergence alone
    does not control normalized moving defect vectors, so two-angle meromorphic Route G remains open.
27. **Regular unit-response / finite-Rees post-fusion architecture is class-completely dead.**
    Updated publication-ready biaxial theorem has four conjunctive hypotheses: same unit response
    on every positive exponent shell; orthogonal `ell²` or Bessel shell modes; reflected
    prime-valuation sewing at one finite Rees grade; and terminal sign only after
    reflection-invariant scalar fusion. Finite reciprocal packets split into one common-divisor
    hyperbolic quotient and centered signature `(N-1,N-1)`. Countable breadth is nonclosable or has
    no bounded constant-response Bessel reader even at zero charge. Nonzero reflected depth forces
    sewing norm beyond every finite inverse-Wold power. Post-fusion invariant scalarization erases
    odd modular charge. These failures are independent.

    Exact survivor inside this class is singular or relation-valued in breadth, beyond all finite
    Rees orders in reflected depth, and source-selected **before** scalar fusion while retaining
    shell, valuation-depth, and reflection labels. The theorem does not cover arbitrary bounded
    functionals of Suzuki's scalar screw data and does not close scalar two-angle producer.
28. **Polynomial conditioning in physical Suzuki aperture is dead for exact reflected-valuation
    sewing.** Suzuki's kernel on `[-a,a]` exposes precisely translations `log n` with
    `n≤exp(2a)`. At cutoff `X`, `a_X=(1/2)log(X+1)`. Harmonic/Euler-product domination gives
    `log(X+1)≤b_(X+1)^(-1)`, where `b_N` is finite Wold boundary volume. Combining this with item 27
    proves, for every exact bounded reflected Hellinger sewing family and fixed `K`,
    `a_X^K=o(||R_(X+1)||)` and `||R_(X+1)||` is not `O(a_X^K)`.
    `SuzukiApertureReesConditioningNoGo.lean` formalizes theorem unconditionally.

    This is a genuine quantitative narrowing, not terminal closure. Singular/relation-valued,
    beyond-all-orders, or source-selected pre-fusion maps and direct scalar two-angle convergence
    remain outside its hypotheses.
29. **Xi identification forces a strict first-defect cone and persistent ground leakage.**
    Normalize the exact Xi Donoghue/Livšic target at `i` and write
    `κ_Xi=Re(2i Theta_Xi'(i))`. Multiplicity-exact squared-zero moments, the unconditional
    first-zero-height gap, and the open critical strip prove

    ```text
    77/85 < κ_Xi < 1,
    2i Theta_Xi'(i) = κ_Xi in R.
    ```

    Therefore every Xi-identifying Suzuki parity state has even energy share `>81/85` and odd
    share in `(0,4/85)`. Weierstrass derivative convergence for the actual disk-conjugated finite
    Livšic quotients forces their exact source defect angles to tend to `κ_Xi`; higher-order-only
    noncollapse cannot identify Xi. Under the exact ground-pole inequality, every such family has
    eventual leakage `>(1-κ_Xi)/4>0`. Thus both free collapse and ground-edge Cayley saturation are
    excluded quantitatively.

    `SuzukiXiFirstDefectJet.lean` and `SuzukiXiFirstDefectJetSource.lean` formalize all statements
    unconditionally. This is a target obstruction plus source-convergence connector, not source
    admission. Per the updated superselection paper, fitting `κ_Xi` from target data would be
    source-provenance theatre. Live arrow is source-only construction of a cofinal schedule in the
    strict cone with full Xi identification, or a proof actual source dynamics cannot remain there.

## Provider/source-sign edge — live but not the whole Route-G terminal class

`SUZUKI-COPOISSON-FIBRE-ORIENTATION`

Items 23--25 and source-ledger `SR-41`--`SR-43` are producer subproblems for this edge, not a second
endpoint: completed cofinal weld must feed the fibre-pointed Berezin orientation below. Finite
Hankel positivity alone does not imply that orientation. `SR-51` does not close this source problem
or the two-angle meromorphic producer.

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

## Historical falsifiable conjecture — source form

Generic `SUZUKI-COPOISSON-KREIN-CONTRACTION` is retired as a research description. Douglas
factorization, Schur realization, quotient Berezin diagonal, and the fixed critical half-weight
gap were already in corpus; naming a Krein colligation did not change source knowledge.

Live source core is corpus's pre-existing cofinal source-bornology/stable-synthesis/passivity
problem. `CRITICAL-HALF-WEIGHT-COPOISSON-UNITARIZATION`, stated with controls and falsifiers in
`critical-half-weight-copoisson-cocycle-unitarization.md`, is one specialization, not a newly
identified conjecture.

Its exact source obligation is to derive from compactly supported co-Poisson seeds, before any
annihilator specialization, either a source-fixed contractive graph between forward and inverse
quotient channels or a Hermitian identity

```text
A_-A_-^*-A_+A_+^*
 =S^*S+R M_(Lambda_b)+M_(Lambda_b)^* R^*.
```

This is the critical-half-weight causal-polarization problem for a reflection-reversible cocycle.
Reflection alone permits exponents `delta,-delta`; it does not force `delta=0`.

## Immediate experiment — symbolic, source-first, not numerical

Finite-Müntz adjoint and Stieltjes autocorrelation pairing live on different source objects, so
their proposed direct insertion is retired. The first existing source orbit carrying both positive
finite-cutoff Stein defect and exact horizontal character is the fixed BV prime-window orbit.

Construct or refute a closable source map from that coefficient orbit into Burnol's co-Poisson
quotient graph such that square-index decimation intertwines compressed normalized dilation,
quotient evaluation equals continued Laurent principal part, and the nonzero off-multiple layer
survives as the aperture defect. Source norm must make decimation contractive while leaving
inflation unbounded or discontinuous; making both maps contractive is already refuted.

This is not a newly discovered general programme. Existing prime--Gamma reflection-decimation
research has already closed finite all-depth balanced packets and killed finite-rank/diagonal
unbalancing. Its exact remaining general arrow is infinite-rank off-diagonal Green--Schur
incidence preserving completed Euler multiplication. Item 19 further requires cofinally unbounded
Ward energy with growing boundary capacity or source-fixed principal subtraction. Present
experiment asks only whether Burnol's co-Poisson quotient supplies that singular boundary
realization.

Outcomes:

- negative-square-plus-multiplier-ideal boundary factorization: proves source sign, then RH;
- unavoidable positive boundary square surviving modulo multiplier ideal: kills this contraction
  and narrows the time-band survivor;
- only abstract Douglas/Krein existence, reflection averaging, global trace zero, or sign asserted
  on zeros: rediscovery/no progress.

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
- **2026-07-22 anti-rediscovery reset.** Ward curvature, Bianchi, and parity are reclassified as
  formal closure/reader-class no-go, not new scientific knowledge. Corpus audit also found that
  generic Krein-colligation and Douglas-factor language was already banked. Dedicated knowledge
  register `suzuki-source-realization-knowledge-ledger.md` now controls future work. General live
  problem is source-canonical unitarization of reflection-reversible quotient dilation across the
  fixed critical half-weight. First allowed experiment is explicit co-Poisson seed-window boundary
  dissipation, not another quotient criterion.
- **2026-07-22 general-core collision.** Corpus already contained broader cofinal
  source-bornology/stable-synthesis/passivity core, exact Douglas target `(ER12)`, actual finite
  Müntz map, and finite Möbius recovery. Critical-half-weight cocycle card is demoted to a
  specialization. First admissible new attack is cutoff-uniform adjoint synthesis of existing
  Stieltjes boundary vector. Algebraic finite synthesis alone is rediscovery.
- **2026-07-22 level-lift and interface correction.** Full S66--S81 and BV-window audit is now
  indexed in `suzuki-source-realization-knowledge-ledger.md`. It closes scalar transport,
  positive-finite-part, invariant-reader, ordinary `ell^2`, and two-sided coefficient-coisometry
  loops. Direct Müntz-adjoint/Stieltjes insertion is ill-typed at source level. Correct containing
  problem is a critical positive boundary representation of multiplicative decimation retaining
  meromorphic principal parts. Current falsifiable experiment is a BV-to-co-Poisson singular graph
  intertwiner; generic operator realization does not count.
- **2026-07-22 broader-form collision.** `prime-gamma-reflection-decimation-defect-resolvent-rh.md`
  already contains the general singular boundary programme, all-depth balanced finite packets,
  and diagonal/fixed-rank no-gos. Its surviving source theorem is an infinite-rank off-diagonal
  Green--Schur incidence preserving Euler multiplication. BV-to-co-Poisson graph is only a direct
  realization test for that known core, not a new conjecture.
- **2026-07-22 Ward--Schur capacity advance.** Literal resolved-channel Euler preservation is
  class-completely dead: its commutant is diagonal and positive-log output energy diverges. More
  strongly, fixed scalar Gamma capacity forces cofinally unbounded resolved commutator energy.
  This changes source architecture before fibre specialization. Surviving Green--Schur incidence
  must be singular or locally finite, with growing boundary capacity or source-fixed
  principal-relative subtraction; uniform finite-packet Ward bounds are ruled out.
- **2026-07-22 even-capacity parity-floor advance.** Corpus already knew the odd Gamma sine kernel
  and all-even Jacobi residue tower separately, so neither was relabelled as new. Their missing
  arbitrary-capacity composition is now proved: every even correction family leaves the exact odd
  Gram floor, and the actual Schur-cost-weighted prime diagonal is nonsummable. This eliminates
  growing reflection-even Gamma/Jacobi capacity before any fibre or zero is read. Falsifier/control
  remains explicit: odd/parity-mixing channels can remove the floor, and signed principal-relative
  subtraction is not a Hilbert projection. Next arrow is construction or class-complete refutation
  of one of those two source-derived survivors.
- **2026-07-22 odd-capacity and finite-weld advance.** Actual odd Gamma--Jacobi ladder now exhausts
  protected floor with least primewise ranks, common absolute-mode zero padding, positive packet
  coherence, and summable weighted residual. Separately, successor Dirichlet kernel has strict
  negative Hankel curvature at every adjacent order. This kills every additive Hankel repair.
  Actual pointed Bianchi feature supplies exact positive survivor only when placed in same prime
  coordinate: forced cross block cancels curvature and yields exact finite all-order Hankel Gram.
  Falsifiers all failed in Lean. Finite placement and cross terms are closed. Terminal source
  subproblem is now `SR-40`: cofinal singular/principal-relative completion preserving cross block,
  odd Jacobi residual, and completed Euler trace before feeding fibre orientation.
- **2026-07-22 principal-relative cofinal advance.** `SR-40` matrix-current question is solved:
  `Head_M-Tail_M=Successor_M+Cross_M` exactly, entries are absolutely convergent von Mangoldt
  successor differences, fixed jet blocks converge, and both finite and limiting kernels obey
  all-order Hankel shift. Hostile control “principal subtraction loses cross block” is false.
  This does not close critical half-weight. It exposes sharper `SR-41` type mismatch: proved jet
  current and proved prime/Jacobi residual are separate marginals. Live source problem is joint
  inclusion-compatible prime--jet completion with completed Euler trace, not another direct sum.
- **2026-07-23 successor-transport inertia advance.** Full `SR-40` aperture sections are
  Vandermonde-congruent to explicit endpoint-divergence masses. Their inertia is counted exactly,
  left endpoint is always negative, and primes `p>3`, `p=3 mod 4` force unbounded negative index.
  This formally excludes positive and every fixed-index Pontryagin realization. Live `SR-41`
  connector is now forced into genuinely infinite-index Krein geometry before completed Euler
  trace and fibre orientation.
- **2026-07-23 bivariate marginal trace-lock advance.** Arbitrary finite product kernels have
  trace-locked coordinate marginals. Actual `SR-40` jet trace strictly increases by the exact
  positive source moment `rho_M(2N+2)` when one jet opens, while the prescribed `SR-38` prime
  marginal is fixed. Thus even an arbitrary infinite-index mixed Krein block cannot realize both
  via ordinary partial trace. Live `SR-41` is narrowed to a singular or non-trace-preserving cyclic
  reader carrying that source flux before completed Euler trace and fibre orientation.
- **2026-08-01 holomorphic-gauge one-angle closure.** Scope audit isolates Suzuki's published
  one-angle characteristic-limit program from the narrower BV/co-Poisson provider.
  Primary-source statement allows a finite holomorphic exponential normalization but still asks
  ordinary compact-open convergence on all of `C` to `z^2 XiC/XiC'`. The gauge-complete no-go
  quantifies over every entire real-zero family and entire exponent gauge; Weierstrass closure and
  the unconditional target-pole theorem refute the whole class. Paper and Lean are dependency
  closed. Route G is not retired: two-angle meromorphic Livšic/Hermite--Biehler reconstruction is
  exact positive survivor and remains its live core.
- **2026-08-01 compact-core rank-drop correction.** Primary-source operator audit refutes earlier
  Suzuki application of stable-deficiency phase locking. Under RH, compact tests are invariant core
  for unitary translation generator, so graph closure is self-adjoint and global deficiency rank is
  zero. Lean now proves finite deficiency projections vanish and all contractive finite boundary
  schedules share same Cayley/resolvent limit. This closes operator phase-selection subclass only;
  scalar two-angle moving-defect limit remains exact Route-G open core.
- **2026-08-01 Xi first-defect cone advance.** Exact normalized Xi target has real anchored
  defect jet `kappa_Xi∈(77/85,1)` unconditionally. Actual locally uniform Suzuki convergence forces
  source angles to this scalar, parity shares into `(81/85,1)×(0,4/85)`, and ground leakage above
  a fixed positive Xi floor. The hard arrow changes from “retain some jet” to source-only entry
  and full identification inside this strict cone. Corpus complete-monotonicity and generic
  Livšic theorems contain ingredients but not this exact ratio/source consequence; falsifier was
  an atom violating `85 Re(r²)<4 Re(r)`, which unconditional zero geometry excludes. This is a
  source necessity law, not RH or source admission.
