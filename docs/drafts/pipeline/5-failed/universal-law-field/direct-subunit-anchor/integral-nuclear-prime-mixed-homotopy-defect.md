# Integral--nuclear prime-mixed homotopy defect

- **ID:** ULF-INHD-001
- **Stage:** 5-failed
- **Type:** RETIRED ROUTE · RH-EQUIVALENT RECEIVER
- **Source:** `tropicalized-defect-capacity-anchor.md` · MUST-129
- **Statement:** The theta-positive relative graph defect between arithmetic formation and
  Meyer/theta completion of one pre-divisor all-prime incidence complex is nuclear, has integral
  trace, and factors through the unscaled prime-mixed Burnol base-Cauchy colligation with trace
  norm `< 1`.

## Goal

Construct one operator, before any divisor is supplied, whose specialization at a strict-right Xi
copy would simultaneously have trace `1` and trace norm `< 1`.  This would contradict
`|Tr T| <= ||T||_1` and close RH.  The construction must be an operator identity upstream of the
divisor, not the RH-equivalent target capacity inequality.

## Big-picture law

Arithmetic formation and theta completion are not two descriptions of one bounded object.  They
are two singular completions of one integral complex.  Their absolute Hodge metrics have the same
non-nuclear principal anomaly.  The arithmetic content is the **relative failure of their
null-homotopies to agree** after that common anomaly is removed.

That relative failure is the requested object `T`.  It is:

- pre-divisor because the complex is parameterized by arbitrary `s : C`;
- prime-mixed because local prime Koszul coordinates are coupled by the full cross-prime incidence
  differential before any trace or norm;
- integral because its trace is a relative index of two multivalued-horizon projections;
- nuclear because only the difference of the two non-nuclear homotopy defects is trace class.

The critical line would then be the locus where the two completions have zero relative index, not
the locus selected by an imposed positivity condition.

## Checked corpus locks

1. `HTGeometry.PreDivisorMeyerKoszulCompletionEscape` constructs, for arbitrary `s` and prime `p`,
   the source/Hilbert Koszul comparison and the inverse-domain quotient
   `D_s,p^-1(R)/R`.  At an off-line Xi specialization it is nonzero.
2. `RHTower.DeningerCalderonWittAllCrossPrimeIncidenceKoszul` constructs the all-cross-prime
   compatibility differential; its kernel is exactly one scalar horizon.  Independent prime
   copies therefore must be totalized, not summed.
3. `RHTower.RoutePPrimitiveBurnolWindowGramSquare` realizes the complete P-G186 primitive
   base-Cauchy kernel, including all off-diagonal prime/depth/clock entries, as an actual `L2`
   Gram of source-defined Burnol columns.
4. `RHTower.RoutePPrimitiveBurnolBaseNuclearSynthesis` constructs the literal all-prime
   Hilbert--Schmidt synthesis and nuclear covariance.  Its trace is
   `B_base=(216/115)B_Euler<1`; no normalization is needed.
5. `RHTower.RoutePPrimeGammaCubicCarrierIdentification` proves literal natural-number von
   Mangoldt provenance of that kernel and its unsquared coefficients.
6. `RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation` gives the exact transported,
   boundary, and tail-cocycle Gram decomposition.  No off-diagonal packet entry is discarded.
7. `RHTower.RoutePPrimitiveBurnolApertureIntertwinerRigidity` proves that any rate-changing
   landing has the prescribed nonzero aperture commutator.  This channel must occur in the
   relative defect.
8. `RHTower.DirectSubunitEscapeCapacityFusion` proves one strict-right Xi copy has unsigned escape
   multiplicity `1`; the base-Cauchy reduction supplies the matching two-unit energy calibration.
9. `HTGeometry.PrimeFormationCompactNonproper` proves an absolute compact prime reporter cannot
   restore properness.  Therefore `T` cannot be one compact endomorphism of the old completion.
10. `RHTower.HedenmalmThetaKakutaniBalancedIndexNoGo` proves reflected signed index is always zero.
    The construction must take the theta-positive half before reflection pairing.
11. `RHTower.RoutePPrimitiveCollisionCapacityTerminal` proves a post-divisor target trace bound is
    exactly RH.  The required theorem must instead construct the relative homotopy identity.
12. `RHTower.FrankensteinMeyerPrimeKoszulGammaReporter` constructs one nonzero source reporter at
    each Xi divisor which is simultaneously a cocycle for every prime Koszul coordinate.  This is
    the vertical common-class witness needed by the totalization.
13. `RHTower.DeningerCalderonWittAllCrossPrimeGammaAdmissionOperator` proves that Gamma admission is
    conservative on the completed Green sector and that annihilating its reflected-Gaussian Green
    vector is already equivalent to RH.  Gamma incidence therefore cannot be used as the missing
    null-homotopy.
14. `HTGeometry.ProvenanceContinuousCompletion.ExactCompletionDiagram.physical_exact` proves that
    a provenance-continuous completion of eventually exact finite stages cannot create homology.
    Therefore an off-line class is precisely a failure of the finite contractions to survive
    completion; it cannot be inserted as a new completed cycle.
15. `RHTower.TraceNormLimit.traceTower_limit` proves that trace-norm convergence passes both
    Schatten-one membership and operator trace to the limit.  Thus a nuclear completion of
    zero-index finite homotopy defects still has index zero.
16. `RHTower.DeningerMeyerHalfDensityXiGraphClosure` proves that the closed literal-source Xi
    relation has zero vertical fibre on line, full scalar vertical fibre off line, and no closed
    single-valued off-line extension.  The completed object must therefore be relation-valued.
17. `RHTower.DeningerMeyerHalfDensityFiniteXiJetRepairIndex` identifies the multivalued horizon
    with the kernel of source projection and proves its off-line dimension is exactly total
    analytic Xi multiplicity.  For one zeroth-order copy, the required integer is already `1`.
18. `RHTower.IntegralNuclearRelationIncidenceHorizon` proves that incidence totalization commutes
    with the multivalued horizon and that a supplied strict-right Xi copy yields the unit rank-one
    horizon projection with operator trace `1`.  It does not construct a pre-divisor relative
    projection or any subunit factorization.
19. `RHTower.RouteRSourceTopologyObserverDichotomy` proves
    `routeR_no_continuousArithmeticCoreHorizonLanding`: every continuous landing which kills the
    dense finite arithmetic core is zero and cannot retain the full-support horizon.
20. `RHTower.DeningerCalderonWittCrossPrimeClosedRelationNoGo` proves the complementary relation
    horn: every closed relation extending the zero graph on the dense arithmetic core is the full
    source space times a constant vertical fibre.  Its output is nonselective.
21. `RHTower.CompleteResolutionPrimeNormalHilbertSaturation` strengthens that horn: retaining the
    full affine prime-normal packet through collapsing inputs forces the entire Hilbert target into
    the vertical fibre.
22. `RHTower.NuclearRankOneSchatten.traceNorm_eq_norm_of_hasRankLE_one`, together with
    `traceNorm_xiRightPrimeMixedHorizonDefect`, makes the supplied strict-right horizon defect have
    trace norm exactly `1`, not merely trace `1`.

Searches run before this conjecture:

```text
scripts/formal_tools.py research "relative heat trace homotopy defect McKean Singer"
scripts/formal_tools.py research "trace class heat difference relative index"
scripts/formal_tools.py research "Fedosov index formula parametrix defect trace"
scripts/formal_tools.py research "difference of projections essential codimension trace integer"
scripts/formal_tools.py research "prime mixed collision Gram unsquared Euler trace class"
scripts/formal_tools.py research "Meyer completion escape theta Kakutani multiplicity"
scripts/formal_tools.py research "finite exact homotopy trace norm limit trace zero projection difference"
scripts/formal_tools.py research "completion contraction commutator defect relative Hodge projection"
scripts/formal_tools.py research "nuclear homotopy defect integer trace completion anomaly"
scripts/formal_tools.py research "P-G186 primitive Burnol window Gram collision kernel zero clock"
scripts/formal_tools.py research "collision kernel Burnol base Cauchy kernel comparison"
scripts/formal_tools.py research "closed linear relation graph multivalued projection completion escape"
scripts/formal_tools.py research "closed relation source projection kernel multivalued defect finrank"
```

No existing corpus declaration constructs the object below.

## 1. Source nuclear carrier

Let `I=Nat.Primes x Nat`, put every source clock at zero, and let

```text
f_alpha = routePPrimitiveBurnolWindowFeatureLp(alpha,0),
B_base  = routePPrimitiveBaseCauchyCubicTraceBudget
        = (216/115) B_Euler < 1.
```

P-G186 proves directly in the corpus that the finite Gram matrices of the actual `L2(0,infinity)`
vectors `f_alpha` are the full primitive base-Cauchy matrices.  Define the synthesis on finitely
supported vectors and extend it:

```text
A_base : ell2(I) -> L2(0,infinity),
A_base e_alpha = f_alpha,
<f_alpha,f_beta> = K_base(alpha,beta),
||A_base||_2^2 = sum_alpha ||f_alpha||^2 = B_base.
```

The extension is Hilbert--Schmidt because the diagonal sum is finite.  This requires no abstract
choice of RKHS: the carrier and every column already exist in Lean.  Explicitly, for finite `c`,

```text
||sum_alpha c_alpha f_alpha||
  <= sum_alpha |c_alpha| ||f_alpha||
  <= ||c||_2 sqrt(B_base).
```

Hence synthesis extends boundedly, and summing `||A_base e_alpha||^2` over the canonical basis
gives its HS norm:

```text
||A_base||_2^2 = B_base < 1.                          (INHD.1)
```

This is the literal scale, with no damping.  The P-G177 collision carrier is not the P-G194
carrier: the corpus proves only a diagonal rescaling between their kernels, not an entrywise
inter-carrier isometry.  The construction deliberately uses `A_base` throughout.

Prime mixing is literal.  At zero clock each cross entry is a nonzero von-Mangoldt amplitude times
the base Cauchy value `2/(lambda_alpha+lambda_beta)^3`; therefore `A_base* A_base` has every
cross-prime entry and is not a direct sum of prime cells.

P-G194 then supplies an actual three-channel isometry on the closure of the source span:

```text
U_c f = (transport_c f, hardBoundary_c f, tailCocycle_c f),
U_c* U_c = I,
A_col,c = U_c A_base,
||A_col,c||_2^2 = ||A_base||_2^2 < 1.                (INHD.1a)
```

The equality follows first from P-G194's finite Gram conservation and then by density.  Thus
prime-mixed nuclear colligation is constructed before any divisor.  Missing content is not its
existence or budget; it is its graded landing on the arithmetic/theta relative graph complex.

## 2. One pre-divisor prime-mixed complex

For arbitrary `s : C`, start with the local Meyer source coordinates

```text
D_s,p = centeredFlow(-log p) - p^(1/2-s) I.
```

Do not direct-sum their escape quotients.  Couple them horizontally by the cross-prime incidence

```text
(delta x)_(p,q) = h_q x_p - h_p x_q,                 (INHD.2)
```

where `h` is the fixed full-support source horizon already used by the all-cross-prime Koszul
module.  Its exact-kernel law says `ker delta = C h`; all compatible local copies become one
global class.  Totalize vertical `D_s,p` and horizontal `delta` into a `Z/2`-graded complex

```text
C_form(s) = Tot(D_s,delta)
```

on the literal finite/integral formation core.  Complete the same core in two ways:

```text
C_ar(s)     arithmetic/provenance completion,
C_theta(s)  Gamma--Meyer/theta Hilbert completion.
```

The identity on the common algebraic core is retained as a closed comparison relation, not forced
to be a bounded map between the two incompatible topologies.  Functional-equation reflection acts
on the total complex; take its theta-positive half before forming an index.

This totalization is the new structural move.  Single-prime Meyer escape supplies vertical
nonexactness; all-cross-prime incidence identifies the common copy; primitive collision supplies
the only summable all-prime metric.

## 3. Intrinsic definition of `T`

For arbitrary `s`, let `R_ar^+(s)` and `R_theta^+(s)` be the theta-positive closed **linear
relations** obtained by completing the same total formation relation arithmetically and in the
Gamma--Meyer/theta topology.  They must remain relations, not operators: the corpus proves that an
off-line Xi evaluation admits no closed single-valued extension retaining the literal source
graph.  Polarization occurs before closure, so reflected signs cannot cancel.

For a closed relation `R subset X directSum Y`, define its multivalued horizon

```text
Mul(R) = { y in Y | (0,y) in R }
       = ker(sourceProjection : R -> X).              (INHD.3)
```

`Mul(R)` is a closed subspace.  It is exactly the output left when a source sequence collapses to
zero: the completion-created failure of a finite contraction to remain single-valued.  Existing
Lean proves that the closed Meyer Xi relation has `Mul=0` on the line and `Mul=C` off line; for a
finite off-line packet, its dimension is exactly total Xi multiplicity.

Take the common output carrier to be the already-constructed
`DeningerCalderonWittCrossPrimePacketHilbert`; write it as `Y_form`.  Its full-support unit vector
`eta=deningerCalderonWittCrossPrimePacketHorizon` satisfies

```text
ker(delta_crossPrime) = C eta.
```

Let `Pi_ar^+(s)` and `Pi_theta^+(s)` be the orthogonal projections in `Y_form` onto the two
horizons after applying this incidence differential.  Define

```text
T(s) = Pi_theta^+(s) - Pi_ar^+(s).                    (INHD.4)
```

This is the requested object.  It does not project onto ordinary homology and requires no closed
range or bounded Green inverse.  At every finite primitive packet both relations are
single-valued, hence both horizons vanish and `Tr T_F=0`.  A nonzero completed `T` is precisely a
relative extension anomaly of the two closures.  The all-cross-prime incidence is applied before
`Mul`, so its surviving vertical direction is one prime-mixed scalar horizon rather than one copy
per prime.

## 4. Integral and nuclear laws

The missing construction theorem is the following exact package.

### Conjecture ULF-INHD-1 — formation-relative horizon factorization

For every `s` in the open critical strip, the total complex above admits source-canonical closed
realizations such that:

```text
(a) Pi_theta^+(s) - Pi_ar^+(s) is trace class;

(b) Tr T(s) = ecodim(Pi_theta^+(s),Pi_ar^+(s)) in Z;

(c) T(s) = B_s* B_s - C_s* C_s;

(d) ||B_s||_2^2 + ||C_s||_2^2
      <= ||A_base||_2^2 = B_base < 1;

(e) on every finite primitive packet, the Gram of (B_s,C_s)
      is the unscaled full P-G194 colligation Gram.                (INHD.5)
```

`B_s,C_s` are not arbitrary witnesses.  They must be the completed boundary/tail/aperture channels
of P-G194/P-G196, with P-G206's prime-resolved environment retained until after totalization.
Equation `(c)` must hold on every finite primitive packet and pass to the completion by the same
coherent homotopy, not merely by convergence of scalar traces.

More explicitly, ULF-INHD-1 must construct a canonical contractive source-coordinate map
`tau_s : Y_form -> H_I` and a source-marked, grading-aware isometric landing `L_s` from P-G194's
three-channel carrier to the relative total complex, and set

```text
A_s = L_s U_c A_base tau_s : Y_form -> E_s^+ directSum E_s^-,
Gamma_hom = diag(+I,-I),
B_s = pr_+ A_s,
C_s = pr_- A_s.
```

`tau_s` must be the boundary-coordinate map of the two closed relations and send each finite
primitive output cell to its canonical basis coordinate; an arbitrary contraction fails
provenance.
`L_s` is not aperture-covariant: on every primitive column its commutator with the Burnol shift
must be the exact P-G196 eigencharacter gap.  In one line, the requested object is

```text
T(s) = Pi_theta^+(s)-Pi_ar^+(s)
     = A_s* Gamma_hom A_s,                           (INHD.5a)
A_s = graded completion landing of the prime-mixed colligation A_col,c.
```

The left equality quantizes `T`; the right equality makes it nuclear and prices it from literal
Euler formation.  Neither equality alone selects: the entire content is their source-canonical
identification before a divisor is supplied.

Consequences are immediate:

```text
T(s) is nuclear,
||T(s)||_1 <= ||B_s||_2^2 + ||C_s||_2^2 < 1,         (INHD.6)
Tr T(s) is an integer.                               (INHD.7)
```

The integer in `(b)` is standard relative-index/Fedosov integrality for a trace-class difference
of projections.  Essential codimension is used only as the integer-valued readout; it is not the
producer.  The new producer claim is the source-fixed factorization `(c)--(d)`.  The pair is
necessarily singular/non-Fredholm at the neutral fibre, so no norm-continuous index jump is being
claimed.  This is why the relative object escapes the ordinary-index no-go without contradicting
it.

### Proven trace-anomaly dichotomy

Let `T_F(s)` be finite-packet arithmetic--theta horizon-projection differences.  Since both
relations are single-valued before completion, `Tr T_F(s)=0`.  If the source construction makes
`T_F(s) -> T(s)` in trace norm, the already
formalized trace-tower theorem gives

```text
Tr T(s) = lim_F Tr T_F(s) = 0.                        (INHD.7a)
```

Consequently a specialization with relative index `1` forces at least one of exactly two failures:

```text
T(s) is not nuclear through the source finite packets,
or the arithmetic/theta contractions are not one coherent completion of those packets. (INHD.7b)
```

This is the operative higher law: **quantized homology cannot be born through a nuclear coherent
completion of integral contractions.**  ULF-INHD-1 is the arithmetic assertion that literal
Euler/Poisson formation supplies precisely that nuclear coherence, with quantitative mass `<1`.
It is stronger than mere pointwise or provenance convergence and is not supplied by
`physical_exact`; it must construct the actual homotopies and their trace-norm control.

### Conjecture ULF-INHD-2 — escape/index identification

At a strict-right Xi copy `q`, specialization of the pre-divisor total relation has zero
arithmetic multivalued horizon and one-dimensional theta-positive multivalued horizon, and

```text
Mul(R_ar^+(q)) = 0,
Mul(R_theta^+(q)) = C eta,
T(q) = |eta><eta|,
Tr T(q) = thetaKakutaniEscapeMultiplicity(q) = 1.     (INHD.8)
```

The target-side dimension is already proved: the closed Meyer zeroth-Xi relation is maximally
vertical off line, and the finite-packet theorem gives one vertical direction per off-line support
point.  The packet-side dimension is also proved: `ker(delta_crossPrime)=C eta`.  What remains is
the commuting-square theorem saying “take the multivalued fibre, then impose incidence” equals
“totalize the closed relations, then take the multivalued fibre,” and proof that the arithmetic
completion has no corresponding multivalued part.  Nonvanishing alone is insufficient.

## 5. Exact RH closure

Assume a strict-right Xi copy `q`.  Existing Lean gives

```text
thetaKakutaniEscapeMultiplicity(q) = 1.
```

ULF-INHD-2 gives `Tr T(q)=1`.  ULF-INHD-1 and `(INHD.1)` give

```text
1 = |Tr T(q)| <= ||T(q)||_1
  <= B_base < 1,
```

a contradiction.  Functional-equation reflection then excludes the strict-left side.  Therefore
every nontrivial Xi zero lies on `Re s=1/2`.

This is not the terminal target-capacity premise.  The new assertion is the pre-divisor operator
identity `(INHD.3)--(INHD.5)`, with fixed source channels and finite-packet restrictions.  The
target inequality is a formal consequence.

## 6. Finite falsification tests

Before any infinite construction is accepted, it must pass:

1. **Two-prime test.** On `{2,3}`, `T` must contain the off-diagonal primitive collision entry.  A
   block-diagonal prime sum fails.
2. **Aperture test.** Its first aperture variation must reproduce
   `routePBurnolLanding_commutator_eq_eigenvalueGap`.  An intertwining landing fails.
3. **Three-channel test.** P-G194's transported, boundary, and tail-cocycle Gram identity must be
   the finite restriction of `(INHD.5)`.
4. **Environment test.** P-G206's rank-one exterior environment must remain prime-resolved before
   shorting.  A prime-independent shared ghost fails.
5. **Anomaly test.** Formation and completion principal traces must each diverge while their
   difference is exactly the unsquared primitive source term.  Subtracting the source remainder
   fails.
6. **Polarization test.** Reflection pairing after positive-half selection must produce two equal
   unsigned copies; forming signed reflected index first must give zero, matching the existing
   no-go.
7. **Topology test.** `s -> T(s)` cannot be trace-norm continuous across the neutral fibre if its
   integer jumps.  A norm-continuous Fredholm family fails.
8. **Finite-contraction test.** Every finite restriction must compare the two multivalued horizons
   of the actual packet relation and have trace zero.  A family carrying index at finite level has
   inserted divisor data and fails pre-divisor provenance.

## 7. Failed nearby objects

- Absolute compact `T` on the old completion: impossible; identity on a nonzero Hausdorff escape
  quotient forces operator norm at least `1`, and compact formation remains nonproper.
- Raw relative heat difference: may be trace class but has no automatic integer trace; without a
  graded relative index it is only anomaly subtraction.
- Local Neumann remainder summed over primes: each local remainder acts as identity on the escape
  class, so weighting either loses identity or costs at least one unit.
- Frobenius homotopy 2-cocycle: already formalized and classified as a diagnostic, not a source
  `H1` producer.
- Gamma admission null-homotopy: its vanishing on the completed Green vector is already an exact
  RH receiver.  Gamma may define the vertical differential but cannot manufacture `h_ar`.
- Ordinary reflected Fredholm index: cancels identically.
- Closed single-valued theta operator: impossible off line; the literal-source graph closure is
  maximally multivalued.  `T` must project the relation's vertical horizon, not an operator kernel.
- P-G177/P-G194 hybrid: invalid.  Their diagonal weights are proportionate, but no all-entry
  isometry between the collision and base-Cauchy kernels is proved.  The present `T` uses P-G194's
  own unscaled base carrier throughout.
- Provenance-continuous exact completion by itself: forces zero homology but supplies no nuclear
  control of the actual arithmetic/theta contractions.  Treating that continuity as automatic
  assumes the missing theorem.

## Current status

**Retired.** `T(s)` was specified intrinsically and has a concrete finite source nuclear carrier.
The generic implication

```text
relative projection integrality + source factorization mass < 1 + off-line index 1 => RH
```

is complete, but it is a receiver rather than a producer.  The proposed construction has a closed
dichotomy:

1. If `tau_s`, `U_c`, and `L_s` are bounded/contractive and the Hilbert--Schmidt factors extend the
   actual finite packet channels, then the completed Gram defect is the unique continuous
   extension of its finite restrictions.  Every finite horizon defect is zero, hence every matrix
   coefficient of `B_s^*B_s-C_s^*C_s` on the dense finite span is zero.  Therefore
   `B_s^*B_s-C_s^*C_s=0`, so it cannot be the nonzero rank-one horizon defect.
2. If the landing is made singular enough to retain the completion-born horizon, it no longer has
   a bounded/contractive factorization through `A_base`.  The estimate
   `||T(s)||_1 <= ||A_base||_2^2` then has no valid derivation.
3. If the construction is kept relation-valued, the dense-zero-core and prime-normal saturation
   theorems make the vertical output constant or full unless a different source topology and a
   nonzero finite arithmetic action are introduced.  Such a replacement is no longer this route.

Thus ULF-INHD-1 can hold with the required finite provenance only by forcing `T(s)=0`.  Identifying
that zero operator with the theta/arithmetic horizon difference at every `s` is exactly the missing
RH statement.  The suggested factorization does not derive this identification from arithmetic;
it repackages it.

The route remains retired, but its two independent positive halves are now Lean-proved.
`IntegralNuclearRelationIncidenceHorizon` formalizes the strongest target-side fact: if a
strict-right copy is supplied, its incidence-reduced horizon is rank one with trace and trace norm
one.  `RoutePPrimitiveBurnolBaseNuclearSynthesis` formalizes the source-side survivor: the unscaled
literal all-prime synthesis is Hilbert--Schmidt and its nuclear covariance has trace `<1`.  No
theorem identifies these two operators; the bounded/singular dichotomy proves this architecture
cannot do so while preserving its finite-core premises.

### Positive survivor — bounded finite-core coherence rigidity

The nontrivial surviving theorem is:

```text
A completion-born nonzero horizon cannot simultaneously
  (i) vanish on every finite arithmetic packet,
  (ii) be retained by a Hausdorff continuous/contractive landing, and
  (iii) inherit a Schatten-one budget from Hilbert--Schmidt finite-source factors.
```

This is not a heuristic.  Horn `(ii)` is Lean-proved by
`routeR_no_continuousArithmeticCoreHorizonLanding`; the closed-relation alternative is classified
by `deningerCalderonWittCrossPrimeClosedRelation_eq_top_prod_vertical`; and trace-norm coherence is
Lean-proved by `TraceNormLimit.traceTower_limit`.  A future route must change source topology
before completion and prove a new norm estimate native to that topology.  It cannot reuse
`B_base` merely through a contractive landing.

### Positive survivor — completed cubic Green signed scalar tail

Restoring the literal Gamma channel and using strict lower wall `log 2` exposes a second sharp
survivor.  After deleting first atom from primitive Route-P budget, signed scalar completion

```text
open prime tail - polar tail + Gamma tail
```

has absolute value strictly below `1`.  Complete unconditional proof is formalized as
`RHTower.abs_ccmRoutePCompletedCubicGreenTail_lt_one` in
`GaloisForLFunctions.RHTower.CCMRoutePCompletedCubicGreenTailSubunit`.  This corrects earlier
prime/polar-only numerical interpretation.  It does not revive route: signed scalar absolute value
does not bound nuclear norm.  Exact surviving operator obligation is a coefficient-faithful
nuclear lift whose norm retains cancellation before entrywise/operator absolute value and whose
source action lands Xi essential codimension.

The most direct lift is now also closed in Lean.  Multiplying canonical unit-trace prime-Hodge
defect by completed scalar produces Schatten-one operator with trace norm `<1`, but trace becomes
scalar and is provably neither `1` nor `-1`.  See
`RHTower.ccmRoutePCompletedCubicGreenScaledIntegralDefect_closed` in
`GaloisForLFunctions.RHTower.CCMRoutePCompletedCubicGreenIntegralDefectNoGo`.

### Positive survivor — theta-survival relative curvature

The canonical non-scalar relative-metric mechanism itself now exists.  The literal theta
Mellin-six survival shift produces compact positive incoming and outgoing metrics which are each
non-Schatten-one.  Their difference is the positive self-commutator curvature with trace `1`, trace
norm `1`, and operator norm `1/3`.  The normalized Stokes prime lift retains all same-history
cross-prime entries, the exact history marginal, both non-Schatten-one metric terms, and the same
trace laws; its operator norm is at most `1/3`.

This is fully formalized by
`RHTower.primeHodgeHistoryRelativeCurvature_closed` and
`RHTower.primeHodgeHistoryRelativeCurvaturePrimeLift_closed`.  It proves relative subtraction is
source-native, not an ad hoc regularization.  It also closes the tempting operator-norm escape:
positive trace-one curvature has nuclear norm exactly one.  A surviving RH producer must therefore
transport signed cancellation through the nuclear norm and cannot replace `||T||_1` by the much
smaller operator norm.  See stage-3 card ULF-TSRC-001.

## Parent theory boundary

Relative heat/relative index theory already permits differences of two non-trace-class heat
operators to be trace class.  Calderon--Fedosov theory already makes traces of parametrix defects
integral.  New content sought here is their arithmetic fusion: the total all-prime incidence
complex, the literal primitive collision nuclear carrier, and the exact completion-homotopy
factorization `(INHD.5)`.

Primary parents:

- Ulrich Bunke, *Relative index theory*, JFA 105 (1992), 63--76.
- Calderon--Fedosov parametrix formula
  `ind A = Tr((1-BA)^m) - Tr((1-AB)^m)`.
- Hilbert--Schmidt synthesis from a square-summable family and graded trace-class factorization.

## Gates

- [x] 0 -> 1: well-posed, source-pure definition; corpus locks and exact RH edge named
- [x] 1 -> 5: bounded/singular landing dichotomy closes route; positive survivor already
  Lean-proved
- [ ] 1 -> 2: closed as impossible for this architecture
- [ ] 2 -> 3: not applicable

## Log

- 2026-09-02 — object frozen after rejecting absolute compact, raw heat, local Neumann, and
  Frobenius-cocycle forms.
- 2026-09-02 — Runpod finite falsification audit completed through 50,000,000 with all-depth
  truncation, exact one-cell algebra, packet spectra, P-G194 channel conservation, aperture scan,
  anomaly subtraction, environment shorting, and coherent-zero tests. Verdict:
  `SURVIVES PRELIMINARY ATTACK`, Stage 1 only. Scalar/source architecture passed; entrywise
  collision/base rescaling and every fixed diagonal grading of the three P-G194 channels failed.
  A surviving producer must be a source-canonical non-diagonal singular boundary landing and must
  not claim trace-norm convergence from the zero finite horizon defects. Report and raw data:
  `docs/drafts/pipeline/2-fully-proven/computations/integral-nuclear-prime-mixed-homotopy-defect/`.
- 2026-09-02 — final theorem audit retired route.  Existing corpus proves continuous dense-core
  landings are zero, closed-relation alternatives are nonselective/full-vertical, and trace-norm
  coherent zero finite defects retain trace zero.  A singular landing can retain the horizon only
  by forfeiting the contractive Hilbert--Schmidt budget.  Relative-index integrality does not
  supply the missing comparison.  Verdict: `RETIRED — BOUNDED/SINGULAR NORM DICHOTOMY`.
- 2026-09-03 — Runpod follow-up closed three remaining variants: exact Gamma-vacuum subtraction
  stays positive; two-step wild-saddle relocation has signed trace zero and is horizontally blind;
  prime/polar-only cubic-Green fracture leaves stable positive surplus about `0.83948446`.  Report
  and raw data:
  `docs/drafts/pipeline/2-fully-proven/computations/predivisor-relative-operator-route-audit/`.
  Route remains retired.  Only positive survivor is new producer obligation for a
  coefficient-faithful non-scalar prime--polar--Gamma relative operator whose cancellation occurs
  before absolute value; no such operator or norm law currently exists.
- 2026-09-03 — Fourth Runpod diagnostic restored literal Gamma channel and strict lower-wall
  convention.  Signed scalar completed tail is about `-0.09914495` at `N=50,000,000`.  Exact
  infinite theorem was then proved on paper and formalized in Lean as
  `RHTower.abs_ccmRoutePCompletedCubicGreenTail_lt_one`.  This is strongest new positive survivor;
  original projection/index route remains retired because scalar cancellation has no automatic
  trace-norm or essential-codimension lift.
- 2026-09-03 — Direct operator lift closed formally: scalar multiplication of canonical
  unit-trace prime-Hodge defect is trace class and subunit, but its trace is scalar and cannot be
  either integral unit.  Any continuation must be genuinely non-scalar and topology-changing.
- 2026-09-03 — Paper/corpus follow-up tested the three strongest available non-scalar producer
  families.  Actual-head completed-error autocorrelation is exactly the restricted-Weil source
  quadratic, while its only unconditional quantile estimate pays
  `ccmOutgoingQuantileGammaChiSquare`, proved to diverge.  Complex polarization therefore changes
  neither the source form nor its RH-bearing sign.  The completed third-grade connection removes
  separate prime, polar, and Gamma growth, but leaves exactly the completed-error endpoint/flux;
  every fixed subcubic bound on that flux already implies RH.  Mass-matched prime--polar cells do
  give a genuine coefficient-faithful all-prime absolute convergence theorem on every aperture
  head (`summable_ccmActualHeadMatchedPrimePolarCellDifference_of_aperture`), which is the strongest
  positive survivor.  It still does not give an `S1` relative operator or an index landing: the
  exact infinite-Fock logarithmic reporter has both signs at literal prime-power frequencies, and
  even the all-frequency PSD Gram kernel cannot force its order
  (`ccmActualHeadMatchedPhaseAllFrequencyFockGramReporterPositivityRouteKilled`).  Thus
  cross-correlation, higher logarithmic grade, and coherent-Fock completion do not supply the
  missing subunit trace transport.  A future route must add a source-specific phase-sensitive
  non-Fock coupling, not another polarization of these carriers.
- 2026-09-03 — Exact theta-survival relative curvature and normalized Stokes prime lift were
  formalized.  They realize two compact non-Schatten-one metrics with a positive trace-one relative
  curvature and sharp operator norm `1/3`.  Nuclear norm remains exactly `1`; result strengthens
  relative-metric infrastructure but confirms it cannot close subunit trace inequality.
