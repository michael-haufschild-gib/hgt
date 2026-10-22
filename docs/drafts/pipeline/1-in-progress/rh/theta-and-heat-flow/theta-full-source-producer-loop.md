# Withdrawn theta slate: corpus grounding for an RH producer

- **ID:** THETA-FULL-SOURCE-PRODUCER-001
- **Stage:** 1-in-progress
- **Type:** SOURCE AUDIT; no active conjecture selected
- **Source:** `theta-all-degree-hankel-producer.md`; current RH frontier; corpus search.
- **Statement:** Audit actual corpus proof mechanisms before selecting a source-derived RH producer. The initial restriction to theta positivity was premature and is withdrawn with the slate below.

## Goal

The user goal is an unconditional Lean proof or falsification of RH. The initially selected
endpoint was `primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis`; identifying
that equivalence did not justify selecting its open premise as a producer conjecture.
No conditional receiver, new carrier, numerical certificate, or finite-order estimate counts as completion.

## Gates

- [x] Source and existing endpoint identified.
- [ ] Dependency-closed paper proof of an all-degree producer.
- [ ] Unconditional Lean producer and RH conclusion verified.
- [ ] Named leaf build, axiom audit, lint, and umbrella wiring verified.

## Corpus anchors

- `PrimeArchThetaAllOrderCumulant`: exact source recurrence and RH endpoint.
- `ThetaGibbsSteinSourceMinor`: existing degree-one source positivity.
- `ThetaRawGramGrowthObstruction`: excludes literal odd-monomial Gram identification.
- `HardExclusionJointCumulants`: exact all-order connected-partition mechanism.
- `TwoSpinFKGLeeYangBridge`: local ferromagnetic mechanism and reciprocal Euler obstruction.

## Withdrawn preliminary slate

These were copied from the existing `theta-all-degree-hankel-producer.md` programme after reading only a small set of modules. They are not new conjectures and have not passed the user's required corpus-wide synthesis. No active candidate is adopted here.

- Hard-exclusion incidence retaining the full mixed moments.
- A positive operator realizing the cleared kernel in the odd-monomial Gram space.
- A synchronized ferromagnetic approximation of the full theta law.

## Evidence and constraints

The first search was unrestricted across an inventory of 58,787 files, including dependencies and prose. Its `partial: false` flag reports search completion, not that this task read or synthesized the whole corpus. Most compiler metadata is source-only or pending; retrieved declarations are candidates until checked in Lean. No numerical computations have been run. The subsequent symbolic scratch check is recorded below.

No RH producer has been proved. The source-realization falsification checked later in this card does not decide RH. Existing unrelated working-tree changes are preserved.

## Proof-body audit after withdrawal

Paths below are relative to `formal/GaloisForLFunctions/`. These are source inspections, not
fresh kernel checks. No claim is made to have read every file in the indexed corpus.

| Actual proof inspected | Mechanism found in its body | Missing input for an RH transfer |
| --- | --- | --- |
| `Hurwitz/JointLadderIndependence.lean`; `JointLadderDeformationBridge.lean` (grid construction) | Independently adjustable finite monodromy coordinates force a polynomial relation to vanish on a full grid. | A corresponding independently movable arithmetic family whose relations are forced by a zeta zero. |
| `HTGeometry/MultipleEllipticGammaCommonStepNilpotence.lean` | Translation removes one face; induction on the remaining finite face set terminates at a constant. | A common source translation step and a terminating face operation for the actual RH source. |
| `HTGeometry/AbelianRepairLeastAction.lean` (energy, termination, uniqueness arguments) | Sink connectivity gives a positive inverse-Laplacian potential bounding legal execution; least action gives uniqueness. | A source-defined legal operation with a proved sink and a faithful arithmetic terminal state. |
| `HTGeometry/AntiEquivariantDescentFormation.lean` | Reversal and an exactly reflection-blind descent force a static target. | The blind descent is an input, not supplied by source reflection symmetry. |
| `RHTower/MobiusBoundaryOppositeSignTransport.lean`; `RouteEParityColumnLoadCircularityNoGo.lean` | A symmetric sign-flipping transport cancels signed row mass; with only row normalization the column defect equals twice the original signed sum. | Construction of the required balanced transport for the literal source. The column error cannot be assumed small as a substitute. |
| `RHTower/PrimeDepthBVWoldResolvedXiLandingAnnihilation.lean` (resolved and scalar landing theorems); `TateKummerWoldGammaIntervalCharacter.lean` (inclusion defect) | Resolved square-zero identities retain vertical coordinates; scalar landing retains an RH-sized obstruction. Finite nilpotent inclusions have a nonzero top boundary. | A faithful scalar descent cancelling the actual boundary, not nilpotence on a larger carrier. |
| `RHTower/PrimeArchThetaAllOrderCumulant.lean`; `HTGeometry/HardExclusionJointCumulants.lean` | Exact logarithmic recurrence; partition collapse when all nonsingleton joint moments vanish. | A realization satisfying those vanishing conditions for the full theta source. The recurrence alone gives no all-degree sign. |
| `RHTower/ThetaRawGramGrowthObstruction.lean` (row obstruction); `PrimeArchThetaGaussianApertureSignedProjectiveCurvature.lean` | Literal raw Gram identification fails; a signed correction repairs specified cold asymptotic coefficients. | Positivity of the full source form at arbitrary degree and parameter, including all cross terms. |
| `RHTower/XiShiftedCanonicalAdmissionProjectiveNextAdmissionRenewal.lean`; `XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal.lean`; `XiShiftedCanonicalAdmissionAdjacentHistoryBudget.lean` | Exact source-work decompositions and finite adjacent-degree sums inside positive Hankel chambers. | Their positive-block premises remain prerequisites. No source theorem closes all blocks or eliminates sparse frontier escape. |

Existing route audits were also consulted: `rh-corpus-architecture-audit-2026-09-05.md`
(first 210 lines only), `frankenstein-source-gamma-centered-monodromy-cartier.md`, and
`../../../5-failed/xi-hurwitz-conormal-graph-source-resolution.md`. They already record failed
endpoint-to-curvature transfers, absent mixed-source couplings, and the compensating
monodromy/scale-zero obstruction. Rephrasing these open transfers is not a new producer.

## Retrieval coverage

Eight search requests ranged across the unrestricted index: unconditional RH producers;
theta connected cumulant positivity; exact signed source cancellation; constructive toy
induction; source rigidity and conservation; sign-reversing mechanisms; source nilpotence;
renewal producers. Candidate statements, source arguments, and available ingredient groups
were inspected to select the proof bodies above and other source files. The toy-induction
request reported partial coverage. Semantic coverage was unavailable and source-index
warnings were present in later requests. None of these search outcomes certifies exhaustive
corpus reading or proves absence of a producer.

Current result: no dependency-closed RH producer candidate has passed this audit. No new repository Lean
module, wrapper theorem, estimate, or numerical experiment was created. The concrete next
mathematical obligation is to find a source construction that supplies one of the missing
inputs, with its dependence proved from the literal arithmetic object.

## Corpus-derived signed-pairing attempt

### Starting evidence

The actual proof in `RHTower/EulerSquarefreeWickDefect.lean` gives one fourfold Euler
monomial but three copies in its ordinary Wick pairing sum. The defect is exactly
`-2*a₀*a₁*a₂*a₃`. Independently, `HTGeometry/ListSignedPositionSum.lean` and
`SignedPairingExpansion.lean` implement crossing signs, and `FermionWickTheorem.lean`
and `FermionExteriorModel.lean` prove the corresponding vacuum formula. These source
bodies, not a remembered theorem, motivated the following test.

### Attempt 1: replace ordinary pairings by signed pairings

Use the literal two-index coefficient `c(i,j)=aᵢ*aⱼ` in `pfaffianPairing`.

**Symbolically verified in Lean:** the four-point signed pairing equals the raw fourfold
Euler coefficient, and equals the already formalized shared-Rademacher four-point moment.
However, its singleton value is zero while the raw coefficient is `a₀`. Thus this direct
vacuum prescription does not reproduce the full source. The all-coefficient proposal is
rejected; the four-point identity is not an RH producer.

Scratch certificate: `/tmp/hgt-euler-signed-pairing-producer-test.lean`, checked with
`lake env lean /tmp/hgt-euler-signed-pairing-producer-test.lean` from `formal`, exit 0.
The four declarations are `euler_signed_pairing_four`,
`euler_signed_pairing_four_is_existing_shared_sign`, `euler_signed_pairing_singleton`,
and `euler_signed_pairing_not_full_source`. Their axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There is one unnecessary-`simpa` style warning.
One foreground Lean process was used and its handle returned terminal exit 0.

**Positive survivor:** exact four-point source recovery and the existing shared-sign even
moment realization. The latter is already formalized in `EulerSquarefreeWickDefect.lean`.
No new carrier module is justified. No all-order new theorem was claimed or checked.

### Attempt 2: positive subset redistribution while preserving full-product fidelity

Inspected `RHTower/CCMSubsetFidelityReadoutRigidity.lean`, including the proof of
`positiveSubsetMixture_eq_fullAtom_of_fullProductFidelity`, and
`PositiveSubsetFidelityRawEulerNonWickUniversalityLaw.lean`. On every proper Boolean face,
nonnegative weights summing to zero must vanish individually; the remaining top weight is
one. Thus this specific proposed repair is already classified and cannot change the raw
source into a Gaussian pair source. This does not exclude arbitrary non-diagonal or
completed constructions.

**Positive survivor:** the exact unique top-atom classification, already formalized in the
named source. No duplicate theorem added.

### Attempt 3: retain the actual completed EWQ interaction

Inspected `EulerSquarefreeWickPrimitiveCompletedInteraction.lean`: removing the two ramified
prime columns gives the genuine primitive character modulo twelve, an exact Euler logarithm
in `Re(s)>1`, and its entire completed L-function with its functional equation. This supplies
a real source construction, but not an RH conclusion.

Inspected `EulerSquarefreeWickPureVacuumMagnitudeRigidity.lean` and the defining transport
and final equivalence proofs of `EulerSquarefreeWickGammaSixPositiveProjectorBridge.lean`.
Positive congruence transport exists for every grade. Preserving the fixed arithmetic
Pauli-X equation on actual Xi fibres is still the RH-equivalent missing clause. The proposed
inference from positive transport to this equation has no proof; adding that equation as a
premise would violate the requested producer scope. The global clause has not been falsified.

### Additional source checks and retrieval limits

Three more unrestricted deep searches covered connected-cumulant production, literal
arithmetic involutions, and signed Euler pairings. All reported completed retrieval but
`source_index_incomplete` and `semantic_coverage_unavailable`; no generated proof idea was
verified by retrieval alone. Exact lexical search located the fermionic source modules.
Their statements and proof bodies were then read as specified above.

`RHTower/CumulantInductionStep.lean` was also read in full. Its `assembled_step` proves
only nonnegativity of a scalar product; it does not prove the analytic cumulant induction
described in the introduction. It cannot serve as an all-order source producer.

This continuation rules out a concrete attempted source realization and two unsupported
repairs. It does not prove or falsify RH, and creates no replacement receiver or estimate.

## Causal-source continuation audit

The next source inspection follows the literal arithmetic half, not an arbitrary kernel:
`ZetaPoleHalfCausalSource`, `ZetaPoleHalfCellRemainder`, and
`ZetaPoleHalfArithmeticLaplace`. The coefficients are constructed in
`SquarefreeConvolutionHalfSelbergDelangeFactorization`; their Dirichlet convolution square
is the constant-one arithmetic function. The weighted full-source transform is checked in
the initial half-plane, while the old-atom cell baseline remains uncontrolled.

The proof bodies of `HTGeometry/OperatorTailDirichletMatroid.logWeight_leibniz` and
`DirichletLogDerivation.pmul_log_mul` supply exact logarithmic product rules. They do not
cancel the retained baseline. `HTGeometry/RenewalOccupationPotential` uses entrywise
nonnegative transition weights and a discount strictly below one in its contraction and
comparison proofs. Neither premise has been produced for this signed source.

Two actual compensation proofs were then checked. In `EulerDeletionLogPrimeForcing`, the
earlier-cutoff harmonic compensator survives as the explicit `forcing` term in the exact
renewal. In `CCMCriticalMellinRieszMobiusRenewal`, the complete divisor cube collapses to
negative von Mangoldt renewal. `CCMUnitRieszExponentialCoherentTrace` identifies the
remaining source as positive prime energy minus positive polar energy. No cancellation
theorem follows just from positivity of these two separate energies.

### Candidate test: a nonnegative full causal root

This candidate is motivated by the actual positive half coefficients and the paper-proved
nonnegative forcing in `dyadic-root-causal-kernel.md`, not by a generic probability analogy.
That card gives, for the normalized complete causal source `g`,

`g*g(u) = 1 - fract(exp u) + integral_0^u fract(exp v) dv`, almost everywhere for `u>0`.

The forcing lies between zero and `1+u`. If `g` were nonnegative, Tonelli would transfer
every positive exponential moment from this convolution square to `g`: the nonnegative
Laplace integral squares to the finite integral of the forcing. Its transform would then
be holomorphic on `Re(s)>0`, with square `(s-1)*zeta(s)/s^2` away from `s=1`.
This is incompatible with an odd-order critical-line zero. The actual source proof of
`GlobalParityWall.exists_odd_order_line_zero_gt` and the unit comparison in
`ZetaLocalZeroCount` were read before selecting this test. The analogous moment-transfer
proof was read in `ThetaTiltXiInfiniteDivisibilityNoGo`.

**Verified analytic component:**
`RHTower.no_positive_halfplane_pole_cleared_zeta_square_root` in
`/tmp/hgt-pole-cleared-root-parity-test.lean` is a closed negated-existence theorem:
there is no `f` analytic on `Re(s)>0` whose square is `(s-1)*zeta(s)/s^2` at every
point of that domain other than `s=1`. Its proof takes an actual odd-order critical-line
zero, retains the nonvanishing completion factor, and contradicts even order of a square.
`lake env lean /tmp/hgt-pole-cleared-root-parity-test.lean` exited 0 without warnings.
The scratch axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.
Imported names were first checked in `/tmp/hgt-pole-root-parity-names.lean`.

**Scope:** the preceding full-source positivity rejection remains a paper argument. The
physical convolution identity and Tonelli transfer for that literal source have not been
newly formalized here. No assertion of nonnegativity, continuation, or RH was inserted as
an axiom. The test does not exclude signed roots on the required domain `Re(s)>1/2`.
No new repository Lean module was added for this consequence of existing parity results.

**Positive survivor:** the obstruction comes from actual critical-line zeros of odd order
above every height, already produced by `GlobalParityWall.exists_odd_order_line_zero_gt`.
The initial-domain arithmetic root remains constructed by `ZetaPoleHalfArithmeticLaplace`.
Neither result supplies its extension through the open region `1/2<Re(s)<=1`.

Six additional unrestricted deep searches covered the causal root, retained arithmetic
baseline, logarithmic renewal, atom/continuum compensation, Landau continuation, and floor
convolution. Each finished retrieval; source-index and semantic-coverage warnings remained.
Candidate statements and source arguments were inspected; the selected proof bodies above
were read directly. A seventh completed deep search inspected fractional-part refinement.
The actual proof bodies in `EulerDeletionMixedRefinementCarry` retain a within-cell correction
and prove its weighted cocycle. `EulerDeletionRemainderRefinementObstruction` proves that the
specified scalar correction-vanishing law fails at zeros; `FractDilateBalance` classifies
the balance required by the original detector. None supplies a correction-free continuation
law for the causal half source. This remains a partial reading of the corpus, not an exhaustive
audit.

## Frozen transfer test: quadratic completion

**Classification:** `[BRIDGE / TRANSFER TEST]`, not a new primary conjecture.
The two-point interlacing mechanism in Jordaan–Kumar, arXiv:2604.25692v2,
requires two real completion points. Deep/method retrieval exposed the literal
`xiShiftedUnitRenormalizedNondegenerateHardEdgeCorrection` and its exact `A² C`
source decomposition. Its coefficient formula and transverse-jet proof were read.

**Frozen test:** for monic adjacent amplitudes with real simple interlacing roots,
does this particular quadratic correction necessarily have two real roots?
This is a necessary feasibility test for the proposed universal transfer, not an
assertion that these amplitudes equal the actual Xi admissions.

**Discriminator:** use `A=X`, `B=(X−1)(X+1/2)`. Their roots interlace, while their
next coefficients are `0` and `−1/2`. Substitute into the literal correction at
`n=1` and check its sign symbolically in Lean. No numerical experiment is needed.

**Whole-route decision:** a failed test forbids importing two-point completion
from monicity/interlacing alone. Any Xi-specific transfer would still require a
new arithmetic restriction on these coefficients. A successful test would only
clear this prerequisite, not prove the source recurrence or RH.

The separate fact-only record is `rh-corpus-producer-facts-2026-09-19.md`.

**Result: generic transfer falsified in Lean.** The initial test passed. A stronger
test also passed with all roots strictly positive:

`A=X−1/16`, `B=(X−1/32)(X−1/2)`, and `0<1/32<1/16<1/2`.

The literal correction at degree one is exactly
`−4(x−15/64)^2−269/1024`, hence has no real root. The scratch file proves
monicity, both complete real zero sets, their strict ordering, and strict
negativity of the correction at every real point. These are symbolic proofs,
not numerical sampling. The test refutes a generic amplitude-level transfer;
it does not assert that either test pair is the actual Xi admission pair.

Verification: `lake env lean /tmp/hgt-quadratic-completion-test.lean`, exit 0.
Four scratch theorem axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. A first pass on the strengthened statement left two elementary
root-equivalence goals; explicitly simplifying `sub_eq_zero` closed both.
The successful final check supersedes that failed pass.

**Positive survivor:** the exact source identity still gives first transverse
jet `−2*x⁻¹*(S'(x⁻¹−y))²` at a nonzero current root. This is already formalized
as `derivative_xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eval_centeredReciprocal`;
its imported declaration was checked and its axiom report is the same standard
three. No new positive RH statement is extracted from it. No production wrapper
or new umbrella import was added.

**Pivot:** stop treating a quadratic correction as a real-root completion from
its degree or interlacing of the input amplitudes. The remaining useful target
is an independent sign law for the literal Xi source before the next positive
block is assumed. This test does not close that target or advance the causal
root continuation. Global lint also remains red on unrelated unreachable
SPE/HB modules in the shared tree; no full/umbrella build was attempted.

### Reframing interrogation

- **Where does the existing proof use the desired sign?** In
  `FiniteExtremeNodePersistence`, positivity supplies the norm ratio in the
  three-term recurrence and the diagonal Christoffel–Darboux value. The actual
  Xi specialization obtains both from the containing Hankel block. Removing
  this premise removes the sign-producing steps.
- **What is the irritant?** The purported inductive source already needs the
  next positive chamber. The degree-two correction looks like the distant
  interlacing paper's completion, but occurs additively multiplied by `A²`.
- **What is invariant?** The first transverse jet at a current root is unchanged
  by that correction. This is an exact source theorem, not an interpretation.
- **Which correspondence must be proved?** A two-root multiplier completing an
  interlacing pair is not identified with an additive `A² C` correction. Both
  its real-root prerequisite and the mixed recurrence must be checked.
- **Am I working on the right problem?** A transfer is useful only if it supplies
  the missing source sign before assuming the containing positive block.
  Another conditional interlacing or budget theorem would not advance that
  obligation. This scratch test decides whether to abandon this transfer;
  it is not a substitute RH deliverable.
- **Primary conjecture gate:** no new primitive compressing three independent
  source results and forcing a new risky consequence has been justified by this
  audit. Do not promote the transfer test to a universal law.

## Frozen arithmetic construction: prime-paired Riesz cancellation

**Target:** the literal `mobiusDilationRieszTail M n` appearing in the
Möbius–divisor source pairing, not an independently chosen positive kernel.
Source definitions and the finite hyperbola duality were read before this test.

**Construction attempt [BRIDGE]:** extend each finite tail coefficient by zero
past its physical cutoff, then pair the terms `d` and `p*d`. In the common
active region their `sqrt M` terms cancel exactly. Test whether this
sign-producing cancellation survives the next distinct prime pairing.
This is a proposed arithmetic mechanism, not a primary universal conjecture.

**Frozen tests:**

1. Identify the zero-extended coefficient with
   `max (sqrt M - sqrt (n*d)) 0`, retaining the cutoff exactly.
2. Derive the first prime difference and its sign.
3. Derive the complete two-prime coefficient, including every cutoff term;
   test the claim that iteration preserves nonnegativity.
4. If the claim fails, classify the exact sign boundary of that same
   arithmetic cell, rather than replacing its coefficients.

**Whole-route test:** a successful iteration would give a candidate source
sign mechanism. A negative two-prime cell forbids that local induction but
does not decide the full sum, where all remaining Möbius terms are retained.
The experiment is useful only for deciding this explicit construction; no
finite cell alone is an RH producer.

### Derived solution and obstruction

Write `h(x,a)=max(x-a,0)`. Exact first pairing gives
`h(x,a)-h(x,b)=min(h(x,a),b-a)` for `a≤b`, hence a nonnegative
remainder. At two distinct primes, the actual Möbius divisor cell is
`h(x,a)-h(x,b)-h(x,c)+h(x,d)`, where
`x=√M`, `a=√n`, `b=√(np)`, `c=√(nq)`, `d=√(npq)`.
The multiplicative square-root geometry forces
`d-(b+c-a)=√n(√p-1)(√q-1)>0`.
Thus the cell is positive exactly when `a<x<b+c-a`, and negative exactly
when `b+c-a<x`. The second pairing does not preserve the first pairing's
nonnegative remainder. Its sharp positive range survives.

The obstruction also occurs in the **complete** tail, not only the selected
four-term cell. Direct symbolic source identities give
`T(2,1)=√2-1>0` and
`T(6,1)=√2+√3+√5-1-2√6<0`.
The latter sign uses `(√2+√3)²<(1+√6)²` and `√5<√6`, without numerical
enclosures. Exact homogeneity
`T(kM,kn)=√k T(M,n)` carries both signs to every positive integral scale.
Finally the literal increment at one is `2γ-1>0`, so
`primeFreeDivisorIncrement 1 * T(6,1)<0` is an actual negative source channel.

**Lean status:** all seven public theorems passed the combined scratch check
without warnings, with only `propext`, `Classical.choice`, and `Quot.sound`.
The finished module is
`formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusRieszPrimeCellSign.lean`,
namespace `RHTower.MobiusRieszCancellation`. Its RH umbrella import is wired.
The named final audit
`lake build GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusRieszPrimeCellSign`
passed; cached dependencies replayed existing warnings, while the new module
built without warnings. Indexes were regenerated. No numerical experiments
or numerical approximations were used; no full or umbrella build ran.
The import-only production audit `/tmp/hgt-prime-riesz-production-audit.lean`
also passed, confirming those same three axioms for all seven public theorems.
Global lint remains red on unrelated unreachable HB angular/Peierls modules;
it reports no error for the new module.

**Meaning for the whole route:** this construction cannot produce the required
global control by declaring the Möbius tail or every source channel
nonnegative. Its signed cancellation must couple different channels.
Neither these identities nor the obstruction establish or refute the
uniform bound on the completed source. Do not continue adding individual
cell examples: the all-scale obstruction and exact positive boundary already
settle the local sign-preservation proposal.

## Completed-source balancing attempt: marked zero-sum lift

**Status:** paper-level producer attempt failed at its source-preserving
transfer. No new RH theorem, no production Lean module, no claim that the
complete-prime-path conjecture is false.

**Source evidence read:** `CCMFUSuzukiMobiusDivisorDilationChannels.lean`,
especially `primeFreeDivisorIncrement_mobius_convolution_eq_atom` and
`increment_rieszTail_eq_completedPrimePolarGamma_window`;
`MobiusDivisorBernoulliPrimeEnergy.lean` (literal merger, conserved sum,
initial and terminal energy);
`RetainedPrimeDescentOrders.lean` and `RetainedPrimeBoundedBatches.lean`
(finite directional witnesses and capacity-limited orders);
`MobiusDivisorSignedPrimeBatches.lean` (isolated-pool endpoint control).
The exact convolution and arbitrarily long batches are already proved.
Neither includes a uniform complete-order construction.

**External mechanism:** Akbas–Sra, *Boolean Small-Ball Inequalities for
Discrepancy Theory*, submitted 17 September 2026,
[Theorem A.5 and proof](https://arxiv.org/html/2609.20785v1).
The paper couples a pair-difference block to a squared-remainder-difference
block, so one choice splits both the sum and its variance. Its unsigned
prefix bound requires zero total; for general unsigned families its proof
adds the norm of the total. Its separate signed conclusion permits choosing
signs. These are inspected paper claims, not imported Lean theorems.

**Constructed arithmetic test [BRIDGE]:** retain the literal signs. For
`1 ≤ k < M`, put

`a(d,n) = μ(d) * primeFreeDivisorIncrement(n) * (√M − √k)`, with `d*n=k`,

and

`g(k) = completedPrimePolarGammaAtom(k) * (√M − √k)`.

The existing exact coefficient theorem gives `Σ_(d*n=k) a(d,n)=g(k)`.
Thus adjoining `−g(k)` makes every product block zero-sum, without an
approximation, omitted Gamma term, or changed Möbius sign. The attempted
producer was to order these exact blocks with the simultaneous sum/variance
split and recover the original source as a controlled marked partial sum.

**Actual transfer test:** give each original entry two coordinates
`(a(d,n), a(d,n))` and each counterterm coordinates `(-g(k), 0)`.
This second coordinate is the marker needed to read the original source.
The total of one marked block is exactly `(0, g(k))`. The full marked family
therefore has total `(0, S(M))`, where `S(M)` is the already identified
complete Möbius–divisor Abel source. Dropping the marker restores zero total
but loses the desired readout; retaining it restores the unknown total in
the paper's general-family conclusion. Centering it requires subtracting
that same total. An unrestricted ordering of the unmarked family does not
ensure that the original entries form a prefix. This explicit construction
has not produced the required complete source control.

**Second transfer tested on paper:** replace fixed prime signs by a
probability law while preserving each literal arithmetic coefficient in
expectation. Already at each prime, coefficient fidelity requires
`E ε_p = μ(p) = -1`, with `ε_p ∈ {-1,1}`. Since `ε_p+1 ≥ 0` and has mean
zero, every positive-weight outcome has `ε_p=-1`. For a finite prime set,
the law is concentrated on the original all-negative prime assignment.
The freely selectable signs needed by this application are therefore
absent. This argument concerns coefficientwise faithful sign randomization;
it does not exclude every possible source-preserving randomized construction.

**Positive-survivor audit:** exact productwise zero-sum completion survives,
but it is precisely the already formalized Möbius convolution, not a new
producer. The marked calculation identifies the retained source exactly;
formalizing that bookkeeping as a new module would add a carrier. No new
positive producer was obtained from either transfer. The existing
fixed-positive-weight complete-path candidate remains open.

**Meaning for the whole route:** the task remains constructing cancellation
for the fixed arithmetic source through complete exhaustion. Finite cone
fullness, large available pools, free sign selection, and zero-sum completion
do not discharge that obligation in the tested construction. This conclusion
comes from the constructed lift and its surviving term, not from missing
search hits. More finite batches or isolated sign examples would not resolve
this particular gap.

**Retrieval limits:** the three new deep/method queries searched signed
channel cancellation, complete ordering, and simultaneous sum/variance
contraction. Candidate and source-argument lanes were inspected. The last
two queries were partial; index warnings included incomplete source and
semantic coverage and a stale coverage snapshot. No corpus-completeness or
absence-of-producer assertion follows. No numerical experiment, Lean build,
or new Lean declaration was used for this paper-level transfer test.

## Fixed-metric construction audit

**Status:** no new producer, no new mathematical theorem claimed. This audit
changes the admissible next construction, not the status of RH.

The full source update was read in `MobiusDivisorMixedTransverseCompensation`:
new transverse defects remain in the post-merger energy, and its compensation
criterion does not assert existence of a suitable prime. The retained-field
homothety in `RetainedPrimeTopHomothety` also retains the coprime mask. Removing
that mask or treating the field as unchanged under core preparation would
change the source.

The attempted fixed-metric repair would assign a positive quadratic energy
to the complete field and make every prime merger contract it. To produce
the requested source bound it would also need cutoff-uniform initial cost
and control of the current head. These requirements imply uniform control
of both the half-prime head and the fully merged source, because both are
reachable partial selections. The existing theorem
`not_uniform_halfPrimeHead_and_total_quadratic` contradicts that consequence.
The diagonal-relative version is explicitly excluded by
`not_uniform_halfPrimeHead_and_total_diagonal`. This is a source obstruction,
not an inference from unsuccessful retrieval. No new no-go module is needed.

Broad arXiv searches used `rearrangement`, `deflation`, and `compensation`,
with 2026 preferred. The relevant transfer audited was
[Liang, arXiv:2608.11986](https://arxiv.org/html/2608.11986v1), Theorem 1.1,
Lemma 2.1 and its direct saddle construction in §2.2. Its positive reverse
edge and left/right eigenvector hypotheses are not supplied by the literal
one-way merger. Adjoining reverse operations is not yet a source-preserving
construction. The paper itself supplies no arithmetic cancellation theorem.

**Meaning for the whole route:** a common metric that certifies every
selection is the wrong target. The remaining possible construction must
select and control a complete compatible history, or introduce a genuinely
source-derived signed mechanism whose cost avoids the excluded simultaneous
head bound. Existing conditional compensation identities and arbitrarily
long batches do not establish that construction. No weaker substitute is
being accepted as goal completion.

The new deep queries completed with source/semantic coverage warnings.
Their candidate, source-argument, proof-idea and ingredient lanes were read;
none was accepted merely from a declaration name. No numerical experiment,
new Lean file, build or axiom claim was made in this audit.

## Coupled receiving-field neutralization [BRIDGE]

**Frozen proof target:** use the actual clipped windows at quotients 2,7,14
to cancel the *current* head/two vector, rather than keep an initially zero
displacement small. For fixed source constants b,R>0 and every C>0, seek
O(sqrt M) distinct unused window primes whose endpoint has
`F_empty^2+F_{2}^2 <= R^2 M`, whose every prefix has raw energy at most
`Q(P)+R^2 M`, and whose endpoint satisfies
`Q(P union L)+F_empty(P)^2+F_{2}(P)^2+M <= Q(P)`.
Here M=14(b+1)N, P contains the existing odd core, omits 2 and the windows,
and Q(P)<=CM^2. An unconditional specialization must supply the preparation
bound at the fixed core. No exhausted order or RH claim is part of this
finite target.

**Inspected source basis:** `exists_mobiusDivisorTwoPlaneWindowGeometry`
supplies genuine unused packets, inward margin and positive removed square
reserve. `exists_planeDisplacement_return_batch` returns an arbitrary initial
vector, not only zero, with every prefix retained. The exact identities in
`MobiusDivisorInheritedTwoCost` identify the changing actual fibres and raw
energy. Existing prescribed-stream repair starts with zero displacement;
the scalar late-prime neutralization controls only the empty coordinate.
Cached deep searches were also run; their incomplete compiler coverage is
not a novelty certificate.

**Paper construction to test:** initialize the return algorithm at
`z0=-(F_empty(P),F_{2}(P))/sqrt M`. Its normalized endpoint is the negative
of the actual new receiving vector. With inward margin c and packet bound
9, put R=324/c+18+c. The radius decreases by c/4 outside that ball.
The initial radius is at most sqrt(C M), so A sqrt M steps suffice for
fixed A. Exact batch energy is
`Qnew=Qold+|Hnew|^2-|Hold|^2-sum(packet square)`.
Each helper supplies at least dM. Enlarge A so its reserve additionally
pays R^2 M+M. The existing PNT square-root capacity supplies all helpers
at sufficiently large N. This produces a new physical state, not a
positivity assumption on an unchanged state.

**Meaning for the whole route:** successful neutralization would remove
the current two-coordinate receiving energy while retaining a controlled
path to that state. It would not control inherited costs in the other
fibres, renew windows indefinitely, or solve the growing retained-field
problem. Those restrictions must remain explicit.

**Kernel-checked result:** both target and unconditional fixed-core
specialization passed `lake env lean /tmp/hgt-two-receiving-neutralization.lean`
without warnings. The new production leaf is
`MobiusDivisorReceivingPairNeutralization.lean`, wired into RHTower.
The public general theorem needs only the initial receiving-pair bound,
not a bound on the entire energy: the initial-radius identity is the only
place admission is used. This strengthening follows from that displayed
paper identity and is checked in the same proof. The fixed-core capstone
supplies that admission from the existing diagonal theorem, controls every
preparation subset, and has no external hypotheses. Its conclusion is a
partial prime order, not RH.

The exact source endpoint pays both initial receiving squares and an
additional M. The prefix allowance is linear in M, rather than accumulating
one error for each helper. These are new source-production conclusions of
the construction; they do not turn the unprocessed remainder into a closed
full-source estimate.

**Final audit:** the byte-identical production leaf passed the named
`lake build GaloisForLFunctions.RHTower.MobiusDivisorReceivingPairNeutralization`
audit in an isolated package using the repository toolchain and cached
dependency oleans. Only the new leaf compiled (121 seconds); no full or
umbrella build ran. Its olean and ilean were installed in the normal cache.
The external import-only scratch audit exited 0: both public theorems use
only `propext`, `Classical.choice`, and `Quot.sound`. Standard-library names
were also checked in that scratch file. The umbrella contains exactly one
new import. Generated indexes were refreshed.

The global lint gate remains red for the same 28 unrelated unwired
Hawking/BM angular and Peierls modules; none names the new leaf. No numerical
experiment or computed certificate was used. The original RH goal remains
open.

## Actual positive-covariance batches [BRIDGE]

**Frozen source-production target:** realize the already-proved positive
real circuit at child cutoffs 2,11,15 by distinct actual parent primes.
Seek fixed constants H,gamma,J>0 and actual common-parent windows such that
every available batch length n has a distinct ordered realization with
all signed displacement prefixes bounded by H sqrt M and total copied
prime-two covariance at least `(gamma*n-J)*M`. The complete inherited
external cost must consequently decrease by that same amount. A closed
cofinal specialization must supply the actual windows and prepared core.
No exact real-weight-to-integer realization is assumed.

**New mechanism derived from inspected source:** write the normalized
profiles as `(A,0),(x,y),(z,w)`, with `A>0`, `x<z<0`, `y<0<w`.
The plane interpolating `q(v)=2*v_1*v_2` at these three points has a
strictly positive intercept. Indeed its first slope is
`2*y*w*(x-z)/((x-A)*w-(z-A)*y)<0`, so its intercept is minus A times
that slope, hence positive. After sufficiently small independent clipping,
one fixed affine lower bound `q(v)>=gamma+ell(v)` survives on every actual
packet. The same profiles retain a strict planar inward margin.

Use fresh inward prime selection to keep the normalized vector sum bounded.
Summing the affine certificate then gives linear covariance growth minus
one bounded boundary term. Exact `mobiusDivisorExternalTwoCost_union`
transports this to the complete inherited cost, including all nonempty
paired fibres. This bypasses rounding circuit weights and requires no
short-interval prime estimate or numerical experiment.

**Whole-route test:** receiving-pair neutralization alone leaves external
prime-two debt unpaid. The proposed construction would supply an actual
debt-removing resource, rather than only the existing real circuit. Fixed
macroscopic windows still have finite capacity; this target does not assert
that their resource pays arbitrary quadratic debt, renews indefinitely,
or produces an exhaustive RH order.

**Kernel-checked construction:** the entire scratch file
`/tmp/hgt-positive-debt-batches.lean` passed with no warnings. The actual
producer is `eventually_exists_mobiusDivisorPositiveDebtBatches`, promoted
to `MobiusDivisorPositiveDebtBatches.lean` and wired into RHTower. Its
constants are fixed before the requested batch length. Every prefix also
retains one quadratic ceiling for the full successor envelope; every
subset of the initial core satisfies that ceiling. No source positivity
or real-weight rounding hypothesis remains in the public theorem.

The affine certificate and inward margin are derived from the inspected
analytic source signs; no numerical experiment was used. The covariance
sum is identified exactly with the physical inherited-cost decrement.
This closes the finite real-circuit realization problem, not the separate
capacity and exhaustion problems identified above.

The unrestricted affine-support deep/method query completed all retrieval
stages but returned mostly scheme-support and kernel-positivity arguments,
none applicable to this source construction. It reported incomplete source
coverage and unmeasured semantic coverage. No absence or novelty conclusion
was inferred from those search results.

**Final production audit:** the byte-identical leaf passed
`lake build GaloisForLFunctions.RHTower.MobiusDivisorPositiveDebtBatches`
in an isolated package with the repository toolchain and dependency cache;
only the new leaf compiled (109 seconds). The resulting olean and ilean
are installed in the regular cache. An external import-only scratch file
passed `lake env lean` and reported exactly `propext`, `Classical.choice`,
and `Quot.sound` for the public producer. No new axioms or proof holes.
The umbrella import is unique; generated indexes are refreshed.

Global lint still exits 1 for exactly the preceding 28 unrelated unreachable
Hawking/BM modules; its error set is unchanged and none names this module.
All owned Lean invocations returned terminal exits. RH is unproved and
unfalsified by this construction.

## Joint receiving-state and inherited-debt production [BRIDGE]

**Frozen target:** construct one actual distinct-prime batch which both
neutralizes the actual initial head/{2} pair to square-root size and reduces
the complete inherited prime-two cost by at least `M*sqrt M`. Require every
raw-energy prefix below `Q(P0)+R^2*M`, release both initial receiving squares
plus M at the endpoint, and supply fixed-core preparation unconditionally.
Use square-root many actual quotient-2/11/15 primes, not independent batches
whose windows may overlap or whose effects may cancel.

**Source-derived paper argument:** start the inward-return algorithm at
minus the actual receiving pair divided by sqrt M. The previous affine
covariance certificate sums to `g*n+ell(sum v)`. The endpoint sum v is the
initial pair divided by sqrt M plus a bounded residual, so its affine loss
is at most a fixed multiple of sqrt M. Choose the batch length A sqrt M
large enough to pay that loss and the required positive debt reduction.
Each squared packet norm dominates its covariance, by `(x-y)^2>=0`.
Thus the same covariance surplus also pays the endpoint raw-energy reserve;
no separate rounding, reserve family, or numerical sign test is required.

**Whole-route audit:** inspection confirms fixed-field descent and arity
accounting are already closed; their growing-field coverage and signed
charge are still open. The joint construction addresses compatibility of
two actual repairs, not renewed capacity. It must not be called a complete
prime order or a solution of the growing-field/cutoff-uniform obligation.

**Kernel check:** the complete joint scratch proof passed `lake env lean`.
The sole warning was a vacuous `change _ = _`; that line was removed before
promotion. The existing producer and the joint producer now share the same
private actual-window geometry proof. The public joint theorem has no external hypotheses.
The byte-identical named-module audit passed (171 seconds), compiling only
this leaf against cached dependencies. Its olean and ilean are installed
in the regular cache. The corrected external import/axiom audit exited 0;
both public theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Auxiliary library-name probes passed with explicit universe
levels. No added axioms, proof holes, or mathematical premises.

The existing umbrella import remains unique. Index generation passed.
Global lint still reports exactly the previous 28 unrelated unreachable
Hawking/BM modules; no new lint error appeared. No full or umbrella build
ran. RH remains unproved and unfalsified.

The affine covariance certificate supplies two concrete resources at once:
its physical covariance lowers the complete inherited cost, and its packet
squares fund the receiving-state repair. This establishes compatibility of
the two actual prime operations. It does not supply renewed windows or an
exhaustive source order. Initial elaboration failures were cast/reducibility
issues; no failed mathematical implication was used as a premise.

## Changing-core, every-cutoff reserve production [BRIDGE]

**Primary target unchanged:** an exhaustive actual prime history with one
cutoff-uniform quadratic budget. The last joint repair does not establish it.

**Frozen discriminatory subtarget:** construct an infinite history of actual
fresh prime pairs, starting at the empty core, with every even and odd prefix
below the original diagonal plus one M-squared allowance at every integer M.
After the first pair, require each complete pair to release a strictly positive
quadratic reserve eventually in M. Cores must grow by two at every stage;
no supplied successful order or source sign is allowed. This is a producer
through changing cores, not a fixed-core batch or a conditional history map.
It deliberately does not assert that the prime sequence exhausts all primes;
that missing quantifier remains the central target, not redefined success.

**Source-derived paper proof:** the exact prime-release sum is supported on
cofactors r with p <= M/r. The already-closed absolute tail law at T=p gives
an all-cutoff insertion cost at most K(P)*M^2/p. Choose each pair beyond a
threshold that makes both insertions cost less than half the telescoping
allowance 1/(n+1)-1/(n+2). The source-derived even-core pair-reserve theorem
permits arbitrarily large pairs while preserving even cardinality. Dependent
choice therefore keeps every physical prefix under the same budget, even
though the source constants change. No asymptotic threshold is used for that
budget; eventuality is confined to each pair's strict reserve.

**Whole-route test:** success would separate the changing-core/every-cutoff
budget problem from exhaustion: neither alone forces coverage. This sparse
construction cannot insert an arbitrary omitted small prime, so it must not
be presented as the missing RH order. A prescribed-prime variant remains
blocked by the source theorem's core-dependent lower threshold, not by an
unproved passage from eventual energy to an all-cutoff bound.

**Kernel-checked producer:** `exists_mobiusDivisorUniformReserveHistory`
constructs the full infinite pair history in Lean. Its cores have cardinality
2n and the prime labels strictly interleave. Both even and odd states obey
`Q_M(state) <= Q_M(empty)+M^2` for every n and every M. Every pair after
the initial pair has a positive eventual quadratic reserve. The complete
scratch file passed without warnings. The byte-identical production leaf passed its named-module Lake audit
(53 seconds; only this leaf compiled with cached dependencies). The external
import/axiom audit exited 0 and reports only `propext`, `Classical.choice`,
and `Quot.sound`. Auxiliary name probes passed after supplying the `Finset`
namespace. Olean and ilean caches are installed, the umbrella import is
unique, and index generation passed.

The first proof attempt exposed only over-aggressive inequality congruence
and a reducible subtype projection in auxiliary proofs; the mathematical
construction was unchanged. No numerical experiment or unproved premise
was used. The primary exhaustive-history target remains open.

## Universal prescribed initial-pair production [BRIDGE]

**Frozen target:** produce arbitrarily large actual primes q such that every
other prescribed prime p, in either order, and every subset of {p,q}, stays
below the original diagonal at every integer cutoff. The threshold for q
must be independent of p. This is an initial-pair producer, not a claim that
these pairs can be concatenated through changed cores.

**Source provenance:** the exact uniform clipped mean in
`DivisorUnsignedChannelExactMean`, the global three-fifths channel ceiling,
all-cofactor four-block energy decomposition in `MobiusDivisorTwoPrimeLocalCriterion`,
and the existing all-cutoff two-large-prime theorem in
`DivisorUnsignedGlobalEnvelope`. The adjacent-channel argument in
`MobiusDivisorTwelveSecondPrimeRecovery` provides the source-derived toy model.
Initial deep and method retrieval returned unrelated general interfaces; those
are not imported as missing arithmetic. A narrower OR query recovered the
actual adjacent-block proof, the separation theorem requiring a parent quotient
threshold, and the fixed-core pair orientation laws. Retrieval was partial and
coverage remains source-index incomplete; all used source bodies were read.

**Paper construction:** choose the common quotient threshold T for mean error
1/1000. For an original cofactor d, if M/(pd) >= T, the a and b channels
are both at least sqrt(M)/16 and differ by at most sqrt(M)/500. The other
channels c,e lie between zero and 3 sqrt(M)/5. Thus
ab >= M/256 while |(a-b)(c-e)| <= 3M/2500; expanding the complete alternating
square proves contraction. If M/(pd) < T and q >= Tp, both qd and pqd
are inactive, and contraction follows from ab >= 0. This supplies one
universal separation ratio with no cutoff or quotient restriction.
Combine it with the existing two-large-prime theorem: a universal q threshold
covers every smaller p from the finite head, while both-large pairs use the
existing theorem. Infinite primes then produce actual cofinal safe partners.

**Whole-route implication:** the first prescribed prime has no remaining
finite-head exclusion in this producer. Exhaustion remains unresolved because
the equal positive leading mean is an empty-core property; a processed core
has signed cancellations, so this proof supplies no changed-core induction.
No numerical experiment or computed cutoff is used.

**Scratch result:** the complete closed producer passes `lake env lean` without
warnings. The actual q-family is cofinal and works for every prescribed p,
including the collapsed p=q case. The proof includes inactive primes and all
four possible subsets. The byte-identical named-module audit passed in 70
seconds; only this leaf compiled. The external import/axiom audit and name
probes exited 0, with only `propext`, `Classical.choice`, and `Quot.sound`.
Both caches are installed and the umbrella import is unique. Index generation
passed; global lint has 28 unrelated unreachable-module errors and no new
error. No full or umbrella build ran. RH remains open.

## Common reserve production across finitely many source states [BRIDGE]

**Frozen target:** for every finite prime field S and epsilon>0, produce a
fresh preparatory prime a and arbitrarily large fresh pairs p<q. One pair
must release positive eventual quadratic energy in every state P+a with
nonempty P subset S, including both parities and states before/after any
prescribed prime in S. Every prefix of a,p,q must stay below Q(P)+epsilon*M^2
at every cutoff, simultaneously in those states. No successful pair, negative
mean, parity, or energy comparison may be supplied as an analytic premise.

**Corpus basis:** `MobiusDivisorDilationMeanUniformRenewal` proves a negative
band for W_(P+a) near a, from W_P(1)>0, independently of parity. A finite
family admits a common width, margin, and onset. The complete pair ratio
profile then supplies one common negative pair coefficient for ratios q/p
in that band. Actual prime intervals supply p,q; the complete energy limit
transfers all finitely many comparisons to one eventual parent tail.
The all-cutoff insertion-cost law is O(4^|P| M^2/p), with constants depending
only on the finite cardinality, so choosing all three primes large pays each
prefix from epsilon/3. This is an actual prime producer with compatible
reserves, not a hypothesis accepting compatible signs.

**Whole-route relevance:** the existing far-ratio incompatibility is avoided
using the interior band near the shared preparatory prime. Reserve existence
is made compatible across an entire finite collection of future processed
states. The initial preparation cost is controlled, but no lower bound yet
forces total reserve to cover a prescribed prime's pre-existing quadratic
debt. Onsets and margins remain field-dependent; complete exhaustion under
one budget is still the actual goal.

**Scratch result:** `exists_mobiusDivisorCommonReserveProducer` passes Lean
without warnings. The public statement supplies the primes, common positive
reserve, simultaneous eventual cutoff tail, and every-cutoff preparation
budget. Empty original cores receive the cost bound only; their strict
reserve is not asserted. First elaboration failures were induction-variable
substitution, multiplication reassociation, and one redundant tactic, not a
failed source comparison. The byte-identical named leaf build passed in 52
seconds, compiling only this leaf. External import/axiom and library-name
audits passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Caches are installed, the umbrella import is unique, and index generation
passed. Global lint has 29 unrelated unreachable modules, the prior 28 plus
`CCMRestrictedWeilPolarSymmetricBoundaryRenormalization`; none names this leaf.
No full or umbrella build ran. Exhaustion and RH remain open.

## Relative reserve production for prescribed-prime debt [BRIDGE]

**Frozen target:** for each nonempty finite prime core P and prescribed fresh
prime r, produce the following unconditional alternative: its limiting debt
E(P+r)-E(P) is nonpositive, or arbitrarily distant actual primes a<p<q
prepare both states and then strictly decrease the actual prescribed-prime
debt. The same pair releases energy in both prepared states, with a common
positive eventual quadratic margin. Every prefix costs at most epsilon*M^2
relative to its original state at every cutoff. No relative-reserve or
negative-correlation premise is accepted by the public producer.

**Corpus basis and paper proof:** specialize the complete correlation-mass
integral to p=1 (its physical theorem requires only positivity). The primitive
is twice the head primitive, while insertion of 1 halves the density. Thus
E(P)=rho(P)*W_P(1) exactly. For R=P+r with positive debt, the continuous
function D(Y)=rho(R)*W_R(Y)-rho(P)*W_P(Y) is positive on a right neighborhood
of 1. The uniform insertion renewal gives
rho(R)*W_(R+a)(Y)-rho(P)*W_(P+a)(Y)
= -sqrt(a)*D(Y/a)+O_P,R(1).
Both inserted densities share the positive factor a/(a+1), bounded below
by 1/2. Hence the weighted difference is strictly negative on a shared band
[a,(1+eta)*a], once a is large. Intersect with the already proven negative
band for P+a. The full pair profile then gives a strictly larger reserve
in R+a than in P+a. Choose actual p,q by the prime-interval theorem; the
complete energy limits transfer both reserves and their strict ordering to
one cutoff tail. The known cardinality insertion bound pays the three
prefixes from epsilon/3 each.

**Whole-route implication:** this targets the missing ordering of compatible
reserves, not merely their existence. It does not assert that the pair pays
the entire original debt, or that preparation lowers debt, or that iteration
exhausts all primes. Those quantifier and cumulative-payment gaps remain.
The exact diagonal identity is an internal lemma of the producer, not a new
public carrier. No numerical experiment is used.

**Scratch result:** the complete producer passes Lean. It supplies arbitrary
preparation distance, arbitrary pair distance after preparation, both actual
reserves and their strict relative ordering on one common cutoff tail, plus
both states' every-cutoff prefix budget. No analytic sign premise is supplied.
The remaining scratch fixes were function extensionality at the p=1 series,
explicit natural-number types for finite suprema, and notation disambiguation;
none changed the paper comparison. Two tactic-sequencing warnings are removed
for the named-module audit. Complete debt payment and exhaustion remain open.

**Named audit:** the byte-identical leaf build passed in 30 seconds, with
only this module compiled and no warnings. The external axiom output contains
only `propext`, `Classical.choice`, and `Quot.sound`. Both caches are installed
and the umbrella import is unique. Index refresh passed. Global lint has 28
unrelated unreachable modules; the earlier CCM polar-boundary reachability
error was resolved elsewhere. No lint error names this producer. The final external import, axiom, and library-name probe exited 0 without
warnings. The name probe uses `Filter.Tendsto.eventually` (continuity unfolds
to Tendsto) and explicit universe levels. No full or umbrella build ran.

## Inherited-core prescribed insertion by two prime clusters [BRIDGE; open]

**Frozen producer target:** for every finite nonempty prime core P and fresh
prescribed prime r, construct an actual finite fresh prime set S beyond any
given bound such that E(P union S+r)<E(P union S). This makes the prescribed
insertion strictly favorable after preparation. It does not bound the final
energy by E(P). Keep every helper internal until that arithmetic producer closes.
No spectral sign or availability assumption may enter the public theorem.

**Source basis:** the exact physical Mellin and diagonal identities give
E(P) as the integral of rho(P)*|M_P(1+it)|^2. Inserting r multiplies this
weight by r/(r+1)*|1-r^(-1/2)*exp(-it log r)|^2. Subtracting the original
weight leaves exactly -2*sqrt(r)/(r+1)*cos(t log r). The corpus's
SteinhausBesselIdentity identifies the full circle exponential average with
I0; BesselIZeroLowerBound and UpperBound supply exponential separation.
LiteralEulerHalfDensityContractionNoGo rules out operator contraction of
raw prime products; no such premise will be used. PrimeWordSynchronizedCluster
is a different, two-state partition source and cannot replace this multiplier.

**Paper mechanism to audit:** choose actual primes in two shrinking relative
windows around T and r*T, with about s*sqrt(T) primes in each. PNT supplies
those counts after a diagonal choice of T. Their exact Euler product approaches
exp(-s*exp(-it log T)*(1+r^(-1/2)*exp(-it log r))) on each compact t-window;
the sum of squared individual weights tends to zero, and the total weight
stays bounded. Fast-phase averaging should therefore give the positive
multiplier I0(2*s*|1+r^(-1/2)*exp(-it log r)|). This has a strictly larger
exponential rate near cos(t log r)=1 than where cos(t log r)≤0. The literal
Mellin weight has positive mass near t=0 (to prove from the positive unit
head and exact finite Euler multiplier). Large s then makes the complete
cosine integral positive. Transfer the strict sign to actual finite S.

**Budget/whole-route check:** this mechanism generally increases the base
energy: its averaged multiplier is at least one. It is not a proof of an
arbitrarily small preparation cost or of exhaustive admissibility. Successful
inherited-core insertion control would replace the present local relative-reserve
gap by a source-dependent preparation-cost and finite-cutoff gap.
All-cutoff uniform budgets and RH remain the final objective. A negative
result on the cost must retain the strongest actual prime producer as survivor.

**Current status:** the complete producer passes the scratch Lean check.
`MobiusDivisorInheritedPrimeInsertionProducer.lean` retains arbitrary P,
constructs actual fresh S beyond any bound, proves the strict coefficient
release at prescribed r, and supplies a positive quadratic release margin
on one common tail of actual integer cutoffs. Actual cluster-product
convergence, full-integral domination, source identification and the energy
conclusion are discharged. The byte-identical named leaf audit passed in
109 seconds. The external import, axiom and library-name probe passed;
the theorem depends only on propext, Classical.choice and Quot.sound.
Regular olean/ilean caches are installed, the umbrella import is unique,
and index refresh passed. Global lint retains 28 unrelated unreachable
modules and reports no error for this producer. No full umbrella build ran.

**Route relevance and exact limitation:** the existing arbitrary-field
batch theorem chooses a complementary preparation core. This target keeps
an arbitrary inherited P and prescribed r, which addresses propagation from
an existing state. E(P union S+r)<E(P union S) controls the prescribed
insertion after preparation; it does not imply E(P union S+r)≤E(P), so it
must not be advertised as absolute payment of the original debt. Uniform
preparation cost and simultaneous all-cutoff bounds through prime exhaustion
remain the hard RH obligations. The producer's value must be assessed
against those obligations, not by counting its private lemmas.

**Sharper mechanism, now checked:** full Bessel averaging is unnecessary.
The source has a positive first block (DivisorContinuousUnitMoment, lines
121–149). Once its Mellin weight is bounded below on a small interval [0,d],
choose log(T)=2*pi*n/d. A continuous nonnegative periodic gate
max(0,-cos(theta)-c), with c<1 close to one, has positive period integral;
its integral on [0,d] after this exact frequency choice is independent of n.
On the gate, both cluster phases lie near pi and give growth exp(2*s*b).
Where cos(t*log(r)) is negative, the ideal two-cluster amplitude is at most
sqrt(1+1/r)<b. Thus positive gated mass beats the entire negative region
for a fixed sufficiently large s. Only then choose a tail cutoff, small
relative windows, and a sufficiently large integer n; the complete finite
Euler-product approximation transfers the strict sign. This replaces the
two-scale limit by exact integer-period integration, without changing the
producer target or its unresolved preparation-cost limitation. The weighted
telescoping bound needed here depends on sum of factor norms, not cardinality.

**Preparation producer [BRIDGE; formalized and audited]:**
`exists_mobiusDivisorBudgetedInheritedPrimeInsertionProducer` chooses K(P,r)
before the lower prime bound B. Every actual preparation subset, at every
integer cutoff, has energy at most K(P,r)*M^2, both before and after inserting
r. The complete coefficient release and eventual actual quadratic release
are preserved. The original producer remains available with its original
statement. This removes the cardinality and distance dependence of the finite
preparation budget. Dependence on the changing P and r, and exhaustive coverage
within one common budget, remain unresolved.

**New paper proof for that producer:** the corpus already closes ambient-label
support and convex smaller-field energy in `sum_mobiusDivisorSelectionFibre_sq_le_energy`
and `sum_mobiusDivisorInterpolatedFibre_sq_le` (the same interpolation module,
lines 167–218). If E_N(P)≤K*N^2 for every N, the interpolated packet is at most
4*K*M^2/p^2 because M/p+1≤2*M/p when p<M. The exact signed merger and weighted
Young inequality then give E_M(P+p)≤K*(1+4/sqrt(p))*M^2. Inactive primes do
nothing. Induction from the corpus's empty-core bound 9*M^2/25 yields
E_M(Q)≤(9/25)*exp(4*sum_(p in Q) 1/sqrt(p))*M^2. All these bounds remain
private ingredients of the actual preparation producer. The cluster supply
already bounds its total inverse-square-root mass before choosing distance.
Thus one K(P,r) controls every helper subset, both before and after inserting r,
at every integer cutoff. The full strengthened producer passes the scratch
check and the byte-identical named leaf audit (106 seconds). Both public
producers pass the external import/axiom/name probe with only propext,
Classical.choice and Quot.sound. Regular caches are installed, the existing
umbrella import remains unique, and index refresh passed. Global lint has
28 unrelated unreachable modules and no error for this leaf. This removes distance and
cardinality dependence of the finite preparation budget, not dependence on
the evolving inherited core or prescribed prime. Marginal release still
does not prove that preparation plus insertion repays the original energy.

**Broad-paper check:** latest-first arXiv search for “amplification” found
[Mayo–Zabokritskiy, 2609.20739v1](https://arxiv.org/html/2609.20739v1).
Section S7 separates sampled-tail error from continuous L2 truncation and
gives unbounded point sampling even for smooth residuals orthogonal to the
finite Hermite space. Consequently its finite unitary norm law supplies no
all-cutoff arithmetic sampling bound. The proof above uses the literal
discrete interpolation instead; no paper premise enters Lean.

**Next route-level attack:** control the combined preparation-and-insertion
cost relative to the original inherited energy, or produce a compatible
history with one budget as P changes. A favorable marginal insertion and a
finite K(P,r) do not imply either result. Before refining constants or margins,
test whether arbitrarily distant bounded-half-weight helpers can reduce the
original complete energy: the literal physical head is unchanged below the
first helper, while their density product approaches one if their total
reciprocal weight vanishes. The exact diagonal identity is available in
MobiusDivisorPrescribedDebtReserveProducer. This is a pending mathematical
test, not a proved obstruction. If it fails, retain the actual sign/budget
producer and change the preparation class rather than adding more carriers.

**Frozen net-cost experiment [BRIDGE; open]:** produce actual inherited even
prime core/prescribed-prime debt witnesses with two simultaneous properties:
fresh preparations still give favorable marginal insertion and the proved
all-cutoff budget, but repayment of the original fixed debt cannot use
arbitrarily distant helpers of uniformly bounded inverse-square-root mass.
The stronger positive invariant to test is a nonzero reciprocal-prime cost.
Source inspection finds a discrete proof: the block primitive depends only
on the two actual fibres at n and n+1 (MobiusDivisorFixedCoreBlockLimit20–33).
Helpers beyond N leave every block n<N unchanged apart from their common
density product. Nonnegative summable block masses (FixedCoreEnergyLimit214–248)
recover the full energy from those prefixes. The product deficit is at most
sum 1/(p+1), and bounded sum 1/sqrt(p) makes this deficit vanish with helper
distance. The parity-oriented actual prime-release theorem supplies strict
debt at arbitrarily large missing primes of every even nonempty inherited
core. This is a source-derived conjecture/proof experiment, not yet a
checked no-go. Its route implication would be to abandon bounded-mass
distant preparation for complete fixed-debt payment, while retaining the
actual marginal-control/budget producer. No numerical test is used.

**Clock specialization requested by user:** retain the actual logarithmic
prime-admission time `log p`, already the shift of the physical head under
`x -> x/p` and the frequency of its Mellin phase. Test the stronger closed
producer: after any real delay τ, actual helpers preserve all literal fibres
at M≤exp τ while reversing the prescribed marginal insertion sign under one
K(P,r). For the same actual debt witnesses, repayment after τ must require
sum 1/sqrt(p)>η exp(τ/2), with η>0 fixed before τ. This is a cost of delayed
arithmetic actions, not an assumed physical time or a zero-location premise.
The delay/cost clock formula and combined capstone are pending Lean audit.
The underlying fixed-prefix/density obstruction and actual even-core debt
prime selection have passed scratch Lean.

**Clock/source and broad-paper audit:** the deep corpus clock search completed
against the available snapshot (compiler coverage remains mostly pending).
`MobiusDivisorDilationMeanRenewal.mobiusDivisorContinuousHead_insert` gives
literal dilation x/p; `MobiusDivisorDilationMean_eq_contour` at log p retains
its exact Mellin phase. `PrimeDelayHerglotzNoGo` excludes positivity of raw
delay modes. `CCMPrimePoleFiniteCoherence` produces delayed finite phase
recurrence but does not give a changing-core energy budget. No raw-delay
positivity or finite recurrence is substituted for the missing producer.
Broad recent arXiv search for synchronization found Hassler et al.,
[2605.30271v1](https://arxiv.org/html/2605.30271v1), May 2026: stationary phase
localization alone does not diagnose dynamical synchronization; their test
retains accumulated phase slips. Here this only suggests keeping accumulated
arithmetic debt alongside phase control. No stochastic or quantum hypothesis,
approximation, or paper theorem enters Lean. The latest-first delay page was
rate-limited; no inference from missing September hits.

## Log

- 2026-09-19 — Opened from the current corpus, after reading the frontier, relevant source constraints, prior theta producer attempts, and source definitions.
- 2026-09-19 — User rejected premature conjecture selection. Preliminary slate withdrawn. Required next step: inspect actual source arguments, positive toy results, and failed mechanisms across theorem areas before adopting a producer conjecture; record exact source provenance.
- 2026-09-19 — Inspected cross-area proof bodies and prior failed transfers as recorded above. No replacement conjecture adopted; no RH progress claimed from retrieval or conditional identities.
- 2026-09-19 — Tested the corpus-derived signed-pairing prescription in Lean; four-point agreement passes but full source fidelity fails at the singleton. Checked the existing positive-redistribution rigidity and the still-missing completed-source reporter law before rejecting these as producers.
- 2026-09-19 — Traced the literal causal half source and exact logarithmic/refinement corrections. Checked the analytic obstruction to a root on the full positive half-plane in Lean; the stronger full-source sign rejection is paper-only. The required signed continuation and RH remain open. Owned Lean checks ran sequentially in the foreground and returned terminal exits; no production build or umbrella build ran.

The final global lint run reports 29 unrelated unreachable modules: the
previous 28 plus `MaassFiniteDeckCuspidalDirichlet`, added elsewhere in the
shared tree. No lint error names the new producer. No full or umbrella
build ran. The all-prime exhaustive history and RH remain open.
