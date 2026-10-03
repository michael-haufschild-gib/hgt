# TG-C9.11: joint prime–Gamma relative lift beyond incompatible finite cubics

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / hard source-construction target
- **Predecessor solved:** `../3-formalized/tg-fourier-jet-two-depth-refinement.md`
- **Route:** TG; unconditional RH goal remains unmet

## What is now excluded

The unchanged actual Fourier-jet finite packet cubics do not define a single-valued
linear action at any nonzero parameter. Their relation already contains nonzero
vertical vectors before completion and has closure G×G. A new completion cannot
silently retain their exact actions or assume refinement compatibility. The survivor
is an explicit invertible refinement symbol, not a new operator on G.

## Existing source facts; do not rebuild them

The latest deep corpus query `prime Gamma completed logarithmic derivative operator
trace source` returned partial reranking coverage but useful precise source hits.
Their actual source statements and proofs were read.

- `CompletedPrimeGammaMovingHankel.primeArchSourceRelativeTrace_completedCenteredCoordinate`
  identifies the honest prime–Gamma scalar source with I logDeriv xi on Re(s)>1.
  Its proof uses `infinitePrimeFlux_eq_vonMangoldtLSeries` and the completed seam-flux
  identity. The two-value source law is also already certified.
- `DeningerArithmeticCharacteristic.deningerArithmeticCenteredCharacteristic_logDeriv_eq_continuedPrimeGamma`
  supplies the continued scalar identity on `XiExplicitAdmissible`. The characteristic
  section is the source quotient's XiC relation; this is explicitly not a constructed
  topological operator determinant. Do not mislabel the scalar identity as open.
- `SoninPrincipalRelativeTraceSplitting` gives a unique signed finite part for an actual
  finite prime Gram corner: logarithmic principal trace plus ordinary trace of the
  exact Schatten-1 residual. `ofQuadraticCorner`, `toOperator_ofQuadraticCorner`,
  `finitePart_ofQuadraticCorner`, and `finitePart_eq_of_toOperator_eq` are concrete
  source interfaces. The file explicitly excludes cofinal compatibility, archimedean
  completion and a floor conclusion.
- `SoninPrincipalShellCyclicTrace.soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient`
  identifies the actual diagonal shell's principal trace with the unsquared prime
  flux coefficient. `soninGramFactorPrincipalCyclicTrace_diagonal_eq_log` is the
  aperture-independent logarithmic source length.
- `SoninPrimePowerRegularization` has actual residual operators and square-summable
  log coefficients, but also `not_summable_norm_soninLogPrimePowerCoefficient`.
  Square summability does not justify the missing operator/relative trace sum.

## Next conjecture

The canonical principal-relative Sonin prime-power system admits a joint completion
with the actual archimedean dilation sector, producing a source-defined meromorphic
relative operator class whose relative logarithmic trace is the already certified
continued prime–Gamma scalar current. Its boundary class on admissible strict-right
contours should then furnish the genuine Hardy cubic/winding realization needed by TG.

This is NOT yet a proved paper statement or a completed definition. The conjecture
must be made concrete from the existing physical shell and exact relative residual
operators, with an independently specified archimedean component and topology.
Defining the operator/determinant from Xi or its zero list would not solve it.
An abstract existence, compatibility, trace-class or sub-unit premise would not solve it.

## Immediate mathematical attack

Construct the actual operator-valued prime-power source on its absolute-convergence
domain from the certified physical shell/residual split. Keep the unsquared prime
flux and every cross term. Derive its continuation and the archimedean counterterm
from source kernels together, retaining the exact relative ideal and its trace.
The hard step is cofinal analytic continuation of this joint object and recovery of
its boundary index, not another scalar log-derivative identity or finite Gram bound.

First inspect the existing operator/current continuation corpus for precisely this
construction; use hits and compiler freshness rather than absence guesses. Any
failed cofinal construction must expose a concrete obstruction and its strongest
positive survivor. Do not return to already-settled all-packet cubic compatibility.

Still required for RH after the construction: the actual Hardy-index comparison and
a source-derived sub-unit producer. No such conclusion follows from C9.10b.

## C9.11a: coherent aperture transgression

The current audit also found the already-existing cyclic extension, diagonal packet
curvature, scalar Ward potential and `SoninSemilocalCorrectedSource`. The latter
constructs its completion carrier by loading the continued scalar remainder onto a
fixed normalized probe. This exact trace realization does not establish the required
source-derived joint transport; do not count its scalar identity as an open problem.

The concrete missing finite step was retention of all mixed prime-scale terms in
aperture curvature. The dependency-closed argument now passes scratch Lean checking:
every mixed curvature entry is in the concrete relative ideal and has trace
−⟨Z_i,Z_j⟩_HS. Arbitrary coherent complex packets consequently have curvature trace
−‖Σu_i Z_i‖²_HS, faithful vanishing, and an exact canonical Ward cancellation. This
uses the actual mixed quadratic corners and actual layer transitions. It works at
the closed crossing boundary c≤r_i a as well as in the strict chamber.

Completed child: `../3-formalized/tg-sonin-coherent-aperture-transgression.md`.
Both production leaves and all 22 public declarations pass the separate audit.
This solves the finite coherent quadratic aperture step, not the cofinal joint
prime–Gamma construction, degree-three comparison, or source-derived sub-unit law.

## C9.11b: the surviving cubic channel

The actual coherent balanced Ward completion B=K+[X,E]†[X,E]/2 retains the
concrete relative ideal and has zero complex trace. It is self-adjoint but
indefinite whenever the lost transition Z is nonzero. Its exact cubic character
is Re Tr B³=-(3/2)||ZZ†W||²_HS, with W=Y Q_c; this vanishes iff Z†W=0.
Thus the scalar cancellation does not remove the retained/lost Gram channel.

Canonical paper proof and completed Lean audit:
`../3-formalized/tg-balanced-ward-cubic-survivor.md`. Both new leaves and all
21 public declarations pass the separate audit. The failed positive-completion
candidate and its strongest survivor are recorded in
`../5-failed/tg-balanced-ward-positive-completion.md`.

The next construction must control this actual cross channel in the joint
prime–Gamma class. C9.11c and C9.11d now prove Z†W=0 iff Z=0 for the literal source,
including every finite coherent packet. The proof derives source injectivity;
it does not assume dense range. The cofinal completion, Hardy index and sub-unit
producer remain the RH-critical open problems.


## 2026-10-02 — C9.11c source rigidity closed; coherent extension next

The actual dilation source now has exact inverse support on bounded forbidden sums:
`D_r v∈T_c ↔ v∈T_(c/r)` for `v∈T_b`, `b,c>0`, `r>1`. This makes `Q_cD_r`
injective on the lost layer in the crossing chamber. At one scale, `Z†W=0 iff Z=0`;
therefore the balanced Ward cubic is strictly negative exactly for nonzero `Z`.
Twelve declarations in `SoninDilationSourceSupportRecovery` and `SoninSingleScaleWardRigidity`
passed foreground final leaf audits and separate axiom audit (standard three only).
See `../3-formalized/tg-sonin-retained-channel-rigidity.md`.

This closes a genuine source-support gap in C9.11b. It does not prove every strict
aperture transition is nonzero, nor complete the prime–Gamma source or identify its
Hardy index. Next conjecture C9.11d isolates the largest active dilation of a coherent
packet and recovers support by a finite contraction; duplicate scales must first be
combined. See `../3-formalized/tg-coherent-dilation-support-rigidity.md`. No uniform cofinal separation
is assumed. RH remains unproved/unfalsified.


## 2026-10-02 — C9.11d complete finite coherent rigidity

Exact grouping of equal scales, removal of canceled weights, and outermost-dilation
support descent now prove retained injectivity for every nonzero finite coherent
source. Applying it to the conjugated source and separately discharging the zero
source proves **Z†W=0 iff Z=0 for arbitrary complex finite packets**. Therefore the
actual balanced Ward cubic is zero iff Z=0, and strictly negative otherwise.
No finite packet nonvanishing or density premise is imported.

`SoninFiniteDilationSourceSupport` and `SoninCoherentWardSourceRigidity` contain
18 new public declarations. Both new leaves, the changed support leaf and the
single-scale dependent passed foreground final audits; all 33 declarations across
the four leaves passed axiom audit (standard three only). Canonical paper proof:
`../3-formalized/tg-coherent-dilation-support-rigidity.md`.

### Next source-construction attack

The finite coherent decoupling question is resolved. Construct the joint Gamma
counterterm on the actual source carrier before attempting a cofinal cubic limit.
Current precise corpus inputs inspected:

- `CCMArchimedeanPhaseOperatorProduct`: literal Gamma scattering unitary on L²,
  `L_Gamma=(1/2) M_(u_Gamma*)[H,M_u_Gamma]`, and Schwartz-tested Schatten-one/infinite-order
  certificates. This is an actual operator, not a scalar completion remainder.
- `SoninSemilocalRelativeTrace`: physical principal/residual linear cross terms
  and their canonical Hilbert–Schmidt pairing with the exact projection correction.
- `SoninSemilocalCorrectedSource`: the completion carrier is a normalized tangent
  probe multiplied by the scalar remainder. Its trace identity cannot establish
  the operator-level Gamma or mixed prime–Gamma terms needed here.
- `FiniteEulerGammaDifferentialWeld` supplies scalar digamma/coth reflection identities;
  `SoninSemilocalGammaDifferentialFrame` supplies Gamma-kernel derivative control.
  Neither is itself the joint operator construction.

The next conjecture is that the literal Gamma phase differential, after the actual
Mellin carrier transport and common aperture cutting, yields the missing relative
operator counterterm and its mixed cubic terms. The carrier transport and exact
operator comparison must be specified and proved; do not assert this from a scalar
trace equality. The infinite prime source has no largest active scale, so C9.11d
cannot be passed to that limit by assumption. Hard RH gaps remain this joint
completion, the source-to-Hardy cyclic index comparison, and the sub-unit law.

## 2026-10-02 — C9.11e literal Gamma normal form and continuum survivor

The actual Mellin carrier transport was already in the corpus. The new comparison
now proves `LΓ=A₁+R₁-1`, hence `LΓQ_b=Q_bLΓ=-Q_b` for b≥1. A bare scalar Gamma
addition leaves `(Q_a-Q_b)H Q_b` unchanged and cannot repair C9.11d's cubic channel.
The positive survivor is exact: `A_g LΓQ_b=-A_gQ_b`, and the actual Schwartz continuum
source `A_gQ_b` is trace class. Ten public theorems in `CCMGammaSoninNormalForm`
passed final leaf and separate axiom audits (standard three only); umbrella wired.
Paper proof: `../3-formalized/tg-gamma-sonin-normal-form.md`.
Closed proposal: `../5-failed/tg-bare-gamma-additive-repair.md`.

Next C9.11f uses the existing finite spherical scattering unitary, which is Gamma
times the product of every local Euler ratio. Its joint differential should have
the exact physical form `V_S* R₁ V_S+A₁-1` and a complementary Gram compression on
Sonin. This is a source-level mixed-product comparison, not an assumed cofinal
limit. See `../3-formalized/tg-finite-scattering-sonin-normal-form.md`.

## 2026-10-02 — C9.11f full finite Euler–Gamma source comparison

The actual finite spherical scattering unitary now has the exact physical
logarithmic differential `D_S=V_S*R₁V_S+A₁-1`. An AE theorem identifies V_S with
the product of every finite local Euler ratio, so no mixed term is replaced by
a scalar remainder. For b≥1, `-Q_b D_S Q_b=B_S*B_S`, where
`B_S=(1-R₁)V_SQ_b`. The full lost transition is exactly
`E V_S*R₁V_SQ_b`. Six public theorems and four definitions pass the final foreground
leaf audit in `CCMFiniteScatteringSoninNormalForm`; umbrella wired.
All ten public declarations passed a separate axiom audit, with the standard three
axioms only. Latest global lint has thirteen unrelated unwired-module errors; both
new leaves have no lint error. Corpus index refreshed, no full build or owned job left.

This solves the finite source-level nonlinear comparison left by C9.11e, not the
cofinal relative ideal or Hardy index. Next is the inverse-free Euler denominator
current in `tg-scattering-euler-denominator-current.md`; it aims to connect the
twisted projection pair to the actual Euler/Burnol four-leg source.

## 2026-10-02 — C9.11g actual Euler denominator and four-leg current

Verified the literal finite denominator A_S, both Mellin symbols, V_S A_S=A_S*,
and inverse-free current congruence A_S*δ_S A_S=J_S. On an unchanged Sonin
carrier, δ_S is a positive boundary Gram and J_S a negative boundary Gram;
equality holds exactly when both boundary maps vanish. Fourteen public theorems
and five definitions pass both leaf audits and all nineteen axiom queries;
standard foundational axioms only, umbrella wired, no raised heartbeat limits.

This advances the actual mixed-source comparison and exposes a necessary carrier
transport. C9.11h now attacks its exact finite Fourier-gap law and whether a
nonzero common carrier core survives all prime stages. Cofinal relative-ideal
admission, degree-three Hardy-index comparison, and the sub-unit law remain open.

## 2026-10-02 — C9.11h exact Euler carrier and nonzero finite survivor

`CCMEulerDenominatorCarrier` passes final leaf and all eight public axiom audits:
seven theorems and one scale definition, standard foundational axioms only.
For any existing positive Fourier gap, R_c A_S f=0 iff R_(P_S*c)f=0. On K_b,
the simultaneous carrier is exactly the additional Fourier gap P_S*b. The
all-finite-stage common core is zero, but every individual finite stage has a
proved nonzero simultaneous-carrier vector. This advances actual cofinal source
admission by exposing a domain obstruction, not an estimate or scalar surrogate.

Next C9.11i strengthens rigidity to eventual admission, without any initial-gap
assumption: set g=A_S₀f, use prime insertion outside S₀ and finite-product
injectivity. Nonzero solutions to every finite collection of stage conditions
must be retained as the positive survivor. Moving carriers and their aperture
transitions remain required for a viable TG cubic relative class.

Validation scope: three new leaves (C9.11g/h), 21 public theorems and six
definitions, all 27 axiom queries passed. Mandatory full formal lint currently
fails only on ten unrelated unwired modules; no new leaf is among its failures.

## 2026-10-02 — C9.11i eventual admission closed

`CCMEulerEventualCarrier` now passes final leaf and all four axiom audits. Actual
prime insertion and finite invertibility remove the original gap/carrier premise:
eventual A_S f∈K_b over every S⊇S₀ holds iff f=0. Every finite collection of
stage conditions still has a nonzero solution. This is a strict strengthening
of the previous all-stage common-core theorem, not its repetition.

Next C9.11j attacks the concrete proposed repair: the closed simultaneous carrier
E_(S,b) may be annihilated by J_S itself, with δ_S annihilating its Euler image.
Its exact current kernel and nonzero complementary boundary should determine
what a provenance-retaining mapping cone must carry. The operator-valued joint
continuation, cubic Hardy-index comparison, and sub-unit law remain open.

## 2026-10-02 — C9.11j moving restriction erases the actual current

Eight theorems, two definitions and two carrier instances in
`CCMEulerMovingCarrierRadical` pass final leaf and all twelve axiom audits.
The current kernel on K_b is exactly the Fourier gap P_S; its actual action is
−A_S*R₁A_S. The canonical simultaneous projection is nonzero, but is annihilated
by J_S, and its Euler image is annihilated by δ_S. Meanwhile J_S Q_b=0 iff P_S≤b.
Thus this particular moving-domain restriction is retired with its exact positive
kernel and activation classification, not with a vacuous zero-carrier argument.

C9.11k now attacks the surviving boundary quotient. Its proposed finite range is
the annulus range(R₁−R_(b/P_S)); the source map and return A_S* must both be
retained. Paper mechanism: Sonin annular surjectivity via a compact Fredholm
compression, followed by nilpotent inversion of compressed forward Euler factors.
Cofinal transition maps must follow actual prime insertion. The joint relative
operator continuation, cubic Hardy-index comparison and sub-unit law remain open.

This turn's validation: two new leaves, twelve public theorems plus four
carrier declarations, sixteen axiom queries all passed; both leaves wired.
Global lint reports twelve unrelated unwired modules, none of these leaves.

## 2026-10-02 — C9.11k actual finite Euler boundary realized

Five new leaves prove the exact range of R_c A_S|K_b for every finite prime set
and b,c>0: the closed even Fourier annulus with edges b/P_S and c. Its exact
kernel is K_b∩ker R_(P_S*c), and the source map induces a Banach quotient
equivalence. At c=1,b≥1, the actual return A_S* reconstructs the full current
as −A_S* B_S f on each source class. The finite source admission question is
therefore advanced by a proved surjectivity and bounded quotient theorem.

The proof uses an actual ambient time-band resolvent, an explicit Sonin section,
nilpotent forward annular dilation and genuine prime insertion. All mixed
Euler terms are retained. All five final leaf audits pass and all are wired.
The full validation record is on P3:tg-euler-boundary-quotient-realization.

All 34 public axiom queries pass with only the standard three logical axioms.
Final global lint reports ten other unwired modules and no error in these five
new leaves. No full build, umbrella build, raised heartbeat, or subagent was used.

C9.11l now tests the source-preserving cofinal transition and its exact kernel
shell. In the active strict case the proposed shell is infinite dimensional,
so an ordinary Fredholm-transition repair may fail; prove the positive kernel
realization and retain the return before drawing that conclusion. Actual
cofinal relative admission, cubic Hardy-index compatibility and the strict
sub-unit law remain open. RH is not proved or falsified by this finite result.

## 2026-10-02 — C9.11l actual transitions and infinite kernel shells

The unique source-preserving Euler boundary transitions are now constructed.
The original source quotient also defines a spectral equivalence Φ_S with
`Φ_S(B_S f)=R_(P_S)f`, and the transition is exactly Fourier restriction:
`Φ_S τ_(S,T)=R_(P_S) Φ_T`. Its complete kernel is boundedly equivalent to the
actual Fourier shell `(max(b,P_S),P_T)`. A nondegenerate shell is infinite
dimensional; from every starting stage there is a later non-Fredholm transition.
The actual return still reconstructs `J_S f=−A_S* τ_(S,T)(B_T f)`.

This closes the Fredholm-transition proposal, with a positive exact carrier
classification rather than a bare no-go. See P3:tg-euler-cofinal-boundary-transitions
and P5:tg-euler-fredholm-transition-system. All four final leaf audits and all
29 public axiom queries pass; all are wired. Global lint still reports ten
unrelated unwired modules, none of these leaves.

C9.11m initially attacked coherent unsquared relative source assembly on the original
common carrier through the exact time-band correction response. Its conjecture
and candidate overlap mechanism are recorded in
P3:tg-unsquared-relative-source-assembly. This is an operator admission problem,
not a squared Gram substitute. Full prime–Gamma continuation, Hardy cubic
compatibility and the strict sub-unit law remain open; RH remains unproved.

C9.11m's first new source reduction is now verified: with the actual resolvent
factor W, `J_a=AB(1-AW)+BAW`. This puts the original projection correction in
the right ideal generated by the two literal time-band blocks and retains
their output regularity. `SoninCorrectionRightFactor` passes its final leaf
audit and both axiom queries and is wired. An exact monomial dilation-overlap
mechanism for coherent prime-square nuclear convergence is recorded on the
C9.11m card; the infinite-source theorem is still open. The latest global lint
run reports thirteen unrelated unwired modules and none of this session's five
finished leaves.

## C9.11m closed: original proper-prime-power family

The complete original proper-prime-power residual family is now unconditionally
summable in the genuine Schatten-one Banach carrier at every positive aperture.
Actual time-band convergence transfers through both exact correction legs;
all deeper modes are jointly absolutely summable. The original product index
is retained. Three new final leaf audits and all eight public axiom queries
pass, with only the standard three axioms; all leaves are wired. See
P3:tg-unsquared-relative-source-assembly.

Completed: P3:tg-principal-source-trace-current. Its exact complete-response trace,
commutator decomposition and linear-prime harmonic obstruction are Lean-audited. The actual
principal-prime/Gamma class, Hardy cubic and strict sub-unit law remain open.


C9.11o: the original linear-prime harmonic law and raw Schatten-one obstruction
are now audited in `SoninLinearPrimeTraceObstruction`. Exact positive survivor:
`p Re Tr S_p → 2(Phi_a(1)+1)>0`. Next hard construction is
P1:tg-principal-polar-operator-cancellation, using the literal polar density
before cofinal operator passage. RH remains unproved.
