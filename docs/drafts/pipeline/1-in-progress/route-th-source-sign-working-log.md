# Route TH: literal source sign research log

- **ID:** route-th-source-sign-working-log
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/rh-current-frontier-map.md, route TH; current Lean corpus
- **Goal:** unconditional Lean proof of `RiemannHypothesis` or its negation.
- **Completion status:** OPEN. No RH proof or counterexample obtained.

## Hard mathematical target

At one fixed positive Gaussian heat time, prove a positive lower fraction of
the native energy in the full real-amplitude channel, uniformly over every
real polynomial. Equivalently, prove positivity of the full Xi heat form.
Alternatively, construct a negative test of that actual form from the
literal source. No unproved sign assumptions may enter a final theorem.

The current corpus already proves more than the frontier-map wording:
`XiGaussianFixedTimePhaseThreshold` makes *any* positive uniform retained
fraction RH-equivalent. `XiGaussianPoleFreeLocalization` retains negative
orbit localization under exact polar cancellation. Neither constructs a
positive fraction or an off-line orbit.

## Plan

1. [done] Read frontier, relevant memories, and actual receiver definitions.
2. [active] Attack the complete signed prime–Gamma balance on the exact
   pole-free Gaussian polynomial class; inspect source-specific mechanisms.
3. [pending] For a genuinely new successful argument, write a dependency-closed
   paper proof, formalize its exact statement, wire its leaf into RHTower,
   audit with foreground `lake --old env lean <module>`, inspect axioms in
   `/tmp`, run formal lint, and remove owned scratch files.
4. [ongoing] Record failures, strongest positive survivors, and next hard
   conjecture. Keep the RH goal active until its stated endpoint is proved.

## Constraints

No subagents, numerical experiments, added axioms, admitted proofs, resource
limit increases, full builds, umbrella builds, commits, or pushes. At most
one owned Lean build at a time. Existing unrelated changes remain outside
scope. Serena symbol access rejects Lean paths as ignored; direct source
reads are the available fallback. No `update_plan` tool is exposed; this
file carries the plan and durable research state.

## 2026-10-01: initial audit

Research command: `scripts/formal_tools.py research "Xi heat all degree
positivity same time phase source capture" --budget-seconds 60 --json`.
Returned partial results, coverage generation 1179333 pending; results are
discovery hints, not compiler-verified evidence. Narrow lexical queries and
actual source reads locate the sharper receivers.

Prior attempts already closed in the corpus:

- Uniform reverse heat retention fails, even on any nonzero principal
  polynomial ideal (`XiGaussianHeatRetentionObstruction`).
- Actual raw theta score floors do not establish the transformed Xi moment
  sign (`PrimeArchThetaPolynomialScoreGap` and derivative-packet boundary).
- The optimized three-halves continuous-norm phase ceiling cannot be paid
  by sampled energy at fixed positive scale
  (`XiGaussianFractionalBudgetObstruction`).

These reads prevented duplicate conjectures but did not advance the hard
sign problem. Improving the cubic degree/time region is set aside: it would
leave fixed-time, all-degree sign open.

### C1: direct arithmetic domination after exact polar cancellation

Investigate whether the actual prime Fourier source is bounded above by
the full Hardy-Gamma integral on every polynomial with `P(-1/4)=0`, at one
positive heat time. The required bound must come from the literal source,
not from an RH-equivalent interface.

Audit hazards: the unrestricted bound is false because polar-normalized
annihilators have vanishing native energy while prime-minus-Gamma tends to
`2*pi*exp(t/4)`. The prime Fourier tests are signed even though the real-axis
Gaussian polynomial density is nonnegative. All polynomial cross terms and
the complete prime sum must remain present.

Current providers read: `XiGaussianCompletedSourceFormula`,
`XiGaussianPolarSourceCancellation`, `XiGaussianPoleFreeLocalization`,
`ThetaCuspPrimeArchSourceEquation` (literal source annihilation alone is
not a sign proof). C1 remains conjectural.

### C2: theta ground transform and a literal jump comparison

Proposed replacing the source-sign question by a weighted jump inequality,
using the positive literal theta source. Corpus search located the exact
construction already formalized in `CCMThetaGroundRHCriterion`:

`Q(u) = E_prime(chi) - E_GammaPolar(chi)`,
`chi = u / Phi`,
`E_GammaPolar = E_polar - E_Gamma`.

Thus the needed statement is `E_polar <= E_prime + E_Gamma` on every
actual smooth core profile, retaining the full source and all mixed terms.
The criterion includes a density argument to the original form domain.
The proposed representation is therefore existing work, not new progress.
Do not create another wrapper or duplicate its formalization.

The literal continuous coefficient is

`b(v) = 2*cosh(v/2) - exp(-v/2)/(1-exp(-2*v))`, `v>0`.

`ThetaGammaPolarKernelOrientation` proves its exact sign threshold and
constructs disjoint nonnegative compact profiles with positive continuous
cross coupling whose support differences avoid all prime-power lags.
Consequently a pointwise sign or direct off-diagonal domination proof cannot
replace the missing full quadratic comparison. This obstruction and its
positive kernel classification are already formalized; no new route is
being retired here.

### Evaluation and next attack

No new mathematical frontier result has been proved in this cycle. No Lean
source was changed, no Lean build was run, and no theorem is claimed verified
by this session. Source reads are not fresh compiler audits.

Abandoned activities: improving degree-dependent heat regions, re-proving
ground-transform identities, and generic positive-kernel comparisons. None
would supply the missing same-time sign. In fact
`PolynomialGaussianCompletedPrimeGammaWedge` already has an independent
`t*(natDegree+1)` small-aperture region, so the cubic route is not the whole
current source frontier.

Continue with the signed nonlocal comparison itself. A concrete mechanism
to assess is transport of the positive long-lag polar/continuous cost to
actual prime-power lags, paying the displacement with the negative short-lag
Gamma part. A valid argument must retain the mixed displacement term and
prove unit total cost on the literal theta weight. Triangle inequalities
with an unspecified coefficient greater than one do not close this gap.
Before pursuing it, inspect the existing `CCMPrimeGammaQuantileCancellation`
and coherent signed-moment modules; the frontier map already records a
sublinear-in-`exp(aperture)` comparison, not the required unit coefficient.

This is an attack direction, not a proved inequality or evidence for either
truth value of RH. The final goal remains active and unsolved.

## 2026-10-01: signed transport and aperture audit

### C3: pay the prime displacement by its coherent norm

Rejected by an existing literal-source theorem, not by an experiment.
`CCMActualHeadCoherentQuantileGammaProducer` gives a lower bound with reserve
`(2 * gammaHardyPhaseRate 0 + 4) * mass - 2 * coherentChiSquare`.
`CCMActualHeadCoherentQuantileGammaNoGo` proves the reserve coefficient is
strictly negative and the proposed budget impossible for every nonzero
actual head. The exact Hardy-Gamma central value is already formalized.
Absolute-value/Cauchy--Schwarz control of the displacement cannot supply
the required sign. The signed mixed term remains necessary.

The broader signed-transport deep search returned partial coverage
generation 1179376, pending. Its results did not supply a unit-cost
comparison. Actual source files, rather than the search ranking, establish
the obstruction above.

### C4: the first nonconstant actual Hankel block

The exact finite target from `PrimeArchThetaCumulantMinor` is

`C = 3*m0*m1*m3 + 15*m1^2*m2 - 10*m0*m2^2 >= 0`,

where `mj = thetaCuspRawEvenMoment j`. This is exactly the first
nonconstant normalized prime--arch Hankel determinant, up to a positive
normalization. Proving it would advance one necessary finite block;
the independent all-degree positivity problem would remain.

The two sufficient ratio gates and the first-atom transfer gates are
already formalized as implications, not established source inequalities.
The Gaussian-aperture composite-balance card identifies the unsplit target
`15*mu0 - 10*mu1 + 3*mu2 >= 0`, `muj = m(j+1)/mj`.
No new equivalence or transfer wrapper should be written.

### C5: exclude negative curvature entering from large degree

The parent aperture card is stale on two decisive points:

- `PrimeArchThetaGaussianApertureColdWatson` already proves eventual
  positive curvature at every fixed degree, using the actual positive
  sixth seam. Its finite-section starting aperture depends on the degree.
- `ThetaColdDegreeCornerLimit` already disproves nonnegative curvature
  at every degree and every negative aperture for the literal full theta
  source. With `L_n=(n+1/2)/9`, its curvature `S_n(-L_n)` is eventually
  strictly negative. More generally `L_n^4*S_n(-L_n)` tends to the third
  derivative of `log(Phi(sqrt(u)))` at the selected positive position `u`.
  `ThetaColdDegreeCornerLogJet` proves this profile negative for `u>=9`.

Thus neither a uniform positive incoming boundary nor a combination of
separate endpoint limits is available. The exact signed incoming-profile
law is already the formalized positive survivor; do not duplicate it.
Relevant completed/failed cards:
`3-formalized/rh-cold-degree-corner-2026-09-26.md` and
`5-failed/rh-global-all-degree-aperture-convexity-root-2026-09-26.md`.
This is not an RH falsification and does not refute degree-zero GABTC.

### C6: positive square forcing against the signed incoming profile

Attempted to use the exact curvature equation

`S_j' = 4*(q_j-q_(j+1))^2 + (j+7/2)*q_(j+2)*S_(j+1) + R_j*S_j`.

At a degree-zero zero crossing, write `q2=c`, `q1=c+d`,
`q0=c+2*d`, and `delta2=q2-q3`. The derivative is

`4*d^2 + (7/2)*c*(d-delta2)`.

Its nonnegativity requires `delta2 <= d + 8*d^2/(7*c)`.
Even granting log-concavity of the adjacent gamma-normalized Turan
defects, the resulting bound is only `delta2 <= d + 2*d^2/c`.
For positive `d`, that allowance is too large. This is an algebraic
audit of a proposed implication, not a verified theta counterexample,
not a new formal theorem, and not an assertion that the extra defect
log-concavity premise has been proved for the source.

Finite Bernstein coefficient positivity through degree thirteen was
also checked. It controls Bernstein basis tests; it does not directly
give positivity of every squared linear polynomial. The source theorem
is `primeArchEndpointBernsteinCoefficient_nonnegative_of_degree_le_thirteen`.
The first-minor search still returned equivalences and conditional
producers, not an unconditional first-minor sign theorem.

### Evaluation and next conjecture

No new hard mathematical inequality was proved in this cycle. No Lean
file was modified and no compiler verification was performed. The
source reads above must not be described as new theorem audits.

The aperture detour added a stronger all-parameter/all-degree burden
that the literal source already falsifies. Set it aside. Next attack
the undamped actual cubic `C` directly, retaining its three terms
together. Investigate whether the already-proved complete-source
reflected fourth/sixth curvature can yield an integrated cubic bound
through symmetrization, with all boundary terms and signs explicit.
Reject this mechanism if it merely restates `C>=0` or needs an
unproved source sign. Do not formalize a wrapper in lieu of closing
that inequality. The RH goal remains active.

## 2026-10-01: actual logarithmic fourth-curvature attack

The reflected fourth/sixth inequalities do not immediately transfer to the
moment cubic. A candidate counterfamily to such a generic transfer is
`exp(-x^2/2-epsilon*x^6)`: the existing sixth-moment card gives a negative
first variation of the moment cubic. Its reflected inequalities appear to
persist for sufficiently small positive epsilon by an elementary uniform
jet bound. This observation is not yet formalized and is not treated as a
new closed no-go.

The direct C5 numerator and its cumulative-flux and Riccati formulations
were inspected. These already exist; no duplicate reformulation was added.
`ThetaCuspC5CompletedGateSigns` needs global curvature facts, while
`ThetaCuspC5RegimeOneCurvatureSigns` proves them for `pi*exp(2*x)>=6`.
In particular, proving `-(log Phi)''''>0` on the omitted compact interval
would discharge a genuine source-specific sign premise. The further
projective and compensation bounds remain separate obligations.

A primary-source lead was retrieved directly from Zenodo:
Hideo Umihara, *A Fourth-Derivative Inequality for the Riemann Xi Kernel
(Letter)*, 12 August 2026, DOI 10.5281/zenodo.21902312.
Its analytic proof uses a three-atom exponential-polynomial head and an
explicit derivative tail, not interval quadrature. No result is imported
as an axiom. Every identity and inequality used here must pass Lean.
The paper normalization is `Phi_paper(x)=thetaCuspFullSource(2*x)/2`.

Concrete proof attempt:

1. Verify the exact leading positive/negative head-ratio bound using the
   displayed polynomial derivative identity and positivity after shifting
   the variable by three.
2. Verify all other head coefficients, bound their exponentially damped
   contribution, and connect the resulting numerator to the fourth
   logarithmic derivative of the literal three-atom sum.
3. Bound all four full-tail derivatives relative to that same head, prove
   the logarithmic perturbation estimate, and conclude actual global sign.
4. Only then transport the sign to the C5 receiver and audit remaining
   premises. This target is not a replacement completion criterion for RH.

Exact-coefficient corpus search for `242830834287616`, `241377489`, and
`21902312` returned no hits. Searches are discovery aids; absence of a hit
does not prove novelty. The paper proof remains untrusted until checked.

### Leading head ratio: checked

`ThetaCuspThreeAtomFourthLeadingRatio.lean` proves the exact shifted
polynomial identity, strict decay of `A3*exp(-3q)/A0` on `q>=3`, and the
uniform bound `<63/100` on `q>=pi`. Cancelling the common factor `q`
reduced the derivative certificate to degree eleven. Positive shifted
coefficients supply the signs; an exact Taylor lower bound supplies
`exp(157/50)>23`. No numerical experiment or interval approximation was
used to infer the sign.

Final leaf audit succeeded with `lake --old env lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaCuspThreeAtomFourthLeadingRatio.olean
GaloisForLFunctions/RHTower/ThetaCuspThreeAtomFourthLeadingRatio.lean`.
Scratch `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`; no added axioms or admissions. Umbrella import added.

This closes one estimate in the candidate three-atom proof. It is not
yet a theorem about the full theta source: the complete numerator
identity, the other head terms, the infinite tail, and the derivative
identification remain to be audited. The next conjecture is the exact
head numerator bound `N3 < -(17/50)*A0` throughout `q>=pi`.

### Complete head numerator: checked

`ThetaCuspThreeAtomFourthNumerator.lean` now proves that conjecture and
the stronger normalized conclusion `N3/G^4 < -17/160`, for every
`q>=pi`. The exact expansion includes all fifteen exponential terms.
All six additional subtracted coefficients are nonnegative after
shifting by three. The seven remaining positive terms have total
majorant `<3/100`; this combines with the leading `<63/100` estimate.
Finally, `G<2*(2q-3)` and `A0>=5*(2q-3)^4` give the normalized margin.

The complete new leaf passed `lake --old env lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaCuspThreeAtomFourthNumerator.olean
GaloisForLFunctions/RHTower/ThetaCuspThreeAtomFourthNumerator.lean`.
Scratch axiom audits for the expansion, numerator bound, and normalized
bound report only `propext`, `Classical.choice`, and `Quot.sound`.
No resource-limit overrides were added. Both leaves are imported by
`RHTower.lean`; no umbrella or full build was run.

`scripts/formal_tools.py index` completed, updating the generated API,
gaps, overview, and search index. `scripts/formal_tools.py lint` failed
on eleven unrelated missing umbrella imports: ten RHTower modules
(`CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`ThetaMovingShellFirstOrderPhase`, `ZetaZeroDensityPowerSaving`) and
`HTGeometry.OrderOneEntireQuotient`. It reported no error in either
new leaf. These unrelated in-progress files were not modified.

### Evaluation and next hard target

This cycle proved the finite-head estimates instead of adding another
equivalence or conditional sign receiver. The actual full-source
fourth logarithmic derivative sign is still unproved here. In
particular, the new `eulerJet` expressions and numerator have been
checked algebraically, but their identification with derivatives of
the literal three-atom theta source is still outstanding.

Use the existing exact differentiation engine in
`ThetaCuspFinitePrimeDerivatives.lean`:
`hasDerivAt_thetaCuspPolynomialAtom`,
`iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom`, and
`thetaCuspLogDerivativePolynomial`. This file's first 205 lines have
been read. Avoid introducing a duplicate general derivative engine.

With the repository coordinate `x`, set `q=pi*exp(2*x)` and
`H(x)=sum_{n=1}^3 thetaCuspSourceTerm x n`. Its proposed factorization
is `H(x)=2*pi*exp(5*x/2-q)*G(q)`, so its fourth logarithmic derivative
should be `16*N3/G^4 < -17/10`. These factorization and derivative
identities still require Lean verification.

The next analytic conjecture is that the remaining source
`T=sum_{n>=4} thetaCuspSourceTerm x n` changes this fourth logarithmic
jet by less than `1`, uniformly for `x>=0`. That weaker error target
already preserves the head's sign; reproducing the letter's much
smaller constant is unnecessary. A concrete mechanism is to bound
Gaussian power tails by twice their first term:

`sum_{n>=4} n^m * exp(-(n^2-1)*q) <= 2*4^m*exp(-15*q)`
for `m<=12`, `q>=pi`. Successive terms are bounded by a geometric
factor using `((n+1)/n)^m <= (5/4)^12` and
`exp(-(2*n+1)*q) <= 1/23^9`. Check corpus for this exact tail bound
before writing new code, then transport it through the existing atom
polynomial jets and the exact fourth-logarithmic-jet formula.

Primary paper and extracted text remain available at
`/tmp/th-fourth-derivative.pdf` and `/tmp/th-fourth-derivative.txt`.
Appendix C starts near text line 2379. No tail constant or global sign
from that paper has been admitted. Even a successful fourth-jet sign
proof leaves the C5 projective/compensation inequalities and the
all-degree TH positivity endpoint open. The RH goal remains active.

## 2026-10-01 continuation: Gaussian tail and actual derivative normalization

Previous turn classified as progress: two finite-head leaves were
kernel checked. The present hard target remains the full-source
fourth-logarithmic-derivative sign, not merely a finite truncation.

The corpus search for the fourth-tail mechanism was partial (generation
1179681, no exact lexical hits). Existing `ThetaCuspDeepTailCalibration`
and `ThetaCuspDeepTailExtendedSupport` control the n>=3 likelihood
sector; their tilt/radius estimates do not directly give the needed
n>=4 source derivative bound.

`ThetaCuspThreeAtomGaussianTail.lean` proves the exact infinite-tail
conjecture through power twelve. The shorter proof uses
`k+4 <= 4*2^k` and `(k+4)^2-1 >= 15+8k`, so polynomial growth costs
at most `4096^k` while Gaussian decay contributes `exp(-8q)^k`.
For `q>=pi`, the resulting ratio is at most one half. It also proves
that the first-three Gaussian weight plus the whole remaining tail
is strictly below two for every power through twelve.

The Gaussian-tail leaf passed `lake --old env lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaCuspThreeAtomGaussianTail.olean
GaloisForLFunctions/RHTower/ThetaCuspThreeAtomGaussianTail.lean` and is
imported by the RH umbrella. The actual atom normalization and tail
derivative bounds are currently being checked in scratch; do not yet
treat those as completed source theorems.

### Actual source derivative tail: checked

`ThetaCuspThreeAtomSourceDerivatives.lean` now proves:

- `derivativePolynomial_factor`: the existing source derivative
  polynomial is `2*pi*X^2*Q_j(pi*X^2)`, at every order.
- `iteratedDeriv_sourceTerm_eq_normalized`: every literal atom
  derivative equals the common positive prefactor times
  `n^2*Q_j(q*n^2)*exp(-(n^2-1)*q)`, for all orders, atoms, and real x.
- `abs_source_derivative_tail_le`: for `j<=4` and `x>=0`, the absolute
  complete n>=4 derivative tail is at most
  `sourcePrefactor(x)*2*S_j*4^(2*j+4)*q^(j+1)*exp(-15*q)`.

Here `q=pi*exp(2*x)` and `S=(5,53,661,9445,151269)`; these deliberately
generous exact coefficient ceilings suffice for the perturbation
budget. The factorization uses the existing differentiation engine,
not a new assumed termwise-derivative formula.

The new source-derivative leaf passed `lake --old env lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaCuspThreeAtomSourceDerivatives.olean
GaloisForLFunctions/RHTower/ThetaCuspThreeAtomSourceDerivatives.lean` and
was wired into the umbrella. A further scratch check now connects the
actual first-three raw derivative jets to the negative numerator.
The full-source fourth-logarithmic sign remains open here until the
nonlinear tail perturbation and logarithmic-derivative identification
are completed.

### Literal three-atom head: checked

`ThetaCuspThreeAtomSourceHead.lean` identifies the actual normalized
head jets and verifies the exact quartic identity

`H0^3*H4 - 4*H0^2*H3*H1 - 3*H0^2*H2^2 + 12*H0*H2*H1^2 - 6*H1^4 = 16*N3`.

`headSourceJet_fourthLogJet_lt` now proves that
`HilbertMetric.logarithmicFourthJet` of the five literal source-head
derivative jets is `< -17/10` for every `x>=0`. The leaf passed
`lake --old env lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaCuspThreeAtomSourceHead.olean
GaloisForLFunctions/RHTower/ThetaCuspThreeAtomSourceHead.lean` and was
wired into the umbrella. This is a raw-jet statement; an explicit
`iteratedDeriv 4 (log source)` identification remains to be connected
when the full-source sign is proved.

### Next conjecture: compare quartic numerators directly

Avoid the originally proposed perturbation of four quotients. Instead
set `E=exp(-15*q)`, and divide the j-th normalized head and full-source
jets by `q^(j+1)`, obtaining `a_j` and `b_j` for j=0..4. The checked
Gaussian-weight bound `<2` should give

`|a_j|, |b_j| <= 2*S_j`,
`|b_j-a_j| <= C_j*E`, where `C_j=2*S_j*4^(2*j+4)`.

Use the same homogeneous quartic polynomial

`P(v)=v0^3*v4-4*v0^2*v3*v1-3*v0^2*v2^2+12*v0*v2*v1^2-6*v1^4`.

The candidate sufficient estimate is
`|P(b)-P(a)| <= 10^16*E`. This estimate has NOT yet been verified.
It can be proved by telescoping each product of four factors and
applying the coordinate bounds; no multivariable calculus is needed.
Candidate derivative ceilings on the constant box are respectively
`10^9`, `10^8`, `3*10^6`, `5*10^4`, and `1000`. Their weighted sum
against `(C0,...,C4)` should be below `10^16`; verify those exact
integer inequalities in Lean rather than treating this note as evidence.

Every monomial in the raw numerator acquires the factor `q^8` under
this normalization. The head margin and `H0>=q` therefore give
`q^4*P(a)<-17/10`. A one-variable decay estimate should establish
`10^16*q^4*exp(-15*q)<1` on `q>=pi`, using monotonicity from `157/50`
and the already checked `exp(157/50)>23`. Consequently
`q^4*P(b)<-7/10`, enough for the desired full-source sign.

Remaining exact joins: normalize and split the full derivative series
(the existing `thetaCuspFullDerivative` and
`iteratedDeriv_thetaCuspFullSource` are available); prove the raw head
and full Gaussian bounds from `headGaussianWeight_add_tail_lt_two`;
then identify the negative quartic with the actual fourth logarithmic
derivative. The corpus lexical search for `logarithmicFourthJet`
returned its definition in `HilbertMetric.ReflectionFourthJet` and
no existing perturbation theorem; exhaustive `rg` found only that
module's usages. This does not rule out equivalent results under
different names. No full-source fourth-sign theorem has been claimed.

### Continuation audit

Scratch `#print axioms` for the Gaussian tail bound, derivative
polynomial factorization, exact source derivative normalization,
literal derivative-tail bound, and literal head fourth-logarithmic
jet bound reports only `propext`, `Classical.choice`, and `Quot.sound`.
All three new leaves passed their required foreground audits without
resource-limit changes. Imports and generated indexes are current.
Global lint again failed on eleven unrelated missing imports; this
time `ThetaHalfLineFiniteOrderGauge` appeared and the earlier
`HTGeometry.OrderOneEntireQuotient` error was absent. No new leaf was
reported. All owned build/search/index/lint processes finished. Scratch
Lean and completed search files were cleaned; the primary paper and
its extracted text remain available for the active proof attempt.

## Complete-source quartic perturbation: checked in scratch

`ThetaCuspThreeAtomFullJets.lean` now gives the exact full derivative
split, Gaussian-weight bounds, constant bounds for the scaled jets,
and `q <= headJet 0 q`, `q <= fullJet 0 q`. Its leaf audit passed.

The telescoping perturbation conjecture succeeded: on `q >= pi`,
`|P(scaledFullJet q)-P(scaledHeadJet q)| <= 10^16*exp(-15*q)` and
`10^16*q^4*exp(-15*q)<1`. Combined with the checked head margin,
`q^4*P(scaledFullJet q)<-7/10`. The resulting theorem
`fullDerivative_fourthNumerator_neg` proves the quartic numerator of
the literal infinite derivative series strictly negative for `x>=0`.
All of these passed a foreground scratch Lean check with default
resources. The permanent perturbation leaf is undergoing final audit.
The actual fourth-logarithmic-derivative identity and global reflection
join are the current next checks; no RH conclusion follows yet.

Corpus search `thetaCuspLogSource fourth reflection --any --mode lexical
--no-refresh` found the prior factor identity, reflected Turan bound,
and exact parity theorem, but no global negative fourth-log source sign
among the returned declarations. The broad query returned 12891 hits;
this is not an exhaustive novelty certificate.

### Literal global fourth-logarithmic sign: scratch proof succeeded

The permanent perturbation leaf passed its required foreground audit.
The subsequent scratch file now proves the exact raw logarithmic
fourth-jet identity and
`iteratedDeriv_four_thetaCuspLogSource_neg_all (x : Real)` with no
mathematical premise: the fourth derivative is strictly negative at
every real x. The positive half-line uses the full-source numerator;
modular reflection covers the negative half-line. The seam x=0 is
included directly, without a limiting strictness argument.
`ThetaCuspLogFourthNegative.lean` is undergoing its permanent audit.

The intended C5 landing is now direct: c''=-L''''>0 everywhere,
c' is strictly increasing and odd, hence c'>0 on x>0; the existing
chord theorem then gives 2*action<=velocity throughout the same-half-line
chamber. These are source inequalities, not conditional RH producers.

The existing C5 card's final 2026-09-05 section explicitly records that
even closing the direct-J gate only supplies the equispaced four-node
stratum, not arbitrary-packet positivity. Remaining actual problems:
projective energy c'c''-c*c''' on the compact source interval, the
compensation growth inequality, and the all-packet/all-degree sign.
Do not present the local gate as a full RH implication.

### Permanent source and C5 audits: passed

`ThetaCuspLogFourthNegative.lean` and
`ThetaCuspC5GlobalCurvatureSigns.lean` both passed their final
`lake --old env lean -o ... <leaf>` audits, sequentially in the foreground.
The latter proves `thetaCuspLogCurvatureJetTwo_pos_all`,
`thetaCuspLogCurvatureJet_strictMono`,
`thetaCuspLogCurvatureJet_pos_of_pos`, and
`two_mul_action_le_velocity_of_sameHalfLine`. All four new leaves are
wired into the RHTower umbrella; no umbrella or full build was run.
The global strict fourth-logarithmic source sign is now a theorem,
not an outstanding conjecture as in the earlier chronological entries.

`formal_tools.py index` completed. Global lint still reports eleven
unrelated missing umbrella imports; the four new leaves are not among
them. Compared with the prior audit, `CCMPrimeDeficitEulerPositiveRigidity`
appeared and `ThetaHalfLineFiniteOrderGauge` disappeared. The other ten
are the previously recorded CCM, Moebius, ThetaMovingShell and
ZetaZeroDensity modules. A scratch axiom audit of the actual conclusions
is running separately.

### Next conjecture and seam strategy

The unresolved compact projective target is
`c'(x)*c''(x)-c(x)*c'''(x) >= 0` for `0<x` and
`pi*exp(2*x)<6`, especially where `c'''(x)>=0`.
It cannot be replaced by the now-closed fourth-source sign.
Deep corpus search (generation 1179982, partial; coverage snapshot
1179987 with compiler metadata mostly pending) returned the existing
projective definitions and cofinal results, with no checked compact
producer. Exact lexical search of the projective energy returned three
hits. These searches do not establish absence of an equivalent theorem.

Useful source-specific seam input already exists:
`thetaCuspGaussianApertureSixthSeamNumerator_pos` in
`PrimeArchThetaModularDifferentialClosure` is the positivity of
`F0^2*F6-15*F0*F2*F4+30*F2^3` at zero. Odd source/logarithmic jets vanish
there. The public Bell identities in `ThetaCuspFullReflectionSixthBellTransfer`
therefore identify this with `F0^3*L6(0)`, so `L6(0)>0` should imply
`c''''(0)<0`. Together with `c'''(0)=0`, this gives a negative-third-jet
neighbourhood and a positive projective neighbourhood. This consequence
has not been formalized here; an unspecified neighbourhood alone will
not close the remaining compact interval. The next real task is a
quantitative compact sign proof retaining modular cancellation at zero,
then joining the existing `q>=6` projective bound. Avoid spending a turn
only repackaging the qualitative seam consequence.

### Final axiom and process audit

Scratch `#print axioms` completed successfully for the exact full-series
split, full quartic numerator sign, global fourth logarithmic derivative
sign, both C5 curvature signs, and the same-half-line velocity floor.
Every output lists only `propext`, `Classical.choice`, and `Quot.sound`.
No owned Lean, search, index, or lint process remains running. The RH
goal remains open; this cycle closed an actual full-source inequality
and its C5 sign consequences, with no RH premise or new axiom.

## Compact projective attack after the global fourth sign

Previous turn classified as progress: four audited leaves closed the full
fourth logarithmic source sign and C5 R2/R3/velocity floor. Current hard
target remains actual compact projective energy, not a new equivalent
receiver. Search with `theta curvature projective compact cancellation
sixth seam --mode deep --module ThetaCusp --budget-seconds 90` returned
partial generation1180026, including existing compact modular source
coordinates and global reflected-sixth positivity. It did not supply the
missing projective sign.

Conjecture under test: the explicit normalized source jets give positive
fifth logarithmic numerator in a compact cone near the modular orbit.
With u=minus modular drift, a=gap amplitude, w=transverse shear, existing
source equations are u'=-3+u^2/3+3a/4, a'=-2aw,
w'=2+a/2+2u^2/9+2uw/3. The known compact interval has 0<=u,w<=1 and
17<=a<=20. An improved relation between w and u may be essential;
independent jet absolute values lose the modular cancellation. Start by
checking the exact polynomial sign, then prove the actual orbit occupies
its sign region. No numerical trajectory is used.

### Compact cone, first checked step

The scratch orbit proof passed: on `0<=x<=1/50`, the actual source has
`0<=u<1/4`, `19<a<96/5`, `u<=w`, and `w<21u/20` for x>0.
This uses the existing `ThetaCuspModularEnergyTube` and a first-contact
comparison, not an assumed trajectory. It is not yet published: the
intended fifth-logarithmic sign on this cone is still under proof.
The first direct positivity tactic did not prove the polynomial sign;
that is not a falsification of the conjecture. A naive fractional
substitution exceeded default recursion depth, so the proof is being
reorganized without raising resource limits. A tighter `41u/40` bound
with `u<23/100` is the current strengthened orbit candidate.

The tighter orbit cone also passed Lean: on `0<=x<=1/50`,
`0<=u<23/100`, `19<a<96/5`, `u<=w`, and `w<41u/40` for x>0.
The polynomial proof now factors the exact common odd coordinate u,
leaving a polynomial in `(u^2,a,w/u)`. This reduces the degree in the
bounded drift variable from fifteen to seven before denominator clearing.
The factorization and cone sign are currently undergoing Lean checking;
no compact projective sign has been claimed yet.

The odd factorization passes Lean after explicit coefficient/exponent types.
The proposed independent cone is too broad: Lean proves the exact corner
`reducedLogFive 0 19 (41/40) < 0`. Thus denominator-clearing optimization
alone cannot establish the intended cone. This does not concern an actual
source point; at zero both drift and shear vanish and their limiting ratio
is constrained by the amplitude. Positive salvage: retain the checked odd
factorization and sharpen the coupled orbit bounds before a new certificate.

A stronger source-specific survivor has now passed Lean in scratch:
for every x>=0,
`(3*a(x)-12)*w(x) <= (2*a(x)+8)*u(x)`.
Its left-minus-right derivative is exactly
`-6*a*w*(w-u)-8*u*w-16*u^2/3`, hence nonpositive from the
already proved `0<=u<=w` and `a>0`. Both sides vanish at zero.
On the compact region a>19 and u>0, this forces `w/u<46/45`,
sharpening the false independent 41/40 cone without trajectory sampling.
The next sign candidate uses this coupled invariant and the existing
u^2<1/16 bound. The global coupling is mathematically new in this attack;
its final publication is held until the source consequence is checked.

User steering: attack the hard source inequalities themselves; tuning isolated
compact constants is not the target. The global coupled-shear invariant is
now published and leaf-audited in `ThetaCuspModularCoupledShear`; scratch
axiom output lists only propext, Classical.choice, Quot.sound. Its compact
corollary is not claimed as a projective-sign proof. The subsequent fifth-log
cone positivity tactic remains unresolved, not falsified.

New structural conjecture based on the corpus's exact curvature and jet
factorizations: `b=c''-4c` is positive and strictly decreasing on x>0.
Then the exact identity `E=c'*b-c*b'`, together with the newly closed c'>0
and existing c>0, would close the full projective sign. This is a stronger
source claim, not an established theorem. For the source split, its derivative
sign is `L5-4L3>0`, a comparison of the rational first-atom defect
`4*BW3-BW5` with `-J5+4*J3`. At the modular seam the two terms agree by
odd-jet vanishing. A source-proved monotonicity of their ratio is a concrete
candidate mechanism for the missing global sign; no ratio sign is assumed.
Searches of the current corpus returned the exact likelihood jet ladder,
cofinal projective theorem, and source ratio monotonicities, without a checked
producer for this defect. Continue attacking the actual source inequality,
not a conditional receiver or a smaller interval.

### Current continuation boundary

The direct positivity attempt for `b=c''-4c`, after substituting the actual
energy-floor coordinates `a=12-4u^2/3+v`, `w=u+h`, does not close by
nonnegative coefficients. Its expansion has mixed coefficients, including
negative high powers of v. This is not a counterexample. The actual orbit
has additional global constraints omitted in that attempt: `u<3`,
`0<v<36/5`, monotone ratio `k>5/4`, `0<=J<=u/3`, and the newly proved
coupled shear defect. Do not declare the structural conjecture false from
a tactic failure or switch targets merely because its proof is difficult.

A useful exact source-split simplification (paper algebra, not yet audited
as a Lean theorem) is, for A=pi*exp(2x), q=A-3/2,
`BW4-4*BW2 = 216*A^2/q^4`,
`4*BW3-BW5 = 864*A^2*(q+3)/q^5`.
The likelihood defect is
`-J5+4*J3 = 32*A^2*(A^3*kappa5-10*A^2*kappa4+24*A*kappa3-12*kappa2)`.
Thus the relevant ratio is
`q^5/(27*(q+3))*(A^3*kappa5-10*A^2*kappa4+24*A*kappa3-12*kappa2)`.
It equals one at the modular seam by odd full-source jets. Proving it
strictly decreases would establish `L5-4L3>0` on the positive ray.
The support-only linear score is not automatically positive; the literal
spectral measure's continuum part and modular coupling must be retained.
No claim of an audited ratio identity or sign has been made.

Final checked leaf: `lake --old env lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/ThetaCuspModularCoupledShear.olean
GaloisForLFunctions/RHTower/ThetaCuspModularCoupledShear.lean` succeeded.
The umbrella import is present. Scratch axiom audit succeeded for the global
coupled source theorem and its compact corollary, standard three axioms only.
Index refresh succeeded. Global lint still reports eleven unrelated missing
umbrella imports, including the new external MobiusDivisorCriticalSourceSimpleJet;
no owned leaf is reported. No full or umbrella build was run.

The RH goal remains active and unsolved. Hard gaps: actual compact projective
sign, completed C5 compensation, and arbitrary-packet/all-degree positivity.
The next task is proving the structural source defect sign or discovering
and proving the exact additional invariant it requires, not tuning local
constants or publishing another conditional receiver.

## Full curvature-defect continuation

Previous cycle is verified progress (global coupled source invariant), not
closure of E. Current hard target is still `L5-4L3>0` on the entire positive
ray, as a sufficient structural producer for E>0. Current corpus searches
(generation1180359, partial) confirm source-positive polynomial chart,
normalized modular barrier defect, and exact spectral likelihood split.
`ThetaCuspModularBarrierCost.normalizedDefect_le_drift` is stronger than
just `0<=J<=u/3`: `(u/3-J)/(t*(k+1/3)) <= u/36` globally. Include this
constraint in any modular sign certificate; earlier polynomial attempts
omitted it.

New concrete proof mechanism under test: keep each literal likelihood
component's Dirac mass AND continuous ray together. For d=n^2-1,
`r_n(A)=(d+1)*((d+1)+(3/2)*d/(A-3/2))*exp(-d*A)`.
The ratio derivative needed for the curvature defect has a polynomial
moment kernel that need not be positive pointwise on t>=3, but integrating
its Dirac-plus-ray component may restore positivity. Exact denominator-
cleared component kernel through moment six is being checked symbolically
in Lean, using q>=3/2 and d>=3. No numerical trajectory or sampling.
If this succeeds, next obligations are transport to the complete ordinary
likelihood response and control of the logarithmic (cumulant) correction;
linearized success alone does not prove the actual source inequality.

The exact point-plus-ray sign is now a checked theorem in
`ThetaCuspCurvatureDefectKernel`; its complete-measure transport is checked
in `ThetaCuspCurvatureDefectMoments.full_coolingFunctional_pos`. Both leaf
final audits passed and imports are wired. This is new global ordinary
spectral positivity, not yet logarithmic positivity or projective closure.

Nonlinear continuation: write S(kappa) by finite cumulant grades as
`S(e)-B2+2*B3-6*B4+24*B5-120*B6`, e_j=M_j/(1+r).
A coupled binary-kernel fusion would bound B2 relative to S(e), preserving
the cancellation lost by separate absolute-value estimates. Odd grades
B3 and B5 appear nonnegative from moment support recurrences and polynomial
coefficient relations. Higher even grades are controlled by existing
moment-product/tail-probability inequalities. Binary fusion and a nonzero
linear reserve are being tested symbolically; neither is claimed proved.
The first expanded binary attempt hit default simplifier depth. Switching
to a factored ring normal form avoided that resource failure, but automatic
positivity did not close. Inspecting the exact residual, rather than raising
resource limits or treating tactic failure as mathematical falsification.

Continuation status (all statements distinguish checked scratch from published audits):
- `ordinaryDefectRatio` has exactly derivative
  `-q^4/(27*(q+3)^2)*coolingFunctional q M`, hence is strictly decreasing
  on q>=3/2. Scratch passed; new Cooling leaf is written/wired, final leaf
  audit still due.
- Complete single-component reserve is checked algebraically:
  `C6(q)*B6(q,d) <= 1000*q*kernel(q,d)` for q>=3/2,d>=3.
  Full-measure transport is in `/tmp/th_defect_reserve_full.lean`;
  only a redundant `dsimp` failed in the first audit and has been fixed;
  recheck still due.
- Exact finite cumulant grading and actual normalized-source grade signs
  passed in `/tmp/th_defect_all.lean`: B3>=0, B5>=0,
  B4<=67*C6*p^3*e6, B6<=C6*p^5*e6. Thus
  `S(kappa) >= S(e)-B2-(402*p^3+120*p^5)*C6*e6`.
  These are unconditional source inequalities on q>=3/2. Published leaf
  still to be assembled from the checked scratch pieces and finally audited.
- Hard remaining producer: B2<=383*p*S(e). Candidate literal point-plus-ray
  binary fusion is `pairKernel <= 384*q*(d*K(d)*B0(e)+e*K(e)*B0(d))`.
  Mathematical falsification has NOT occurred: monolithic normalization and
  positivity exhausted the default recursion/heartbeat limits. No limits
  were raised. Splitting into positive coefficient certificate blocks is
  the current proof-engineering step. The literal pair-moment identities
  in `/tmp/th_defect_bare.lean` are prepared but not yet checked.
- Existing corpus 400*p<1 combines these inequalities and the linear
  reserve to force S(kappa)>0 if binary absorption is proved.
- Search for the seam bridge (partial generation1180714) located exact
  positive-ray L5 source jets and global smoothness/odd-jet vanishing.
  L5 factor identity currently requires x>0; its seam identity can be
  obtained by continuity. No need to assume an unproved seam formula.

Binary kernel breakthrough: `/tmp/th_defect_pair_certificate.lean` passed
Lean (exit0) under default resource limits. Its exact normalized difference
has 616 positive monomials. The proof uses 20 small prefix-positivity lemmas;
all terms were copied from Lean's symbolic ring normal form, not computed
by numerical sampling or an external algebra engine. New PairKernel leaf
contains this checked ordered-gap certificate plus the symmetric extension;
its final leaf audit is still due.

Dependency-closed paper absorption mechanism:
1. Literal atom moments factor into an exponential weight times `bareMoment`.
   Their binomial convolution is exactly `pairMomentNumerator/q^(j+2)`.
2. The checked binary kernel implies pairCooling(m_n,m_k) <=
   384*(S(m_n)*m_k(0)+m_n(0)*S(m_k)).
3. Two HasSum transports give pairCooling(M,M)<=768*r*S(M).
   Exact diagonal polarization is pairCooling(M,M)=2*r*S(M)+2*B2(M).
4. Normalize by P=1+r to get B2(e)<=383*p*S(e).
5. Existing 400*p<1 on the actual x>=0 source, the checked odd/higher-even
   grade estimates, and T=C6*e6<=1000*S(e) imply
   S(kappa)>=(1-383*p-402000*p^3-120000*p^5)*S(e)>0.
Formal pair-moment identities, the double HasSum transport, and the final
absorption application remain to be checked. The actual source coordinate
is essential in step5; no claim that the activity estimate holds for every
abstract q>=3/2 is made. This still does not close projective curvature until
log-ratio/source-jet/seam/asymptotic connectors are checked.

Final audits now passed for `ThetaCuspCurvatureDefectReserve`,
`ThetaCuspCurvatureDefectGrades`, and
`ThetaCuspCurvatureDefectPairKernel.pairCoolingKernel_fusion` (including
both gap orderings). PairKernel and Grades audit logs are empty. Reserve
has one harmless unreachable trailing ring warning; no errors. All leaves
are wired. Current next audit is `/tmp/th_defect_source_pair.lean`, containing
literal convolution identities, atom/full pair bounds, normalized binary
absorption, actual-source S(kappa)>0, and the logarithmic ratio derivative.
No conclusion about these new scratch statements until that audit succeeds.
Cooling final leaf audit and combined scratch axiom audit are still due.

Complete nonlinear sign CHECKED: `/tmp/th_defect_source_pair.lean` now
passes with exit0 and an empty log. This includes literal pair moments,
`full_pairCooling_le`, `gradeTwo_normalized_le`,
`source_cooling_cumulant_pos` for every actual x>=0, and
`hasDerivAt_logarithmicDefectRatio`. No added axiom or unproved sign premise.
New `ThetaCuspCurvatureDefectCumulants` leaf is written and wired; final
leaf audit is currently running. The source bridge in
`/tmp/th_defect_bridge_audit.lean` is prepared but untested. It identifies
L5-4L3 with the positive first-atom factor times (1-sourceDefectRatio),
uses strict decrease of the ratio and modular odd-jet vanishing to recover
its exact seam value1, and aims to conclude L5-4L3>0 on x>0. Projective
curvature still requires that bridge and the decay of b=c''-4c.

Sharper corpus-based projective landing found (avoid duplicating a full b-decay
calculation): `ThetaCuspCompletedCurvatureProjectiveFarTail` already proves
there exists x0>0 with R=c''/c strictly decreasing on [x0,infinity).
Existing scaled log-jet limits give R->16/4=4. Hence R(x)>4 on that tail:
4<=R(x+1)<R(x). Therefore b=c''-4c>0 cofinally. The new H=L5-4L3>0,
once the prepared source bridge checks, gives b'=-H<0 on x>0.
Strict decrease of b propagates its cofinal positivity to every x>=0.
Finally E=c'*b+c*H>0 on x>0, using previously proved c>0 and c'>0.
This uses already formalized tail projective monotonicity and only a ratio
limit from existing source asymptotics. No additional quantitative bound
or unproved asymptotic cancellation is required. This is the next intended
mathematical landing after the source-jet bridge.

GLOBAL PROJECTIVE GAP CLOSED IN CHECKED SCRATCH: the complete bridge audit
now exits0. It verifies source_defect_pos (L5-4L3>0 for x>0),
curvatureDefect_pos (c''-4c>0 for x>=0), projectiveEnergy_pos
(c'c''-cc'''>0 for x>0), and projectiveRatio_strictAntiOn on [0,infinity).
Axiom audits of the source sign and both projective endpoints report only
propext, Classical.choice, Quot.sound. No external sign premise remains.
New Source and ProjectiveGlobal leaves are written/wired; final leaf audits
are next, together with the previously deferred Cooling leaf audit.
The finite C5 compensation gate and arbitrary-packet positivity remain open;
this does not prove RH. Next corpus search targets the exact compensation
receiver now that global projective monotonicity is available.

FINAL LEAF AUDITS PASSED: Source, ProjectiveGlobal (including unconditional
C5 center negativity on 0<t<=u), and the deferred Cooling leaf all exit0
with empty logs. All nine new defect/projective leaves are wired into
RHTower.lean; no umbrella build. Combined axiom audit and index/lint pending.
The route map now records compact projective closure and retains the exact
remaining compensation/arbitrary-packet gaps.

Next hard conjecture under investigation: control displacement growth of
B=-H_center directly through the positive decreasing defect b=c''-4c,
rather than tune frozen-jet interval constants. The exact gate reads
M=(W-5)B-5tB'; strict projective positivity now supplies B>0 everywhere
in 0<t<=u. A bound on tB'/B must retain the source's higher derivative
coupling; positivity of b alone is not yet known to imply it.
Corpus deep searches returned broad/unrelated candidates; exact lexical
search located the compensation and frozen-jet receivers. No claim of a
compensation proof or a universal comparison law is made.

Combined final axiom audit: all 19 checked endpoints report only propext,
Classical.choice, Quot.sound. Index refreshed. Global lint exits1 because
12 unrelated modules are absent from their umbrellas; no finding names any
new defect/projective leaf and no forbidden proof declaration is reported.

New hard source-growth conjecture, derived from the exact C5 seam polynomial:
write H=L5-4L3=F(q)(1-R), F=864*(q+3/2)^2*(q+3)/q^5 and R=sourceDefectRatio.
To control the dangerous second derivative H'', test the coupled inequality
T(kappa)=(q+9)*S(kappa)-(q+3/2)*q*dS(kappa)/dq >=0.
It implies R_x'' >= 2*(-F_x'/F)*R_x', a favorable comparison because R_x'<0
and c'>0. This retains signed seventh-order information rather than separate
absolute jet bounds. The source inequality is NOT proved. A literal
point-and-ray kernel for its ordinary-moment version is now being checked.
The eventual C5 conclusion still requires the exact F coefficients and the
remaining lower-jet reserve to be positive; neither is assumed.

Growth-kernel continuation: corrected coefficient reduction made the exact
seventh-order ordinary point-and-ray polynomial positive by ring_nf and
positivity, under default resources. ThetaCuspCurvatureDefectGrowthKernel
is now saved, wired, and finally audited (exit0, empty log). The complete
ordinary-moment transport is next under audit; no full cumulant T sign.
The new growth card records an essential exact seam cancellation T(kappa)=0
at q(0), deduced on paper from H(0)=H''(0)=0. Therefore the next nonlinear
proof must preserve that cancellation, e.g. by monotonicity of a normalized
nonlinear correction, rather than a strict uniform absorption at the seam.
Existing likelihoodCumulant covers only orders2..6; the growth source needs
a new seven-jet readout. Cleanup removed32 obsolete proof scratch files and
12 superseded diagnostic logs; finished formal modules and final audit logs
are retained. No owned Lean processes overlap.

2026-10-02 CHECKPOINT: all twelve new defect/projective/growth leaves now
pass final lake --old env lean leaf -o audits. Main closure remains global
E=c'c''-cc'''>0 and global C5 center negativity. Three Growth leaves add
complete ordinary seventh-order positivity, exact actual-source jet identity,
and the proved cumulant seam value zero. Scratch axiom audits of all
endpoints (including the two GrowthSource statements) report only propext,
Classical.choice, Quot.sound. No axiom, sorry, resource-limit increase,
computation experiment, full build, or subagent was introduced.
Next hard source target is strict decrease of 1-Tk/To from its exact seam
value1, retaining the eighth cumulant and literal theta weights. To>0 is now
proved, Tk(0)=0 is proved; Tk(x)>0 for x>0, the full C5 compensation growth,
and arbitrary-packet/all-degree positivity remain open. Goal remains active.
The frontier map and direct-gate card reflect compact projective closure.

Final post-growth index refresh completed. Final global lint still exits1
on12 unrelated missing umbrella imports; no finding names the12 new leaves,
and scoped forbidden-proof/resource scans are empty. All owned foreground
Lean and search processes have exited. Completed owned scratch is removed;
proof modules, research cards, search results, and final audit logs retained.

2026-10-02 binary-growth continuation:
Route TH; global C5 compensation and arbitrary-packet/all-degree positivity
remain open. The immediate target is Tk>0 for x>0, where Tk is the checked
seventh-order growth functional with exact modular-center value zero.
Search1181531 and1181879 were partial; no matching global growth producer
was returned. Existing EighthFockSector/Bell absorption mechanisms were read
as source ingredients, not assumed to prove the new target.

The proposed fixed one-unit relative decay reserve is false on q>=3/2:
its exact n=2 self-pair numerator is strictly negative at q=3/2. This now
has a closed Lean theorem. The positive survivor is strict relative cooling
without a fixed rate: the self-pair moment-chain expression
binaryGrowth*growthSlope-binaryGrowthSlope*growthFunctional is positive
for all q>=3/2. Exact polynomial-to-moment transport proves the actual n=2
theta spectral statement and its actual-coordinate specialization for x>=0.
Growth coefficients share factor q+3; that factorization and their exact
HasDerivAt formulas are checked. Separate atomic-moment derivative/ratio
transport is not yet published, so the formal endpoint is stated as the
explicit moment-chain inequality.

New leaves ThetaCuspCurvatureDefectBinaryGrowthKernel and
ThetaCuspCurvatureDefectBinaryGrowthCooling both pass final foreground
lake --old env lean leaf -o audits with empty logs and are wired. Scratch
axiom audits of both kernel endpoints, coefficient derivative, and actual
source self-pair endpoint show only propext/Classical.choice/Quot.sound.
No new axioms, admissions, resource-limit raises, full build, numerical
experiment, or subagent.

Next exact conjecture uses the differential comparison kernel
K(q,t)=a' R(q,t)+t*a*R(q,t)-a*partial_q R(q,t), where a is the literal
second-component growth contribution and R=sum D_j t^j. Test K>0 for
t>=6, retaining the atom-and-ray anchor. This could orient every convolution
sector of order>=2 at once. Full-source growth still needs the gap6 dominant
binary contribution to absorb the gap8 single-tail and gap9 higher-sector
losses. The new pointwise test is running in
/tmp/th_growth_fock_transfer_kernel.lean; no sign is yet claimed.

GrowthTransferKernel final leaf audit now passes with empty log and leaf is
wired. Its stable sign q>=3/2,t>=8 and exact negative value at(3/2,6) both
have only the standard3 axioms. The failed t6 strengthening exposes a
source-specific split: keep the dominant self-pair coupled and use the
stable pointwise sign for the remaining supports. This is not an RH
falsification. No source Tk sign is claimed.

The canonical full convolution pair adds a positive term to the already
proved positive-composition pair. Proposed exact identity:
fullPairGrowthCooling(q,m)=selfGrowthCooling(q,m)+2*m1*T(q,m)^2.
It follows from fullPairGrowth=2*m0*T+binaryGrowth and the chain derivative
fullPairSlope=2*m0*growthSlope-2*m1*T+binaryGrowthSlope. A scratch audit in
/tmp/th_growth_full_pair.lean is repairing only unfold order; no new
mathematical assumption. Its first failed draft printed sorryAx and is NOT
accepted. Await a successful clean axiom audit before publishing.

The next complete-source target is a*Tk'-a'*Tk>0, a the literal n=2
ordinary growth contribution. For the new stable transfer kernel, the hard
signed comparison is the gap6 canonical pair contribution against the
single-component tail atgap8 and higher odd convolution losses starting
atgap9. Full logarithmic/Fock resummation for this operator remains to be
built. Existing Bell/Fock source modules supply moment multiplication and
summable sector bounds; they do not establish the new comparison.

The full-pair identity and actual full-pair cooling positivity now pass
in the updated BinaryGrowthCooling leaf. New BinaryGrowthFlow also passes:
the tilted atom moments differentiate to minus their successor moments;
the literal full-pair growth / dominant atom growth ratio is strictly
decreasing on q>=3/2. Scratch endpoint axioms: standard3 only. Saved,
wired, final `lake --old env lean -o ...` audit exits0 with empty log.

Index refreshed. Lint exits1 for11 unrelated unreachable RHTower modules;
no finding belongs to these TH leaves. No umbrella build was run.

Next conjecture uses an exact degree8 finite convolution expansion of the
cumulant operator, not an assumed infinite Fock identity. Its paper proof
and exact weights are recorded in theta-c5-curvature-defect-growth.md.
The rebase identity and positive weights are being checked in
/tmp/th_growth_finite_log.lean. No complete-source sign is claimed.

FiniteLogConvolution now passes its final leaf audit and is wired.
All actual cumulants2..8 are identified with finite logarithmic jets;
the full-power moments obey the literal momentConvolution recurrence.
The exact complete growth-transfer operator decomposes into eight
alternating sectors with positive weights. Exact remainders prove the
normalized weights are bounded by840/k. The proposed infinite-resummation
gap has been replaced by a checked finite identity. It does not prove the
remaining signed-sector domination. Repeated direct coefficient expansion
hit200000 heartbeats; cached power2..8 coefficient lemmas close the proof
at unchanged defaults. A final sum-body parenthesis error was repaired;
the successful final log is empty.

Current owned Lean scratch /tmp/th_growth_source_transfer_test.lean tests
the exact derivative of sourceGrowth/dominantAtomGrowth, prints axioms for
that endpoint and the finite source decomposition, and tests the next
operator-specific degree8 monomial envelope. The source ratio vanishes at
the modular center. The desired next sign is the negativity of the full
transfer functional, not a positivity assumption added to the ratio.

GrowthTransferEnvelope and GrowthTransferFlow both now pass final leaf
audits with empty logs and are wired. The combined scratch verifies their
core endpoint axioms and the finite source decomposition: standard3 only.
Envelope keeps the exact leading coefficient C(q)=q*D7(q)*N(q); no
coordinate dependence is discarded. Flow gives the actual ratio derivative
and center-zero identity. The complete signed comparison is still open.

Next actual-measure transport is /tmp/th_growth_convolution_transport.lean,
currently under first audit. It verifies the relevant current mathlib
names before proving polynomial integrability, binomial convolution
moments, and additive support bounds. This supplies the source-specific
convolution sectors required by the exact finite identity. The actual
tilted measure is already defined in ThetaCuspLikelihoodSpectralMeasure
(lines450+), with all integrable moments. Its finite mass and support>=3
are in ThetaCuspCassiniMarkovBoundaryTransport (362,402). Corpus deep
search1184834 was partial with mostly pending/stale compiler metadata;
direct mathlib source provides integral_conv, integral_map, integral_prod_mul,
integrable_finsetSum and ae_prod_iff_ae_ae. No external conjectural input.

The dominant-pair polynomial for the coming absorption test is P2(q)=
anchorCoolingNumerator(q,3,3)+2*polynomialMoment(q,3,1)*N(q)^2.
Its K integral before the literal atom scale square is P2(q)/q^9.
That exact K-pair transport still needs the finite binomial successor
identity; no mass-times-eighth-moment absorption is claimed yet.

Current transport audit: first draft needed two API elaboration fixes,
not mathematical changes. Product-a.e. theorem lives in MeasureTheory.Measure;
integral_prod_mul needs explicit functions and measures in this rewrite.
Both are fixed in /tmp/th_growth_convolution_transport.lean and its second
audit is running. Its saved-source endpoint prints already reconfirm the
finite decomposition, source ratio derivative, kernel envelope and leading
coefficient use only standard3 axioms. The new generic moment-convolution
theorem is not accepted until this retry succeeds.

Prepared continuation /tmp/th_growth_convolution_source.txt (NOT YET RUN)
defines the actual k-fold tilted convolution measure, proves finite mass,
all moments integrable, identifies moments<=8 with spectralPowerMoment,
and proves support>=3k. Append it after the generic lemmas pass, then add
the finite-polynomial kernel integral identity and the actual k>=3 sector
sign/envelope. The growth card records the exact remaining signed inequality.
Latest lint reports12 unrelated missing umbrella imports; none ours.

The actual convolution transport and its all-k moment envelope now have
clean endpoint axiom audits (standard3). The literal dominant K-single is
zero and its full K-self-pair positive; these too are checked. New leaf
ThetaCuspCurvatureDefectGrowthConvolution is saved and wired, with final
foreground `lake --old env lean -o ...` audit running. No umbrella build.
The factor16 pair-reserve trial failed only because positivity was not
receiving a zero-comparison goal after norm_num rewrote sub_pos. Move the
sub_pos conversion after normalization and retry; this is not a falsification.
Prepared /tmp/th_growth_signed_absorption.lean transports the exact finite
source decomposition to raw moments with positive normalized weights<=1/k,
and drops favorable even sectors. It targets the explicit complete-source
upper bound; the final pair-vs-single-and-odd domination remains open.

GrowthConvolution final leaf audit exits0 with empty log. Wired and frontier
record updated. All main scratch endpoints use standard3 only. Index refresh
started. Current sole owned Lean audit is /tmp/th_growth_signed_absorption.lean:
normalized raw-sector decomposition, finite odd-sector upper bound, and
factor16 pair polynomial reserve (sub_pos tactic ordering repaired).

The normalized sourceTransfer_signed_upper now has a clean standard3 axiom
audit. The same scratch also closes deepTransfer_bounds, exact single-sector
cancellation, and sourceTransfer_pair_dominant_le (all standard3). These are
saved and wired as GrowthSignedSectors and GrowthStableComponents. Final
SignedSectors leaf audit is running; StableComponents must be audited next.

The factor16 uniform pair reserve fails at q=3/2: Lean's symbolic residual
has strictly negative constant term and negative coefficients through degree4.
This only rejects the enlarged-domain reserve, not the actual source sign.
A literal rational endpoint proof is prepared in /tmp/th_growth_absorption_residual.lean.
Its positive survivor is the exact dominant pair contribution and full-source
residual inequality; the route remains active. Do not repeatedly tune this
constant. New attack retains P2(q) and uses support-gap relative cooling.

Prepared (not yet audited): /tmp/th_growth_absorption_residual.lean defines
the exact remaining residual, proves the complete transfer <= minus that
residual, transports dominantPairTransfer to scale^2*P2/q^9, and tests the
literal factor16 failure. /tmp/th_growth_loss_cooling.lean proves actual
moment-product derivative/rate inequalities and deep-moment support8.
Corpus gap-comparison search1185125 was partial/pending; direct source
identities, not an absent-search claim, motivate the derivative conjecture.
Index refresh passed; lint lists10 unrelated unreachable modules, none ours.

GrowthSignedSectors and GrowthStableComponents final leaf audits both exit0,
empty logs. Frontier updated. Current only Lean audit is
/tmp/th_growth_absorption_residual.lean, now also including the actual
loss-cooling draft. No final sign claimed. Exact modular seam closure through
order8 exists in PrimeArchThetaModularDifferentialClosure and the reflected
Hankel seam modules; it is a possible source-specific center certificate,
but its Hankel determinant sign has not been identified with our residual.

Residual draft's first audit verified the literal factor16 failure at q=3/2,
deepMoment_gap, and sourceMomentProduct_cooling (standard3). Remaining
errors were match reduction, one rational simplification, a redundant ring,
and Pi.pow_apply in the derivative bridge; repaired in canonical
/tmp/th_growth_absorption_residual.lean. This combined scratch now also
contains the new pair-gap derivative-sign trial, built by actual deriv
rules and polynomial normalization at unchanged resource limits. Sole
owned Lean process is the combined scratch; inspect its audit log before
accepting any new endpoint. Separate loss_cooling and pair_gap_derivative
files are preparation copies and may lag canonical repairs.
Latest signed-sector index passed; lint14 unrelated unreachable modules,
none belonging to these TH leaves. No umbrella build.

The full residual receiver sourceTransfer_le_neg_residual and exact
pair formula dominantPairTransfer_eq now pass standard3 audits, as does
the literal factor16 failure. The sourceMomentProduct derivative bridge is
fixed and all three loss-cooling endpoints pass. Saved/wired new leaves
GrowthAbsorptionResidual and GrowthLossCooling; final AbsorptionResidual
leaf audit running, LossCooling must run next.

The new pair-gap derivative trial did not settle its mathematical sign:
norm_num expansion beneath deriv exceeded default200000 heartbeats. Do not
raise limits. Prepared /tmp/th_growth_pair_polynomial_form.lean to expose
checked shifted polynomial identities for P2 and Q in two small standalone
proofs; use their exact coefficients to cache derivative blocks before
retrying the sign certificate. The full literal pair and loss supports
remain the mathematical target.

Continuation: previous goal turn made progress (five new source-operator
leaves, exact residual/cooling scratch endpoints, and a formal reserve
counterexample). Interrupted final AbsorptionResidual session65585 is gone;
pgrep finds no matching Lean and its olean is absent, so the required final
leaf audit was restarted, sole owned session34632. No live job duplicated.
Current source files and scratch polynomial-form preparation re-read.
Fresh corpus residual-frontier search is running; loss final audit and
pair polynomial-form audit follow sequentially.

Restarted GrowthAbsorptionResidual final leaf audit exits0, empty log.
Negative reserve and exact residual/formula survivor now recorded in
5-failed/theta-growth-uniform-pair-reserve-sixteen.md and frontier map.
GrowthLossCooling final leaf audit is now the sole owned Lean job,
session16679. Fresh residual-frontier search1185273 was partial/pending;
actual endpoint source statements were inspected directly. Next audit is
/tmp/th_growth_pair_polynomial_form.lean, then cached polynomial derivative
sign. No complete-source sign or RH result claimed.

GrowthLossCooling final leaf audit exits0, empty log; both new leaves are
wired and frontier entries updated. Index passed; latest lint12 unrelated
unreachable modules, none ours. Current only Lean job: shifted polynomial
form scratch /tmp/th_growth_pair_polynomial_form.lean (session24455).
It also prints axioms from
the saved residual and loss modules. No pair-relative-decay sign accepted yet.

Shifted polynomial-form diagnostic passed. Saved residual/formula,
reserve-failure, and loss derivative/cooling endpoints print standard3
axioms from their compiled imports. Lean supplied two explicit degree32
shifted forms, each33 positive coefficients. No sign inference accepted
from coefficient output alone. /tmp/th_growth_pair_gap_cached.lean copies
those literals (text extraction only) and audits both source identities,
a generic finite-polynomial derivative lemma, the exact boundary test,
and the full rate8 Wronskian sign. Sole owned Lean session7290; log
/tmp/th-growth-pair-gap-cached-audit.log. No resource limits changed.

### Pair comparison closed; center-residual obstruction test

Saved and wired `ThetaCuspCurvatureDefectGrowthPairRelativeCooling`.
Required final leaf audit exits0, empty log at
`/tmp/th-growth-pair-relative-cooling-final.log`. The source ratio
`dominantPairTransfer/C` satisfies `R'+8R>0` on q>=3/2, hence exp(8q)R
strictly increases. Scratch axiom endpoints were standard3; a saved-import
recheck is included in the next residual-monotonicity audit.

The next exact theorem combines this pair comparison with support-gap
cooling and decreasing partition: exp(8q)*transferAbsorptionResidual/C
strictly increases. Current scratch `/tmp/th_growth_residual_monotonicity.lean`.
This alone does not give the center sign. The source-based obstruction test
retains only the literal second atom in the cubic loss at q=5/3. If even
that loss exceeds the pair reserve, monotonicity transports a strict
negative residual to the actual center q0=pi-3/2<5/3. This would falsify
only the coarse eighth-moment absorption strategy, not sourceGrowth, C5,
or RH. The test uses exact rational polynomial identities and analytic
exponential inequalities, no numerical evaluation. It is not accepted
until Lean checks both the algebraic sign and actual source transport.
Fresh searches1185507/1185585 were partial with pending/stale compiler
metadata; actual source formulas inspected. Modular eighth center jets
remain another exact diagnostic for the genuine growth sign.

### Actual-center coarse-residual no-go (2026-10-02)

All three new leaves are saved, wired, and final-audited with exit0 and
empty logs: GrowthPairRelativeCooling, GrowthResidualMonotonicity,
GrowthResidualCenterObstruction. The last proves
`transferAbsorptionResidual (thetaCuspLikelihoodCoordinate 0)<0`.
The pair inequality and weighted residual monotonicity are positive
survivors; see 5-failed/theta-growth-coarse-eighth-absorption.md for the
exact obstruction and dependency-closed paper proof. This falsifies only
the coarse eighth-moment sufficient comparison, not sourceGrowth or RH.

Next attack restores the literal cubic kernel cancellation: three copies
of the point-and-ray measure have an exact finite gamma-mixture moment
numerator. Test the degree-eight pair comparison on that numerator, then
transport it to the actual source and bound only mixed deep-tail errors.
Scratch /tmp/th_growth_exact_cubic.lean; no new sign accepted before audit.
Corpus1185664 complete search supplied current convolution/source formulas;
compiler metadata still requires individual Lean audits.

### Exact dominant cubic repaired (2026-10-02)

`ThetaCuspCurvatureDefectGrowthDominantCubic` saved/wired; required final
leaf audit exit0, empty `/tmp/th-growth-dominant-cubic-final.log`.
`dominantCubic_transfer_le_pair` proves actual J3<=2^8*a0*J2 for q>=3/2.
`dominantCubic_weighted_lt_quarter_pair` proves w3*J3<J2/4 at every actual
source x>=0 using 399*M0<1. Exact finite gamma-mixture moments through8,
source rational transfer, and positive shifted-polynomial reserve all
have standard3 scratch axiom audits. The saved center obstruction was
also re-audited through its compiled import: standard3.

The first combined cubic sign attempt hit default200000 heartbeat at
ring_nf. Splitting out the already established pair polynomial identity
fixed it without increasing limits. Two redundant rings and one unfolded
convolution identity were the only remaining source-transport repairs.
No mathematical failure of the exact cubic comparison occurred.

Next exact decomposition: full k-fold tilted source equals its dominant
power plus a positive mixed remainder E_k, recursively
E_(k+1)=(A+D)*E_k+D*A^k. Its support is at least 3k+5. Hence
0<=Jk(full)-Jk(dom)<=C*(M8(full^k)-M8(dom^k)). For k=3 the support gap is14;
only this mixed difference will receive a monomial bound. Current scratch
/tmp/th_growth_mixed_convolution.lean. This is unverified until exit0.
Deep single-tail absorption and sectors5,7 still open; sourceGrowth,C5,RH
not proved. Index passed; latest lint has10 unrelated unreachable modules,
none ours, recorded /tmp/th-growth-pair-residual-lint-final.log.

### Exact mixed-tail isolation and repaired residual (2026-10-02)

`ThetaCuspCurvatureDefectGrowthCubicTailIsolation` saved/wired; final leaf
`lake --old env lean -o ... <leaf.lean>` audit exit0, empty log
`/tmp/th-growth-cubic-tail-isolation-final.log`.
For every k>=1, full k-fold transfer minus dominant k-fold transfer lies
between zero and C times the difference of their eighth moments. The
positive remainder measure has support>=3k+5. The repaired residual is

`R3=[1/(2P^2)-(256/3)a0]*J2-C*[D8+E3_8/3+(5^7M0^4+7^7M0^6)M8]`.

The complete source transfer is <=-R3; the bracket is strictly positive
on every actual x>=0. Its full sign remains OPEN. Generic/source mixed
transfer and repaired-residual scratch axioms are standard3; saved-import
axiom audit (including the newly added bracket positivity theorem) is
included in the next scratch run. Source assembly needed normalization
of inverse products in the pair denominator, not a mathematical repair.

Next conjecture attacks the remaining mixed cubic loss directly:
`E3_8 <=384*[D8*M0^2+256*D0*M0*M8]`. Every term keeps a deep factor and
cools at least at rate14. Paper mechanism: E3<=three copies of
D*(full*full) as positive measures; integrate the even-power two-summand
inequality twice. No numerical evaluation or all-moment sign premise.
Scratch /tmp/th_growth_mixed_eighth_budget.lean is auditing this exact
inequality, together with saved-import axioms. Center and complete R3
positivity, genuine sourceGrowth sign, C5 compensation and RH remain open.

### Mixed eighth budget proved; next stable-kernel conjecture

Scratch generic and actual-source endpoints now pass with standard3:
`mixedPowerMoment_three_eight_budget` proves
E3_8<=384*(D8*M0^2+256*D0*M0*M8). Saved as
ThetaCuspCurvatureDefectGrowthMixedEighthBudget, wired in RHTower.
Final leaf audit is running, sole owned Lean session83782, log
/tmp/th-growth-mixed-eighth-budget-final.log. No source sign is accepted
from the budget alone. Earlier CubicTailIsolation saved-import residual
and positive pair coefficient axioms are standard3.

Next corpus-grounded conjecture: K(q,t)<=C(q)*t^7*(t-3) on q>=3/2,t>=8.
It retains the literal dominant spectral edge3 instead of replacing the
kernel by its leading monomial. Existing exact dominant transfer=0 and
pointwise kernel polynomial motivate this structural cancellation. If
proved, the deep loss becomes D8-3D7, retaining rate8 through the support
identity t^7*(t-3)*(t-8)>=0. This is not yet proved. Scratch
/tmp/th_growth_root_three_envelope.lean prepared but NOT run. Corpus
search1186003 partial, source formulas verified; no numerical fitting.
The repaired complete residual's center and global signs remain hard
open problems, followed by C5 compensation and arbitrary-packet positivity.

GrowthMixedEighthBudget final leaf audit exits0, empty log. All six new
leaves are now saved/wired/final-audited. Root-three envelope scratch is
now the sole owned Lean audit, /tmp/th-growth-root-three-envelope-audit.log;
it also rechecks the mixed eighth-budget axiom endpoint from its saved import.
No root-three sign accepted before its result. Mixed budget and positive
pair coefficient do not by themselves establish complete residual positivity.

### Root-three stable envelope closed; direct modular-center sign attack

GrowthRootThreeEnvelope final leaf audit exits0, empty log
/tmp/th-growth-root-three-envelope-final.log. K(q,t)<=C(q)t^7(t-3) for
q>=3/2,t>=8; literal deep transfer <=C(D8-3D7), this loss is nonnegative,
and exp(8q)(D8-3D7) is antitone. Its support proof uses the nonnegative
integrand t^7(t-3)(t-8)exp(-qt). Integral elaboration repairs only; no
heartbeat changes. Saved-import axiom audit included in next scratch.

New center conjecture uses exact even mass jets through10 from
PolynomialODEJetOddRankThreeClosure and source F=(H''-H/4)/2.
With f_j=F^(j)/H, b=3f2^2-f0*f4, c=-f0^2*f6+15f0*f2*f4-30f2^3,
d=-f0^3*f8+28f0^2*f2*f6+35f0^2*f4^2-420f0*f2^2*f4+630f2^4,
test signs of 4b*f0^2-c*f0 and d-4c*f0 in physical modular chamber.
Together with beta>0 these would give growth-source center derivative
sign directly, independent of the sufficient residual. Scratch
/tmp/th_growth_center_modular_sign.lean tests exact symbolic polynomial
signs; actual source-jet transport has NOT yet been formalized. No
numerical evaluation. Corpus1186241 retrieval complete with compiler
pending/stale; actual source formulas read. Full transfer sign, C5, RH open.

### Exact modular center sign polynomial closed

GrowthCenterModularPolynomial saved/wired/final leaf audit0, empty log
/tmp/th-growth-center-modular-polynomial-final.log. Standard3 for
centerGrowth_modular_pos and factorCurvature_ge_twoHundred.
The positive certificate is d-(4+beta)c*f0+4beta*b*f0^2 for every
X>=191/10,beta>=200; separately 4b*f0^2-c*f0>0. The factorCurvature
of q in[3/2,5/3] is >=200, which includes the actual center. Initial
attempt to demand positive d-4c*f0 alone was not proved; the correct
coupled polynomial absorbs its negative coefficients through the
sixth-jet gap. This is source-specific modular cancellation, no sampled
or numerical sign evidence. Actual source identification is now being
audited in /tmp/th_growth_center_modular_jets.lean: exact scalar ODE
jets through10, chart-to-seam transport, Bell identity, and a proposed
unconditional sourceCenter_growthLogValue_pos. None accepted until audit.

Exact source center sign now scratch-verified, standard3:
sourceCenter_growthLogValue_pos gives
-L8(0)+(4+beta)L6(0)-4beta L4(0)>0 for actual beta=factorCurvature(q0).
The single long recurrence exceeded default200000; splitting its ten
steps into separately checked theorems resolved this with no limits raised.
GrowthCenterJetElimination saved/wired/final audit0, empty log.
GrowthCenterModularJets saved/wired, final leaf audit running. Source
modular-to-actual and Bell transports passed together in scratch.
Next /tmp/th_growth_center_source_transfer.lean differentiates the exact
source identity on the right at0 to obtain growthSlope(q0)>0,
complete transfer Kcum(q0)<0 and sourceGrowth(q(x))>0 near0. Not yet run.
The remaining hard frontier is extending genuine source positivity over
all x>0, then C5 compensation/all-degree positivity; RH remains open.

### Genuine center transfer and local growth proved in scratch

sourceCenter_growthSlope_pos, sourceCenter_growthTransfer_neg,
sourceGrowth_coordinate_eventually_pos now audit0 with standard3.
SourceGrowth(q(x))>0 in some right neighborhood of0; complete Kcum(q0)<0.
One-sided differentiation used the already unconditional source identity,
odd-jet center vanishing and UniqueDiffWithinAt(Ici0), so no center sign
was imported as a premise. SourceGrowthCenterSourceTransfer saved/wired;
final leaf audit running, /tmp/th-growth-center-source-transfer-final.log.
The earlier actual-center failure belongs only to the coarse residual.
This new genuine source-center theorem rules out a local source-growth
obstruction. It does not prove global source positivity, C5 or RH.

Next hard conjecture: on the actual source orbit, any zero of sourceGrowth
above q0 has positive growthSlope. Together with the new local positivity
this would exclude a first downward crossing. This is weaker than demanding
complete transfer negativity at every point, while retaining the exact
finite cumulant chain. It is an open source-specific boundary inequality,
not a premise to be accepted. Search1186541 partial; source declarations
verified, no corpus absence claim. Alternative exact route still open:
compare stable tilted transfer kernels directly against literal dominant
pair via their Wronskian, then retain all signed log sectors.

Precise alternative global comparison conjecture (UNPROVED): let P(q)
be dominantPairPolynomial and K(q,t)=growthTransferKernel. Since
J2(q)=a(q)^2 P(q)/q^9 and a'/a=-3, the literal stable kernel ratio
exp(-qt)K(q,t)/J2(q) has nonpositive derivative exactly when

W(q,t)=((q*(t-6)-9)*K-q*partial_q K)*P+q*K*P' >= 0.

Target domain is actual q>=pi-3/2,t>=8. A failure only on enlarged
q>=3/2 does not refute the physical comparison. This retains exact
stable transfer rather than replacing its center value by an upper
moment envelope. To attack next: build the missing second growth-
coefficient jet/transfer-kernel derivative, certify or refute W with
symbolic Lean algebra, then confront normalized signed-sector weights.
No assertion that this inequality or subsequent sector assembly holds.

Latest formal index passed, /tmp/th-growth-center-index-final.log.
Lint before final source-transfer leaf reports12 unrelated unreachable
modules (none ours), /tmp/th-growth-center-lint-final.log. A final lint
including source-transfer is running. Owned saved modules contain no
sorry/admit/axiom/opaque/unsafe/native_decide or raised resource options.
Completed modular-sign/polynomial/jets scratch copies removed; current
only proof scratch is /tmp/th_growth_center_source_transfer.lean.

GrowthCenterSourceTransfer final leaf lake --old env lean -o audit0,
empty /tmp/th-growth-center-source-transfer-final.log. All new center
modules now final-audited, saved/wired. The actual source center slope,
negative complete center transfer and positive sourceGrowth on a right
neighborhood are proved, standard3 axioms checked in scratch. Global
source positivity and downstream C5/RH remain open. The goal stays active.
Final lint exit1:11 unrelated unreachable modules, no owned TH new leaf
violations (/tmp/th-growth-center-source-transfer-lint-final.log).
All owned Lean/search/index/lint handles terminal; completed proof scratch
removed. Logs/search snapshots retained. No commits or umbrella builds.

### Stable-kernel/pair differential comparison attack

Previous turn classified PROGRESS: exact actual-center slope/transfer
and local genuine sourceGrowth positivity are saved/final-audited.
New corpus1186599 partial confirmed the available kernel/pair polynomial
and finite-sector source arguments; source formulas inspected. Current
hard target remains global propagation, not a new assumed sign condition.

Built symbolic second growth-coefficient jet, polynomial-moment jets,
growth/slope numerator derivatives and full transfer-kernel derivative
in /tmp/th_growth_transfer_kernel_derivative.lean. First audit found
finite-sum scope parentheses and a redundant dsimp; coefficient calculus
itself passed. Fixed and reauditing. This is the missing exact derivative
needed for W=((q(t-6)-9)K-qKq)P+qKP'. No sign of W claimed yet.

Transfer-kernel differential chain scratch now audit0/standard3.
Saved/wired GrowthTransferKernelDerivative; final leaf audit running.
PairRelativeCooling exposes its already checked shifted P coefficients
and has a new exact P' formula awaiting its targeted final audit.

Refined literal-component conjecture: A(q,d)=S(q,3)N(q,d)-N(q,3)S(q,d).
A/q^8 is the exact transfer of a bare point-and-ray atom with gap d.
Hence its literal tilted ratio to J2 decreases iff
U(q,d)=((q(d-6)-1)A-q A')P+q A P' >=0.
This keeps the whole theta atom together rather than demanding a stronger
pointwise inequality at its spectral edge. First test d=8 (literal n=3)
on enlarged q>=3/2 is prepared in /tmp/th_growth_atom_pair_wronskian.lean.
No conclusion from an unaudited or enlarged-domain failure. Exact all-
component and signed-sector assembly still required for global growth.

GrowthTransferKernelDerivative final leaf audit0, empty log. Exact kernel
q derivative is now saved/wired. The additional repairs were function-
product application reductions before ring; no mathematical assumption
or resource-limit change. PairRelativeCooling targeted final audit now
checks exposed P coefficients and exact P' transport. The prepared
literal-atom scratch also proves transfer=A/q^8 and ratio derivative
=-exp(-(d-6)q)*U/P^2, so any sign outcome has exact source meaning.

PairRelativeCooling final leaf audit0, empty log. The literal atom
transfer and atom/pair ratio derivative identities check with standard3.
The first d=8 Wronskian sign attempt exhausted the default200k heartbeat
limit during one oversized ring normalization; this is no mathematical
counterexample. Split the exact atom polynomial from the final Wronskian
certificate. A normal-form extraction scratch is running; no resource
limit increase and no numerical sampling.

Exact shifted third-atom numerator A(q,8) now normalized symbolically
in Lean: 32 positive coefficients in y=q-3/2. Its polynomial identity
and derivative-by-uniqueness transport passed in the next scratch.
The remaining Wronskian audit again hit default200k, this time while
repeatedly unfolding finite coefficient sums before ring. Cached each
polynomial/value-jet expansion in a separate lemma, following the
already checked dominant-pair proof. The full sign remains unverified.
Corpus search1186806 partial: applicable exact source-transfer chain
verified; unrelated general cumulant hits not used.

Cached Wronskian sign tactic closes for all y>=0, d=8; only redundant
post-norm_num tactics in two cache lemmas failed. Removed them and
transported toward the literal n=3 atom. First transport audit exposed
broad norm_num changing a scalar equality into a disjunction and a
function-application rewrite; replaced by explicit gap/exponent rewrites
and dsimp. Final corrected scratch is pending. No negative sign or
mathematical obstruction was found.

Next generalization, grounded in the literal polynomialMoment formula:
expand A(q,8+v)=sum(k=0..9) A_k(q)*v^k. Conjecture each
exp(-2q)*q*A_k(q)/P(q) is nonnegative and antitone for q>=3/2;
k=0 is the current Wronskian result. k=9 reduces to the already
proved relative cooling of the leading coefficient versus the pair,
since A_9=q^8*C. This would give every d>=8 atom/pair ratio decreasing
by the positive factor exp(-v*q) and finite positive sum. Intermediate
coefficient signs/relative derivatives must be proved, not assumed.
This reduces a large bivariate Wronskian to ten exact coefficient
identities and differential inequalities, retaining every deep atom.
Even success leaves the exact signed cumulant-sector assembly open.

Literal n=3 transport scratch now audit0, standard3 axioms only.
Saved/wired GrowthAtomPairCooling: thirdAtomTransfer_relative_strictAntiOn
is the exact physical point-and-ray atom divided by dominantPairTransfer,
strictly decreasing throughout q>=3/2. Redundant final ring removed;
final leaf audit is running. General all-gap coefficient expansion and
intermediate coefficient normal forms are prepared in
/tmp/th_growth_atom_gap_coefficients.lean, not run until the final leaf
import is available. Latest lint exit1 reports10 unrelated unreachable
modules, none this route's new leaves; log /tmp/th-growth-atom-pair-lint.log.

### Exact third-atom relative cooling (2026-10-02)

GrowthAtomPairCooling saved/wired; final leaf lake --old env lean -o
audit0, empty /tmp/th-growth-atom-pair-cooling-final.log. The exact
literal n=3 transfer divided by dominantPairTransfer is strictly
decreasing on q>=3/2, standard3 dependencies. This preserves the whole
point-and-ray atom. GrowthTransferKernelDerivative and the P' extension
to GrowthPairRelativeCooling also final-audited. Index0; lint1 with10
unrelated unreachable modules, no new TH leaf violations.

Continuing all-gap attack: A(q,8+v)=sum A_k(q)v^k, k=0..9. The exact
coefficient expansion and intermediate polynomial normal forms are
being checked in /tmp/th_growth_atom_gap_coefficients.lean. The stronger
coefficientwise ratio cooling is still a conjecture. Full signed-sector
assembly, global sourceGrowth, C5 and RH remain open.

All-gap finite expansion now checks with standard3 dependencies in
scratch. Eight middle A_k shifted normal forms have 32 positive rational
coefficients each (symbolic Lean normalization, no sampled evaluations).
Exact strings retained in /tmp/th-atom-gap-coefficient-rows.json. The
k=9 zero-target probe simplified to a zero-product disjunction before
normalizing; replaced its target by an arbitrary symbol to preserve the
whole polynomial. This is proof-shape repair, no failed sign conjecture.

Prepared /tmp/th_build_atom_gap_certificate.py, a text-only generator
that copies the Lean-emitted coefficient strings into checked identities
and ten separate Wronskian lemmas; it requires row9 before running.
Prepared /tmp/th_atom_gap_transport.txt with the finite derivative
transport, positive-sum Wronskian identity, and proposed all-n>=3 literal
atom/pair monotonicity. Both still need Lean audit; no all-atom result
claimed yet. Only current Lean job is the corrected row9 normal-form
probe. Prior missing-file attempt terminated without checking a proof.

All ten coefficient certificate scratch generated, but first audit
stopped at a missing imported ThetaCuspCurvatureDefectKernel.olean, before
checking mathematics. Restored only that required leaf with foreground
lake --old env lean -o: exit0, empty
/tmp/th-growth-required-kernel-restore.log. Resumed the same all-coefficient
audit; no route pivot or full/umbrella build.

Corpus lexical HasSum+deepMoment had no hits; broader hasSum_atomMoment
found the exact theorem in GrowthReserve's actual path
ThetaCuspCurvatureDefectReserve.lean. Source inspected. Prepared countable
transport in the existing all-gap snippet: dominant atom transfer zero,
finite linear HasSum transfer, strict sum comparison with witness n=3.
This would turn all-atom relative cooling into exact complete deep-tail
relative cooling once the component certificates/transport pass.

### Next complete-source propagation conjecture (paper algebra, unproved sign)

Let T(q)=growthTransferFunctional q (likelihoodCumulantEight q),
J2=dominantPairTransfer. Differentiate H=T/J2. With K the current
pointwise transfer kernel, the next linear kernel is
B(q,t)=(t-6+P'/P-9/q)*K(q,t)-partial_q K(q,t).
Then H'=-B_q(kappa_through_9)/J2. This is the same exact tilted
atom Wronskian currently being certified: B(atom d)=scale_d*U/(q^9 P).
The literal single dominant atom and literal dominant self-pair are
both annihilated by B (their original T values are identically0 andJ2).
Thus the first surviving positive log sectors are deep single atoms
(gap>=8) and pure dominant cubic (gap9); adverse mixed pairs start at11
and pure quartics at12. Target a coupled B-kernel reserve that absorbs
negative even sectors with the actual proved small source activity,
retaining deep single and pure cubic contributions separately.

If the complete B cumulant sign is proved positive, H strictly decreases
from its already verified negative actual-center value, giving global
T<0 and then global sourceGrowth>0. No complete B sign, cubic B reserve,
pointwise B positivity, or signed-sector absorption is assumed/proved.
This is a source-specific new conjecture based on the corpus's exact
transfer-flow and finite logarithmic sector identities. It explains
why all-atom relative cooling is a direct prerequisite for propagation.

BREAKTHROUGH: all ten coefficient Wronskians and coefficient values
strictly positive on y>=0, audited in mathlib-only scratch with standard3.
Saved/wired GrowthAtomGapPolynomial; final leaf audit running,
/tmp/th-growth-atom-gap-polynomial-final.log. The stronger coefficientwise
comparison conjecture succeeded, with no spectral-gap or coordinate
shrinkage, sampling, added premises, or raised resource limits.
Prepared thin source bridge /tmp/th_growth_atom_gap_cooling.lean includes
exact source coefficient identities, U=sum W_k v^k+qPvA, all n>=3 atom
comparison, and exact HasSum complete deep-tail comparison. Audit after
polynomial leaf finishes. Source/all-tail conclusions not yet accepted.

GrowthAtomGapPolynomial final leaf audit0, empty log. All ten exact
coefficient Wronskians are saved/wired. Source bridge audit now running
against restored available dependencies: /tmp/th-growth-atom-gap-cooling-audit.log.
No all-atom/deep-tail theorem claimed before its terminal result.

Further paper-derived normalization identity, NOT yet Lean-audited:
for p=M0/(1+M0), w_k=finiteLogWeight(p,k)*(1-p)^k/840,
(1-p)*finiteLogWeight'(p,k)-k*finiteLogWeight(p,k)
  =-840*choose(8,k)*p^(8-k), 1<=k<=8.
Hence w_k'(q)=choose(8,k)*M0^(8-k)*M1/(1+M0)^9.
The complete alternating weight-derivative contribution is exactly
-8!*C(q)*(normalizedMoment(q,1))^9: binomially it is minus mean times
the transfer of the eighth power of the centered moment series. That
power has zero moments below8 and eighth moment8!*mean^8. Thus weight
derivatives supply a favorable ninth-power term, rather than eight
independent errors. Verify this exact identity from the finiteLogWeight
table and PowerSeries coefficient API before relying on it.

For polynomial rather than rational source comparison, use
Psi(q,t)=((q*(t-6)-9)*K-q*Kq)*P+q*K*P'. This equals q*P*B.
Psi(atom d)=scale_d*U(q,d)/q^8, so the current all-atom U proof
directly supplies positive deep Psi transfer. Dominant single and
self-pair Psi transfers vanish. Desired next hard theorem is complete
Psi cumulant positivity, retaining pure cubic + deep single and
absorbing adverse even sectors. Full T/J2 derivative is
-a(q)^2/(q^10*J2(q)^2) times complete Psi. No Psi source sign or
pure cubic Psi reserve is yet claimed. Search1187225 partial gave no
applicable ninth-cumulant producer; exact raw moment derivatives for all
j exist in ReflectedLikelihoodCumulantObstruction. Can differentiate
the existing finite eight-sector identity directly and exploit the
normalization cancellation, without first expanding a giant ninth Bell
polynomial. This is an algebraic choice, not an effort-based pivot.

### All deep atoms and complete infinite tail closed (2026-10-02)

PROGRESS: GrowthAtomGapPolynomial and GrowthAtomGapCooling saved/wired;
both final leaf lake --old env lean -o audits exit0, empty logs. Exact
U(q,d)>0 for every q>=3/2,d>=8 yields atomTransfer_relative_strictAntiOn
for all literal n>=3. hasSum_atomTransfer_deep and strict sum comparison
give deepTransfer_relative_strictAntiOn for the complete infinite deep
tail, retaining exact transfers. Scratch endpoints standard3 only.
No source-global sign, C5, arbitrary-packet result or RH proof claimed.

Final index0 /tmp/th-growth-atom-gap-index-final.log. Lint1 reports12
unrelated unreachable modules, none these new leaves; details in
/tmp/th-growth-atom-gap-lint-final.log. No active proof holes, new axioms,
unsafe/native_decide, or raised resource options in owned modules.
All owned Lean/search/index/lint handles terminal. Completed coefficient
probes, text generator, coefficient JSON and source transport scratches
removed; audit logs/corpus snapshots retained. No commits or umbrella
builds. Goal remains active.

Next hard producer: positivity of complete polynomial Psi transfer after
normalizing original complete transfer by its dominant self-pair.
Dominant single and self-pair cancel; deep single and pure dominant cubic
are the prospective reserve against adverse even sectors. Exact finite
weight differentiation appears to contribute the favorable term
8!*C*mean^9. These new source-sign/cancellation statements still require
Lean proofs and signed-sector absorption; see working-log paper algebra
and memory rh/route-th-pair-normalized-transfer-frontier-2026-10-02.

### Next transfer normalization attack (2026-10-02)

Previous turn PROGRESS: all-gap/complete-tail relative cooling is saved
and final-audited. Current hard target remains complete next-transfer
Psi positivity and adverse even-sector absorption. Tested finite weight
derivative and centered eighth-power laws in
/tmp/th_growth_weight_derivative.lean. Centered eighth transfer identity
checks with standard3: only highest moment survives, giving40320*C*m1^8.
First derivative attempt hit numeric-projection parser syntax and
universe metavariables in API-check lines, no mathematical contradiction.
Fixed explicit Nat.choose and real type instantiations. Appended exact
binomial sector cancellation and actual-source strict negative weight
derivative sum; these are now being audited, not yet accepted.
Corpus1187330 partial; PowerSeries Basic shift/X coefficient API verified
from installed source. No absence claim and no outside literature used.

Normalization cancellation PROVED: clean scratch exit0, all three endpoints
standard3. Exact finite weight derivative plus eighth centered-power
vanishing gives normalizationWeightTransfer=-40320*C*mean^9<0 on q>=3/2.
Saved/wired GrowthWeightDerivative; final leaf audit next. This is direct
progress on the next transfer: normalization derivatives are favorable,
not eight independent errors. Complete Psi signed-sector absorption still
open. Corpus search1187330 successor partial/source-only results expose
existing convolution bounds, not an applicable next-transfer sign.
New conjecture: dominant cubic transfer divided by literal dominant pair
strictly decreases. For cubic numerator Q and pair numerator P, exact
Wronskian is ((3q+1)Q-qQ')P+qQP'. Need prove its positivity on q>=3/2,
then absorb mixed pair and higher even sectors against cubic/deep reserves.

Next kernel coefficient conjecture SUCCEEDED: all ten exact shifted
coefficients strictly positive for y>=0 (q=3/2+y,t=9+v). Clean scratch0
and standard3, /tmp/th-growth-next-kernel-polynomial-audit.log. The direct
unsplit test hit default200k simp limit; splitting into checked finite
coefficient caches closed every sign without raising limits. Saved/wired
GrowthNextKernelPolynomial; final audit next. Source coefficient and
derivative-uniqueness bridge /tmp/th_growth_next_kernel.lean prepared.
Until that bridge passes, no positivity of the original Psi claimed.
This prospective kernel law would cover cubic and all higher positive
convolution sectors; mixed-pair/higher-even absorption remains open.

Psi source bridge clean scratch0, standard3: pairRelativeTransferKernel_pos
proves actual Psi(q,t)>0 for every q>=3/2,t>=9. Nine exact source
coefficient identities, derivative uniqueness, and ten positive next
coefficients connect the certificate to original K,Kq,P,P'. Saved/wired
GrowthNextKernel; final leaf audit next. This closes the stable pointwise
next-kernel sign on every cubic/higher support. Mixed pair and higher
even-sector absorption remains the hard gap. Prepared source ninth-moment
convolution/derivative bridge /tmp/th_growth_next_convolution.lean; not
checked yet. No source-global sign or RH conclusion.

Next hard mixed-pair conjecture (paper algebra, NOT proved): let B(q,d,e)
be q^9 times the original transfer of convolution(bareMoment(q,d),
bareMoment(q,e)); B(q,3,3)=P(q). The next bare-pair transfer equals
V(q,d,e)/q^8, where V=((d+e-6)B-Bq)P+B P'. Thus the dominant self-pair
vanishes exactly. For d=3,e>=8, seek the coupled source inequality
q*V(q,3,e) <= 256*polynomialMoment(q,3,0)*U(q,e).
It states next mixed transfer <=256*dominant bare mass*next deep transfer;
actual 399*M0<1 would leave a strict deep reserve after the full pair
multiplicity and finite weight. This preserves the entire point-and-ray
components, unlike the failed coarse eighth-moment residual.
Use e=8+v coefficient rows: if B=sum B_k v^k, then
V_k=(5B_k-B'_k)P+B_k P'+(k>0 ? B_(k-1)*P :0).
U_k are the already-audited deep Wronskians plus qP*A_(k-1).
Test all eleven coefficient inequalities; no constant or sign is assumed.
Pure quartic versus cubic, and higher mixed even grades, remain separate
absorption obligations. This is a source-sign attack, not a bound-tuning
project or a new conditional RH theorem.

Exact mixed-pair simplification for that attack: convolution of the bare
3-component with bare d-component has support3+d and consists of
4(d+1) delta, ((21/2)d+9/2) exponential ray, and (27/4)d times the
shape-two gamma ray. Its jth moment numerator at denominator q^(j+2) is
4(d+1)(d+3)^j q^(j+2)
 + ((21/2)d+9/2)q sum_i choose(j,i)(d+3)^(j-i)i! q^(j-i)
 + (27/4)d sum_i choose(j,i)(d+3)^(j-i)(i+1)! q^(j-i).
For d=8+v, use (d+1)=(d+3)-2 to extract binomial coefficients at11;
ray linear=(21/2)(d+3)-27; gamma linear=(27/4)(d+3)-81/4.
This replaces nested convolution expansions with one exact finite row.
Still paper algebra pending Lean; do not assume resulting mixed-pair sign.

Actual source next-sector bridge PROVED, scratch0 standard3:
sourceConvolution_pairRelativeTransfer_nonneg for every k>=3, q>=3/2;
exact hasDerivAt_rawTransferSector from source moment chain through9.
Saved/wired GrowthNextConvolution; final leaf audit next. Exact full
pair-relative source derivative including favorable normalization correction
prepared /tmp/th_growth_next_source_flow.lean; not audited yet.

GrowthNextConvolution final0, empty log. Full-source pair-relative flow
scratch now running. Additional absorption structure to test (not assumed):
Psi <= (q*P*C)*t^9 on t>=9. Its shifted coefficient differences are
pairRelativeShiftCoeff(9,y)*choose(9,k)*9^(9-k)-pairRelativeShiftCoeff(k,y),
k0..8; all source/certificate identities already available, so this is
an exact nine-coefficient sign conjecture. This would bound higher even
mixed grades after retaining exact dominant mixed-pair and pure quartic
comparisons. Need strict actual-source absorption, not isolated optimized
constants or a conditional endpoint. The favorable mean^9 term and
positive odd sectors may be retained as additional reserve.

Stronger higher-mixed-grade idea (unproved, corpus/source-derived): the
normalized bare d atom is delta_d mixed with d+Exp(q), with ray probability
beta(d)=(3d/(2q))/(d+1+3d/(2q)), increasing in d. Thus the normalized deep
mixture should stochastically dominate the dominant atom and full source.
Combined with deep-moment Chebyshev, this should give D_i*M_j <= M0*D_(i+j),
removing the separate D0*M_j loss in old mixed budgets. Induction then gives
moment_j(D * M^(k-1)) <= k^j * M0^(k-1)*D_j; marking one deep factor bounds
full mixed remainder by k^(j+1)*M0^(k-1)*D_j. With finite sector weight<=1/k,
the extra k cancels. This is a structural replacement for the old coarse
mixed budget, not numerical calibration. Check the literal normalized
moment comparison and deep Chebyshev in Lean before using either. Corpus
search /tmp/th-deep-moment-dominance-corpus.json pending; direct source
HighCumulantCalibration has the positive-measure Chebyshev proof (private
helper) and full-source product bound, while all bare moments are explicit.

Paper proof of all-order bare normalized moment ordering, pending Lean:
write b_d=bareMoment(q,d,0)=d+1+3d/(2q), q>0. Separate i=0 in the
explicit bare moment sum:
M_j(d)=b_d*d^j+(3/2)d sum_(i=1..j) choose(j,i)*d^(j-i)*i!/q^(i+1).
For 0<=a<=d, b_a*d-b_d*a=d-a>=0. Therefore
b_a*d*d^r-b_d*a*a^r = b_a*d*(d^r-a^r)+(d-a)*a^r>=0.
Consequently b_a*M_j(d)-b_d*M_j(a) is the sum of
b_a*b_d*(d^j-a^j) and positive multiples of these expressions. This proves
normalized moment ordering for every j without distribution coupling or
finite-degree case splits. Pair with atom/deep positive-measure Chebyshev
and exact countable summation to obtain D_i*M_j<=M0*D_(i+j). This is a
concrete dependency-closed paper argument for the missing source moment
ordering, not a numerical conjecture. Lean/source sum transport still open.
Corpus1187837 partial found deep moments/support and existing calibrations,
no applicable ordering theorem in returned hits; no absence claim.

Exact complete source pair-relative flow PROVED, scratch0 standard3:
(T/J2)'=-pairRelativeSourceTransfer/(q*P*J2), with next source expression
=sum eight alternating weights*rawPairRelativeSector +40320*q*P*C*mean^9.
All derivatives come from actual source moments, no producer premise.
Saved/wired GrowthNextSourceFlow; final leaf audit next. The sign of this
explicit expression is the exact remaining propagation target. Its mixed
pairs and even4,6,8 losses still require absorption. Do not equate this
identity or separate positive sector signs with full source positivity.

Concrete full-sign assembly plan, all polynomial reserves still conjectural:
use Cnext=q*P*C, exact mixed dominant/deep bound256*a0*PsiDeep,
PsiDeep>=Cnext*D9/64, PsiPure3>=Cnext*a0^2*a9,
PsiPure4<=256*a0*PsiPure3, and Psi<=Cnext*t^9 on stable support.
All-order deep/source moment ordering yields mixed even k budget
Cnext*k^(10)*M0^(k-1)*D9, weight<=1/k leaves k^9. Pure even6,8 then
use ordinary k^9 moment budget and the cubic reserve. Split pair into
zero pure2, twice dominant/deep, and deep/deep; deep/deep ninth budget
2^9*D0*D9 is sufficient. Corpus exact calibration already gives
D0(19/20)<=1/1000000, hence D0(q)<=1/1000000 for q>=3/2 by cooling.
Together with actual399*M0<1, the rational reserve budgets have room:
deep losses bounded by256/399 +16384/1000000
 +64*(4^9/399^3+6^9/399^5+8^9/399^7), versus w1>=399/400;
cubic losses bounded by64/399+6^8/399^3+8^8/399^5,
versus w3>=(399/400)^3/3. These are symbolic rational sign obligations
for Lean, not numerical experiments or proved source conclusions. They
show which exact source inequalities suffice without tuning constants.
Need prove all the stated polynomial/component reserves; none assumed.

All-order deep/source moment ordering PROVED, clean scratch0 standard3:
bareMoment_normalized_order, deepMoment_source_normalized_order, and
crucially deepMoment_mul_source_le: D_i*M_j<=M0*D_(i+j) for every i,j,
q>0. Exact countable atom sum, deep mass positivity and positive-measure
Chebyshev close the source transport; no finite-degree sampling or
calibration premise. Saved/wired GrowthDeepMomentOrdering; reduced import
to GrowthStableComponents, final leaf audit next. This removes the
separate D0*M_j error from the planned higher mixed-sector budget.

Final checkpoint: all six new leaves pass final direct lake --old env lean
-o audits; all endpoints standard3. Index0 refreshed generated formal
indexes. Final lint1 reports13 unrelated unreachable modules, none owned
(/tmp/th-growth-next-transfer-lint-final.log). All owned handles terminal;
no live Lean/search jobs. Completed scratches/generators removed, pending
mixed-pair probe retained and marked unrun. This turn PROGRESS: exact next
source flow and stable kernel signs, plus all-order D_i*M_j<=M0*D_(i+j).
Hard signed absorption/global growth/C5/all-degree gaps remain; RH goal
active and unachieved. Next exact proof plan stored in working log and
Serena rh/route-th-pair-relative-absorption-plan-2026-10-02.

### Exact mixed-pair absorption attack (next goal turn,2026-10-02)

Previous goal turn PROGRESS: six new leaves, source flow/kernel signs and
all-order deep moment ordering final-audited. Current-state source rechecked.
Running prepared mixed-pair probe: exact point/ray/gamma moment identities
j0..8 plus ten gap coefficient normal forms, default proof limits. This
starts the direct qV<=256*polynomialMoment(q,3,0)*U comparison, not a
conditional source result. Corpus search /tmp/th-next-mixed-pair-corpus.json
running. Global E sign, source growth, C5 and all-degree remain open.

Mixed probe16136 terminal1: exact mixed moment identities j0..8 all passed;
six gap rows normalized, rows1..4 hit default200k at norm_num expansion.
No mathematical sign failure. Prepared cached probe using the already
source-checked dominant numerator/slope polynomials to avoid expanding
those inside every mixed moment sum. Running /tmp/th_growth_next_mixed_pair_probe_cached.lean,
log /tmp/th-growth-next-mixed-pair-probe-cached.log, handle30960. Corpus
search91700 terminal0 generation1188087 partial; retrieved existing cubic
and old mixed bounds plus new next-functional API, no applicable solved
mixed-pair comparison in returned hits. No absence claim.

Mixed-pair polynomial certificate PROVED: audit71683 terminal0, all eleven
coefficient reserves strictly positive, standard3 axioms only. Cached probe
30960 terminal1 only because row9 had no remaining slope term to unfold;
corrected ninth-only probe96821 terminal0, exact coefficient text matches.
Saved/wired GrowthMixedPairPolynomial. Source identification and transport
remain pending; this certificate alone is not complete source positivity.

GrowthMixedPairPolynomial final leaf audit99901 terminal0 (empty log).
Corpus flow search71622 terminal0, gen1188237, partial=false, source-only
candidates include actual atom derivative and convolution chain. Source
coefficients/moment bridge and derivative numerator assembled in
/tmp/th_growth_mixed_pair_kernel.lean; first audit started. Prepared
/tmp/th_growth_mixed_pair_absorption.body derives Fbare=U/q8 and
Fmixed=V/q8 by differentiating exact T moments; not yet audited.
