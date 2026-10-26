# PM: actual signed damping covariance below half damping

- **ID:** pm-signed-damping-covariance
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, PM; corpus searches listed below.
- **Statement:** The actual Bézout-corrected relative damping loss has a horizon-uniform signed integral bound from cofinally small positive damping to one half.
- **Status:** OPEN. Reorientation and failed-inference analysis; no new mathematical bound or Lean theorem claimed.

## Goal and exact hard problem

Continue route PM/FZZ-P through actual Möbius energy admission. Write

`Aε(n) = pmPowerDampedCenteredDivisorPrefix ε n`,
`Dε(n) = dampedChebyshevError ε n`,
`Eε(T) = Σ_(1≤n≤T) Aε(n)^2/(n(n+1))`,
`Rε(T) = Σ_(1≤n≤T) (Aε(n)-1)^2/(n(n+1))`,
`Vε(T) = Σ_(1≤n≤T) (Aε(n)-1)Dε(n)/(n(n+1))`.

Prove, from the actual arithmetic source, with no admission premise:

`∀ δ>0, ∃ a, 0<a<min(δ,1/2) ∧ ∃ L, ∀ T,`
`  ∫_(a..1/2) -2Vε(T)/(1+Rε(T)) dε ≤ L`.

The upper endpoint is already admitted. The exact RH equivalence is
`ArithmeticCompensationTheory.riemannHypothesis_iff_cofinal_bezoutCorrected_loss`
in `ConstructingAnArithmeticCorrector.lean`. This equivalence is a receiver,
not a proof of the displayed arithmetic bound. Constants may depend on a;
no bound uniform as a tends to zero is required.

## What the new corpus already settles

1. Admission threshold equals zeta zero width. Half-damping admission,
   compact operator tails and right operator-norm continuity are established;
   none extends admission to a fixed damping below half.
2. `bezoutCorrectedEnergy = 1+R`, comparable within factor three to `1+E`.
   Its derivative is `2V`. Integrated relative loss is the exact endpoint
   logarithmic ratio. Comparable correctors alter that ratio by bounded
   endpoint terms; their existence with the required budget is itself
   equivalent to admission (`TheAdaptedEnergyIsExactlyAdmission.lean`).
3. Scalar work `W-V` is paid on each compact positive damping interval.
   Pointwise or positive-part loss bounds can demand more than admission.
   The signed integral is the calibrated target.
4. `TheNormalizedReceiverBlowUpProfile.lean` classifies the alternative:
   at fixed `0<ε<1/2`, unbounded energy yields unit-energy profiles escaping
   every fixed window and concentrating beyond growing sub-horizons.
   Exact inversion retains the full forcing defect and all cofactor terms.
   Pointwise homogeneous convergence is not global energy convergence.
5. Two-scale scalar compensation and relative transverse-energy summability
   are established. Absolute source energy and connection terms remain.
   The compensated Bézout interior equals the source energy plus a bounded
   remainder with coefficient one; strict contraction is still unproved.

These source statements were read, not freshly compiled in this batch.
No claim of a new dependency audit is made.

## Concrete proof input and attack

`DampingWorkAsArithmeticMarkovBoundaryFlux.lean` gives the actual finite
downward generator G, with departure rate `log n`, and, for `vε(n)=Aε(n)/n`,

`∂ε Eε(T) = B_T(vε) - J_T(vε) - 2m(ε) F_T(vε)`,
`F_T(v) = Σ_(1≤n≤T) n/(n+1) v(n)`,
`m(ε) = dampedReadout ε`, `J_T(v)≥0`.

Here B is the counting-measure boundary flux. The pronic measure is not
invariant. `TheDampingChainInReceiverCoordinatesAndHTransform.lean` already
integrates this full identity and proves
`mem_receiverDampings_iff_integral_markovWork_bound`; this integration is
finished work, not the next theorem to duplicate.

The arithmetic attack is the signed finite residue Gram expression for the
same v, retaining the constant boundary defect. For modulus cutoff D≥T,

`vε(n) = Σ_(1≤d≤D) μ(d)d^(-ε)(floor(n/d)/n - 1/d) + δε(D)`

for positive n≤T, where `δε(D)=Σ_(d≤D) μ(d)d^(-1-ε)-density(ε)`.
Both linear and quadratic defect terms are compulsory after squaring or
differentiating. Existing exact declarations include
`normalizedCenteredPrefix_eq_residuePartialPrefix_add_boundaryDefect` and
`orbit_partial_energy_eq_residueGram_add_boundaryDefect`.

Next proof attempt must bound the complete signed damping-integrated Gram
expression using μ(d)μ(e), including mixed entries and defect terms. Taking
absolute values termwise restores the half-damping obstruction. Merely
integrating `(de)^(-ε)` returns the already-known endpoint energy identity;
the missing step is an independent arithmetic inequality on the combined sum.

## Conjecture / proof-attempt log

### 2026-10-24: reorientation

- Stronger trial conjecture: `Vε(T)≥0` throughout `0<ε≤1/2`, all T. This
  would imply the desired bound, but no proof or counterexample was found.
  Actual first-cell positivity near zero and escaping positive residual work
  do not establish its all-horizon sign. Keep it unproved, not falsified.
- Failed proof step: infer backward energy control from nonnegative Markov
  jump energy. In the exact derivative, J enters with a minus sign; backward
  continuation needs a lower bound on total work. Boundary flux and density
  forcing remain. Dropping either does not give the required estimate.
- Failed proof step: infer exclusion of normalized escape from half-damping
  compactness. Compactness can send weakly escaping unit profiles to zero;
  no bounded inverse is supplied. The full inversion-defect pairing must be
  controlled on moving horizons, not only at fixed cells.
- These are failed inferences, not retired routes or new no-go theorems.
  Their surviving exact identities and classifications are already in Lean.
  No additional wrapper or generic countermodel is being formalized as a
  substitute for the actual signed covariance estimate.

## Search provenance and contribution assessment

Used `scripts/formal_tools.py research` directly, ten corpus-only searches:
route-PM frontier; normalized escape; half-damping chain; two-damping tangent
sign; semigroup interpolation; corrected signed loss; Markov flux; two-scale
compensation; residual-work monotonicity; generator/adjoint boundary flux.
All completed with `partial=false`, no reported errors/index warnings and
no generated proof-idea or ingredient groups. Candidate and source statements
were inspected; decisive statements were checked in source. No mathlib search
was needed. No web search or novelty check followed the user's prohibition.

Prior leading prime-current compensation is genuine but controls only a
relative leading term. Newer scalar compensation already goes further; the
absolute signed remainder is still unpaid. This reorientation advances target
selection, not the hard mathematical frontier. The next useful success must
be an actual-source signed covariance bound or an arithmetic exclusion of
the normalized escape alternative. More endpoint identities, scalar rate
improvements and conditional RH wrappers would not discharge this gap.

No Lean changes, builds or numerical experiments in this reorientation batch.
RH and its negation remain unproved here; the overall goal remains active.

## 2026-10-24: signed Gram and complete dilation attempts

The replacement goal supplied in
`/Users/michael/.codex/attachments/4c5bbddf-7584-4f53-911d-93a2febe1afc/pasted-text-1.txt`
was read. Success now explicitly means an unconditional Lean proof of RH.
The PM section of the frontier map and relevant entries in
`docs/reports/rh-killed-routes.md` were checked. New criteria, no-gos and
numerical improvements are not the requested deliverable.

**Previous-turn classification:** progress in selecting the attack from newer
corpus evidence, but no progress on the required arithmetic estimate.

### Signed Gram attempt

The existing residue diagonal estimate is `G_T(d,d)≤2/d`. Thus, for fixed
positive ε, the diagonal with weights `μ(d)^2 d^(-2ε)` is bounded independently
of both cutoffs. The hard sum is genuinely the complete mixed Gram expression
and its boundary correction, not the diagonal or coefficient square sum.

Attempted proof by prime pairing does not close: each opposite-sign pair has
a favorable mixed term because the residue Gram entries are nonnegative,
but the norm of the sum of such pairs includes all interactions between
different pairs. No estimate on that complete interaction was proved.
The existing Bessel estimate replaces this structure by `Σ d^(-2ε)` and
therefore supplies no below-half admission. A local-pair inequality cannot
be silently promoted to an inequality for the complete actual source.

No actual-source counterexample was established. No new no-go was pursued.

### Dilation forcing attempt

Read the exact normalized self-improvement and cofactor-energy sandwich in
`TheNormalizedReceiverBlowUpProfile.lean`, including the remaining inversion
defect. The known pointwise bound `ρ(n)/√E_T≤n/√E_T` does not control its
pairing over the energy-carrying moving horizon. The individual deep-cofactor
vanishing theorem does not justify interchanging a growing cofactor sum with
the limit; its norm weights meet `Σ j^(-ε-1/2)`.

A continuous-source completion was examined on paper. Let
`Cε(x)=Σ_(k≤x) cε(k)`, `mε=1/ζ(1+ε)`, and
`Fε(t)=Cε(1/t)-mε/t` for t>0. The proposed complete identity is

`Σ_(j≥1) j^(-ε) Fε(jt) = floor(1/t)-1/t`.

Its algebraic mechanism is finite raw-prefix convolution
`(μ(d)d^(-ε)) * (j^(-ε)) = δ₁`, together with
`mε Σ_(j≥1)j^(-1-ε)=1`. The raw terms vanish for j>1/t; the remaining
mean tail is absolutely summable for ε>0. The existing
`RHTower.dilationCenteredSource_ofReal` in `FermiDilationMeanInversion.lean` identifies the
continuous source with the discrete prefix minus the within-cell mean term.

This cancels the artificial large forcing only by retaining the complete
mean tail and within-cell correction. It does not supply an energy ceiling:
pairing the identity with Fε on a truncated physical horizon still leaves
the full signed proper-cofactor covariance. The half-damping obstruction
reappears if that covariance is bounded by individual dilation norms.
This is an unfinished proof attempt, not a new frontier theorem; no Lean
module is being added for an identity that leaves the required bound open.

### Search and verification record

Seven further direct corpus searches covered signed residue Gram cancellation,
prime-paired modes, centered-prefix signs, Abel smoothing, the exact normalized
identity, deep-cofactor boundary moments, and continuous floor-source inversion.
The Abel-smoothing query returned a partial result with a semantic runtime
deadline error and no candidates; no mathematical inference used that absence.
Other hybrid queries completed without reported errors or warnings; the
known-name normalized-identity lookup used lexical mode. Retrieved candidate
and source statements were inspected, and the decisive modules were read.

No mathematical obstacle was solved in this batch. No Lean source was changed,
no build was run, and no numerical computation, web search or novelty check was
performed. The next successful step must control the complete actual signed
covariance; neither pairwise signs nor the completed forcing identity does so.

## 2026-10-24: transverse, translation, and cotangent attempts

**Contribution assessment:** no new hard bound. The preceding activity did not
solve the signed covariance problem. The attempts below remain paper attempts;
none has a dependency-closed proof to formalize. They are not counterexamples
to actual-source admission and do not retire PM.

### Common-head transport does not pay the new shell

Read `ATwoScaleCompensationRate.lean`,
`TheCompensatingProjectionMovesSummablyAcrossScales.lean`,
`TheCompensationDefectDecaysFasterThanEveryLogPower.lean`, and
`FiniteHeadCutoffTransportAndPhysicalShellCost.lean`.

Trial: telescope the summable changes of the compensation projection to bound
the absolute transverse remainder. The complete shift cancels the same actual
source on the common head. Its estimate is therefore independent of the size
of that source; the transition identity still retains sector and connection
energies. Enlarging the physical horizon adds a new shell not covered by the
common-head estimate. Summable relative transverse energies cannot be multiplied
by the growing sector energy and treated as summable absolute energies.

No estimate of that new shell was proved. Choosing a faster cutoff sequence
would pay common-head transport only, so no such rate variant was formalized.

### Translation averaging leaves the distinguished origin unpaid

Trial: compare the actual-origin shell with translation-averaged short-interval
variance, then use the exact damped singular series. Inspected
`ExactDampedSingularSeriesAndGallagherPrefixDiscrepancy.lean`,
`PMRamanujanPeriodDiagonal.lean`, and
`PMPowerDampedMobiusRamanujanVariance.lean`.

The fixed-lag autocorrelation density and complete-period covariance are
available. They do not bound a distinguished origin on a moving horizon.
In particular, `pmPowerDampedRamanujanEnergyVariance` is an anchored pronic
variance, not a translation average. Passing from fixed-lag Cesaro limits to
the required moving interval would require an additional uniform estimate;
it was not supplied by these identities. No stationary-variance bound or
actual-origin comparison is claimed proved here.

### Möbius–Vasyunin inversion retains the complete signed quadratic form

Read `MobiusVasyuninFormulaForThePronicGramAtAllModuli.lean`,
`VasyuninReciprocityForAllModuliFromPronicCovariance.lean`, and
`PMPowerDampedMobiusRamanujanQuadratic.lean`.

Trial: sum the cotangent reciprocity terms with the actual Ramanujan weights
before estimating. The exact formula is

`G(m,n) = sum_(ab=m,cd=n) mu(a)mu(c) S(b,d)`,

where S is the residue second moment. At finite modulus cutoff this is a
change of coordinates in the same signed quadratic form. It does not delete
the mixed terms. The available reciprocity inequalities control individual
entries, not the complete coefficient-weighted sum. Passing to infinite
cofactor sums and canceling Euler factors also requires convergence of the
quadratic expression; that convergence cannot be assumed as part of this
attempt. No such rearrangement was used to claim admission.

### Prime and divisor signs do not yet control the full pairing

Read `DampedPrimeHorizonSlopeReversalAndCrossover.lean` and
`MoebiusBuchstabStepSmoothCoreLaw.lean`. The eventual negative prime-horizon
step controls the raw sieve response energy, not the centered-prefix pronic
energy. Composite steps and the prefix operation remain. It cannot be used
as a PM energy monotonicity theorem.

Read `MobiusDivisorMonotoneSignLaw.lean`. Its nonpositive Möbius sum covers
divisor-comparable pairs against nonnegative nonincreasing weights of the
anti-diagonal. The PM residue kernel has a different dependence on the pair;
incomparable pairs remain even if the comparable section is controlled.
No promotion of this sectional sign to a full Gram sign was justified.

Read the exact prime-dilation tangent law and damping autocorrelation law in
`TheTangentIsADilationAverageOfTheSource.lean` and
`TheSignedWorkIsTheTangentAutocorrelation.lean`. Positive prime weights do not
make a signed source/dilate pairing nonnegative. The explicit centering
correction must also be retained. The second-tangent and escaping-residual
work results were checked: neither supplies a uniform lower bound for the
complete work. No proof or disproof of nonnegative tangent autocorrelation
for the actual source was found.

### Continuation target and checks

Keep the signed integrated loss target above. Subsequent proof work must
estimate a complete actual-source expression, rather than manufacture a new
equivalence, telescope away only the common head, or discard incomparable
pairs. In particular, the next arithmetic step must retain the long-modulus
sawtooth together with its full mean tail; a pointwise limit or fixed-lag
average does not control their energy on the moving horizon.

Ten direct corpus searches covered transverse compensation, new-shell energy,
translation variance, origin/period comparison, Möbius–Vasyunin cancellation,
prime-dilation work, prefix signs, normalized profiles, Euler-sieve covariance,
and tangent correlation. All completed with `partial=false`; no reported
search errors or index warnings. Candidate and source statements were
inspected; the decisive modules listed above were read. Search results were
not treated as fresh Lean audits. No mathlib or web search, novelty check,
numerical experiment, Lean edit, or build was performed. No proof of RH or
its negation was obtained. Goal remains active.

## 2026-10-24: joint long-modulus / tail quadrature attempt

The active-goal attachment was reread. Previous turn is classified as **no
progress on the mathematical obstacle**. Its search results and bookkeeping
are not being counted as a new bound.

### Exact paper expression being attacked

For fixed `0<ε<1/2`, set `b(d)=mu(d)d^(-ε)` for d>=1. For integers
`1<=D<=n`, define

`B_D(x)=sum_(D<d<=floor x) b(d)` and
`Qε(n,D)=sum_(D<d<=n) b(d) floor(n/d) - n sum_(d>D) b(d)/d`.

The centered prefix is its short sawtooth plus `Qε(n,D)`:

`Aε(n)=sum_(d<=D) b(d)(floor(n/d)-n/d)+Qε(n,D)`.

At `D=floor(sqrt n)`, the short sawtooth has a horizon-uniform pronic
energy bound from `|mu(d)|<=1`: its absolute value is at most a constant
depending on ε times `n^((1-ε)/2)`, whose squared pronic majorant is
summable. This is the same short-modulus mechanism already formalized for
the oscillating probes, not a new arithmetic cancellation result.

The combined long and tail term has the quadrature expression

`Qε(n,D)=sum_(j>=1) B_D(n/j) - integral_(u>0) B_D(n/u) du`.

Paper justification: the sampled sum is finite, because `B_D(n/j)=0` for
`j>n/(D+1)`. Swap its finite sums to count `j<=n/d`. For the integral, each
coefficient b(d) contributes on `0<u<=n/d`. Absolute integrated mass is
bounded by `n sum_(d>D) |b(d)|/d`, finite for ε>0, which justifies swapping
the sum and integral. No cancellation estimate is used in this identity.

**Exact unproved conjecture:** for every fixed `0<ε<1/2` there is `Cε` such
that, for every T,

`sum_(1<=n<=T) Qε(n,floor(sqrt n))^2/(n(n+1)) <= Cε`.

This is a concrete expression for the existing admission problem, not a new
criterion claimed as progress. It is not encoded as a Lean premise.

### Attempts at the missing inequality

1. **Bound the quadrature error by variation.** The available absolute
   jump majorant is `sum_(d>D) d^(-ε)`, which diverges in this range. Keeping
   the integrable mean tail does not produce a bounded-variation estimate.
   The endpoint near u=0 contains the large-argument weighted Möbius sums;
   discarding that endpoint would discard part of the sought cancellation.
   No signed variation estimate was proved.

2. **Use short bilinear Möbius reconstruction before squaring.** Read
   `MobiusSquareResidueShortBilinear.lean` and
   `BilinearCountertermRemainderAndDefectDriftObstructions.lean`. The exact
   identity replaces coefficients through N² by two factors at most N,
   with both low-product and high-product terms retained. It gives no sign
   for the resulting complete quadratic expression. In particular, a
   nonnegative scalar kernel is not sufficient to infer a nonnegative
   quadratic form. No such inference was used. The harmonic tail beyond
   the finite reconstruction also remains compulsory. No bound for the
   combined form was obtained.

3. **Use short-window mean-square cancellation on quotient fibers.** Read
   `ShortIntervalSumsOfTheDampedDivisorCoefficients.lean` and
   `TheBalancedRegimeAndTheOmittedResidueClassLaw.lean`. The first retains
   the exact harmonic tail and gives a sign-blind short-interval bound.
   The second supplies qualitative balanced-block savings and explicitly
   distinguishes them from power saving for the complete receiver. The
   existing theorem `moebiusPowerWindowSaving_iff_receiverDampingRate_lt_half`
   prevents treating that stronger input as already supplied by the
   qualitative mean-square theorem. No required moving-fiber estimate was
   proved here.

The probe module
`OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations.lean` was
checked at its exact hyperbola merge and finite Euler–Maclaurin packet
theorems. Those are statements for smooth oscillating coefficients; the
packet evaluation is not available for actual Möbius coefficients merely
by substituting them.

### Assessment and verification

No significant obstacle was solved. The exact quadrature identity is a
paper-level organization of the open signed estimate; formalizing it alone
would not meet the requested frontier contribution. No new Lean module,
criterion, no-go, or numerical bound was added.

Six direct corpus searches covered long-modulus cancellation, the known
`longSawtooth` name, hyperbola remainder, the discrete-energy module, complete
signed bilinear forms, and damped harmonic-tail/window estimates. Four hybrid
queries completed without partial results, errors, or index warnings; two
known-term lookups used lexical mode. Decisive statements were checked in
source. No mathlib or web search, novelty check, numerical experiment, or
Lean compilation occurred. Continue the actual quadrature/covariance problem;
do not restart the already-failed separate-tail or absolute-variation bound.

## 2026-10-24: formalization significance gate

The user requested formalization of noteworthy paper proofs, then reiterated
that the result must significantly advance a hard PM obstacle. The completed
quadrature identity and short-head bound were separated into
`../3-formalized/leftovers/pm-long-modulus-quadrature.md`, with their complete paper
proof and explicit scope. They do not prove the signed remainder estimate.
Standalone formalization was therefore deferred at the significance gate;
it must not be presented as the requested hard mathematical advance.

Four project searches inspected quotient covariance, termwise reciprocal
integration, and the existing power-sum estimates. Two were hybrid and two
lexical. A subsequent mathlib lookup for integration of series was partial
with an interrupted text-retrieval stage; a narrower `integral_tsum` search
completed. These were dependency lookups, not new mathematics.

One foreground `lake --old env lean /tmp/pm_longtail_api.lean` process was
started only to inspect API names. It was deliberately terminated after the
significance review; exit 143, no diagnostics or verification result. No
repository Lean module, olean, umbrella import, axiom, or premise was added.
The temporary probe and completed search scratch files were removed.

No noteworthy completed paper proof of a new signed-covariance estimate is
available from this batch. The full bound, and hence RH, remains unproved.
This is an unresolved mathematical problem, not a missing permission or an
external-state blocker. The overall goal remains active.

## 2026-10-24: Markov work and cross-programme reorientation

Route remains PM: actual signed Möbius energy, cofinal small-damping
admission, RH. No new source estimate or Lean theorem was established in
this batch.

### Failed Gram argument

The exact Markov work is boundary flux minus nonnegative jump energy minus
the centered-density forcing. Forward jump dissipation alone does not bound
backward work. A proposed alternative was positivity of the logarithmically
weighted residue Gram matrix
`K_T(d,e)=(log d+log e) G_T(d,e)`.

Universal finite-horizon positivity is false. At `T=1`, for `d,e>=2`, the
residue values are `-1/d,-1/e`, so `G_1(d,e)=1/(de)`. The corresponding
two-by-two determinant of K is exactly
`-(log d-log e)^2/(d^2 e^2)`, negative for distinct d,e. This is an algebraic
paper check, not a numerical experiment. It refutes the proposed universal
inequality, not an inequality on the actual Möbius source, infinite-horizon
Gram positivity, or RH. No no-go module was added. The actual finite residue
identity also retains a constant boundary defect and both of its energy
terms. No closure theorem placing the reciprocal source in the residue span
in the required norm was established or assumed.

### Leads from the fourteen programme READMEs

Reviewed programme overviews, relevant mechanism sections and open-problem
sections in all fourteen paths supplied by the user. These were targeted
reads, not a claim to have audited every theorem in the programmes. Corpus
search located the declarations; decisive statements below were inspected
in their Lean source.

1. **BVI gives the most concrete remaining arithmetic object.**
   `UniformRenormalizedInteriorEnergyRemainder.exists_pmBezoutInterior_compensated_energy_bound`
   proves `|B_epsilon(T)-E_epsilon(T)|<=C_epsilon`, where
   `B=2*pmBezoutInteriorMartingaleSum +
   2*pmInteriorLogCounterterm*pmCompensatedHarmonicSum`.
   The coefficient is exactly one: this is not a contraction.
   `SignedModulusSumOfTheInteriorMartingale` evaluates the signed conditional
   orbit drift by Selberg coordinates, proves radical invariance, and pays
   its double-modulus drift absolutely. The remainder, with its actual
   signs and anchored horizon, is still unpaid. Birth-delayed centering
   retains modulus birth and the harmonic tail; its stated envelope grows
   with the progression length. It is not a uniform-energy estimate.

2. **SAEI supplies a possible method, not its arithmetic premises.**
   `FrustrationIsPaidAlongCanonicalPaths.PathCertificate` requires a positive
   signed supersolution, path-resistance budgets and packing of every shared
   aligned edge. `KronReductionNeverCreatesFrustration` gives
   `R_st=c_st-beta_st`; nonnegative conductance requires an aligned, coercive
   interior. These are useful mechanisms for paying correlated adverse terms
   without spending one positive contribution repeatedly. Neither a PM
   coupling with the needed properties nor its supersolution, coercivity or
   horizon-uniform packing was constructed here. Those inputs must be
   proved on the actual source, not introduced as structure fields and
   reported as progress.

3. **Compensation identifies what such a construction must control.**
   `TheCompensatingProjectionMovesSummablyAcrossScales` proves summable
   amplitude variation and relative transverse energy. The absolute
   transverse and interscale connection energies remain unpaid. A new
   contribution must bound these actual terms or the BVI compensated
   bracket, not reprove relative anti-alignment or an abstract recurrence.

4. **Prime-horizon dissipation needs a norm transfer.**
   `DampedPrimeHorizonSlopeReversalAndCrossover.eventually_pmPowerDamped_prime_horizon_step_neg`
   is an actual-source sign theorem at fixed positive damping, uniform in
   trans-horizon prefixes. Its energy is the raw sieve-row square sum.
   PM uses centered prefix energy with pronic weights; composite updates,
   mean subtraction and that norm transfer are not paid by this theorem.
   It was not used to assert PM energy monotonicity.

5. **TTPC suggests subtracting the exact continuum contribution before
   estimating a signed remainder.** Its coalescent surplus remains open;
   its arithmetic mean-value premise cannot be imported into PM. AOT and
   SSIC explain why source signs and origin-sensitive data must survive any
   such transfer. The aperture positivity, geometric effectivity and
   spectral visibility programmes do not supply the missing PM bound merely
   through their receiver dictionaries.

### Selected attack and significance gate

Try to construct a source-specific payment of the already compensated BVI
interior remainder, using shared-edge packing or effective conductances as
the proof mechanism. A substantive result must establish an actual uniform
arithmetic bound, with means, modulus birth, cross terms and tails retained.
An abstract canonical-path criterion, an additional RH equivalence, or
formalization of the failed Gram test does not meet that gate.

This is a research lead, not a closed paper proof. The recent searches and
source inspection have corrected the proposed mechanism but have not solved
a hard PM blocker. No Lean compilation, new module, umbrella import, axiom
or added mathematical premise occurred. No web search, novelty check or
numerical computation occurred. The full RH goal remains active.

## 2026-10-24: actual-source shape conjecture and failed positivity mechanisms

The preceding turn changed the proposed attack but discharged no mathematical
premise. This batch attempted proofs, rather than treating additional corpus
matches as a result. No new PM energy estimate was obtained.

### Canonical-path test

On a finite squarefree support let S be the diagonal matrix of Möbius signs.
Then S is its own inverse, and `x^t(S K S)x=(Sx)^t K(Sx)`. Consequently an
all-vectors positivity certificate after this sign conjugation is equivalent
to one before it. Merely moving the signs into the coupling matrix does not
exploit the actual source. A useful certificate would also have to use the
relations between its fixed coefficients; those were not proved to imply
the required shared-edge budget.

The exact BVI identity remains `B_epsilon(T)=E_epsilon(T)+O_epsilon(1)`
with coefficient one. Applying the existing local quadratic-gradient
identity and summation by parts returns this same energy, not a strict
contraction. The source files for these identities were inspected. No
supersolution, coercivity or packing field was introduced as an assumption.

Two possible sources of the missing arithmetic relation were examined:

- Divisor-comb resonance annihilation requires maximal autocorrelation at
  every divisor ratio. That premise is not established for the actual PM
  residue kernel. Its nonnegative Gram theorem alone gives no upper bound.
- Fixed-lag damped autocorrelation is a complete-period statement, with a
  bound depending on the lag. It cannot be inserted into the growing-lag,
  origin-anchored interior sum without a uniform transfer estimate. No such
  estimate was obtained. Exact common-divisor reindexing retains the
  coprime Möbius product; it does not sign the remaining kernel.

### Conjecture C1: contraction from the zero anchor

For every epsilon>0 and every natural T, conjecture

`E_epsilon(T) <= E_0(T) = T/(T+1)`.

This is an explicit conjecture about the literal source, stronger than the
admission needed for PM. It is not proved and is not encoded in Lean. The
zero-damping identity uses the established fixed-horizon limit, including
the continued density at zero. No interchange with an infinite horizon is
assumed.

The first attempted proof was to realize the damping energy by a Dirichlet
expansion with nonnegative coefficients. This fails already at horizon one.
Write `rho(epsilon)=1/zeta(1+epsilon)`. The exact first cell gives

`E_epsilon(1) = (1-rho(epsilon))^2/2`.

For epsilon>0 the reciprocal-zeta Dirichlet series is absolutely convergent,
so multiplication gives

`E_epsilon(1) = sum_(m>=1) a(m) m^(-epsilon)`,
`a(m) = (1/(2m)) sum_(d e=m, d,e>=2) mu(d)mu(e)`.

For distinct primes p,q and m=p^2 q, the only nonzero factorizations with
both factors at least two are `(p,pq)` and `(pq,p)`. Each Möbius product is
negative one. Hence `a(p^2 q)=-1/(p^2 q)<0`. This is a symbolic coefficient
argument, not a numerical experiment. It excludes the proposed termwise
positivity proof; it does not refute C1 or convexity. No claim about general
Laplace representations is needed for this conclusion.

### Conjecture C2: the weaker second-derivative sign

Allow cancellation rather than demanding positivity of every Dirichlet
coefficient. The exact source expression to prove is

`||D_epsilon||_T^2 + <A_epsilon,F_epsilon>_T >= 0`,

where D and F are the first and second damping tangents. The corpus already
contains its derivative identity and its RH-sufficient convexity implication
in `TheSecondDampingTangentAndConvexity`; these are not new results.

The divisor derivative factors through the positive kernel
`Lambda(d)d^(-epsilon)`. Differentiating again introduces
`(Lambda*Lambda)(d)-(log d)Lambda(d)`, with prime-power subtraction retained.
The nonnegative first-tangent square does not by itself dominate the signed
source/second-tangent pairing. Taking absolute values instead needs the
unproved tangent-norm estimate. This is the first unresolved step in the
attempt; neither Cauchy--Schwarz nor the positive divisor coefficients
discharges it.

C1 and C2 remain open, not falsified merely because these proofs failed.
Further work must attack their actual signed pairing or return to the weaker
integrated loss. Another implication assuming C1/C2 would add no progress.

### Verification and scope

Seven completed hybrid corpus searches and one lexical definition lookup
covered the interior kernel, divisor differences, lag densities, comb
incidence, jump reciprocity, coprime reindexing and actual work signs.
Hybrid outputs reported no partial results or errors. Relevant statements
were read in source; the search returned sign criteria, not a proved global
sign for the actual work. Three completed-paper cards were also inspected:
their graph comparison, observation recovery and rough-shift averaging do
not discharge the PM estimate, so they were not substituted for it.

No Lean file, umbrella import or compiled artifact was added. No axiom,
unproved premise, web search, novelty check or numerical computation was
used. There is no completed significant paper proof to formalize from this
batch. Mathematical frontier progress: none; failed proof steps and the
remaining exact conjectures are recorded to avoid repeating them.


## 2026-10-24: second-tangent payment and joint-prime test

Route remains PM: actual signed damping energy, admission at cofinally small
positive damping, then RH. This batch has no frontier advance and no closed
significant paper proof. C1 and C2 remain conjectures, not Lean assumptions.

### Exact attempted payment

The source identity in `TheSecondTangentIsAnIteratedDilation` was read in full.
Its kernel is `K = Lambda * Lambda - (log) Lambda`. For a prime p and k>=1,
its elementary prime-power coefficient is `K(p^k)=-(log p)^2`: convolution
has k-1 nonzero ordered factors, whereas the subtraction has coefficient k.
For distinct primes p,q and positive a,b, `K(p^a q^b)=2 log p log q`.
It vanishes at integers with at least three distinct prime factors. These
symbolic observations describe the attempted pairing, not a new energy
estimate; no numerical computation or Lean formalization was performed.

The proposed argument paired negative one-prime contributions with the
positive two-prime convolution and the first-tangent square. It did not
close: after passage to prefixes, every dilation is paired with the signed
centered source, and both density corrections survive. Positivity of the
un-centered divisor coefficients does not give the sign of this pairing.

A local algebra check explains why independent prime factors cannot simply
be declared convex. For fixed vectors X,Y in a real inner-product space,
r=p^(-epsilon), and l=log p,

`(1/2) d^2/d epsilon^2 ||X-rY||^2
  = l^2 (2 r^2 ||Y||^2 - r <X,Y>)`.

This has an uncontrolled mixed term. In the actual source, X and Y also
vary with epsilon through the other primes and the density. Thus this
calculation neither proves nor refutes actual-source convexity. A proof
must retain their joint derivatives rather than sum independent convexity
claims. The attempted termwise payment is unfinished, not a counterexample
to C1 or C2.

### Joint-prime cancellation checked against source

The exact theorem `hypercubeGram_eq_cancelled_diag_sub_residueGap` already
cancels the zeroth Euler moment and bounds the remaining diagonal factor
by one. Its complete signed residue-gap sum remains present. Gram
nonnegativity gives a lower bound for the energy, not the upper bound
needed here. No bound for that signed gap was constructed.

`MobiusDivisorThirdEnergyInteraction` supplies a negative third selection
energy difference at the original core and a precise late-block transport
law. Its carrier is the divisor selection energy. No identification with
the centered pronic second-tangent pairing was found or asserted.

`PrimePairLevelSumAndRelativePrecisionCancellation` was also inspected.
The double-damping square is exactly a squared source difference plus its
boundary square. Its nonnegativity does not bound the mixed-damping
negative contribution. The advertised relative-precision estimate is
unconditional above the zero width, not on a new sub-half-damping band.
It cannot serve as the missing input below that width.

### Research state and next attack

The first unresolved step remains the complete signed pairing, including
prime-power subtraction, mixed prime contributions, and density forcing.
A successful next attempt must construct a joint cancellation estimate
for these literal terms. Repackaging any of them as a positivity premise,
using the nonnegative double-integral square as an upper bound, or proving
another conditional receiver would not move this frontier.

Corpus searches covered second-tangent pairing, sieve/Markov contraction,
Castelnuovo-Severi leads, joint-prime differences, the exact hypercube
identity, and prime-power structure. Exact source statements were checked.
No web or novelty search, subagent, numerical experiment, Lean build,
umbrella edit, or compiled artifact was used. No missing analytic input
was hidden in a theorem binder. There is no required user decision or
external-state blocker; the mathematical proof remains unresolved.

## 2026-10-24: inversion forcing after its explicit power term

Previous batch classification: no frontier progress. This batch attacked
the centered inversion equation rather than trying another primewise sign.

Write m = Re(1/zeta(1+epsilon)), A for the actual centered source, and
Phi(n) = sum_(j<=n) j^(-epsilon) floor(n/j). The inspected source proves

`A(n) + O(n) = rho(n) = n - m Phi(n)`,

where O is the proper-unit dilation. The candidate was to remove the
explicit growing part of rho and pay the remaining forcing in pronic L2.
For 0<epsilon<1, put

`Z = Re(zeta(1-epsilon))/(1-epsilon)`,
`b = -m Z`,
`r(n) = rho(n) - b n^(1-epsilon)`.

The weighted hyperbola formula suggests
`r(n) = -m R(n)`, with `|R(n)| <= K n^((1-epsilon)/2)`.
Squaring and dividing by n(n+1) then gives a summable
`O(n^(-1-epsilon))` majorant. This paper argument is already in the corpus:
`SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws` defines
`subHalfRemainder`, proves `abs_subHalfRemainder_le`, and supplies the
stronger dilated pronic norm estimate. Its coefficient is zeta(1-epsilon),
not zeta(epsilon). The source identification
`inversionDefect_eq_neg_density_mul_majorantCenteredPrefix` was also read.
Verdict: existing mathematics, not a new premise discharge.

Retaining the same subtraction in the actual dilation gives the exact
paper identity

`E(T) = <A,r>_T - <A,O - b n^(1-epsilon)>_T`.

The first term is bounded in absolute value by `K_epsilon sqrt(E(T))`
using the existing remainder theorem. This does not bound the second:
the inversion equation also says `O - b n^(1-epsilon) = r - A`.
Substituting that equality returns E with coefficient one. Therefore the
renormalization alone is not coercivity, and encoding the remaining lower
bound as a premise would only create another receiver. No such theorem
was added.

A Mellin-side test asked whether a completed-zeta modulus comparison could
control this inverse response. Corpus search found local horizontal
monotonicity with an explicit zero-location premise and the earlier
vertical-modulus research card with its analytic Pick continuation still
open. Neither is an unconditional source bound. No external source was
opened and no novelty check was performed.

The next mathematical task is still constructive: estimate the literal
signed inverse response using more than its defining inversion identity.
The explicit power forcing is already understood; re-formalizing its
remainder would not meet the requested significance gate. This batch
produced no significant closed paper proof, no Lean module, no audit, and
no RH proof. No computation, build, subagent, added axiom, or hidden premise
was used. The goal remains active, with no user-input or external-state
blocker.


## 2026-10-24: two-scale connection and the literal sector profile

Previous turn: no frontier progress. This batch tested whether compatible
prime-sector decompositions can supply the missing absolute estimate.
The exact two-scale source and projection formulas were read, not inferred
from their theorem names.

Write S_P for the complete Ramanujan prefix at cutoff P^2-1, L_P for
`pmRamanujanLargePrimeSector`, and C_P=S_P-L_P. The established estimate
for S_Q-S_P cancels the same cutoff-independent divisor remainder on both
sides. It controls cutoff error, not that remainder. Telescoping these
estimates on a fixed common head does not control energy in newly added
physical cells. No summation over enlarging heads was justified by it.

### Source-specific direction attempt

The exact prime-cofactor head theorem supplies, for Q>=2 and N<Q,

`L_Q(N) = H_Q m N + sum_(Q<p<=2Q) w_p S_(floor(Q^2/p)-1)(N)`,

where `w_p=1/(p^(1+epsilon)-1)>0`, `H_Q=sum w_p`, m is the actual density,
and the subscript on S in this displayed formula denotes the literal
Ramanujan cutoff, not its square-root parameter. This is just
`pmRamanujanPrimeCofactorPacket_head` summed over the selected prime band.
No cofactor or mean is discarded.

For 0<epsilon and 0<=a<=1 with 1<epsilon+a, the existing uniform estimate
`norm_pmPowerDampedRamanujanCumulativePrefix_le_rpow` consequently gives

`|L_Q(N)-H_Q m N| <= H_Q C_(epsilon,a) N^a`,
`C_(epsilon,a)=sum_(d>=1) d^(-(epsilon+a))`.

Thus the sector's common-head direction can be compared with the explicit
linear density profile. This was the proposed new input beyond scalar
amplitude convergence. Its significance test fails for the present goal:
the correction is a weighted average of the complete shorter-cutoff
prefixes whose absolute energy is unpaid. Direction comparison alone neither
bounds that average in critical energy nor bounds new physical shells.
The generic projector identity

`R_Q-R_P = (I-Pi_Q)(S_Q-S_P) + (Pi_P-Pi_Q)S_P`

also retains the complete source norm in its connection term. Moreover,
using a projector defined on a common head changes the full-head amplitude
used by `pmCompensationAmplitude`; these were not silently identified.
No direction-only theorem was formalized as a substitute for absolute
signed compensation.

### Outcome

Corpus searches covered actual interscale connection energy, exact sector
definitions, sector directions, and density subtraction. The source
`PMRamanujanGrowingCofactorHead` confirms the selected band is (Q,2Q],
with every cofactor through floor(Q^2/p), and that its head contains the
linear density term as well as the centered prefix. The frontier and
killed-route entries explicitly retain the distinction between relative
alignment and absolute admission.

No actual horizon-uniform signed estimate, significant closed paper proof,
or Lean premise discharge was obtained. No Lean build, compiled artifact,
umbrella edit, numerical experiment, web search, subagent, added axiom, or
conditional replacement for the missing estimate was introduced. Goal
remains active; there is no user-input or external-state blocker. The
next attempt must control the actual signed energy in the growing physical
shell, not just the changing cutoff or the coherent sector's direction.


## 2026-10-24: short-window transfer to growing physical shells

Previous turn classification: no frontier progress. This attempt tried to
use actual short-window cancellation as a contracting input for shell
energy, retaining the signed rows and both rank-two terms.

The inspected theorem `eventually_abs_rowBilinear_moebiusWindowRow_le`
controls

`B(c,mu_Q) + m(c) R(mu_Q) + beta(c) H(mu_Q)`

for c supported on primes satisfying its lower support threshold. Its
leading norm is

`sqrt(sum_p c(p)^2 p^2) sqrt(Q+2Q0^2) Q^(-3/2)`.

It is not the complete receiver energy. The actual PM sieve coefficients
are `mu(d)d^(-epsilon)`, as checked in
`PowerDampedPronicMultiplicativityAndRoutePMBridge`; they cannot be replaced
by Ramanujan coefficients `O(d^(-1-epsilon))` in this norm. Such a
replacement would create an erroneous extra inverse power of d. The
existing qualitative small factor therefore was not shown to be a
contraction against the energy being estimated. Both rank-two readouts
also remain present in the theorem.

### Composite-modulus attempt

The proposed extension was to regroup nonprimitive roots by conductor
and use Möbius cancellation to remove repeated composite contributions.
The prime proof uses that powering by k permutes nontrivial p-th roots
when p does not divide k. For composite modulus d, gcd(d,k) creates
proper-conductor fibres; there is no such permutation on all nontrivial
roots. Those fibres must be accounted for explicitly.

The stronger hoped-for automatic cancellation is not available. The exact
source formula already proved in `PMPowerDampedMobiusRamanujanWeights` is

`w_epsilon(q) = rho_epsilon mu(q) /
                 product_(p|q) (p^(1+epsilon)-1)`.

Its definition is the complete sum over multiples of q. For positive
epsilon and squarefree composite q this coefficient is nonzero. Regrouping
by divisibility produces a real weighted composite source, not a row
supported only on primes. This does not rule out a useful general-modulus
transfer theorem; it invalidates the attempted immediate reduction to the
existing prime theorem. No general-modulus bound or full shell estimate
was proved.

`ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis` was read directly:
its power saving is equivalent to `zetaZeroAbscissa < 1`, not supplied
unconditionally. The established Matomaki--Radziwill input is qualitative
short-window cancellation. Neither the zero-free strip nor a power saving
was inserted as an assumption. Extending a qualitative coefficient-norm
bound alone would still leave the source-relative absorption step open.

### State

Four completed corpus searches covered shell/window cancellation, exact
bilinear normalization, composite-modulus transfer, and coprime Euler
weights. Relevant source declarations and definitions were inspected.
No significant closed paper proof or premise discharge emerged; no Lean
file or umbrella was edited, and no compilation was run. No numerical
experiment, web search, novelty check, subagent, added axiom, or conditional
stand-in for the missing estimate was used. Goal remains active. The
unresolved mathematical step is cancellation of the full composite signed
row at the receiver-energy scale, not cancellation relative to an unsigned
coefficient norm.

## 2026-10-24: Newton remainder, divisor correlations, and paired Markov work

Previous batch made no frontier advance. This batch tested the full signed
row rather than another coefficient-norm estimate.

### Newton form of the actual two-cutoff identity

The checked declaration `moebius_vaughan_identity` in
`VaughanTypeIIShortAndAllHorizonMobiusL2Energy` gives, with Dirichlet
convolution, `a=trunc_U(mu)` and `b=mu-a`,

`mu = 2a - a*a*zeta + b*b*zeta`.

The conjectured mechanism was to treat the last term as positive quadratic
control. This fails: convolution squaring is not pointwise or Hilbert
squaring. At cutoff U=2, `a=delta_1-delta_2`. For distinct odd primes p,q,
the exact identity gives `(b*b*zeta)(pq)=2` and
`(b*b*zeta)(2pq)=-2`. Indeed, at 2pq the short-row term
`(a*a*zeta)(2pq)=1-2=-1`, while `mu(2pq)=-1` and `a(2pq)=0`.
These are symbolic arithmetic identities, not a numerical experiment.
They reject only this positivity mechanism; no conclusion about the
sign of the complete energy or about RH follows. A bound for the signed
residual pairing was not obtained.

### Positive divisor source and arithmetic damping flow

Corpus searches and direct source reads checked
`PMAdjacentDivisorCorrelation.tendsto_pm_adjacent_divisor_mean` and the
period-correlation/dissipation laws in TransHorizonIncidenceMechanics.
The adjacent theorem uses positivity and two dominated limits. Its
translation average supplies neither a horizon-uniform anchored-prefix
bound nor a summable estimate for the full growing set of covariance lags.
No interchange with that growing set was justified.

The next attempt retained the literal damping flow. Directly checked
`DampingWorkAsArithmeticMarkovBoundaryFlux` and
`TheDampingChainInReceiverCoordinatesAndHTransform`. The normalized
centered source v=A/n satisfies `v'=Gv-rho'`, and its exact energy law is

`E' = Flux(v) - Jump(v) - 2 rho' sum_(n<=T) n/(n+1) v(n)`.

The nonnegative jump term alone does not bound backward work; forward
control still requires its cancellation with counting-measure flux and
the density forcing. Integrating the paired expression reproduces the
endpoint energy difference. The existing infinite-horizon theorem
explicitly assumes admission at both endpoints, so it was not used to
produce admission. The size-bias column estimate likewise retains
`E_T(eta)+rho_eta^2` as its factor despite its summable column weights.
No independent estimate for the actual paired work was proved.

### Status

No significant closed paper proof, Lean theorem, or premise discharge
resulted. No Lean source, umbrella, or compiled artifact was changed; no
build was run. No web search, numerical experiment, novelty check,
subagent, added axiom, or assumed analytic input was used. Goal remains
active, with no user-input or external-state blocker. The hard open step
remains an absolute, horizon-uniform bound for the full signed source at
cofinally small positive damping. Neither a convolution-square identity,
translation-averaged correlation, nor the exact Markov accounting closes
that step.

## 2026-10-24: collective deletion, new critical-family positivity, and prime-sieve averaging

Previous turn: no frontier advance. The objective and current PM map were
reread. No significant PM estimate was obtained in this batch either.

### Collective Ramaré attempt

Direct source checks covered `EulerDeletionRamarePhysical`,
`EulerDeletionRamarePhysicalEnergy`, and
`RouteERamareIncidenceConditionalNegative`. The complete physical packet
includes its affine harmonic correction. Its squared norm retains the
rough--packet and packet--packet cross terms. Conditional negative
incidence requires the active scalar sum to vanish; the unconditional
identity instead contains the square of that sum minus the prime-load
energies. Centering by adding an auxiliary coordinate therefore does not
remove the original source energy for free. No cancellation estimate for
the actual complete packet field was proved.

### Reorientation to the updated positivity result

The current frontier map now cites
`exists_suzukiCriticalFamily_strict_deficit`. Its source and the sources
of `CompactCriticalSourceWeilPositivity` and
`DoublyCollaredCriticalSourcePositivity` were inspected. The theorem gives
positive complete Weil energy for arbitrary real coefficient patterns
in a sufficiently high dyadic critical family, uniformly over its allowed
compact truncations. The finite positive-shift neighbourhood depends on
the source and smooth approximant.

The literal family uses

`Phi_N(v) = P(lambda_N v) - P(N v)`,
`4 lambda_N^3 = N^2 (4N+1)`,
`1/15 <= lambda_N-N <= 1/12`,

with both collars and the `exp(x/2)` envelope. In particular the collar
displacement does not tend to zero. The tested transfer to PM reciprocal
floor packets has neither an established approximation nor a bound in
the required energy norm. Multiplying reciprocal frequencies by a common
multiple gives integer frequencies, but does not supply the shifted
branch, the collars, or control of the original physical head. No density
or source-identification claim was made. Existing low/high and lacunary
Schur bounds also concern this same critical family; their existence is
not a transfer theorem for PM.

### Exact finite prime-sieve averaging test

The checked PM Euler-product formula suggested averaging sieves with
independent prime selection. This was tested algebraically on a finite
prime set P; no infinite probabilistic limit is used here. Put
`r_p=p^(-epsilon)` and let `xi_p` have values 0,1 with mean r_p. Define

`Z_P(N) = sum_(n<=N) product_(p in P,p|n)(1-xi_p)
          - N product_(p in P)(1-xi_p/p)`.

For Q contained in P, let A_Q(x) be the finite damped sieve prefix
through floor(x), centered by `x product_(p in Q)(1-r_p/p)`.
Independence gives `E Z_P(N)=A_P(N)`. Expanding
`xi_p=r_p+sqrt(r_p(1-r_p)) eta_p`, where the products of the eta_p
are orthonormal for the finite product weights, gives exactly

`E[Z_P(N)^2] = sum_(S subset P)
    (product_(p in S) r_p(1-r_p)) A_(P\S)(N/product_(p in S)p)^2`.

Indeed, the S coefficient is the product of the negative square-root
factors times the displayed shorter sieve discrepancy: divisibility by
the squarefree product of S reindexes the count, and its primes are
coprime to every prime of P\S. The empty product supplies A_P(N).
Orthogonality then proves the finite identity without exchanging limits.

This exposes the failure of the proposed variance-only proof: the empty
subset contributes the full squared mean discrepancy. Controlling the
nonempty fluctuation terms cannot upper-bound that term. A bound for
the entire averaged square remains unproved; Jensen's inequality alone
does not provide one. This finite accounting was not formalized or
counted as the significant PM progress requested.

### Remaining state

Corpus searches also checked the existing convex-energy receiver and
second-tangent declarations. Their convexity input remains unproved;
neither reciprocal-zeta concavity nor a scalar density estimate was
silently substituted for the full mixed second-tangent pairing.
No Lean theorem, source edit, umbrella edit, build, numerical experiment,
web search, novelty check, or subagent was introduced. Owned search
scratch files were cleaned after their processes terminated. The goal
remains active, with no user-input or external-state blocker. The missing
mathematics remains horizon-uniform cancellation for the actual signed
source at cofinally small positive damping.

## 2026-10-24: direct second-tangent pairing and stationary-point test

Previous turn classification: no frontier advance. This batch stayed on
the actual second-tangent sign rather than another source representation.
Read the current objective and PM map, and checked the statements and
proofs in `TheSecondDampingTangentAndConvexity`,
`TheSecondTangentIsAnIteratedDilation`, and
`TheSignedWorkChangesSignOnce`. Two completed corpus searches covered
the full second kernel and stationary curvature. No source-derived sign
estimate was obtained.

For positive epsilon the actual positive divisor product gives an exact
way to inspect the mixed term. With

`L_n = sum_(p|n) log(p)/(p^epsilon-1)`,
`J_n = sum_(p|n) log(p)^2 p^epsilon/(p^epsilon-1)^2`,

finite differentiation gives `c_n' = c_n L_n` and
`c_n'' = c_n (L_n^2-J_n)`. The density has the corresponding formulas
with `p^epsilon` replaced by `p^(1+epsilon)` and all primes included;
these sums converge at positive epsilon. Thus positivity of c_n does not
itself supply the sign of its second derivative or the sign of the
centered source pairing. The terms `L_n^2-J_n`, the density derivative,
and all prefix cross terms must remain present. No scalar density sign
was used as a substitute for this full pairing.

The precise unresolved quantity remains

`Q_T(epsilon) = ||D_epsilon||_T^2 + <A_epsilon,F_epsilon>_T`.

The checked dilation identity expresses F using `Lambda*Lambda-log*Lambda`
and the exact density correction. The convolution square is not a norm
square. In particular, its prime-power and two-prime terms cannot be
assigned a common positive sign after pairing with the actual source.
The attempted use of stationarity `<A,D>_T=0` supplies only one scalar
orthogonality relation and did not eliminate the remaining second-kernel
pairing or its correction.

A logical issue was caught before adding any receiver: proving only
`Q_T>=0` at stationary points would not by itself exclude a flat interior
maximum. A strict curvature conclusion at an excessive stationary value,
or a proved control preventing a downward crossing of the work, would
be needed. Neither was proved here. No new criterion or generic
counterexample was formalized as a replacement for that missing result.

No significant closed proof or premise discharge emerged; no Lean file,
umbrella, or compiled artifact was changed, and no build was run.
No numerical experiment, web search, novelty check, subagent, or added
analytic assumption was used. Goal remains active; the obstacle is the
unproved arithmetic pairing, not a user-input or external-state block.

## 2026-10-24: Liouville transfer and signed square-count averaging

Previous turn: no frontier advance. The current objective, PM frontier,
and squarefree-discrepancy killed-route entry were checked. This batch
tested a different actual source via the verified square-kernel transfer.

Direct reads of `AnIndexFormulaForTheActualReceiver` and
`MoebiusAndLiouvilleReceiversAreEquivalent` confirm

`lambda = 1_square * mu`,
`mu = squareMoebius * lambda`.

After damping, both convolution kernels are critical Wiener units because
their norm is controlled by `sum_j j^(-1-2 epsilon)`. The identities retain
the SAME positive damping parameter. They do not convert admission at
2 epsilon into admission at epsilon. Pointwise `lambda(n^2)=1` is not an
inverse or contraction identity for the full receiver.

### Signed renewal attempt

The source of `SquarefreeDiscrepancyMellin.response_eq` and
`response_eq_one_iff` was checked. For the actual squarefree discrepancy,

`q(a) = 1 + a zeta(1-a)/(rho (1-a) zeta(2(1-a)))`.

Its real-axis comparison does not bound the actual oscillating source;
the complex unit-response condition still detects the reflected zeros.
No absolute contraction was used, since the corpus already disproves
that estimate near the half threshold. The exact cofactor transport in
`LiouvilleSignedCofactorDilation` retains its nondivisible remainder.

### Tested positive-average mechanism

Write `H_mu(t)=sum_(n<=t) mu(n)/n` and
`P_lambda(x)=sum_(m<=x) lambda(m)(x/m-1)`. For x>=1, finite summation gives

`P_lambda(x) = integral_1^x H_mu(t) floor(sqrt(x/t)) dt`.

To check the identity, expand the square count into the conditions
`j^2 t<=x`. Integrating each finite harmonic-prefix step gives

`sum_(j^2 n<=x) mu(n)(x/(n j^2)-1)`.

Regrouping by m=n j^2 gives the actual Liouville coefficient through the
checked square-convolution identity. There is no infinite interchange.

The hoped-for positive-average argument fails at its weight: on [5,6),
`H_mu=1-1/2-1/3-1/5=-1/30`, since mu(4)=0. This is a symbolic finite
identity, not a numerical experiment. The square-count kernel is
nonnegative, but the integrating weight is not. The identity neither
disproves positivity of P_lambda nor pays its full signed integral.
No uniqueness assertion about alternative integral representations was
made. This failed mechanism was not formalized as another no-go result.

The corpus's harmonic square-dilation identity and triangular Mellin
formula were also inspected as leads. The positive recurrence in
`LiouvilleEvenIndexPositiveRecurrence` supplies cofinally many positive
binary additive correlations, not a uniform estimate for this source.

### Status

No significant source estimate, closed paper proof toward admission, or
Lean premise discharge resulted. No Lean source, umbrella, or compiled
artifact was changed; no build was run. No web search, numerical
experiment, novelty check, subagent, or analytic assumption was used.
Owned search files were removed after all four searches terminated.
Goal remains active. The hard blocker is still collective cancellation
of the complete source; there is no external-state or user-input block.

## 2026-10-24: Haar endpoint and finite-prime Liouville resolvents

PM route remains complete signed source admission at cofinally small
positive damping. The preceding square-count attempt made no frontier
advance. Corpus searches and direct source reads checked whether the
orientation, compensation, Haar, or new critical-family results supply
the missing source estimate. They do not currently supply it.

The Haar Gram kernel is already explicit in
`PMPowerDampedMobiusFiniteSmoothSource`: for positive dilation indices
its entries are `max(0, 2/max(m,n)-1/min(m,n))`. Its positivity concerns
the finite or absolutely convergent smooth-prime source. Passing to the
complete pointwise source near zero still needs norm control. The fold
geometry already isolates the harmonic shadow and leaves the fold-free
endpoint error unpaid. Neither identity was counted as new knowledge.

### Exact prime-resolvent conjecture and attack

For a finite set P of primes, define the literal triangular source

`F_P(x) = sum_(n<=x, all prime factors of n in P) lambda(n)(x/n-1)`.

The empty-prime source is `f(x)=max(x-1,0)`. For a prime p outside P,
unique p-adic decomposition and complete multiplicativity give

`F_(P union {p})(x) = sum_(k>=0) (-1)^k F_P(x/p^k)`.

At each positive x this sum has only finitely many nonzero terms. This
is a source identity, with every cofactor retained. The candidate was to
prove positivity by a cone preserved by these alternating resolvents.
If that worked for every P, taking P to contain all primes up to x
would cover the actual triangular Liouville source at x.

Two natural proposed invariants fail directly on the source:

* Convexity is lost at the first prime insertion. For P={2}, F_P(x)
  is x-1 on (1,2), and x/2 on (2,4). Its slope drops at 2.
* Monotonicity of the quotient F_P(x)/x is lost at the next insertion.
  For P={2,3} and 3<x<4, the only active integers are 1,2,3, so
  `F_P(x)=x/6+1` and `F_P(x)/x=1/6+1/x`, strictly decreasing.

These symbolic identities reject those particular inductive cones.
They do NOT refute positivity of F_P, do not imply negativity of the
full triangular source, and do not rule out a different invariant.
Positivity or a usable complete-source upper estimate remains unproved.
No finite-prime sign statement was substituted for the all-prime input.
The already proved smoothing threshold for finite Mobius packets also
does not settle this Liouville resolvent: its square dilations must be
retained. No further no-go module was added.

### Scope of the newer critical-family positivity

The actual statements in `CompactCriticalSourceWeilPositivity`,
`SuzukiCriticalFamilyContraction`, and
`MultiScaleLowModeAndGridTentSchurBridge` were checked. In particular,
`DyadicScaleBlock S M` denotes a scale window, not the assertion that
every index is a power of two. Separate lacunary-family theorems have
additional hypotheses. No density claim or lack-of-density claim was
proved here. The missing energy-controlled approximation of the actual
PM source cannot be replaced by positivity on this family alone.

### Audit

No significant mathematical blocker was discharged. No closed paper
proof of a new admission estimate, Lean theorem, source edit, umbrella
edit, or compilation resulted. The work tested exact source mechanisms
but did not move the RH frontier. There were no web searches, novelty
checks, numerical experiments, subagents, added assumptions, or axioms.
All owned searches terminated before scratch cleanup. Goal remains
active; unresolved mathematics is not an external-state blocker.

## Existing quadrature proof formalized

The later completion request formalized the retained quadrature and short-head
proofs in four arithmetic-continuation leaves. Their direct source checks,
20-declaration standard-axiom audit, unique umbrella imports and indexed names
are complete; the certificate is on
[the formalized card](../3-formalized/leftovers/pm-long-modulus-quadrature.md).
No new signed-covariance estimate or contribution is claimed. Further research
is paused under the user's instruction.
