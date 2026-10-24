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
`../2-fully-proven/pm-long-modulus-quadrature.md`, with their complete paper
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
