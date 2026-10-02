# Logarithmically smoothed Möbius Fermi approximation

- **ID:** pm-log-smoothed-mobius-haar
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Route PM; raw-coefficient tail obstruction; exact linear mollifier/von Mangoldt convolution
- **Target:** Determine whether logarithmic smoothing yields literal Haar approximation, or identify its exact remaining arithmetic obstruction.
- **Novelty:** The coefficient convolution is already formal in the corpus. The proposed literal Fermi/Chebyshev head identity and its energy transfer need a separate applicability and novelty audit.

## Conjecture and scope

For `N≥2`, set `b_N(d)=μ(d) log(N/d)/log N`, `1≤d≤N`, and
`A_N^log(t)=-Σ b_N(d) φ_d(t)` for the actual Fermi generators. Test
`∫_(0,1] |h-A_N^log|² → 0` from unconditional source estimates.
Do not assume RH, zero simplicity, reciprocal-zeta bounds, or the desired error decay.
Failure of raw coefficients does not decide this modified sequence.

## Exact bridge to prove first

Let `ψ(x)=Σ_(n≤x) Λ(n)` and `K_N=Σ_(d≤N) μ(d) log(N/d)/d`.
Finite divisor regrouping should give, whenever `0≤x<N+1`,

`Σ_(d≤N) μ(d) log(N/d) floor(x/d) = log N · 1_(x≥1) + ψ(x)`.

The `n=1` divisor term is `log N`; every `n>1` term is `Λ(n)`.
All terms beyond `floor x` vanish. This is an exact real-floor statement, not an
extension from integer samples without proof.

Consequently, on `1/(N+1)<t≤1`,

`h(t)-A_N^log(t) = [2ψ(1/(2t))-ψ(1/t)]/log N`.

The reciprocal harmonic term `K_N/(t log N)` cancels under the literal Fermi
difference. The formula must retain the cutoff endpoint and the `n=1` target term.
This gives a concrete dyadic prime discrepancy to estimate. It does not bound the
remaining interval `0<t≤1/(N+1)`.

## Proof obligations

- [x] Real-floor logarithmic inversion, using existing divisor-convolution infrastructure (audited Lean).
- [x] Exact literal Fermi head identity, including the upper half of the unit interval (audited Lean).
- [x] Integrability and an exact head/tail energy decomposition (audited Lean).
- [ ] Identify a source-derived bound for the normalized dyadic prime-discrepancy energy.
- [ ] Control the complementary small-`t` tail without inserting a critical cancellation premise.
- [ ] Audit whether zero multiplicities obstruct this fixed smoothing before asserting it is an RH-equivalent sequence.
- [ ] Formalize every nontrivial positive survivor before retiring a failed subroute.

## Inspected evidence

- The preceding raw-coefficient card proves that exact growing head support alone
  cannot force norm convergence: its shrinking tail has a cofinal positive energy floor.
- Deep smoothing search completed with `partial=false`, no errors, complete source
  inventory; compiler metadata remains mostly pending/stale. All 20 candidate statements
  and 20 source-argument statements were reviewed. Its proposed ingredient set has no
  verified transfer from a smoothed scalar Möbius bound to the literal Haar norm.
- `Sieve/LinearMollifierVonMangoldt.lean` proves the exact short-range divisor identity
  `Σ_(d|k) μ(d)log(N/d)=Λ(k)` for `1<k≤N`.
- `Sieve/LevinsonLinearMollifier.lean` identifies the same logarithmic coefficient,
  with the critical Dirichlet-polynomial factor `n^(-1/2)` kept separate.
- `Sieve/MoebiusLogarithmicNormalization.tendsto_sum_moebius_log_div_one` proves
  `K_N→1`. This is scalar normalization, not a critical mean-square estimate.
- `PNTPlus/Consequences.mu_log_mul_zeta` and mathlib's
  `ArithmeticFunction.sum_moebius_mul_log_eq` supply the logarithmic convolution law.
- `MoebiusMollifiedCriticalMoment` and `MoebiusMollifiedErrorThreeLines` supply upper
  bounds with a growing critical-edge budget and strictly displaced interpolation.
  Their inspected statements do not produce convergence to zero at the critical edge.

## Log

- 2026-10-01 — candidate recorded while the raw-Fermi leaf undergoes final audits.
  A second deep search now targets the real-floor/Chebyshev identity. No new Lean code
  for logarithmic smoothing yet. RH remains unproved; the original goal stays active.
- The second deep search completed with `partial=false`, no errors and complete source
  inventory; all 20 candidate and 20 source-argument statements reviewed. It located
  `EulerDeletionLogMoebiusCellIdentity.physical_log_moebius_cell_eq_chebyshev` and its
  private integer-floor identity. Those prove the analogous exact discrete cell law,
  including a separate full divisor tail, but do not give the literal continuous Fermi
  energy bound. Their full initial-cell proof was inspected. Reuse the arithmetic
  convolution mechanism; do not claim the divisor identity itself as new. A third
  search targets a quantitative dyadic-Chebyshev mean-square producer.
- The third deep search completed with `partial=false`, no errors, complete source
  inventory; all 20 candidate and 20 source-argument statements reviewed. Returned
  integral comparison tools require a pointwise bound; the dyadic prime-window results
  require a `ChebyshevErrorPowerSpectrum` or equivalent source estimate. The returned
  half-plane equivalence and square-sampling RH receiver do not discharge that estimate.
  No independent bound for this literal squared discrepancy appeared in these hits.
- Scratch implementation has verified real-floor cell reduction, cutoff extension,
  logarithmic Möbius/Chebyshev inversion, and the floor-sum expression for the literal
  smoothed Fermi combination. Initial probe failed only on unconstrained universes in
  three generic API `have` lines; those are specialized to `ℝ`. The continuous Haar
  head identity is now being checked. No convergence or critical-energy claim is made.
- The exact continuous head identity now passes scratch Lean. The full energy splits into
  the unchanged small-`t` tail plus
  `(log N)^(-2) ∫_(1/(N+1),1] [2ψ(1/(2t))-ψ(1/t)]² dt`; measurability,
  integrability, and this exact decomposition are now being checked. This is an equality
  exposing two remaining source estimates, not an estimate that discharges either one.
- All 13 declarations, including integrability and the full energy decomposition, passed
  scratch Lean with empty diagnostics. New 217-line leaf `FermiNymanLogMobiusHead.lean`
  is wired and undergoing targeted build, final actual-leaf and axiom audits. The next
  corpus search targets Mellin/Plancherel and zero-expansion estimates for the Chebyshev
  mean square; it must distinguish a source estimate from a zero-location premise.

## Formal certificate for the exact source bridge

`formal/GaloisForLFunctions/RHTower/FermiNymanLogMobiusHead.lean`: 13 declarations,
217 lines. The two main theorems are `dyadicHaar_sub_logMobiusFermiApprox` and
`logMobiusFermiErrorEnergy_decomposition`. Their only restrictions are the literal
cutoff/domain conditions; no RH, zero simplicity or cancellation premise appears.

- Targeted `lake --old build +GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead:olean`
  passed; own leaf built in 201s, dependencies replayed.
- Final `lake env lean GaloisForLFunctions/RHTower/FermiNymanLogMobiusHead.lean`
  passed, exit 0 with empty diagnostics.
- All 13 declarations passed separate `#print axioms`: only `propext`, `Classical.choice`,
  `Quot.sound`. Both main theorem types checked. All 13 names unique outside this leaf.
- Leaf wired. Generated indexes refreshed; the subsequent global `lint --check-generated`
  found 13 unrelated unwired modules and concurrent generated-index drift. No own-leaf
  finding. Indexes refreshed again after the audit; final plain lint is recorded below.

The canonical convergence conjecture remains open. The Mellin/Plancherel search was
partial because its local judge returned malformed JSON; all 20 available candidate
and 20 source-argument statements were reviewed. Stronger returned Chebyshev power
bounds assume RH or a half-plane bound. The unconditional continuous input instead is
`integrableOn_chebyshevError_div_sq` from `MertensVonMangoldtEulerConstant`.
Together with `sum_abs_barbanVehovWeight_le_linear`, it supports the separate candidate
`pm-log-mobius-weighted-endpoint.md`: explicit approximation in `L²(t dt)`.
That card retains the extra weight and records the precise missing power for `L²(dt)`.

Final plain `scripts/formal_tools.py lint` exits 1 solely for the same 12 unrelated
unwired modules listed on `5-failed/pm-raw-mobius-haar-tail-floor.md`; no proof-debt or
own-leaf finding. All owned completed scratch, search and audit files were cleaned.
No full/umbrella build, numerical experiment, new axiom, hole, heartbeat increase,
commit or push. The original RH goal remains active.


2026-10-01 — the separate weighted candidate is now fully formalized in
`3-formalized/pm-log-mobius-weighted-endpoint.md`: unconditional error convergence
in `L²(t dt)` with explicit rate. Two leaves / 23 declarations passed targeted
build, final direct leaf and standard-axiom audits. This canonical card remains
open. The now-formalized `3-formalized/pm-log-mobius-auxiliary-variance.md` exposes the exact
finite arithmetic variance needed for the stronger norm. The scalar source theorem
`B_N→1` alone does not control that variance at its critical scale.


2026-10-01 — exact canonical auxiliary variance and its mean/variance split now
formalized in `FermiNymanLogMobiusAuxiliaryVariance`, using the new general finite-
coefficient error leaf. All 31 declarations passed target build, final actual-leaf
and standard-axiom audits. No upper estimate follows from the scalar limit alone.
Four complete source searches returned no independent critical producer. Next
paper audit: `pm-weighted-source-input-power-boundary.md`; its explicit power
family tests the available analytic inputs and retains a sharp positive variance
classification. This actual logarithmic arithmetic candidate remains open.


2026-10-01 — the analytic-input inference is now disproved and its positive
variance classification fully formalized in three `PMAnalyticPower*` leaves
(46 declarations, all target/direct-leaf/standard-axiom audits passed). See
`5-failed/pm-weighted-source-input-power-boundary.md`. This rules out obtaining the
missing canonical estimate solely from the analytic inputs already used; it says
nothing negative about this literal arithmetic approximation. Next arithmetic
input audit: `pm-selberg-recursion-power-response.md`.


2026-10-01 — queued audit of the existing multiplicity obligation: the exact
canonical scalar normalization term may be more restrictive than RH. Proposed
mechanism, not proved: a multiple critical zero gives a higher-order singularity
in the Mellin transform of the logarithmic Möbius normalization, whereas the
prime-profile mean has only the corresponding logarithmic-derivative pole.
The necessary normalization budget from PM-26 could then force critical zeros
to be simple. A corpus query for logarithmic Möbius approximation, critical norm
and multiplicity is running before accepting this argument or writing Lean.
No contour expansion, Mellin continuation, or simplicity implication is assumed.
The original approximation conjecture remains open.


Multiplicity audit — proposed analytic mechanism (unverified): extend
`B(x)=Σ_(d≤x) μ(d)log(x/d)/d` continuously in real `x`, and let
`m(x)=x⁻¹∫_0^x ψ(t)/t dt`. The formal PM-26 budget would imply
`B(N)−m(N+1)=o(log N/√N)` if the canonical error tends to zero. Elementary
cell-increment bounds should transfer this to real `x`. For `Re s>0`, the
proposed exact Mellin transform of their difference is

`F(s)=1/[s²ζ(1+s)] + ζ'(1+s)/[(1+s)²ζ(1+s)]`.

The little-o budget would extend the literal integral to `Re s>−1/2` and force
`ε² F(ρ−1+ε)→0` for a critical zero `ρ`, by an Abelian split of the integral.
If `ρ` has multiplicity at least two, the numerator after clearing the common
denominator is `(1+s)²+s²ζ'(1+s)`, equal to `ρ²≠0` at `s=ρ−1`; the transform
therefore has a pole of order at least two, contradicting that limit.

Required gates before claiming this: exact continuous coefficient transform;
prime-mean transform with both denominator factors; discrete-to-real budget;
analytic continuation from the literal integral; boundary Abelian estimate;
analytic-order comparison; and corpus/novelty audit. These are obligations,
not assumed theorems. No new Lean for this conjecture.


2026-10-01 — PM-28 coarse Selberg-input inference is disproved and its exact
positive operator-response survivor fully formalized. Three leaves / 45
declarations passed all targeted/direct-leaf/standard-axiom audits. The same
analytic power model obeys both inequalities with unchanged constants but
retains arbitrary-centering divergence. See
`5-failed/pm-selberg-recursion-power-response.md`. This actual arithmetic
approximation remains open; the multiplicity obligation above remains pending.

Multiplicity query completed: `partial=false`, no errors, complete 63,604-file
inventory. All 20 candidate and 20 source statements reviewed. Most returned
zero-valued coefficients or unrelated critical norms; the proposed ingredient
set does not address multiplicity of zeta zeros. No simplicity implication was
found in these hits. A narrower Mellin/pole-order audit is still needed.

A targeted source search found an existing related result: read
`MobiusLaplaceBoundaryMultiplicity.lean` lines 1–36 and 216–325. Exact half-power
decay of the discrete Möbius–Laplace source already implies RH and boundary
simplicity. Its proof propagates a denominator-free Mellin identity and combines
a radial Abel bound with vanishing zeta slope. This does not by itself apply to
the current logarithmic Fermi coefficients: the literal coefficient/mean
transform and its weaker little-o logarithmic budget remain new transfer
obligations. Do not claim the general Abel/multiplicity mechanism as new.

Narrower Mellin query completed: `partial=false`, no errors, 63,609-file
inventory; all 20 candidates and 20 source statements inspected. It returned
`ChronologicalWeightedMellin.chronologicalMobiusWeightedSource_mellin`, a general
Möbius-weighted source transform equal to `mellin(w)/ζ(s)` on `Re s>1`. Its
literal source definition and applicability to the current logarithmic ramp
still need inspection. The proposed Fourier ingredient set does not supply the
missing coefficient identity or boundary estimate.

Read `ChronologicalWeightedMellin.lean` lines 1–158, including full absolute
interchange proof and finite-cutoff source identity, and all of
`Sieve/MoebiusShiftedLogRealCutoff.lean`. The latter already defines the real
coefficient sum `moebiusShiftedLogKernelReal 0 x`. For
`w(t)=log(1/t)/t` on `(0,1]`, zero outside, the literal identity should be
`B(1/t)=t·chronologicalMobiusWeightedSource(w)(t)`. Thus the existing general
Mellin theorem at parameter `s+1` should yield `1/[s²ζ(s+1)]` after proving
the elementary ramp integral and finite-sum equality. Bounded-weight corollaries
do not apply to this unbounded ramp; only the theorem requiring its actual
Mellin convergence is proposed for reuse.


2026-10-01 — PM-29 hypothetical sublinear-response inference is now disproved
and its positive affine-response/unique-amplitude classification formalized:
32 declarations in two leaves, all targeted/direct-leaf/standard-axiom audits
passed. See `5-failed/pm-selberg-sublinear-response-boundary.md`. The actual
fixed-coefficient multiplicity obligation is tracked in
`pm-log-mobius-boundary-multiplicity.md`; its first Mellin ingredient scratch
is under verification, with no simplicity implication or RH conclusion yet.

2026-10-01 — First PM-30 ingredient completed: `PMLogMobiusMellinPair`
identifies the literal real-cutoff sum and proves its exact Mellin pair, including
absolute convergence. All 11 declarations passed targeted build, final direct
actual-leaf and standard-axiom audits; wiring/API/index checked. General
arithmetic dilation interchange also passes Lean, with its bookkeeping audit
pending. Prime-mean, discrete-to-continuous, continuation and quadratic Abel
transfers remain open; no simplicity or RH conclusion.

PM-30 completed: six audited leaves / 64 declarations prove that convergence
of this fixed logarithmic approximation forces every critical zeta zero simple.
The literal transforms, continuous scalar budget, analytic continuation and
quadratic Abel limit are certified. Card: `3-formalized/pm-log-mobius-boundary-multiplicity.md`.
Canonical convergence and RH remain unproved; the result is a necessary condition.

PM-31 alternate source: `PMPowerDampedMobiusSource` now certifies the literal
power-damped family, its pointwise Haar limit, exact Chebyshev first derivative,
and canonical `MemLp` admission for `ε>1/2`. All 14 declarations / 250 lines passed
leaf/build/standard-axiom audits. Admission for arbitrarily small positive damping
remains open. Card: `pm-power-damped-mobius-haar.md`.

PM-31 Mellin ingredient also completed: `PMPowerDampedMobiusMellin` adds 200
lines / 14 audited declarations. The literal transform is exactly
`(1−2^(1−s))ζ(s)/(sζ(s+ε))` on its absolute-convergence strip. Explicit canonical
`MemLp` gives absolute Mellin convergence and analyticity on `Re s>1/2`.
Combined PM-31 certificate: fifteen leaves / 3595 lines / 226 declarations.
`PMPowerDampedMobiusCriterion` now proves the pole-cleared continuation and
cofinal-admission RH receiver, with all five declarations fully audited. Under
`¬RH`, a whole interval of small positive dampings fails canonical admission.
The actual small-damping estimate remains open; no unconditional RH claim.

PM-31 prefix-energy ingredient fully audited: `PMPowerDampedMobiusPrefixEnergy`
transfers the existing full modular norm to the literal Fermi source and proves
unconditional `O(N/log(N)^q)` square-energy bounds for every fixed positive
integral order. `PMPowerDampedMobiusEndpoint` now certifies unconditional
admission at `ε=1/2` and hence every `ε≥1/2` (246 lines / 12 declarations).
Targeted build, final actual-leaf, standard-axiom and exhaustive API/body/name/import
audits passed. Arbitrarily small positive damping remains open.

PM-31 exact Gram diagonal fully audited: `PMPowerDampedMobiusGramDiagonal`,
259 lines / 18 declarations. Each generator has squared norm `log(2)/a`;
the damped Möbius diagonal is summable for every positive damping. Positive
blocks disprove every coefficient-independent fixed diagonal ceiling. Actual
Möbius cross-term control and arbitrarily small canonical admission remain open.

PM-31 prime-contraction no-go closed with a positive survivor: canonical
prime cutoffs must sometimes increase norm arbitrarily near zero damping, and
every limiting uniform norm budget is at least one. All 19 new declarations
passed targeted/direct-leaf/standard-axiom and exhaustive source/API audits.
Card: `../5-failed/pm-power-damped-prime-contraction.md`. Finite budgets allowing
this growth and small-positive-damping admission remain open.

PM-31 large-damping asymptotic fully audited: `PMPowerDampedMobiusLargeDamping`
proves `2^ε(E_ε−log 2)→−2κ` with `κ≥1/12`, hence actual canonical norm growth
beyond every damping threshold. The proposed eventual damping monotonicity is
retired with this positive survivor on `5-failed/pm-power-damping-monotonicity.md`.
The unit upper budget and small-positive canonical admission remain open.

PM-31 exact mean fully audited: `PMPowerDampedMobiusMean` (203 lines / 12
declarations) proves canonical L¹ admission at every positive damping, mean
`log 2/ζ(1+ε)`, and mean/ε→log 2. For an admitted L² source, the exact Haar-error
identity is `error²=source²−1+2 Re(mean)`. No unit budget or small-positive L²
admission follows yet. Next: certify the paper-proved canonical L¹ error bound
`||A_ε−Haar||₁≤Cε` from shrinking raw-prefix support and finite Abel sums.

PM-31 canonical L¹ convergence fully audited: `PMPowerDampedMobiusL1Convergence`
(260 lines / 19 declarations) proves `||A_ε−Haar||₁≤Cε`, where the explicit
constant `C=Σ_n ||R_n−Haar||₁/n` is finite. Shrinking raw-prefix support converts
the known L² logarithmic savings to this reciprocal L¹ budget; finite Abel
sums and Fatou transfer it to the literal source. Small-positive L² admission
remains open. Next: the canonical L¹ derivative and its distinct L² boundary.

- PM-31 derivative audit closed: `PMPowerDampedMobiusDerivative` (304 lines /
  29 declarations) passed targeted old build, final actual leaf, every axiom
  report (standard three only), exact body/API/name/unique-import gates.
  The actual difference quotients converge in canonical L¹ to the dyadic
  Chebyshev source, whose signed integral is log 2. Combined: twelve audited
  leaves / 2917 lines / 181 declarations. Small-positive L² admission and RH
  remain open; the derivative's proposed L² exclusion is not yet certified.

- PM-31 Hilbert-tangent obstruction audit closed: two additional leaves,
  `PMPowerDampedMobiusDerivativeMellin` (153/10) and
  `PMPowerDampedMobiusDerivativeBoundary` (226/6), passed targeted builds,
  both final actual leaf checks, every standard-axiom report, exact body,
  exhaustive name, public API and unique-import audits. Combined PM-31:
  fourteen fully audited leaves / 3296 lines / 197 declarations. The exact
  strong L¹ Chebyshev tangent is outside canonical L²; actual quotient norms
  exceed every finite budget arbitrarily near zero. Closed failed card:
  `5-failed/pm-power-damping-hilbert-tangent.md`, retaining the positive L¹
  convergence and exact mean log 2. Small-positive L² admission and RH remain
  open. Next: exact prime-two-deleted Haar resolvent and the all-subset unit
  ceiling, tracked in `pm-dyadic-prime-deletion-unit-budget.md`.

- Dyadic resolvent ingredient fully audited: `PMPowerDampedMobiusDyadicResolvent`
  (299 lines / 29 declarations), targeted old build 18s, final actual leaf empty,
  all standard-axiom/body/name/API/unique-import gates passed. Exact canonical
  energy 2, mean 0, norm sqrt 2 and pointwise support/recurrence uniqueness are
  certified. Combined PM-31: fifteen leaves / 3595 lines / 226 declarations.
  Odd-Möbius identification and all-subset budget obstruction remain pending;
  no closure of the prime-deletion no-go yet. Small-positive L² admission and
  RH remain open. Latest lint: twelve unrelated unwired modules and concurrent
  LEAN_API staleness; no owned or proof-debt finding.

- PM-31 prime-two deletion audit closed: `PMPowerDampedMobiusDyadicDeletion`
  (257 lines / 26 declarations), targeted old build 7.3s, final actual leaf
  empty, all bodies/names/API/unique-import/standard-axiom gates passed.
  The literal odd-Mobius source equals the Haar resolvent: canonical L2,
  exact energy 2, mean 0, norm sqrt 2. Every finite-prime all-subset budget
  below sqrt 2 fails arbitrarily near zero damping, with admitted actual
  finite sources as witnesses. Moved `pm-dyadic-prime-deletion-unit-budget`
  to `5-failed`, preserving the fully proved positive survivor. Combined:
  sixteen leaves / 3852 lines / 252 audited declarations. Latest global lint:
  twelve unrelated unwired modules; no owned or proof-debt finding.
  Next conjecture: `pm-finite-prime-deletion-energy` tests whether every
  finite all-subset budget fails via the nonnegative Haar Gram kernel and
  smooth-number harmonic energy. Canonical full cutoffs and RH remain open.

- PM-31 Haar Gram leaf fully audited: `PMPowerDampedMobiusHaarGram`
  (211 lines / 26 declarations), targeted old build 152s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  It proves K(a,b)=max(0,2/max(a,b)-1/min(a,b)), finite Haar-sum energy,
  diagonal lower bounds and energy monotonicity under finite inclusion.
  Combined PM-31: seventeen leaves / 4063 lines / 278 audited declarations.
  Latest lint: thirteen unrelated unwired modules; no owned/proof-debt finding.
  Hilbert-series scratch1045 is checking; smooth-source scratch1046 is
  prepared but unrun. The stronger all-subset budget no-go is not closed.
  Canonical small-positive admission and RH remain open.

- PM-31 Hilbert-series leaf fully audited: `PMPowerDampedMobiusHaarSeries`
  (151 lines / 16 declarations), targeted old build 92s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Summable dilation norms identify the actual pointwise series with its
  Hilbert sum; exact energy is the iterated Gram sum and dominates every
  finite reciprocal diagonal. Combined: eighteen leaves / 4214 lines /
  294 audited declarations. Latest global lint: seventeen unrelated unwired
  modules and three concurrently stale generated files; no owned or proof-debt
  finding. Sixteen-declaration smooth-source scratch1046 checks next;
  nine-declaration arithmetic scratch1047 is prepared and unrun. The broader
  no-go and canonical small-positive admission/RH remain open.

- PM-31 smooth-source leaf fully audited: `PMPowerDampedMobiusSmoothHaar`
  (147 lines / 16 declarations), targeted old build 4.6s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Each fixed smooth-number Haar source is canonically L2/L1, supported in
  (0,1], with zero mean and exact nonnegative Gram energy. Its energy
  dominates the harmonic sum and diverges with the prime cutoff. Combined:
  nineteen leaves / 4361 lines / 310 audited declarations. Latest global
  lint: ten unrelated unwired modules and three concurrent generated-file
  changes; no owned/proof-debt finding. Full 23-declaration arithmetic/budget
  scratch1047 checks next. The broader all-subset no-go is not closed yet.
  A separate paper candidate `pm-canonical-prime-aperture-threshold` tests
  divergence at fixed epsilon<1/2 even for canonical prime cutoffs, paired
  with explicit all-subset bounds for epsilon>1/2. No Lean proof of that
  stronger candidate is claimed. Actual small-positive admission/RH stay open.

- PM-31 arithmetic/deletion leaf fully audited: `PMPowerDampedMobiusFiniteDeletion`
  (283 lines / 23 declarations), targeted old build115s, final actual leaf empty,
  every exact-body/name/API/unique-import/standard-axiom gate passed. Literal
  deleted Mobius sources equal smooth Haar sums. For every finite budget and
  every positive damping neighborhood, an admitted actual finite prime source
  exceeds that budget. Combined: twenty leaves / 4644 lines / 333 declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The strongest arbitrary-finite-set
  positive survivor is prepared in scratch1050 (22 declarations), now checking.
  No-go closure awaits that exact generality; actual small-positive admission
  and unconditional RH remain open.

- PM-31 arbitrary finite-deletion survivor fully audited:
  `PMPowerDampedMobiusFiniteSmoothSource` (220 lines / 22 declarations), targeted
  old build7.7s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For every finite E, the literal deleted-Mobius
  source equals its strongly summable smooth Haar series, is canonically L2/L1,
  has zero mean and exact nonnegative double-Gram energy, with reciprocal Euler
  product diagonal lower bound. Combined: twenty-one leaves / 4864 lines /
  355 audited declarations. Global lint: thirteen unrelated unwired modules
  and two concurrently stale generated files; no owned/proof-debt finding.
  Retired `pm-finite-prime-deletion-energy`: every finite all-subset bound
  uniform in damping near zero is impossible, with the exact arbitrary-finite-E
  positive survivor now on paper and in Lean. This does not exclude a finite
  C(epsilon), canonical-only bounds, or actual small-positive admission.
  Next candidate: `pm-canonical-prime-aperture-threshold`; scratch1051 checks
  the upper boundary and real Euler decay, while1053/1055 remain unrun.
  Unconditional RH/negRH remain unproved.

- PM-31 canonical prime threshold fully audited: `PMPowerDampedMobiusPrimeThreshold`
  (436 lines / 22 declarations), targeted old build197s, final actual leaf empty,
  all exact-body/name/API/unique-import/standard-axiom gates passed. For every
  fixed0<epsilon<1/2, canonical prime-aperture norms tend to infinity and
  eventually exceed every finite budget. The exact positive survivor is the
  explicit common finite budget `3 sum_d d^(-epsilon-1/2)` for epsilon>1/2,
  valid for every finite integer aperture, together with the proved finite
  Mellin identity and bounded-cofinal Mellin transfer. Endpoint1/2 unclassified.
  Combined: twenty-two leaves /5300 lines /377 audited declarations. Latest
  global lint: eleven unrelated unwired modules and two concurrently stale
  generated files; no owned/proof-debt finding. Retired canonical prime-budget
  producer with the strict-interval classification fully proved on paper and
  in Lean. Actual source admission at arbitrarily small positive damping and
  unconditional RH/negRH remain open. Next card:
  `pm-centered-divisor-haar-criterion`, an exact mean-centered discrepancy
  energy criterion with paper argument and corpus audit; no new Lean yet.

- PM-31 centered-divisor arithmetic leaf fully audited:
  `PMPowerDampedMobiusDivisorHaar` (295 lines /29 declarations), targeted old
  build24s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. Positive divisor coefficients have exact
  Euler factors; their summatory mean is `1/zeta(1+epsilon)`. The actual
  Fermi source is both a finite weighted Haar sum and the dyadic difference
  of its mean-centered reciprocal summatory remainder. The backward boundary
  vanishes and the finite dyadic sums converge pointwise to that literal
  centered source. Combined: twenty-three leaves /5595 lines /406 audited
  declarations. Global lint has ten unrelated unwired modules and three
  concurrently stale generated files; no owned/proof-debt finding.
  Scratch1063 now checks reverse L2 admission with constant `1+sqrt2`,
  forward admission, and reciprocal weighted-energy equivalence. The actual
  small-positive arithmetic energy bound remains open; RH/negRH unproved.

- PM-31 centered-energy criterion fully audited:
  `PMPowerDampedMobiusCenteredEnergy` (226 lines /22 declarations), targeted
  old build119s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For epsilon>0, actual Fermi-source canonical
  L2 admission is equivalent to integrability of the literal centered divisor
  discrepancy squared against dx/x^2. Backward finite-sum norms have the
  explicit bound (1+sqrt2) times the source norm; Fatou identifies the actual
  boundary-normalized remainder. The reciprocal energy identity, inherited
  epsilon>=1/2 admission, and cofinal weighted-energy RH receiver are proved.
  Combined: twenty-four leaves /5821 lines /428 audited declarations.
  Global lint has eleven unrelated unwired modules and three concurrently
  stale generated files; no owned/proof-debt finding. The energy receiver's
  small-positive premise remains open. New producer card:
  `pm-centered-divisor-dyadic-energy-budget`; scratch1068 checks the exact
  pointwise absolutely summable damped Nyman/fractional-part representation.
  No RH/negRH proof or small-positive geometric energy bound is claimed.

- PM-31 literal Nyman-series leaf fully audited:
  `PMPowerDampedMobiusNymanSeries` (95 lines /11 declarations), targeted old
  build34s, final actual leaf empty, every exact-body/name/API/unique-import/
  standard-axiom gate passed. The centered discrepancy is the negative
  damped fractional-part series, pointwise absolutely summable at every
  positive damping and positive physical time. Its natural integer prefixes
  converge pointwise to the actual centered source; the density is real.
  Combined: twenty-five leaves /5916 lines /439 audited declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The actual small-positive
  dyadic/cumulative energy bound remains open. Next: exact unrestricted
  discrete weighted-energy/covariance bridge, then the signed arithmetic
  bound. No global L2 interchange or RH/negRH proof is asserted.

- PM-31 unrestricted discrete-energy leaf fully audited:
  `PMPowerDampedMobiusDiscreteEnergy` (224 lines /18 declarations), targeted
  old build143s, final actual leaf empty, every exact-body/name/API/unique-
  import/standard-axiom gate passed. Unit-cell integrability and countable
  assembly remove the old bounded-sequence premise. For every epsilon>0,
  actual canonical admission is equivalent to summability of
  D_epsilon(n)^2/(n(n+1)), where D is the cumulative centered divisor
  coefficient. Equivalently, its exact finite signed maximum-index
  covariance has a common bound in the cutoff. The epsilon>=1/2 range is
  unconditional; cofinal small-positive budgets would imply RH but remain
  unproved. Combined: twenty-six leaves /6140 lines /457 audited declarations.
  Global lint reports eleven unrelated unreachable modules; no owned or
  proof-debt finding. No RH/negRH proof is claimed.

- PM-31 positive-divisor Haar prefix leaf fully audited:
  `PMPowerDampedMobiusPositiveHaarPrefix` (239 lines /21 declarations),
  targeted old build64s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. The exact clipped
  counts give stabilization to the actual source and the initial plateau
  -C_epsilon(N), with energy contribution C_epsilon(N)^2/(2N). Rescaled
  prefixes converge pointwise to alpha_epsilon times the universal boundary
  profile beta, with common 3min(1,1/u) envelope. Each finite prefix has zero
  integral. Combined: twenty-seven leaves /6379 lines /478 declarations.
  Strong L2 profile/leading energy is checking in scratch1080; do not retire
  this cutoff candidate until that positive survivor is fully audited.
  Actual small-positive source admission and RH remain open. Global lint:
  eleven unrelated unwired modules and concurrent generated-document
  staleness, no owned or proof-debt finding.

- PM-31 universal boundary profile fully audited: `PMPowerDampedMobiusHaarBoundaryProfile`
  (292 lines /19 declarations), targeted old build46s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Rescaled raw positive-Haar prefixes converge strongly in
  L2 to alpha_epsilon*beta; integral beta^2=2-2log2 and integral beta=-log2.
  Their energy divided by the cutoff tends to the strictly positive
  |alpha_epsilon|^2*(2-2log2), so raw-prefix common budgets fail at EVERY
  positive damping. Their L1 error is at least |alpha_epsilon*log2|.
  This does not refute actual-source admission. The exact positive survivor
  closes this no-go; the raw cutoff card is retired. Combined: twenty-eight
  leaves /6671 lines /497 audited declarations. Follow-up: centered Haar
  cutoff/endpoint-trace criterion; the small-positive signed energy
  producer and RH remain open. Global lint: eleven unrelated unwired
  leaves and concurrently stale generated docs, no owned/proof-debt finding.

- PM-31 clipped Haar source fully audited: `PMPowerDampedMobiusClippedHaarSource`
  (242 lines /22 declarations), targeted old build49s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Subtracting alpha_epsilon*N*beta(Nt) gives exactly the
  dyadic difference of R_epsilon(min(N,1/t)); every finite corrected
  prefix is admitted and stabilizes pointwise to the actual source.
  Its primitive energy is exactly truncated divisor energy plus
  |R_epsilon(N)|^2/N. Generic dyadic difference norms lie between
  (sqrt2-1)||f|| and (sqrt2+1)||f||. Combined: twenty-nine leaves /6913
  lines /519 audited declarations. The endpoint convergence and cofinal
  selection proofs are in scratch, not yet certified. Small-positive
  arithmetic admission remains open. Global lint: ten unrelated unwired
  modules and stale LEAN_GAPS/LEAN_OVERVIEW, no owned/proof-debt finding.

- PM-31 cutoff trace/cofinal criterion fully audited:
  `PMPowerDampedMobiusHaarCutoffTrace` (324 lines /16 declarations),
  targeted old build15s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. Under actual
  admission, both clipped-primitive and density-repaired-prefix L2
  convergence are equivalent to |R_epsilon(N)|^2/N tending to zero.
  Actual admission supplies a strict cofinal trace-zero sequence, and is
  equivalent to a common cofinal repaired-prefix norm budget. The exact
  criterion card moves to formalized. Combined: thirty leaves /7237 lines
  /535 audited declarations. Full-sequence endpoint-atom correction is
  the next paper-proved conjecture; actual small-positive energy admission
  and RH remain open. Global lint: ten unrelated unwired leaves, all three
  generated docs concurrently stale, no owned/proof-debt finding.

- Endpoint correction fully audited: `PMPowerDampedMobiusEndpointHaar`
  (215 lines /17 declarations), targeted old build294s, final actual-leaf
  check with empty diagnostics, all17 standard-axiom reports, exact body,
  exhaustive names/API, unique import and proof-debt checks passed. Its
  exact truncated-source identity removes the endpoint trace, giving
  full-integer-cutoff L2 convergence under actual admission and an exact
  full-sequence energy-budget criterion. Global lint still reports twelve
  unrelated unwired leaves, no owned/proof-debt issue. Combined: thirty-one
  leaves /7452 lines /552 audited declarations. The actual small-positive
  signed energy bound remains open. Next: divisor second-moment density.

- Second-moment density fully audited: `PMPowerDampedMobiusSecondMoment`
  (268 lines /18 declarations), targeted old build36s, final actual-leaf
  check with empty diagnostics, all18 standard-axiom reports, exact body,
  exhaustive names/API, unique import and no-proof-debt checks passed.
  It proves the literal coefficient square's summatory mean and Euler
  product, the centered mean-square gamma-alpha^2>=0, and gamma<=alpha.
  Combined: thirty-two leaves /7720 lines /570 audited declarations.
  Strict positivity, small-damping variance and the logarithmic signed
  covariance calibration remain on the second-moment card. The actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  has eleven unrelated unwired leaves and three generated freshness
  findings; no owned or proof-debt finding, no global pass claimed.

- Signed covariance calibration fully audited:
  `PMPowerDampedMobiusCovarianceCancellation` (269 lines /17 declarations),
  targeted old build7.8s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The variance is strictly positive
  at every positive damping. The actual centered diagonal/log N tends to
  this variance and has no common finite budget, including the admitted
  safe range. The exact off-diagonal/log N tends to its negative under
  actual admission, unconditionally at epsilon>=1/2. Combined: thirty-three
  leaves /7989 lines /587 audited declarations. Small-damping variance
  asymptotic is drafted; the canonical small-positive energy bound and RH
  remain open. Global lint has twelve unrelated unwired leaves and stale
  API/overview, no owned/proof-debt finding; no global pass claimed.

- Small-damping variance refinement fully audited:
  `PMPowerDampedMobiusSmallDampingVariance` (251 lines /17 declarations),
  targeted old build76s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The exact Euler correction
  tends to one; gamma_epsilon/epsilon and v_epsilon/epsilon both tend to
  1/2 as epsilon->0+. All pole identities use positive damping.
  Combined: thirty-four leaves /8240 lines /604 audited declarations.
  The coefficient second-moment card is now formalized; the actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  reports ten unrelated unwired leaves, no generated freshness error and
  no owned/proof-debt finding; no global pass claimed. Next candidate:
  natural-denominator Ramanujan expansion and its anchored energy budget.

- Actual Ramanujan expansion fully audited:
  `PMPowerDampedMobiusRamanujanExpansion` (245 lines /21 declarations),
  targeted old build37s, final actual-leaf check with empty diagnostics,
  all21 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The literal coefficient has an
  absolutely convergent Ramanujan expansion; centered natural-denominator
  prefixes converge, as do every fixed cumulative sum and finite energy.
  A common cutoff-energy budget would give actual PM admission, but that
  budget remains unproved. Combined: thirty-five leaves /8485 lines /625
  audited declarations. Global lint reports eleven unrelated unwired
  leaves and stale API/overview, no owned/proof-debt finding; no global
  pass claimed. The explicit multiple-weight Euler formula has a paper
  proof and a draft Lean proof, not yet checked. RH remains open.

- Actual Ramanujan weights fully audited:
  `PMPowerDampedMobiusRamanujanWeights` (230 lines /17 declarations),
  targeted old build160s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. The coefficient is exactly
  alpha*mu(q)/product_(p|q)(p^(1+epsilon)-1), is real with Mobius-aligned
  sign, and has total absolute mass one. These are unconditional for
  every positive damping, including nonsquarefree vanishing and q=0.
  Combined: thirty-six leaves /8715 lines /642 audited declarations.
  Global lint reports twelve unrelated unwired leaves, no owned or
  proof-debt finding; no global pass claimed. The finite cofactor rewrite
  is checking next. No small-positive anchored energy budget or RH proof.

- Actual Ramanujan cofactors fully audited:
  `PMPowerDampedMobiusRamanujanCofactors` (286 lines /18 declarations),
  targeted old build49s, final actual-leaf check with empty diagnostics,
  all18 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. Natural-denominator cumulative
  prefixes are exactly finite cofactor-weighted fractional-part sums,
  with exact density cancellation. Absolute multiples inversion gives
  the exact mass on squarefree multiples; cofactors preserve Mobius
  signs and have norm at most d^(-epsilon). Combined: thirty-seven
  leaves /9001 lines /660 audited declarations. Global lint has ten
  unrelated unwired leaves and no owned/proof-debt finding; no global
  pass claimed. A proposed logarithmic coefficient-square comparison
  remains unproved; its summable coefficient side is being checked.
  No small-positive anchored energy budget or RH proof.

- Actual Ramanujan logarithmic square mass fully audited:
  `PMPowerDampedMobiusRamanujanLogMass` (59 lines /5 declarations),
  targeted old build47s, final actual leaf empty, all5 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Pointwise |a(q)|<=q^(-1-epsilon); the proposed
  logarithmic square mass is dominated by
  (2^epsilon/epsilon)*q^(-1-epsilon), hence summable for every positive
  damping. Combined: thirty-eight leaves /9060 lines /665 audited
  declarations. Global lint has eleven unrelated unwired leaves, no
  owned/proof-debt finding; no global pass claimed. The energy
  comparison remains unproved. The actual primitive-period mean is
  the next check; no small-positive energy bound or RH proof.

- Actual Ramanujan primitive fully audited:
  `PMPowerDampedMobiusRamanujanPrimitive` (206 lines /18 declarations),
  targeted old build37s, final actual leaf empty, all18 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive is periodic and bounded for q>1. Its
  exact period mean is -phi(q)/2, also its Cesaro and logarithmic
  harmonic limits. Combined: thirty-nine leaves /9266 lines /683
  audited declarations. Global lint has twelve unrelated unwired
  leaves, no owned/proof-debt finding; no global pass claimed. The
  fixed-q prime Gram asymptotic is checking next. No common cutoff
  energy comparison, small-positive admission or RH proof.

- Actual primitive Gram fully audited:
  `PMPowerDampedMobiusRamanujanGram` (188 lines /13 declarations),
  targeted old build9.9s, final actual leaf empty, all13 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Every fixed pair is absolutely summable; for fixed
  q>1, K(p,q)/log(p)->phi(q)/2 along primes. The exact harmonic head
  has a tail error bounded by the finite-period primitive norm bound.
  Combined: forty leaves /9454 lines /696 audited declarations.
  Lint1129 has fourteen unrelated unwired modules and two shared
  generated-file staleness findings after concurrent changes; no owned
  or proof-debt finding and no global pass claimed. Finite signed Gram
  reduction draft1128 is next; common quadratic bound, small-positive
  admission and RH remain unproved.

- Actual finite signed Ramanujan quadratic fully audited:
  `PMPowerDampedMobiusRamanujanQuadratic` (107 lines /12 declarations),
  targeted old build238s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Each fixed natural denominator cutoff has finite
  total energy equal to its exact signed primitive Gram quadratic.
  The common Q,T energy budget is equivalent to a common Q bound
  on those literal quadratic forms. Combined: forty-one leaves
  /9561 lines /708 audited declarations. Lint1132 has ten unrelated
  unwired modules and three shared generated-file staleness findings;
  no owned/proof-debt finding and no global pass claimed.
  First-moment/centering draft1133 is checking. Uniform quadratic
  upper bound, small-positive admission and RH remain unproved.

- Actual primitive reciprocal first moment fully audited:
  `PMPowerDampedMobiusRamanujanMoment` (200 lines /17 declarations),
  targeted old build43s, final actual leaf empty, all17 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive first moment under reciprocal energy
  weights is exactly -Lambda(q), and their mass is1. Period centering
  yields the explicit totient/Lambda correction; energy centering
  R_q+Lambda(q) has weighted mean0 and splits K into Lambda(p)*Lambda(q)
  plus its centered Gram. Combined: forty-two leaves /9761 lines /725
  audited declarations. Lint1135 has eleven unrelated unwired modules
  and two shared generated-file staleness findings; no owned/proof-debt
  finding and no global pass claimed. Actual finite variance reduction
  and centered mixed-Gram law draft1136 are checking. No uniform actual
  variance bound, small-positive admission or RH proof.

- Actual finite energy-centered variance fully audited:
  `PMPowerDampedMobiusRamanujanVariance` (129 lines /12 declarations),
  targeted old build43s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Actual weighted mean M has a common finite bound at
  each positive damping; G=M^2+V with V>=0, and common Gram/variance
  budgets are equivalent. Centered prime Gram/log(p) tends to
  phi(q)/2-Lambda(q), so logarithmic cross terms survive centering.
  Combined: forty-three leaves /9890 lines /737 audited declarations.
  Lint1139 has twelve unrelated unwired modules and two shared
  generated-file staleness findings; no owned/proof-debt finding and
  no global pass claimed. Absolute natural-cutoff control for damping
  above1/2 is checking in draft1140. Uniform small-positive variance
  upper bound, admission and RH remain unproved.

- Strict absolute natural-denominator budget fully audited:
  `PMPowerDampedMobiusRamanujanAbsolute` (111 lines /7 declarations),
  targeted old build103s, final actual leaf empty, all7 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Common Q,T energy, Gram and centered-variance bounds
  hold for epsilon>1/2 by the exact cofactor fractional-part bound and
  two convergent power sums. No assertion at epsilon<=1/2.
  Combined: forty-four leaves /10001 lines /744 audited declarations.
  Lint1144 has ten unrelated unwired modules; no owned/proof-debt
  finding and no global pass claimed. Endpoint transfer via finite
  Dirichlet convolution remains a paper candidate. Small-positive
  admission and RH remain unproved.

- Exact finite Ramanujan-to-Mobius prefix transfer fully audited:
  `PMPowerDampedMobiusRamanujanTransfer` (132 lines /14 declarations),
  targeted old build55s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Cofactor Fermi prefix equals the triangular sum of
  actual dilated Mobius prefixes with the explicit convolution kernel;
  no norm bound inferred before the kernel-mass audit.
  Combined: forty-five leaves /10133 lines /758 audited declarations.
  Lint1150 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Kernel prime-factor formula is checking in draft1149. Endpoint and
  small-positive natural-cutoff budgets remain open; RH unproved.

- Exact transfer kernel prime-factor/norm formula fully audited:
  `PMPowerDampedMobiusRamanujanKernel` (196 lines /14 declarations),
  targeted old build62s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The norm kernel equals |A(m)|*r^(-epsilon) times
  product_(p|r)(if p|m then 1 else 1/(p^(1+epsilon)-1)); the finite
  product lies in [0,1]. No squarefree premise on m is needed.
  Combined: forty-six leaves /10329 lines /772 audited declarations.
  Lint1156 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Combined mass/Euler/budget draft1157 is checking. Uniform transfer
  norm and endpoint natural-cutoff energy remain unproved; RH unproved.
