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
Combined PM-31 certificate: twelve leaves / 2917 lines / 181 declarations.
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
