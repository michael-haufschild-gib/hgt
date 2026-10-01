# Power-damped Möbius Fermi approximation

- **ID:** pm-power-damped-mobius-haar
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Route PM; replacement-source investigation after PM-30.
- **Statement:** For every `ε>0`, the literal power-damped Möbius Fermi source has finite canonical `L²(dt)` norm; investigate whether these sources converge to Haar as `ε↓0`.
- **Status:** Twelve fully audited leaves / 2917 lines / 181 declarations: literal source, canonical admission for `ε≥1/2`, exact Mellin quotient, cofinal-admission RH receiver, full-prefix energy savings and endpoint Abel/Fatou admission. Exact Fermi diagonal geometry, the unit limiting norm budget and mandatory canonical prime-cutoff growth and the exact large-damping first-prime asymptotic are certified. Canonical L¹ admission, exact mean, residue slope, admitted error-energy identity and linear-rate canonical L¹ convergence to Haar are now certified; small-positive-damping L² admission remains open.

## Goal

PM-30 proves that the fixed logarithmic approximation requires critical
simplicity as well as its known RH consequence. Investigate a different literal
arithmetic family without importing that boundary requirement. The intended RH
producer is an unconditional canonical norm bound. Pointwise approximation alone
does not supply it.

For `t>0`, define

`A_ε(t) = −Σ_(1≤d≤floor(1/t)) μ(d)d^(−ε) φ_d(t)`.

This is the pointwise infinite Fermi sum as well: the existing support theorem
gives `φ_d(t)=0` for `d>1/t`. In particular, the definition remains finite at
`ε=0`. Möbius floor inversion identifies `A_0` with the dyadic Haar target, and
continuity of each finite coefficient should give `A_ε(t)→Haar(t)` for every
fixed positive `t`. Neither fact controls the shrinking region near zero.

The candidate norm statement must assert integrability or `MemLp` explicitly.
A real-valued integral defined to be zero for nonintegrable functions is not an
admission certificate.

## Gates

- [x] State a literal arithmetic source and the unresolved canonical norm claim.
- [x] Initial prior-research searches and relevant support/floor API inspection.
- [x] Complete the exact pointwise source identities on paper.
- [x] Prove and formalize pointwise convergence and unconditional `ε>1/2` norm admission.
- [x] Identify the exact Mellin quotient with its absolute-convergence domain.
- [x] Audit whether canonical admission for every `ε>0` implies RH without a critical multiplicity cap; cofinal positive admission already suffices.
- [ ] Prove or refute the actual small-positive-`ε` admission conjecture.
- [ ] Formalize the strongest dependency-closed result and audit every declaration.

## Mechanism and remaining producer

The already proved generator transform suggests, on
`0<Re s<1` and `Re(s+ε)>1`,

`mellin A_ε(s) = [(1−2^(1−s))/s] ζ(s)/ζ(s+ε)`.

Absolute coefficient interchange must be verified for these exact coefficients.
For `ε>1/2`, the support bound and `|φ_d|≤3` should give a summable canonical
`L²` majorant. This safe range does not approach `ε=0`.

If all positive dampings were admitted to canonical `L²`, their compact support
would extend each literal Mellin transform to `Re s>1/2`. The cleared quotient
identity at an off-line zero `ρ`, with `0<ε<Re ρ−1/2`, would then force
`ζ(ρ−ε)=0`, since the Haar factor is nonzero inside the strict strip. Varying
`ε` would give an interval of zeta zeros and contradict analyticity. This is a
proposed receiver for the admission claim, not a proof of that claim. Check its
domains, zero exclusions and source identities before relying on it.

Pole audit: continuation must use the entire residue unit
`U(z)=(z−1)ζ(z)`, rather than treating `ζ(s+ε)` as analytic at `s=1−ε`.
On the convex strip `1/2<Re s<1`, the identity becomes
`U(s+ε)F_ε(s)=(s+ε−1)H(s)ζ(s)`, where
`H(s)=(1−2^(1−s))/s`. The initial absolute-convergence domain overlaps this
strip for every `ε>0`. At `s=ρ−ε`, the factors `ρ−1` and `H(s)` are nonzero.
An isolated-zero theorem, with zeta's nontriviality verified from the corpus,
would exclude the continuum of translated zeros. This repairs a potential
domain gap in the proposed receiver. Its Lean proof is now certified below.

Receiver refinement: it suffices that admitted positive dampings are arbitrarily
close to zero. Fix an off-line zero `ρ` and choose admitted `ε` below both
`Re ρ−1/2` and the isolation radius of `ρ`. The cleared identity then gives the
distinct zero `ρ−ε` inside that radius, a contradiction. Isolation can be applied
to the entire residue unit `U`, whose value at one is one, avoiding any global
meromorphic-domain issue. Thus neither admission for every positive damping nor
a norm limit to Haar is needed for this receiver. Its Lean certificate is complete;
no arbitrarily small admitted positive damping has been proved.

A further literal identity to audit is
`F_ε(x)=Σ_(n≤x) a_ε(n)` with
`a_ε(n)=Σ_(d|n) μ(d)d^(−ε)=Π_(p|n)(1−p^(−ε))` for positive `n`, and
`A_ε(t)=F_ε(1/t)−2F_ε(1/(2t))`. The finite Euler product is nonnegative when
`ε>0`. Its derivative at zero should be `Λ(n)`, since only prime powers have
one distinct prime factor. This would relate the new family to the literal
Chebyshev channel already studied in PM. Verify existing generalized totient
APIs before proving anything new; positivity alone is not a variance bound.

## Corpus evidence and limits

- `fermiNymanGen_eq_zero_of_inv_lt` in `FermiNymanBeurlingDyadicWitness`,
  lines 34–65 inspected, gives the exact finite-support cutoff.
- `fermiNymanGen_eq_floor_difference` in `FermiNymanLogMobiusHead`, lines
  90–105 inspected, supplies the literal floor expression.
- `sum_moebius_floor_truncated` in `FermiNymanRawMobiusTailFloor`, lines
  76–103 inspected, supplies the finite inversion receiver.
- The PM-30 arbitrary-coefficient dilation theorem is available for a verified
  `LSeriesSummable` input; the shifted Möbius coefficients still need checking.
- Two preceding deep searches returned complete 63,661-file inventories but
  `partial=true` from reranking deadlines. All 20 candidate and 20 source
  statements in each were reviewed. Their heat-flow, Barnes-product and
  future-pulse proposals do not identify this source or bound its canonical norm.
- Lexical `research '"nyman" damp' --mode lexical` returned zero hits. Targeted
  source-pattern searches also returned none; this is not a universal absence
  or novelty claim. A broader power-weighted Mellin/quotient query is running.
- Existing `MobiusLaplacePolylogBoundaryMultiplicity` and
  `MobiusLaplacePolylogSharpCoefficientLaw` already prove graded multiplicity
  and coefficient restrictions for a different source. Do not relabel that
  mechanism as a new result here.

## Paper ingredients proved here

For fixed `t>0`, put `N=floor(1/t)`. Every omitted generator is zero by the
inspected support theorem, so any larger cutoff gives exactly the same source.
At `ε=0` all powers are one. The existing raw Möbius head identity applies
because `1/(N+1)<t`, giving `A_0(t)=Haar(t)` on `(0,1]`. A finite sum of
continuous functions of `ε` is continuous, hence the pointwise limit follows.

Termwise differentiation at zero gives `Σ_(d≤N) μ(d)log(d)φ_d(t)`.
The inspected exact logarithmic floor inversion evaluates this as
`ψ(1/t)−2ψ(1/(2t))`. Thus the error's first parameter derivative is the same
dyadic Chebyshev channel appearing in the logarithmic approximation. These are
finite identities; no interchange of an infinite derivative or canonical norm
is used. Their Lean certification is the next ingredient task.

The existing shifted-Euler product theorem and its first-jet theorem already
give the proposed divisor product and derivative after the exact normalization
`a_ε(n)=n^(−ε/2)c_(ε/2)(n)`. The first jet is `2Λ(n)` before normalization.
This mechanism is already present in the corpus and is not a new general
prime-derivative claim.

Safe-range norm proof: for `d≥1`, support in `(0,1/d]` and the bound
`|φ_d|≤3` give `‖φ_d‖₂≤3d^(−1/2)`. Hence every finite source cutoff has
norm at most `3Σ_(d≥1)d^(−ε−1/2)`, finite for `ε>1/2`. The cutoffs are
eventually equal to the literal source at each `t>0`. Measurability and Fatou's
inequality therefore give `MemLp A_ε 2 (volume.restrict (Ioi 0))`. This proof
uses absolute generator norms and provides no bound when `0<ε≤1/2`.
The proof is dependency-closed on paper; Lean certification is in progress.

Initial Mellin identity: write `φ_d(t)=φ_1(dt)`. For `0<Re s<1`, the
existing generator theorem identifies the absolutely convergent transform as
`−H(s)ζ(s)`. Dilation changes the integral of its weighted absolute value by
`d^(−Re s)`. Thus `Re s+ε>1` makes the sum of absolute integrals finite,
bounded by a constant times `Σd^(−Re s−ε)`. Interchange is justified and the
Möbius Dirichlet identity gives `F_ε(s)=H(s)ζ(s)/ζ(s+ε)` on precisely this
initial domain. Lean must still identify these coefficients and this literal
finite source with the existing absolute dilation theorem.

## Lean certificate: literal source and safe norm

`formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusSource.lean` has 250 lines
and 14 declarations, including one private measurable-selection helper. The
capstone `memLp_pmPowerDampedFermiSource` proves
`MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0))` for `ε>1/2`.
The pointwise Haar limit and exact Chebyshev derivative are certified as well.

- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusSource:olean`
  passed; new leaf took 183 seconds.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusSource.lean`
  passed with empty output.
- Exact leaf copied to `/tmp` for all 14 axiom reports, including the private
  helper. Every report contains only `propext`, `Classical.choice`, `Quot.sound`.
- Exhaustive declaration-name uniqueness, source-body equality, all public API
  entries and exactly one umbrella import checked. Generated index refreshed.
- Formal lint exits 1 on ten unrelated unwired modules: `CCMApertureChainProfile`,
  `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
  `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
  `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`,
  `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
  `ZetaZeroDensityPowerSaving`. No PM31, forbidden-declaration or stale-generated
  error. The global gate is not reported as passing.

This certificate proves safe-range admission, not admission arbitrarily close to
zero or RH. The card remains in progress for those unresolved gates.

## Lean certificate: exact Mellin quotient and canonical analytic domain

`formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusMellin.lean` has 200 lines
and 14 declarations. `hasMellin_pmPowerDampedFermiSource` identifies the literal
transform, with absolute convergence, on `0<Re s<1` and `1<Re s+ε`.
`mellinConvergent_pmPowerDampedFermiSource` and
`analyticOnNhd_mellin_pmPowerDampedFermiSource` give absolute convergence and
analyticity on `Re s>1/2` from explicit canonical `MemLp` admission.

Targeted old build passed (14 seconds for the leaf), final actual
`lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusMellin.lean` passed
empty, and all 14 exact-source-copy axiom reports use only the same standard
three axioms. Source-body equality, all names, public API and unique umbrella
import passed. Index refreshed; lint still reports precisely the same ten
unrelated unwired modules listed above. No own or proof-debt finding.

Combined source/Mellin certificate: two leaves / 450 lines / 28 declarations.
The continued identity and RH receiver are certified by the third leaf below;
the actual small-damping admission conjecture remains unproved.

## Lean certificate: cofinal admission and the failure gap

`formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusCriterion.lean` has 146
lines / 5 declarations. It continues the fully cleared identity through the
right critical strip, derives translated zeros from canonical admission, and
proves `riemannHypothesis_of_pmPowerDamped_cofinal_admission`. Its contrapositive
`pmPowerDamped_admission_gap_of_not_riemannHypothesis` gives a whole interval
`0<ε<δ` of nonadmission under `¬RH`. Zero isolation for the entire residue unit
supplies the contradiction; no critical simplicity premise is used.

Targeted old build passed (30 seconds for the leaf). Final actual
`lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusCriterion.lean`
passed empty. All five axiom reports use only `propext`, `Classical.choice`,
`Quot.sound`. All declaration names, source-body equality, public API entries
and the unique umbrella import passed exhaustive checks. Index refreshed.
At this receiver audit, lint exited 1 on the ten unrelated unwired modules already listed plus
`WeilPositivityLinearDuality`; no PM31, proof-debt or stale-generated finding.

Combined certificate: three leaves / 596 lines / 33 declarations. This closes
the receiver, not its admission premise or the unconditional RH goal.

## Lean certificate: full Fermi prefix energy

`formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrefixEnergy.lean` has 342
lines / 17 declarations. It identifies the literal physical modular source with
`bdMobiusModularApproximantVec` by reciprocal half-density, proves explicit
canonical admissions, and derives
`∫|R_N|² ≤ 12‖bdMobiusModularApproximantVec N‖²+18H_N²`.
The capstone `pm_rawMobiusFermiApprox_energy_log_saving` gives, for every natural
`q`, an unconditional eventual bound `∫|R_N|² ≤ C_q N/log(N)^(q+1)`.

Targeted old build passed (94 seconds for the leaf); final actual
`lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrefixEnergy.lean`
passed empty. All 17 axiom reports use only the standard three axioms; exhaustive
body/name/API/import checks passed. Index refreshed. Latest lint exits 1 on the
ten unrelated unwired modules in the source audit plus `LiClockThetaGammaMixture`;
`WeilPositivityLinearDuality` is no longer reported. No own or proof-debt finding.

Combined certificate: four leaves / 938 lines / 50 declarations. Endpoint
`ε=1/2` admission still requires the Abel/Fatou argument; no small-damping
admission or unconditional RH proof is claimed.

## Lean certificate: unconditional endpoint admission

`formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusEndpoint.lean` has 246
lines / 12 declarations. Finite Abel summation, logarithmic raw-prefix savings
and summable coefficient gaps give uniformly bounded half-damped prefixes.
Fatou proves `memLp_pmPowerDampedFermiSource_half`;
`memLp_pmPowerDampedFermiSource_of_half_le` covers every `ε≥1/2`.

Targeted old build passed (161 seconds for the leaf); final actual
`lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusEndpoint.lean`
passed empty. All 12 exact-source-copy axiom reports use only `propext`,
`Classical.choice`, `Quot.sound`. Exhaustive declaration-name uniqueness,
source-body equality, all public API entries and the unique umbrella import
passed. The API probe needed its own `noncomputable section`; the leaf needed
no change. A slow audit script timed out cleanly and was replaced by one source
scan. Its axiom parser was corrected to trim multiline whitespace.

Index refreshed. The first lint snapshot also saw concurrent generated-file
changes; after regeneration, `scripts/formal_tools.py lint --check-generated`
exits 1 only for the ten unrelated unwired modules listed in the source audit.
`LiClockThetaGammaMixture` is no longer reported. No own, proof-debt or stale
generated-file finding in this final snapshot. Global lint is not passing.

Combined certificate: five leaves / 1184 lines / 62 declarations. Endpoint
admission is unconditional; admission arbitrarily close to zero and RH remain
unproved.

## Lean certificate: exact Fermi diagonal and positive-block obstruction

`formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusGramDiagonal.lean` has
259 lines / 18 declarations. It proves `φ_a∈{0,−1}` and exact canonical
squared norm `log(2)/a` for every `a>0`. The actual power-damped Möbius
diagonal is summable for every positive damping. Positive blocks on
`2N≤d≤3N` have energy at least `N/12` and diagonal at most `log(2)`,
so no coefficient-independent fixed multiple of the diagonal bounds synthesis.
These are exact symbolic proofs, with no numerical experiments.

Targeted old build passed (20 seconds); final actual
`lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusGramDiagonal.lean`
passed empty. All 18 exact-copy axiom reports use only the standard three
axioms. Exhaustive body/name/index/public-API/import checks passed.
Index refreshed. Formal lint exits 1 for the ten unrelated unwired modules
listed in the source audit plus `HorizontalSimplicityDeficitCount`; no own,
proof-debt or stale-generated finding. Global lint is not passing.

Combined certificate: six leaves / 1443 lines / 80 declarations. The literal
Möbius cross-term estimate, small-damping admission and RH remain open.

## Log

- 2026-10-01 — Created after PM-30's complete Lean audit. No computations,
  added axioms, norm premise silently discharged, or unconditional RH claim.
- Broader power-weighted Mellin query completed: `partial=true` from semantic
  deadlines, complete 63,665-file inventory. All 20 candidate and 20 source
  statements reviewed. Incidence-algebra inversion and generic Mellin inversion
  do not supply the missing canonical norm estimate. Inspected
  `BaezDuarteMobiusSeries` 1–46: its binomial coefficients are a different source;
  `DeningerDirichletAbel` 18–40 gives the useful harmonic-weighted absolute series;
  `CoupledFloorMobiusShiftIncidence` 1–72 has an extra power weight on the inner
  summation, so it cannot be substituted directly. Its coefficients may identify
  the proposed positive divisor weights after an exact power normalization; audit
  that relation before adding duplicate definitions.
- Exact normalization found: `shiftedEulerCoefficient_eq` in
  `ShiftedEulerMobiusSynthesis` (1–90 inspected) already proves
  `c_ω(n)=n^ω Σ_(d|n) μ(d)d^(−2ω)`. Thus the proposed divisor coefficient is
  `n^(−ε/2)c_(ε/2)(n)` for positive `n`; its convolution need not be reproved.
  `ShiftedEulerFloorMobiusTailCoupling` 65–99 identifies this existing coefficient
  with Suzuki's product form. Reuse and verify the remaining product/jet APIs;
  none of these identities proves the small-`ε` canonical bound.
- Inspected `ShiftedEulerMobiusSynthesis` 289–316 and
  `CCMFUSuzukiCriticalChordMeasure` 32–64, 531–582. The exact Euler product,
  critical coefficient vanishing and first jet `2Λ` are already formalized.
  Read `FermiNymanRawMobiusTailFloor` 198–215 for the exact head identity and
  `FermiNymanLogMobiusHead` 40–67 for the signed logarithmic floor sum.
  The first scratch `/tmp/pm_power_damped_source_1010.lean` now checks the literal
  finite source, its zero-parameter value, parameter continuity and pointwise Haar
  limit. No source-tree leaf, derivative theorem or norm admission is claimed yet.
- The initial five-declaration scratch passed; its deprecated continuity alias
  was replaced and the recheck passed empty. Appended the arbitrary larger-cutoff
  identity, exact logarithmic Fermi sum and finite parameter derivative at zero;
  this expanded scratch is now checking. A preparation command initially used
  the wrong relative guarded-runner path, made no edits, and was corrected.
- Expanded eight-declaration scratch passed with empty output after repairing a
  missing closing parenthesis. The derivative is exactly
  `ψ(1/t)−2ψ(1/(2t))`. Next: explicit canonical norm admission for `ε>1/2`,
  using summable generator norms; this safe range does not settle small damping.
- Mellin/L² deep search completed with `partial=false`, no errors, complete
  63,678-file inventory; all 20 candidate and 20 source statements reviewed.
  Coverage warns of an older-generation snapshot and unavailable semantic
  coverage, and returned statements are source-only. The proposed decay-based
  ingredient chain assumes stronger pointwise input and is unnecessary here.
  `MellinHeadChart` (100–124, 203–end inspected) already provides the L²
  logarithmic head chart and exact Laplace transform identity.
  `CausalL2LaplaceHolomorphy` (1–50, 105–115, 167–end inspected) gives analytic
  admission from L² data. At aperture one and parameter `1−s`, these yield the
  needed `Re s>1/2` transform domain after checking the literal source support.
- Additional name/source audit: `DampedMobiusSumsZeroFree` 1–180 treats general
  prime damping with a separate small-residue hypothesis; that hypothesis is not
  discharged by `f(p)=p^(−ε)`. `NymanBeurlingCriterion` 1–95 supplies the existing
  off-line-zero receiver. `BaezDuarteMobiusPrefixApproximation` 1–95 concerns raw
  modular coefficients and leaves a complementary norm tail open. These do not
  prove PM31's small-damping norm claim.
- Full 14-declaration scratch passed with empty output. Created and wired
  `PMPowerDampedMobiusSource.lean`: literal source, cutoff and Haar limit, exact
  Chebyshev derivative, measurability/support, generator and coefficient norm
  bounds, and explicit canonical `MemLp` for `ε>1/2`. Optimized two costly
  higher-order elaborations using an explicit measurable selector and named
  summands; no heartbeat increase. Targeted old build is running; actual-leaf,
  axiom and lint audits remain pending. The Mellin coefficient/source scratch is
  drafted separately and has not yet been checked.
- Source audit completed as recorded above. The separate nine-declaration
  Mellin/source scratch is now checking for the first time. No Mellin quotient
  or RH receiver is yet claimed as Lean-certified.
- Initial nine Mellin declarations passed after explicit function/parameter
  annotations. Added the exact logarithmic head-chart identity and conditional
  analyticity on `Re s>1/2`; the resulting 12-declaration scratch passed empty.
  `HalfLineLaplaceL2.differentiableOn_laplaceRay` (235–263 inspected) supplies
  holomorphy directly, avoiding an extra transform adapter. Added explicit
  Mellin-convergence proofs from Cauchy–Schwarz and the existing power-witness
  square integral (Fermi generator file 283–299 inspected); these two final
  declarations are checking. No second source-tree leaf has been created yet.
- Full 14-declaration Mellin scratch passed after adding explicit real integration
  variable types. Created/wired `PMPowerDampedMobiusMellin.lean`, 200 lines / 14
  declarations. It includes exact coefficient shift, absolute Mellin quotient,
  head-chart identity, and conditional absolute convergence and analyticity on
  `Re s>1/2` for canonically admitted sources. Targeted build and audits are
  underway. The next receiver will use the fully cleared identity
  `s U(s+ε)F_ε(s)=(s+ε−1)(1−2^(1−s))ζ(s)`, avoiding division by `s` during
  continuation across the strip.
- Second leaf audit completed as recorded above. All owned compiler/index/lint
  jobs for these two leaves exited. Next: continue the entire-unit identity and
  formalize the translated-zero contradiction for cofinally admitted dampings.
- Receiver scratch now includes the initial and continued fully cleared
  identities, zero translation, the cofinal-admission RH criterion, and its
  contrapositive: under `¬RH`, some whole interval `0<ε<δ` has no canonical
  admission. The proof selects `ε` below the off-line zero's isolation radius
  directly in the complex metric; no limiting multiplicity argument is needed.
  The five-declaration check is pending. A new corpus query is investigating
  power-weighted Möbius floor sums and logarithmic hyperbola savings as possible
  tools for extending the safe damping range; no endpoint claim is accepted yet.
- Receiver promoted, built and fully audited as recorded above. The next task
  is an unconditional admission estimate, starting with the endpoint `ε=1/2`.
- Weighted-floor/hyperbola search completed with `partial=true`, pending
  inventory coverage and semantic/reranking failures. All 20 candidate and 20
  source statements reviewed; no weighted logarithmic error bound was supplied.
  `MobiusPowerSumBoundaryLaplace` 1–130 was inspected: its weight is the unsigned
  power sum, not the needed Möbius cancellation estimate.
- Mertens/log-decay search completed with `partial=false`, no errors, complete
  63,697-file inventory; semantic coverage unavailable, returned statements
  source-only. All 20 candidate and 20 source statements plus the proposed
  ingredient chain reviewed. The chain assumes a Mertens power bound and does
  not discharge the required producer. Direct source search located unconditional
  `Sieve.deningerMertensM_log_pow_rate` and
  `DeletionMobiusGlobal.primitiveEnergy_log_saving` /
  `modular_norm_log_saving`. Their exact statements and proofs were inspected.
  The latter bound is for the full discrete carrier; its transfer to the literal
  continuous Fermi prefix must be proved before applying Banach-valued Abel
  summation at damping one half. No endpoint theorem is claimed yet.

## Endpoint subproblem: paper mechanism under audit

Let `R_N=−Σ_(d≤N) μ(d)φ_d`, `H_N=Σ_(d≤N)μ(d)/d`, and let `B_N` be the
literal Nyman modular combination, pulled back from `bdMobiusModularApproximantVec`
by `u=1/t`. The half-density substitution preserves its canonical norm. Finite
algebra should give `R_N=B_N−2B_N(2t)−H_N φ_1`. The existing full modular-energy
logarithmic saving and boundedness of `H_N` would then imply, for every fixed
`q`, `‖R_N‖₂=O(sqrt(N)/log(N)^q)`.

Finite Abel summation for `w_n=n^(−1/2)` gives the weighted prefix as
`w_N R_N + Σ_(n<N)(w_n−w_(n+1))R_n`. The derivative bound
`0≤w_n−w_(n+1)≤(1/2)n^(−3/2)` and the preceding estimate with `q=2` make
the sum of term norms finite; the boundary term tends to zero. Therefore the
weighted prefixes have a uniform finite canonical norm. They stabilize to
`A_(1/2)` at each positive `t`, so Fatou would certify endpoint admission.

This is an unconditional endpoint mechanism based on inspected corpus inputs.
The exact continuous/discrete identification, finite Abel identity and norm
transfer still require audit and Lean checks. Below one half, this estimate
leaves `n^(−ε−1/2)/log(n)^q`; logarithmic savings alone do not make that
majorant summable. No propagation from the endpoint to small positive damping
is claimed.

- Reciprocal-carrier search completed with `partial=false`, no errors and a
  complete 63,698-file inventory. Coverage warns of an older-generation snapshot
  and unavailable semantic coverage. All 20 candidate and 20 source statements
  and the proposed chain reviewed; the chain's unrelated polynomial/invariant
  isometries do not establish this transfer. Direct source inspection found
  `ArchimedeanMellinFourier.integral_Ioi_comp_inv` (namespace to verify) and
  `BurnolSoninDividedShift.integral_Ioi_one_eq_integral_Ioo_inv`, both exact
  reciprocal change-of-variable identities. An owned scratch now checks the
  literal modular prefix, its reciprocal carrier formula and its compact support.
- First four carrier-transfer scratch declarations passed after explicit cast
  normalization: admitted-function integral/norm identity, literal modular source,
  exact reciprocal formula and support. A root-directory compiler invocation
  failed to resolve the project and was rerun in `formal`; no theorem was accepted
  from that failed command. The expanded scratch adds reciprocal square-integrability
  transfer, measurability and equality almost everywhere with the existing carrier.
  The source of `integral_Ioi_comp_inv` is `ArchimedeanMellinFourier.lean`, but its
  actual namespace is `RHTower`, verified in source and in Lean.
- Expanded carrier scratch passed all 11 declarations. It now certifies exact
  equality of the physical modular square integral and the existing carrier norm,
  explicit `MemLp` admission, and the literal Fermi/harmonic correction identity.
  One unused simp argument was removed. The next five declarations bound the
  full Fermi energy by `12‖bdMobiusModularApproximantVec N‖²+18H_N²`; they are
  checking. No tree module or endpoint certificate has been promoted yet.
- Full 17-declaration carrier/prefix scratch passed with empty output. Created
  and wired `PMPowerDampedMobiusPrefixEnergy.lean`: exact continuous/carrier
  identity, explicit admissions, harmonic correction, full Fermi energy bound
  and unconditional arbitrary logarithmic saving relative to `N`. Targeted old
  build is running; final actual-leaf, axiom and formal gates remain pending.
  The endpoint admission itself still needs finite Abel summation and Fatou.
- Prefix-energy audit completed as recorded above; all owned 1011 build/audit
  jobs exited and all 12 completed scratch/audit files were removed. The 1012
  endpoint draft now contains the norm/energy identification, normalized
  logarithmic bound, finite Abel identity, vanishing boundary term and a
  reciprocal-log summability proof. Additional coefficient-gap summability is
  checking. Uniform finite-prefix admission and the final Fatou step are drafted
  separately; no endpoint source-tree leaf exists yet.
- Started a deeper producer query on power-damped Möbius/generalized-totient
  summatory variance and dyadic `L²` error. The endpoint proof mechanism leaves
  a positive power gap below one half, so further logarithmic savings of the same
  kind cannot supply cofinal small-damping admission. No new producer bound is
  assumed from the query.
- Endpoint scratch's first eight declarations passed (with an informational ring
  suggestion, now removed by an explicit arithmetic equality). These include
  the exact finite Abel identity and unconditional summability of the coefficient
  gaps times the literal raw-prefix norms. The full draft now checks uniform
  finite-prefix bounds, Fatou admission at `ε=1/2`, and admission for all
  `ε≥1/2`. These final four declarations are not yet certified.
- Generalized-totient/variance query completed with `partial=false`, no errors,
  complete 63,710-file inventory; older-generation snapshot and unavailable
  semantic coverage warnings. All 20 candidate and 20 source statements and the
  proposed ingredient chain reviewed. The chain only supplies inversion identities
  and an unrelated Gaussian source, not the required variance estimate. Inspected
  `ChronologicalDampedRepair` 1–140: its geometric Lambert coefficients and small
  rational-response error leave finite truncation convergence open.
  `DampedComplementaryPacketConnection` 1–105 uses unsigned power sums and a
  different damping. Neither identifies or admits PM31's small power dampings.

- Full endpoint scratch passed empty. Created/wired
  `PMPowerDampedMobiusEndpoint.lean`, 246 lines / 12 declarations, including
  unconditional `memLp_pmPowerDampedFermiSource_half` and admission for every
  `ε≥1/2`. Targeted old build is running; final actual-leaf and axiom audits
  remain pending. No admission below one half or RH is claimed.
- Fermi/Möbius Gram query completed: `partial=false`, no errors, complete
  63,710-file inventory, older-generation and unavailable-semantic warnings.
  All 20 candidate and 20 source statements and the ingredient chain reviewed.
  Its generic diagonal extraction does not cancel this arithmetic cross sum.
  `MobiusAbelPrefixGramIntegral` 1–220 and `MobiusAbelPrefixGramSign` concern
  cubic Gamma atoms, a different source. `SquarefreeMoebiusCrossGram` 1–200
  controls a diagonal operator on a squarefree sequence space, not physical
  Fermi synthesis. `EulerDeletionMobiusGramCancellation` 1–48 and 102–192
  already isolate the modular off-diagonal obstruction: unconditional diagonal
  bounds do not supply its RH-bearing signed cross-term ceiling.

## Fermi Gram subproblem: paper audit

The literal floor formula gives `φ_a(t)∈{0,−1}` for every real `a,t`:
`floor(x)−2 floor(x/2)` is either zero or one. Thus `|φ_a|²=−φ_a`
(the latter is real). The existing dyadic-log-mean integral, specialized to
the constant witness one, gives `∫φ_a=−log(2)/a` for `a≥1`. Support and
dilation extend the norm identity to every `a>0`:
`∫_(0,∞)|φ_a(t)|² dt=log(2)/a`. Therefore the power-damped Möbius
diagonal is summable for every `ε>0`, by comparison with `Σd^(−1−2ε)`.
This paper argument uses the inspected literal kernel and integral theorem;
its new identities still require Lean verification.

This does not prove a uniform bound for the full Gram form. Indeed, a
coefficient-independent diagonal ceiling cannot hold: for scales
`a∈[N,3N/2]`, all generators equal minus one on
`(1/(2N),2/(3N)]`. A positive block with order `N` terms consequently
has energy of order `N`, although its diagonal mass stays bounded.
The useful positive survivor is the exact kernel/diagonal geometry; an actual
small-damping producer must retain and bound the Möbius cross terms.
The block obstruction has not yet been formalized; no route is retired here.

- Second Fermi Gram search: `partial=false`, no errors, complete 63,715-file
  inventory, older-generation/unavailable-semantic warnings. All 20 candidate
  and 20 source statements and the proposed chain reviewed. The chain supplies
  known dilation/support identities only. `FermiNymanCorrelationKernel` concerns
  witness jets, not the generator Gram. `MobiusDivisorFibreCoareaVariance` gives
  a finite weighted-Cauchy decomposition, not the missing upper bound.
  `integral_fermiNymanGen_mul_of_dyadicSelfSimilar` in
  `FermiNymanBoundedSpuriousClassification` (16–87 inspected) is the exact
  integral input for the proposed diagonal law.

- Endpoint leaf audit completed as recorded above. All 1012 owned compiler and
  audit jobs exited; the next scratch checks the exact parity/diagonal identities.

- Exact Fermi Gram scratch: parity values `{0,−1}`, the sharp pointwise norm
  bound, squared-norm identity and dyadic logarithmic mean passed elaboration.
  The support-transfer step needed the larger set's measurable-set argument.
  The expanded 258-line scratch now checks all 18 declarations: exact diagonal
  integral, summability for every positive damping, and a contiguous positive
  block obstruction to a coefficient-independent diagonal ceiling. Its latter
  arguments are not yet certified. No new source-tree leaf exists.
- A more specific lexical search now traces every `shiftedEulerCoefficient`
  use, seeking an actual arithmetic upper bound for the normalized generalized
  totient source. The earlier broad variance search supplied no such bound.

- Full Fermi Gram scratch passed empty. Created/wired
  `PMPowerDampedMobiusGramDiagonal.lean`, 259 lines / 18 declarations:
  exact parity and diagonal norm, actual Möbius diagonal summability for every
  positive damping, and a positive-block counterexample to every fixed
  coefficient-independent diagonal ceiling. Targeted build and final audits
  are pending. The specific Möbius cross-term bound remains open.

- Specific shifted-Euler lexical query returned four total hits, with three
  shown under the per-module cap. Exhaustive `rg` traced all 20 direct uses
  across four files. The uncapped coupled-error query returned all six hits.
  These lexical outputs have no deep coverage/freshness metadata. Inspected
  `ShiftedEulerFloorMobiusTailCoupling` 1–42, 150–225;
  `MobiusChannelCriticalMassEscapePaperCertificate` 125–158;
  `CCMFUSuzukiCriticalChordMeasure` 98–124;
  `SuzukiTailSummatoryErrorTransform` 1–78;
  `CoupledFloorMobiusCriticalBoundaryCancellation` 1–40, 112–192;
  `CoupledFloorMobiusAffineRieszHandoff` 1–95;
  `CCMFUSuzukiCompletedRieszGraphEnergy` 1–110; and the interim verdict's
  exact error-transform fields. The available unconditional coupled carrier
  uses `exp(−(1+ω)t)E_ω(exp t)` and the elementary `X^(1−ω)` envelope.
  Its norm is not PM31's canonical Fermi norm. The coefficient-faithful affine
  handoff explicitly retains an RH-equivalent boundedness premise. No stronger
  PM31 producer follows from these inspected certificates.

### Next producer question: actual vertical twists

The summable diagonal suggests averaging `μ(d)d^(−ε−iτ)` over a real
vertical clock. For each fixed finite prefix, a long clock average suppresses
unequal frequencies `log d`. The unresolved interchange is uniformity in the
prefix cutoff and recovery at an actual finite real clock. A formal diagonal
average, or Haar measure on a larger character space, does not by itself
admit the literal real-clock source. Search this distinction before treating
it as a new producer; no interchange or probability conclusion is assumed.

- Vertical-twist query completed: `partial=false`, no errors, complete 63,723-file
  inventory; older-generation and unavailable-semantic warnings. All 20 candidate
  and 20 source statements and the ingredient chain reviewed. Its Bohr Parseval
  chain assumes an already bounded, uniformly continuous function with totally
  bounded orbit; it supplies no admission for the literal infinite source.
  `VerticalMeanCharacter` and `BohrTransfer` fully inspected,
  `BohrCesaroMean` 1–145, `SecondMoment` 1–90 plus declaration map, and
  `SteinhausModel` 330–357. They certify finite-prefix diagonal averaging with
  a cutoff-dependent off-diagonal constant. The profinite tensor average in
  `CCMRationalAdelicTensorHaarMobiusCompression` 1–120 concerns different data.
  No uniform-cutoff or actual-clock recovery has been proved.
- Gram leaf targeted build passed (20 seconds); final actual source check passed
  empty. Exhaustive name/body/public-index/import audit passed for all 18
  declarations. Axiom/API probes remain pending. Latest formal lint exits 1
  on the ten prior unrelated unwired modules plus
  `HorizontalSimplicityDeficitCount`; no own/proof-debt/stale-generated finding.
- Next kernel query investigates exact Nyman/Fermi Gram reciprocity and
  coprime-scale decomposition before proposing an arithmetic cross-term bound.
  The diagonal averaging observation alone is not accepted as a producer.

- Reciprocity query completed: `partial=false`, no errors, complete 63,723-file
  inventory, older-generation/unavailable-semantic warnings. All 20 candidate
  and 20 source statements and chain reviewed. The suggested smooth Salem
  Fermi kernel is a different function; it cannot replace the floor-parity
  generator. Direct inspection of `BaezDuarteGramDiscrete` 1–150,
  `GramResidueDecomposition` and `MoebiusResidualTailForm` gives exact modular
  cell/residue series and tail decompositions, without a signed upper bound.

### Next conjecture to audit: prime-step source contraction

For a finite prime set `P`, consider the literal finite Euler source
`B_(P,ε)=−Π_(p∈P)(I−p^(−ε)D_p)φ_1`, where `D_p f(t)=f(pt)`.
Its prime insertion has exact energy increment
`p^(−2ε−1)||B||²−2p^(−ε) Re⟨B,D_pB⟩`.
A source-specific lower bound on this correlation could control prime-ordered
cutoffs and hence admit `A_ε` by their pointwise stabilization. Neither a
generic operator contraction nor the required arithmetic correlation is assumed.
Search prior Euler/dilation covariance work before judging this conjecture.
The finite-source identity and insertion law are algebraic paper observations;
no prime-step sign claim is proved or formalized.

- Paper obstruction to the strongest prime-contraction guess: the seed has
  squared norm `log(2)<1`, while the literal zero-damping source equals Haar
  on `(0,1]`, whose squared norm is one. If all prime insertions were norm
  nonincreasing for every positive damping, pointwise stabilization in the
  prime cutoff would bound every `A_ε` by the seed norm. Fatou as `ε↓0`
  would then give `1≤log(2)`, a contradiction. This uses no zero hypothesis.
  Thus a viable prime-step argument must allow cumulative norm growth.
  Strong positive statement to formalize: every limiting uniform canonical
  norm budget along dampings tending to zero is at least one. The concrete
  finite-prime stabilization and insertion-failure theorem are not yet Lean
  certified; the conjecture is not marked formally retired.

- Gram diagonal audit completed as recorded above; all 1013 owned compiler,
  index and audit jobs exited. Continuing the prime-step covariance investigation.

- Prime-contraction deep query completed with `partial=true` from interrupted
  text retrieval, complete 63,725-file inventory and unavailable-semantic warning.
  All 20 available candidate and 20 source statements and chain reviewed; the
  proposed dilation-isometry chain does not establish prime-step contraction.
  `MobiusDivisorPrimePairEnergy` fully inspected: it contracts a cofactor
  diagonal under one pairing, not PM31's physical synthesis norm.
  `MobiusDivisorInheritedPrimeInsertionProducer` 1–120 and 1305–1352
  proves prepared energy release over a fixed inherited core; its budget depends
  on that core and it explicitly leaves uniform exhaustive control open.
  `MobiusFinitePrimeApertureSourceConsumption` 1–88 supplies a reusable exact
  prime-coverage identity. `RetainedPrimeMobiusEulerIdentity` 1–80 concerns
  retained-label coefficients and does not assert the required energy sign.
- A six-declaration norm-floor scratch is checking: exact Haar norm, a Fatou
  lower bound, universal limiting-budget floor, and exclusion of even a local
  source ceiling at the seed norm. A first check exposed notation and limit-domain
  mismatches; the revision uses the already-proved full parameter continuity
  directly. These statements are not yet certified.

- Norm-floor scratch passed empty. Created/wired `PMPowerDampedMobiusNormFloor.lean`
  with six declarations. Targeted build and final audits pending. The concrete
  finite-prime insertion obstruction is next; small-damping admission remains open.

- Norm-floor targeted build passed (29 seconds). Finite-prime scratch proved
  exact coefficient support, canonical cutoff stabilization, transfer of a uniform
  finite-prime norm budget, and an actual norm-increasing insertion arbitrarily
  near zero damping. Strengthening to consecutive canonical prime cutoffs and
  finite-source exceedance of every subunit budget; two API fixes are checking.
  No numerical computation or small-damping admission is used.
- Next producer question: can damping itself act through a bounded source-specific
  operator on Haar, allowing the necessary growth from the seed? A corpus query
  is testing this direction; no such operator or unit norm ceiling is assumed.

- Full strengthened finite-prime scratch passed empty. Created/wired
  `PMPowerDampedMobiusPrimeGrowth.lean`: exact finite coefficients and
  pointwise cutoff stabilization, finite-to-literal budget transfer, strict
  norm growth at a consecutive canonical prime cutoff arbitrarily near zero,
  and finite-source exceedance of every subunit budget. Targeted/final audits
  pending. No actual prime-step energy-increment formula is claimed Lean-certified.

- Parameter-contraction deep search: `partial=false`, no errors, complete
  63,735-file inventory, semantic coverage unavailable; result generation
  1,170,033 versus coverage generation 1,170,038. All 20 candidate and 20 source
  statements plus the proposed chain reviewed. That chain confuses coefficient
  bounds and normalized sequence-space energy with the physical Fermi norm.
  `ZetaTwoShiftContraction` fully inspected: a normalized translation average
  on the safe `σ>1` side. `MobiusCriticalComplexPhaseHardySource` 1–120 uses
  normalized squarefree `ℓ²` mass; `DampedMobiusSumsZeroFree` 140–185 bounds
  individual coefficients; `ChronologicalDampedRepair` 1–72 has a different
  rational source; `DeningerAdiabaticGreenStokes` 223–270 supplies an `L¹`
  majorant. None identifies a bounded damping operator on this canonical source.
- Canonical prime-contraction no-go has its own pending-audit card,
  `pm-power-damped-prime-contraction.md`. Its positive survivor is the unit
  limiting budget floor and exact finite-source budget transfer.

- Prime-budget query completed: `partial=false`, no errors, complete 63,738-file
  inventory; semantic coverage unavailable, result generation 1,170,098 versus
  coverage 1,170,106. All 20 candidate and 20 source statements and chain read.
  The proposed polynomial sieve remainder and prime-count damping chain does not
  estimate PM31 norm. `EulerDeletionPrimeCountAmplification` 1–132 instead
  exhibits amplification under a different multiplicative damping.
  `Sieve/SieveRemainderBound` fully inspected. All `ccmEulerMobius` uses across
  `CCMPrimeDeficitEulerResidual`, `CCMPrimeDeficitEulerRenewal`, and
  `CCMPrimeDeficitEulerDeletedDynamics` traced; all three modules read.
  They give exact rough-source renewal and prime-force identities, retaining
  signed deficit values; no physical Fermi norm upper estimate follows.

### Next conjecture: monotonicity under increased power damping

A candidate weaker than prime insertion contraction is that increasing `ε`
never increases the norm of the literal family itself. Before using it, test
its large-damping asymptotic. Formally the first nontrivial term is
`A_ε=−φ_1+2^(−ε)φ_2+o_(L²)(2^(−ε))`. Both generators are negative parity
indicators and have strictly positive overlap, so this predicts approach to the
seed norm from below, contradicting eventual nonincreasing dependence on `ε`.
This is a paper mechanism to audit through corpus search and a rigorous tail
bound, not yet a proved asymptotic. No computation is proposed.

## Lean certificates: limiting norm floor and canonical prime growth

`PMPowerDampedMobiusNormFloor.lean`: 89 lines / six declarations.
`PMPowerDampedMobiusPrimeGrowth.lean`: 203 lines / 13 declarations.
Combined PM31: eight leaves / 1735 lines / 99 audited declarations.

- Targeted `lake --old build +…:olean` passed (29 and 18 seconds).
- Final actual-source `lake env lean` passed empty for both leaves.
- All 19 axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`;
  every public `#check` probe elaborated.
- Exhaustive body equality to checked scratch, name uniqueness, public API index
  entries and exactly one umbrella import verified. Generated index refreshed.
- Formal lint exits 1 on 14 unrelated unwired modules:
  `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
  `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
  `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
  `HorizontalShiftOverlapExact`, `HorizontalSimplicityDeficitCount`,
  `HorizontalTradeoffHyperbolicBounds`, `HorizontalTradeoffWindowDeficit`,
  `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
  `ThetaMovingShellFirstOrderPhase`, `ZetaZeroDensityPowerSaving`.
  No own, active proof-debt, or stale-generated finding.

Closed no-go card: `../5-failed/pm-power-damped-prime-contraction.md`.
Even canonical increasing-prime cutoffs must have a norm-increasing step in
every positive damping neighborhood. Every subunit budget is exceeded by a
canonical finite-prime source arbitrarily near zero. The positive survivor is
an exact unit floor for limiting norm budgets, not a claimed upper bound.

- Large-damping query completed: `partial=false`, no errors, complete 63,739-file
  inventory, older-generation and unavailable-semantic warnings. All 20 candidate
  and 20 source statements plus the ingredient chain reviewed. It returns the
  existing generator norm estimates but no literal source asymptotic. Direct
  inspection of mathlib `LSeries/Injectivity` 1–168 gives the scalar first-coefficient
  mechanism; `Analysis/Normed/Group/Tannery` 35–59 gives dominated convergence
  for Banach-valued series. These suggest an exact canonical first-prime expansion
  with a summable tail majorant. This expansion is not yet Lean-certified.

- All 1018/1019 owned compiler and audit jobs exited; all associated scratch
  files and the fully reviewed 1020–1022 query outputs cleaned.

### Large-damping paper proof to formalize

Put `x=2^(−ε)` and `κ=Re⟨φ_1,φ_2⟩` in the canonical carrier. The two
negative parity indicators have nonnegative product everywhere. Both equal
`−1` on `(1/4,1/3]`, so `κ≥1/12>0`.

After removing indices one and two, the norm of each term scaled by `2^ε`
is at most `3(2/d)^ε` for `d≥3`. For `ε≥2` this is at most `12/d²`, a
summable majorant; each individual term tends to zero. Dominated convergence
for this real majorant, finite-sum Minkowski and pointwise stabilization/Fatou
therefore give `||2^ε(A_ε+φ_1)−φ_2||₂→0`.

Expanding the squared norm gives
`2^ε(||A_ε||₂²−log 2)→−2κ<0`. Hence the energies approach `log 2` strictly
from below. A nonincreasing function on any final parameter interval cannot
lie below its own limit, so actual-source norm monotonicity fails even
arbitrarily far inside the already admitted large-damping range.

The positive survivor is the precise first-prime canonical asymptotic and
strictly negative leading energy correction. This is a dependency-closed
paper argument using existing canonical admission for `ε≥1/2`, the exact
parity geometry and standard dominated convergence; its detailed Lean
interchanges and overlap integral are still being checked. No retirement yet.

- Scratch `/tmp/pm_large_damping_1023.lean` now checks the summable majorant,
  its vanishing parameter limit, exact first-two-prefix extraction and a
  scaled generator norm estimate. No new source-tree leaf yet.

### Next producer candidate: unit canonical budget and exact mean

The limiting unit floor and the large-damping seed value suggest testing the
explicit extended-norm bound `eLpNorm A_ε 2 (dt)≤1` for every `ε>0`.
This includes admission; a totalized square integral alone would not suffice.
The conjecture permits the norm increases already exposed. It is unproved.

An exact preliminary identity is accessible in the weaker canonical `L¹`
space: absolute generator integrals are `log(2)/d`, so the damped family is
integrable for every `ε>0`, and its mean should be
`∫A_ε = log(2)/ζ(1+ε)`. The existing weighted-dilation Mellin theorem at
`s=1` applies once the generator's endpoint integral is identified directly
from the parity/norm identity. This avoids extrapolating the old open-strip
formula through its apparent pole.

Because `A_ε=1` on `(1/2,1]` and Haar is `−1` on `(0,1/2]`, the proposed
canonical energy identity, for an admitted source, is
`||A_ε||² = 1 − 2 Re(log(2)/ζ(1+ε)) + ||A_ε−Haar||²`.
Thus a unit budget would require the actual squared error to be at most twice
this explicit mean. Neither that error estimate nor small-damping admission
is assumed. First certify the unconditional mean and the exact decomposition.

- Mean query completed: `partial=false`, no errors, complete 63,751-file
  inventory, unavailable semantic coverage; result generation 1,170,573 versus
  coverage generation 1,170,575. All 20 candidate and 20 source statements and
  proposed chain reviewed. The damped divisor-sum identity plus an unrelated
  reciprocal integral does not supply this source mean or canonical norm.
  Inspected `PMDilationMellin` 35–89 and the existing power-damped Mellin
  application 99–130; the generic theorem has no `Re s<1` restriction once
  actual generator convergence at `s=1` is supplied. Mathlib's
  `MemLp.integrable_norm_pow` gives the parity-based endpoint integrability.

- Full 22-declaration large-damping scratch passed empty. Created/wired
  `PMPowerDampedMobiusLargeDamping.lean`; targeted/final audits pending.
  The exact energy correction and large admitted norm-growth pairs are certified
  in scratch. Pending no-go card: `pm-power-damping-monotonicity.md`.

- Large-damping leaf: 415 lines / 22 declarations. Targeted build (32 seconds),
  final actual-source check (empty), and exhaustive body/name/index/import checks
  passed. Axiom/API probe checking. Next six-declaration scratch
  `/tmp/pm_power_mean_1025.lean` prepares unconditional positive-damping `L¹`
  admission and exact mean through the verified endpoint generator integral.
  It has not yet been run; only one owned compiler process is active.

- Large-damping audit closed: all 22 declarations have exactly the standard three
  axioms and correct public signatures. Combined PM-31: nine leaves / 2150 lines /
  121 declarations. The failed monotonicity card moved to
  `5-failed/pm-power-damping-monotonicity.md`, retaining the exact positive
  survivor `2^ε(E_ε−log 2)→−2κ`, `κ≥1/12`. This gives norm growth beyond every
  damping threshold, without deciding small-positive admission or the unit budget.
  The six-declaration endpoint-mean scratch is now running.

- Unit-budget deep search 1026 completed without errors or partial results.
  Inventory complete: 63,759 files; result generation 1,170,754, coverage
  1,170,763, current 1,170,766; semantic coverage not measured within reporting
  budget, background refresh incomplete. All 20 candidate and 20 source
  statements plus the proposed ingredient chain reviewed. The chain invokes
  `IsCancelling.energy_cancel`, which assumes antisymmetric trilinear interaction;
  no such interaction is supplied for the literal Fermi source. Its other links
  give individual coefficient bounds and an absolute finite coefficient sum,
  not a unit canonical budget. `MobiusDivisorFiniteClockCountingCancellation`
  1–115 and 175–255 retains both signed source factors in its mixed term; the
  nonpositive copied-diagonal payment does not bound that complete mixed term.
  No usable canonical unit-budget producer was found in these returned hits.
- Mean scratch now includes the residue slope and exact admitted energy
  decomposition. First check exposed cast/function elaboration issues and the
  incorrect use of floor≤1 from reciprocal<2; corrected to floor<2. No numerical
  experiment or unproved estimate is being used.

### Canonical L¹ convergence from shrinking prefix errors

Let `R_N` be the raw Fermi prefix and put
`e_N=||R_N−Haar||_{L¹(0,1)}`. Exact Möbius inversion makes this error vanish
on `(1/(N+1),1]`. Cauchy–Schwarz on the remaining interval gives
`e_N≤||R_N||₂/sqrt(N+1)+1/(N+1)`. The existing normalized prefix estimate
therefore gives `e_N≤C/log(N)^2+1/N` eventually, and hence
`Σ_{N≥1}e_N/N<∞` and `e_N→0`. All prefixes are individually admitted, so
finitely many initial terms cause no issue.

Finite Abel summation writes the damped prefix error as its final weighted
raw error plus `Σ_{n<N}(n^(−ε)−(n+1)^(−ε))(R_n−Haar)`. The coefficients
plus final weight sum to one, and each nonnegative difference is at most
`ε/n` for `ε>0`. Minkowski gives
`||A_{ε,N}−Haar||₁≤N^(−ε)e_N+εΣ_{n<N}e_n/n`. Letting `N→∞`, pointwise
stabilization and Fatou prove the dependency-closed paper conclusion
`||A_ε−Haar||₁≤C₁ε` for all `ε>0`, with the finite canonical constant
`C₁=Σ_{n≥1}e_n/n`. In particular the literal sources converge in canonical
L¹. This supplies neither L² admission nor its uniform bound.

The same summable majorant suggests an L¹ parameter derivative equal to the
pointwise Chebyshev difference. Its Banach-space derivative proof is a separate
stronger candidate; do not report it as Lean certified.

- Corpus query 1027: partial=false, no errors, complete 63,760-file inventory;
  result generation 1,170,804, coverage 1,170,811, current 1,170,812; semantic
  coverage unmeasured within reporting budget, background refresh incomplete.
  All 40 candidate/source statements and proposed chain reviewed. The chain
  mixes other source families and improper integral convergence with exact
  finite-prime stabilization; it does not provide a uniform norm estimate.
  Existing raw-prefix Haar equality, full-prefix normalized norm bound, finite
  Abel identity, and summable reciprocal-log-square lemma are the exact inputs.
  No duplicate canonical L¹ convergence theorem found among returned hits.

- Mean leaf created/wired: `PMPowerDampedMobiusMean.lean`, 203 lines / 12
  declarations. Targeted old build passed (34 seconds); final actual leaf check
  passed empty. All declaration bodies and unique names passed exhaustive scan.
  API audit initially expected qualified table names; actual generated entries
  are unqualified with a separate module column. Corrected API check passed for
  all 12 entries and the unique umbrella import. Axiom probe running. Lint has
  only ten unrelated unwired modules (the prior LiClockCoshCosCutoff issue is gone),
  with no own/proof-debt/generated-file finding.
- L¹ shrinking-error scratch prepared at `/tmp/pm_power_l1_1028.lean`; not yet
  run. It uses the exact localized prefix error and the corpus Cauchy–Schwarz
  integral theorem. After the summable reciprocal error budget, finite Abel
  error sums stabilize pointwise, so Fatou can transfer a uniform `C₁ε` budget
  directly; no limiting boundary term estimate is needed for that last step.

- Mean audit closed: all 12 declarations have exactly `propext`,
  `Classical.choice`, `Quot.sound`; public signatures checked in full. Combined
  PM-31: ten leaves / 2353 lines / 133 audited declarations. Canonical positive
  L¹ admission, exact mean, mean/ε→log 2, first-band value, Haar mean and admitted
  source/error energy identity are certified. Small-positive L² admission and
  the unit budget remain open. Owned mean scratch/audits and reviewed research
  1026/1027 outputs cleaned. The seven-declaration shrinking-error scratch 1028
  is now the sole owned compiler job.

- Shrinking-error scratch first run: the localized Cauchy–Schwarz/energy
  estimates elaborated, but final addition orientation, one nested lambda and
  denominator comparison tactics needed repairs. Expanded scratch now checks
  all prefix summability and finite Abel norm estimates (15 declarations).
  The final pointwise stabilization/Fatou/L¹-convergence fragment is prepared
  separately and will be joined only after the current compiler exits.

### Next candidate: canonical L¹ derivative and its L² boundary

The known pointwise derivative is `D(t)=ψ(1/t)−2ψ(1/(2t))`. For `n≥1`,
put `ℓ_n=log(n+1)−log n`. Then `0≤ℓ_n≤1/n`, while the Abel quotient
`λ_{ε,n}=(n^(−ε)−(n+1)^(−ε))/ε` satisfies the same bounds for `ε>0`
and tends to `ℓ_n` as `ε↓0`. The reciprocal error budget makes
`Σ 2e_n/n` finite, so dominated convergence of the scalar series gives
`Σ|λ_{ε,n}−ℓ_n|e_n→0`. Differentiating the exact pointwise stabilized
finite Abel identity identifies `D(t)` with its logarithmic-gap error sum.
Minkowski/Fatou therefore give the dependency-closed paper conclusion
`||(A_ε−Haar)/ε−D||₁→0`. In particular `D` is canonically integrable and
its integral is `log 2`, by the already-certified mean slope. This stronger
right-derivative conclusion is not yet Lean formalized.

A separate boundary candidate is `D∉L²(dt)`. Its safe-half-plane Mellin
formula should be `−(1−2^(1−s))ζ′(s)/(sζ(s))`. A critical zeta zero would
produce a nonzero simple pole even when the zero is multiple, while canonical
L² Cauchy–Schwarz permits only inverse-square-root boundary growth. The
Mellin identity/continuation, critical-zero existence and boundary estimate
still need exact corpus interfaces and a dependency audit; this is currently
a candidate, not a certified obstruction.

- Query 1029 completed: partial=false, no errors, complete 63,768-file
  inventory; result generation 1,171,038, coverage 1,171,039, current 1,171,047;
  semantic coverage unmeasured within reporting budget, background refresh
  incomplete. All 40 candidate/source statements plus ingredient chain read.
  Existing Chebyshev error L¹ integrability is useful, and PM-25 already proves
  the weighted `t dt` square integral. The chain's Xi-half-plane equivalence
  still requires a prime-window power bound and gives no unweighted derivative
  admission. No literal derivative L¹ convergence or L² nonadmission theorem
  was supplied by the returned hits.

- Full 19-declaration L¹ convergence scratch passed empty. Created/wired
  `PMPowerDampedMobiusL1Convergence.lean`; targeted and final audits now pending.
  It certifies the shrinking-support Cauchy–Schwarz bound, summable reciprocal
  raw error budget, positive Abel gap estimates, exact finite error decomposition,
  canonical finite-sum budget, pointwise stabilization and Fatou transfer, and
  the literal source's canonical L¹ Haar convergence with linear damping rate.
  No L² admission is inferred.

- L¹ convergence leaf: 260 lines / 19 declarations, targeted old build passed
  (186 seconds). Exhaustive declaration body/name/API/unique-import audit passed.
  Final actual source check is running. First lint snapshot has ten unrelated
  unwired modules and concurrent staleness in LEAN_GAPS/LEAN_OVERVIEW; index and
  lint refresh is running. No source edit or repeated compiler check was needed.
- Critical-pole query 1030 completed: partial=false, no errors, complete
  63,771-file inventory; result generation 1,171,063, coverage 1,171,069, current
  1,171,072; semantic coverage unmeasured, background refresh incomplete. All
  40 statements and proposed chain reviewed. Near-one log-derivative estimates
  and one explicit crossed-pole energy do not furnish the proposed general
  boundary conclusion. Direct source inspection found the applicable generic
  `HTGeometry.norm_laplaceRay_le` (`rayL2Norm/sqrt(2 Re w)`), existing PM Mellin
  head-chart bridge, `logDeriv_residue_of_factorization`, and unconditional
  `exists_riemannZeta_zero_re_half`. These are interfaces for the candidate,
  not an already proved dyadic-source L² obstruction.
- Prepared `/tmp/pm_power_derivative_1031.lean` with eight initial declarations
  for the actual difference quotient, its pointwise derivative, uniform L¹
  norm budget, and canonical integrability of the Chebyshev derivative source.
  It has not been run. Strong derivative convergence and L² nonadmission are
  still subsequent proof obligations.

- L¹ convergence audit closed: final actual leaf passed empty; all 19 axiom
  reports and public signatures passed using exactly the standard three axioms.
  Combined PM-31: twelve leaves / 2917 lines / 181 audited declarations.
  The source has the unconditional canonical bound
  `eLpNorm(A_ε−Haar,1)≤ofReal(ε*Σ_n e_n/n)` and converges to Haar in L¹.
  Small-positive L² admission and RH remain open. The final global lint snapshot
  still reports ten unrelated unwired modules plus concurrent staleness of
  LEAN_API/LEAN_GAPS/LEAN_OVERVIEW after regeneration; no owned or proof-debt
  finding. Do not report global lint as passing or chase concurrent changes.
  All owned 1028 compiler/audit files and reviewed 1029/1030 searches cleaned.
- Derivative scratch 1031 expanded to 19 declarations: the initial canonical
  quotient/source package plus logarithmic gap limits and a summable vanishing
  scalar error majorant. First run is now active. Strong L¹ derivative and exact
  derivative mean still need their final finite-sum/Fatou assembly; L² boundary
  nonadmission remains a separate unformalized candidate.

- Derivative scratch: initial 19 declarations reached only a final real-ring
  rearrangement in the logarithmic gap derivative; corrected it. All other
  pointwise/norm/Fatou and scalar dominated-series parts elaborated. Joined the
  ten-declaration finite-sum and integral assembly; full 29-declaration scratch
  is checking. No derivative leaf has been promoted yet.

- Full derivative scratch passed; promoted/wired `PMPowerDampedMobiusDerivative`
  (304 lines / 29 declarations). Targeted old build passed in 33 seconds and
  final actual `lake env lean` passed empty. All promoted bodies, 29 exhaustive
  name checks, public API entries and unique umbrella import passed. Axiom
  reports are running. Global lint has the same ten unrelated unwired modules;
  no generated-document staleness or owned/proof-debt finding this snapshot.
- Boundary query 1032: partial=false, 63,776 files, generation 1,171,395,
  coverage 1,171,395/current 1,171,396; query 1033: partial=false, 63,778 files,
  generation/coverage/current 1,171,429. Both have no errors, semantic coverage
  unmeasured within reporting budget, background refresh incomplete. All forty
  candidate/source statements and query chains per query reviewed. Existing
  continuous-Chebyshev log-derivative transform is applicable after a source
  transfer, but returned Haar/Mangoldt hits do not supply the exact dyadic
  transform.

### Exact derivative-transform construction (paper proof)

Use the supported Haar function `h₀=1_(0,1] * Haar`, since the existing
`dyadicHaar` definition alone is not zero outside the carrier. For every t>0,
`D(t)=Σ_n Λ(n) h₀(nt)`: both sides are exactly
`ψ(1/t)−2ψ(1/(2t))`, including endpoints. These sums are locally finite.
The certified arithmetic dilation Mellin interchange applies for Re s>1,
using absolute summability of the von Mangoldt Dirichlet series and
`Mellin(h₀)(s)=(1−2^(1−s))/s`. Hence
`Mellin(D)(s)=−(1−2^(1−s))*logDeriv(ζ)(s)/s`. This is a direct absolutely
convergent transform proof; no infinite parameter derivative interchange.
The L² obstruction still needs pole-cleared continuation and the boundary
residue contradiction; do not treat this paper construction as Lean-certified.

- PM-31 derivative audit closed: `PMPowerDampedMobiusDerivative` (304 lines /
  29 declarations) passed targeted old build, final actual leaf, every axiom
  report (standard three only), exact body/API/name/unique-import gates.
  The actual difference quotients converge in canonical L¹ to the dyadic
  Chebyshev source, whose signed integral is log 2. Combined: twelve audited
  leaves / 2917 lines / 181 declarations. Small-positive L² admission and RH
  remain open; the derivative's proposed L² exclusion is not yet certified.

### Canonical derivative L² obstruction (dependency-closed paper argument)

Assume D is in canonical L² on the positive ray; D vanishes above one. Its
Mellin transform F is analytic on Re s>1/2. Put U=(s−1)ζ with U(1)=1.
The exact safe-half-plane identity extends on that whole connected half-plane
after clearing denominators:
`s(s−1)U(s)F(s)=−(1−2^(1−s))*((s−1)U′(s)−U(s))`.
Both sides are analytic there, including s=1. At any critical zeta zero ρ,
U has finite positive order m (U is entire, U(1)=1). Its isolated-zero
factorization gives `(s−ρ)logDeriv U(s)→m` on the punctured neighborhood.
Along s=ρ+x, x>0, the cleared identity therefore gives
`x F(ρ+x)→−m*(1−2^(1−ρ))/ρ`, a nonzero value.
Canonical L² Cauchy–Schwarz instead yields
`|F(ρ+x)|≤C/sqrt(2x)`, hence `xF(ρ+x)→0`. Contradiction.
Unconditional critical-zero existence is already in the corpus. Thus D is
not canonically L²; together with the strong L¹ derivative and weighted
`t dt` energy, this gives a sharp distinction between available tangent
control and the canonical Hilbert tangent. It does not rule out L² admission
for every positive damping. All source/continuation/boundary assembly gates
remain Lean-open at this point; no failed card has been closed.
