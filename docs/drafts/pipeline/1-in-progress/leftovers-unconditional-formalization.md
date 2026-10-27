# Unconditional formalization of every leftover paper card

- **ID:** leftovers-unconditional-formalization
- **Stage:** 1-in-progress
- **Execution:** ACTIVE; resumed by the user's 2026-10-27 attachment.
- **Type:** FORMALIZATION PROGRAMME
- **Source:** user attachment `7b8e0d61-b048-4085-aa55-1ca6d2ead9d1/pasted-text-1.txt`
- **Scope:** Every proven theorem in all 14 cards initially in
  `docs/drafts/pipeline/2-fully-proven/leftovers/`, including their referenced paper proofs.

## Completion requirements

Preserve exact statements and constants. Supply every missing mathematical dependency;
do not replace producers with implications assuming their conclusions. No new axioms,
admissions, trusted computation, computations, or raised Lean limits. Search the project
corpus before mathlib or new proof code. Compile each changed leaf directly with
`lake --old env lean`, one foreground process at a time. Audit transitive dependencies
with `#print axioms`. Wire leaves into their owning umbrellas without compiling umbrellas.
Move each card to stage 3 only after every theorem on that card is covered and audited.
Existing unrelated worktree changes must be preserved.

## Resumed scope and current evidence (2026-10-27)

The new attachment `de463029-56c4-4da2-b432-00025a675f49/pasted-text-1.txt`
resumes the full programme. All eleven cards currently under
`2-fully-proven/leftovers/` remain in scope, including every proved ancillary
claim and required infrastructure. The historical pause below is superseded.
Stage-3 promotion still requires exact statement coverage, direct source
checks, transitive axiom audits and umbrella wiring; historical logs alone
do not establish current completion.

The resumed inventory contained eleven stage-2 cards. Initial source search
located existing cycle-recovery leaves. The near-complete bi-scale cards
still explicitly record missing parameter selection, counting, exact-incidence
energy and common-model transport. The geometric and analytic cards retain
their complete original scope. The finite-cycle card is now promoted;
ten stage-2 cards remain. Four of the original fourteen cards are fully
formalized, including the three cards completed before the resumption.

**Completed resumed card:**
[finite closed-cycle recovery](../3-formalized/leftovers/biscale-finite-cycle-recovery-1810.md).
All fourteen canonical leaves have final direct source checks, and all 133
public declarations have standard-axiom audits. Source hashes, final logs
and unique imports are verified together in
`/tmp/leftovers-cycle-full-evidence.json`. The historical combined audit
contains one redundant-tactic warning, already removed before its canonical
final check; every canonical final log is free of errors and warnings.
The full programme remains active.

Pre-existing edits to the RH reports, the arithmetic-electrostatics source,
renormalization sources, and selective-positivity source are unrelated and
must be preserved.

### Finite-cycle completion argument

Set `c=exp(-1/2)`, `R=max(1,32E/(c ε²))`,
`η=exp(-1-128E/(c ε²))`, `d=ceil(R/ρ_E)`, where
`ρ_E=exp(-1-8E/c)`. Then `R≤(d+1)ρ_E` by the ceiling
inequality. The literal pair/spoke family has at most
`2(ceil(2R/η)+1)` observations, each closed and of length at most
`d+2`. The exact existing grid theorem gives
`‖h-g‖∞≤max(ε,2^(d+1)(δ_C+(d+1)δ₂)+ε/2)`.
Writing `A=2^(d+1)(d+2)`, any common bound `δ` on every
literal observation discrepancy gives `‖h-g‖∞≤max(ε,Aδ+ε/2)`.
Thus the explicit positive threshold `ε/(2A)` guarantees error
at most `ε`. Against arbitrary measured arrays the sum of both
source fitting residuals is such a discrepancy bound, by the
triangle inequality. Every parameter depends only on `E,ε`.

For a general finite η-net, the scalar recovery theorem at each
sample gives the same separate pair/spoke maximum bound. For any
window point select a net point and use two modulus inequalities
and the triangle inequality. Outside the common support both
correlations vanish. This establishes the paper's arbitrary-net
statement, including endpoints and radius zero, without imposing
uniform spacing. Formalization of these exact ancillary claims is
the active dependency-complete step; all other cards remain in scope.

`GridCycleRecoveryParameters.lean` is certified and wired. The second
scratch audit exited 0 with all 21 declarations depending only on
`propext`, `Classical.choice`, `Quot.sound`. The identical canonical leaf
passed its direct final check with exit 0 and no diagnostics (tool session
66674, `/tmp/leftovers-cycle-parameters-final.log`). Source hash:
`9aba018dce162eb2d792fc34587a546921693300f07cca511692a845cf8f7931`.
Its new declarations are indexed. The first audit's two elaboration errors
were resolved; no mathematical statement changed.

Only the missing `GridFiniteCycleRecovery` and `ClosedCycleDataResiduals`
oleans were built for the parameter leaf's imports (sessions 91383 and
74044, both exit 0, no diagnostics). No existing olean was rebuilt, and
no olean was written for the new parameter leaf because no new file imports it.

`/tmp/leftovers_finite_net_cycle.lean` includes arbitrary finite nets and
measured-array residuals with exact coefficient
`(1+(d+1)/(2κ))/κ^(d+1)`. Its first source/axiom audit passed all 12
declarations using only standard axioms; it reported three unused-instance
warnings. The section variables were narrowed to remove those warnings.
The revised audit exited 0 without warnings, with the same twelve
standard-axiom declarations (`/tmp/leftovers-cycle-finite-net-audit-r2.log`).
The identical canonical `FiniteNetClosedCycleRecovery.lean` passed its
direct final check with exit 0 and no diagnostics (session 13857,
`/tmp/leftovers-cycle-finite-net-final.log`); its umbrella import is wired.
Source hash: `d02e14edf392e0876441cb577887f1c9e1f7e076426236a570ae8bde53f838e9`.
Its missing olean was built successfully solely for the downstream derivative
and L² imports (session 79035, exit 0, no diagnostics;
`/tmp/leftovers-cycle-finite-net-build.log`).

Full source review found that the existing exact derivative-conditioned
bound still specializes to uniform meshes. The same scalar derivative bound
at arbitrary net points, followed by the two source Lipschitz estimates,
gives `2δ_C+2(d+1)δ₂+2sqrt(B)η` for every finite net. For measured arrays,
replace both discrepancies by the total fitting residual, yielding coefficient
`2(d+2)`. This exact remaining coverage is drafted in
`/tmp/leftovers_finite_net_derivative_recovery.lean`, intended canonical
`FiniteNetDerivativeRecovery.lean`. It imports the new finite-net base and
`DerivativeCycleConditioning`. Both missing dependency oleans have now been
built individually. The derivative-conditioning build exited 0 (session
45794, `/tmp/leftovers-cycle-conditioning-build.log`), with the same two
informational ring notices already recorded for that unchanged source.
The two-declaration derivative-net audit passed without diagnostics and with
only standard axioms (session 55203,
`/tmp/leftovers-cycle-finite-net-derivative-audit.log`). The identical canonical
leaf is wired and passed its final direct check (session 33158, exit 0,
empty `/tmp/leftovers-cycle-finite-net-derivative-final.log`). Source hash:
`b5003d1a916f58649a5f0214ae7a2164c54321e312b30a4591b39c78664ea6f4`.
The complete statement review and source-hash/import checks passed, and the
card was moved to stage 3. Matching plain scratch mirrors were removed;
the audit sources and evidence logs remain.

The base collar theorem has an additional source-domain obligation: its
paper statement uses nonzero real L² sources, whereas the existing
`LevyEnergySource` wrappers require compact C² sources. Corpus search found
`RHTower/Suzuki/SuzukiCriticalL2Energy.lean`, whose actual `MemLp` lemmas prove
continuity, the translation matrix-coefficient identity, origin mass equal
to squared L² norm, and the absolute correlation bound. Its olean already
exists. A full L² source extension must use these proved inputs, literal
normalized cycle products and the same scalar recovery lemma; no finite
energy, compact-source or smooth-source premise is allowed in this base
extension. The actual correlation-support, collar, modulus and finite-net
conditions are precisely the original controlled-class conditions. The
derivative and singular-energy specializations retain their stated source
regularity assumptions. Card promotion waits for this full-domain extension
as well. No scope reduction is accepted.

The full-domain draft is `/tmp/leftovers_l2_closed_cycle_recovery.lean`
(intended canonical `L2ClosedCycleRecovery.lean`). It defines actual integral
correlations of `SobolevShear.Velocity=L²(ℝ,ℝ)` sources, proves normalization,
evenness, unit bounds and representative invariance, and uses literal finite
cycle products. Its exact norm and measured-array recovery theorems require
only the original control conditions. The modulus is monotone only on the
nonnegative ray, matching its mathematical domain. All seventeen public
declarations had appended axiom queries in
`/tmp/leftovers_l2_closed_cycle_recovery_audit.lean`. The first check found
two interface issues: `Velocity` does not support field notation `f.memLp`,
and bounded-continuous-function notation needed its scope opened. The source
now derives the bound and continuity directly from the proved translation
matrix coefficient and translation isometry, adding a named continuity lemma.
The third **18-declaration** audit passed with only standard axioms and no
diagnostics (`/tmp/leftovers-cycle-l2-audit-r3.log`, session 37236, exit 0).
An explicit argument fixed the remaining modulus-membership elaboration.
The identical canonical `L2ClosedCycleRecovery.lean` is wired and passed its
direct final source check (session 85675, exit 0, empty
`/tmp/leftovers-cycle-l2-final.log`). Source hash: `e5c8619c7059039704b60013e8137e740706a1d3597f234345e744091a5b608c`. No new hypothesis or mathematical
statement weakening was used to resolve the errors.

### Exact-incidence and common-model completion argument

Define the physical exact energy as the sum over all ordered window pairs
of `(f(j)-f(i))²` when `x(j)=2x(i)`, and zero otherwise. For integer positions,
the sum reduces exactly to the existing doubling energy. For the specified
quadratic nodes, the proved incidence exclusion makes every term vanish.
The already proved exact linear-signal variance then forces the original
lower constant `N(N+1)/12`, whereas integer positions retain `24N`.
Choosing `δ=min(ε/2,1/8)` gives a strictly ordered incidence-free grid within
any positive displacement tolerance.

The finite Möbius coefficients already reconstruct every prescribed value
on `1,…,N`. Every endpoint used by the adjacent and doubling sums lies in
this window; all-pairs physical energies use only its values as well.
Termwise substitution therefore preserves every centered sum, its minimizing
mean and variance, and adjacent, doubling, exact-incidence and weighted
energies simultaneously. Consequently the set of valid joint constants is
identical for arbitrary finite signals and actual divisor sieves. The
perturbed quadratic lower bound and weighted positive survivor use the same
coefficient model, with no additional premise.

The weighted survivor's stated sharpness is also made explicit. For
`N=2^(h+4)-1`, the original tent has weighted energy zero, additive energy
at most two, and variance at least `N/2048`. Any valid constant `C` must be
nonnegative, since otherwise its nonnegative-energy right side contradicts
the positive variance. Thus `N/2048≤2C`, yielding `N/4096≤C` for every
allowed perturbation. Exact finite-sieve energy transport gives an equivalence
of the valid weighted constants and the same lower bound on actual divisor
sieves. These three consequences are included in the arithmetic transport
draft. It additionally imports the existing `DyadicMantissaVariance` leaf.
The logarithmic-coordinate identity is explicit as well: each physical node
is at least `1−δ>0`, so exponentiating its logarithm recovers the node and
preserves every actual all-pairs weight. The transport audit now contains
eighteen public declarations.

Uncertified drafts: `/tmp/leftovers_exact_doubling_energy.lean` and
`/tmp/leftovers_finite_sieve_graph_transport.lean`. Their imported existing
leaves `QuadraticPerturbedNodes`, `IntegerLinearVariance`,
`FiniteSieveRealization`, and `WeightedDoublingIncidence` lack oleans and
require individual direct dependency builds before these drafts can compile.
No second Lean process is started while a check is live.

### Original dyadic ancillary statements

Further uncertified drafts preserve the paper's separate intermediate claims:
`/tmp/leftovers_binary_depth_coercivity.lean` has the exact geometric path
sum, weighted Cauchy--Schwarz, descendant bound at actual binary depth,
`8N(2/3)^k` edge charge, and the stated `8NT` tree bound.
Its first six-declaration audit found a rewrite issue in the geometric path
sum; the four descendant/tree declarations already had standard axioms.
The successor step now uses the qualified `Finset.sum_range_succ` rewrite.
The revised audit is running (session 79411,
`/tmp/leftovers-binary-depth-audit-r2.log`).
`/tmp/leftovers_dyadic_level_counts.lean` counts explicit last-level blocks:
`[10r,14r)` is high, `[8r,9r) ∪ [15r,16r)` is low, where `r=2^h`.
Their counts are `4r=q/2` and `2r=q/4`, respectively. The original tent
also disproves doubling-only coercivity on every stated dyadic window.

### Continuum comparison argument

The actual quadratic logarithmic displacement is at most `δ/N`. The
existing singular-energy modulus therefore gives, for the same actual
source, a sample change at most
`sqrt(8E/(exp(-1/2)(-log(δ/N))))`. This transfers exact zeros to approximate
zeros in either direction without identifying correlation constraints with
graph incidence. A zero-to-half correlation jump at displacement `d≤1`
forces `E≥exp(-1/2)(-log d)/32` directly from the squared-increment bound.
These exact statements are drafted in
`/tmp/leftovers_perturbed_correlation_samples.lean`, not yet certified.

For the complementary exact-zero obstruction, let `log 2<T<log 3` and
choose a smooth positive-mass seed with correlation support radius
`ρ=min(1,log(2)/2,(T-log(2))/2,(log(3)-T)/2)`. Two equal copies separated by
`T` have normalized correlation `1/2` at `T` and zero at every `log n`,
`n≥2`: every such lag and both shifted lags miss all three correlation
packets. The existing small-support producer has energy at most `C-log ρ`.
The two-copy normalized correlation agrees with the seed on the fixed
origin interval of radius `log(2)/4`, so the existing local-energy stability
theorem bounds the additional energy by a fixed kernel-tail constant.
Thus exact constraints can fail maximally close to an integer lag only
with logarithmically increasing energy, while bounded-energy sample data
remain quantitatively stable. This is an elementary consequence of existing
source constructions, not an external novelty claim; Lean construction and
the exact quadratic-node specialization are drafted in
`/tmp/leftovers_integer_gap_correlation_peak.lean`, awaiting compilation.

Both Route-E cards have now been read in full. Current lexical corpus search
and direct inspection of `MatomakiTeravainenTwistedFourthMoments` and
`MatomakiTeravainenWattReflection` confirm that their universal Watt/DI bounds
remain `Prop` definitions and short-case consumers, not discharged inputs.
The historical exponent retune to `123/79` does not establish the original
`1.55` statement requested here. Full exact-exponent completion remains required.

### Selberg spectral dictionary re-audit

The non-vacuous witness card's source audit is partly stale: current corpus
search locates `RHTower/HyperbolicOrbitalIntegral.lean`, including actual
hyperbolic dilation orbital integrals, conjugated annuli, and the Abel-transform
formula. This supplies a genuine geometric ingredient, not the zeta dictionary.
The existing `NonvacuousSmallEigenvalue` source remains the small-eigenvalue
producer. Searches for `selbergZeta` in this corpus and then mathlib returned
no matching declaration; searches for representation-valued Eisenstein/Fredholm
continuation did not surface the required noncongruence continuation.
The current sources do not yet discharge the actual Euler product, primitive
class decomposition, noncongruence continuation, truncated trace identity,
or zeta-zero dictionary. The card's warning about residual eigenvalues at the
reflected root remains material: proving only the upper root does not certify
the original two-root assertion. No substitute spectral-parameter polynomial
or assumed trace formula will be treated as a solution.

## Historical user steering: finish started Lean work, then pause (superseded)

The requested closure is complete. All already-started Lean work is checked,
audited, wired and recorded. No Lean process or search job remains active.
Do not start another route, conjecture, auxiliary draft or proof to close the
remaining paper gaps. Resume only on a new user instruction.

The frozen work comprised physical-producer supplements, four PM leaves,
five dyadic leaves and the edited tree owner, two perturbed-incidence leaves,
and ten finite-cycle leaves. All are complete within that frozen scope.

## Frozen checkpoint before the 2026-10-27 resumption

- Three of the 14 original cards are fully formalized and promoted:
  [Nyquist](../3-formalized/leftovers/nyquist-critical-finite-part-2026-10-18.md),
  [physical producers](../3-formalized/leftovers/compact-physical-box-producers.md),
  and [PM quadrature](../3-formalized/leftovers/pm-long-modulus-quadrature.md).
  Their complete statements, source hashes and verification evidence are on
  those cards. Nyquist has eight checked leaves and 96 audited declarations.
  Physical covers the recovered report's claims (1)–(23), with seven checked
  leaves and 134 public declarations plus one reused parent. PM has four
  checked leaves and 20 audited public declarations.
- The five dyadic leaves and edited `FiniteHorizonPositiveCoercivity` owner
  passed final checks. Their 38 public declarations and three changed owner
  declarations use only standard axioms. Exact tree comparison, original tent,
  linear variance, finite Möbius realization, mean/infimum characterization,
  and the exact `N/4096≤C_N≤24N` bounds are certified. The stage-2 card retains
  separate unstarted path/counting and common-model energy-transport gaps.
- Both perturbation leaves passed final checks; all 24 public declarations
  have standard-axiom audits. Actual quadratic nodes, exact incidence
  exclusion, log gaps, all-pairs weighted comparison and the stated weighted
  coercivity constant are certified. The stage-2 card retains exact-incidence
  energy, arithmetic transport and continuum-correlation gaps.
- All ten cycle leaves passed final checks; all 80 public declarations have
  standard-axiom audits. Source derivative bounds, actual unit-mass sources,
  arbitrary-collar recovery, literal finite observations, measured residuals,
  exact grid recovery, derivative conditioning and controlled sharp copies
  are certified. Ancillary parameter-selection coverage remains on the
  stage-2 card; item 9 and the entire paper card are not declared closed.
- Final closure ledger `/tmp/leftovers-final-check-ledger.json` records 22
  canonical source checks: the 21 new PM/dyadic/perturbation/cycle leaves and
  the edited tree owner. Every check exited 0, with no errors or warnings.
  Twenty-one logs are empty; `DerivativeCycleConditioning` emits two
  informational ring notices, matching its clean axiom audit. Its tactic
  composition warning was removed and its final source checked.
- Ten missing internal oleans were built solely for imports by already-started
  modules: three PM, two dyadic and five cycle dependencies. Every build passed.
  The one missing external variance-owner olean also built successfully;
  `/tmp/leftovers-dyadic-mean-owner-build.log` records it. No existing olean was
  rebuilt, and no umbrella or full project build was run.
- All 21 new leaves have exactly one import in their owning umbrellas: four
  arithmetic-continuation and seventeen bi-scale. The tree owner's existing
  import is unique. Final hashes, exact indexed module paths and proof-integrity
  scan passed for all 22 checked sources. Physical and Nyquist certificates
  retain their earlier successful import/hash/index checks.
- Global lint `/tmp/leftovers-frozen-final-lint.log` reported 20 unrelated
  structural errors and 417 size warnings, with no frozen-scope diagnostic.
  This is not a claim that global repository lint passes.
- Identical plain scratch mirrors for every finished group were removed.
  Valid combined source/axiom audits, declaration manifests and logs remain
  in `/tmp`. The frozen module manifest is
  `/tmp/leftovers-frozen-module-manifest.json`; it contains 24 new module paths,
  including the three physical supplements already certified separately.
- Both Route-E historical cards were read. Existing assemblers retain
  `MTDeshouillersIwaniecBound` and `MTWattBound`; inspected short-block
  reductions retain their short forms as hypotheses. No unconditional
  completion or absence claim was made. These and all other unstarted cards
  remain paused. No contribution count or RH claim was advanced.

## Inventory and current evidence

| Card | Required completion / current evidence |
|---|---|
| `biscale-dyadic-joint-coercivity-1810` | **Started Lean scope complete and wired.** Five leaves plus edited tree owner checked; 38+3 standard-axiom declarations. Remaining unstarted path/counting/transport gates recorded; card not promoted. |
| `biscale-finite-cycle-recovery-1810` | **Started Lean scope complete and wired.** Ten checked leaves, 80 standard-axiom declarations, exact recovery/source controls/sharpness. Ancillary parameter-selection coverage remains; card not promoted. |
| `biscale-perturbed-incidence-1810` | **Started Lean scope complete and wired.** Two checked leaves, 24 standard-axiom declarations. Exact-incidence energy, arithmetic transport and continuum questions remain; card not promoted. |
| `compact-physical-box-producers` | **Complete, promoted to stage 3.** Recovered report (1)–(23), seven leaves, 134 public declarations plus one reused parent, clean axiom and final source checks, unique imports and indexed names. |
| `nonvacuous-independence-and-polarization-import-law` | Audit small-eigenvalue witness, complete actual Selberg-zeta dictionary and nonvacuous clauses. Historical log reports witness complete; current source audit pending. Import table explicitly an observation. |
| `nyquist-critical-finite-part-2026-10-18` | Finite part, signed broad-test expansion, actual-source classification and witnesses. Existing 591-line parent inspected. Primitive, signed cell bounds, exact broad tests and source classification pass Lean. Primitive-tail leaf passes its final direct check. Quantitative source and signed witness claims are complete; all 96 public declarations have clean axiom audits. All eight final direct checks passed; complete card promoted to stage 3 after source/hash/index/import audit. |
| `pm-long-modulus-quadrature` | **Complete, promoted to stage 3.** Four checked and wired leaves, 20 standard-axiom declarations, exact Möbius quadrature and square-root-head pronic bound; full tail retained past max(n,D). |
| `route-e-cofactor-amplified-e3-token-supply` | Exact all-interval supply with all elementary bounds; shared Matomäki–Teräväinen/DI analytic input. Full historical-log and current-source audit pending. |
| `route-e-forbidden-support-e3-stability` | Exact forbidden-support all-interval count with shared analytic input. Full historical-log and current-source audit pending. |
| `route-tt-structural-theorems-2026-10-14` | All actual theorem statements, corrected T3, T5, L7, exact T2 exponent and later proven addenda. Historical coverage list is evidence to investigate, not completion. Explicit conjectures/gapped sketches must stay labelled. |
| `smooth-stein-order-two-autonomous-ade-frequency-rank` | Actual Stein/CR/contact/Reeb geometry, Weinstein input, dimension theorem and ADE hull corollary. Paper read; no theorem-shaped assumptions allowed. |
| `twisted-minimum-principle` | Audit existing TMP and consequence; construct the explicit primal annihilator, corner/Dirichlet/Green ingredients, and audit rigidity claim. Paper read. |
| `verified-height-one-zero-turing-extension` | Exact endpoint `768044885196911/256`, unconditional verified prefix and increment. External Arb/Platt–Trudgian numbers do not constitute Lean proofs; generic implication does not close this card. No computations authorized. Current corpus re-audit pending. |
| `weil-cone-pole-duality-anatomy` | Actual automorphic/Dirichlet/curve Weil functionals and A–C, precise conductor thresholds, and proved spectral addenda. Paper read; generic cone abstractions alone insufficient. |

## Working record

- 2026-10-26: attachment read; 14-card inventory established. Root/formal instructions read.
  Initial broad corpus search was partial and unhelpful; targeted lexical search located
  compensated-producer, Nyquist, and energy-cycle leaves. No absence inference.
- Search evidence: `/tmp/leftovers-existing-leaves-search.json`.
- First active leaf: finish actual convergence and compact-source forms for the compensated
  physical producer, reusing the existing construction. This is one dependency-complete
  card within the full programme; the other 13 remain in scope.
- The missing compensated-producer paper report was not found under `docs/`; its exact
  convergence argument is now written on the original card. A new convergence leaf is
  being checked; no card has been promoted on the basis of uncompiled source.

## Completed physical-producer verification

- New leaf: `BiScaleUncertainty/CompensatedPhysicalProducerConvergence.lean`.
  First direct check reached all declarations and found only elaboration/rewrite errors;
  explicit pointwise powers, function composition reductions and square-zero rewrites
  were repaired. Second direct check (tool session `43673`) exited 0 with no diagnostics.
- Downstream leaf written: `BiScaleUncertainty/CompensatedPhysicalProducerFormLimits.lean`.
  It proves actual source/jump energy limits, beyond convergence in the form error.
  The convergence leaf's missing olean was built successfully (session `77026`, exit 0)
  solely for this import. Downstream direct check (`17384`) found one explicit
  `Iic`-membership elaboration error; repaired, along with two deprecated lemma names.
  Updated-source scratch audit (`24204`) exited 0, no diagnostics. All 110 axiom
  lists contain only `propext`, `Classical.choice`, `Quot.sound`.
  Final direct downstream check (`24077`) exited 0, empty log.
- Both leaves wired into `BiScaleUncertainty.lean`; exact statement audit complete.
  Card moved to stage 3. Global lint: 19 unrelated structural errors, 416 existing
  size warnings; neither new leaf has a diagnostic. Corpus index returns new limits.
- Public declaration inventory so far: `/tmp/leftovers-physical-public-names.json`
  (16 restriction, 67 construction, 21 convergence, 6 downstream declarations).
  Audited scratch source: `/tmp/leftovers_physical_axioms.lean`.
- `scripts/check_axioms.sh` imports the package umbrella and audits unrelated names.
  Use a targeted `#print axioms` scratch file covering every public declaration of
  the exact leaves instead; do not claim that the global script was run.
- Additional corpus leads for the later Nyquist/cycle cards are in
  `/tmp/leftovers-nyquist-kernel-search.json`, `/tmp/leftovers-smooth-autocorrelation-search.json`
  and `/tmp/leftovers-autocorr-increment.json`. No new Nyquist/cycle proof code written.
## Active Nyquist checkpoint

- Nyquist broad-test proof mechanism: freeze the test at each cell's left endpoint.
  The discrepancy contribution is bounded by `6 D Lip(H)/L`, using
  `log n ≤ 2 sqrt(n)` and the existing power-tail bound at exponent `-3/2`.
  Cell oscillations contribute `(2 D + 4 c) Lip(H)/L`, using positivity and
  the power-tail bound at exponent `-2`. This recovers the exact paper constant
  `8 D + 4 c` without differentiating a Lipschitz test. Complete proof record is
  on the card; formalization still pending, no completion or novelty claim.
- Nyquist completion proof now recorded on its stage-2 card, including continuous
  primitive, exact broad-test constant, source classification and witnesses.
  Primitive scratch check (`89244`) reached all declarations, exposing two `0+k`
  reductions, one explicit set-membership elaboration and one rational-expression
  normalization issue. All repaired. Source is now
  `BiScaleUncertainty/NyquistCriticalPrimitive.lean`.
  First olean attempt (`76728`) found a line-broken field-notation elaboration
  issue in the local-integrability helper. Replaced it with typed local facts.
  Recheck/build (`98466`) exited 0 with no diagnostics; primitive olean now exists
  for the cell-bound import. Log `/tmp/leftovers-nyquist-primitive-build.log`.
  Final direct source check and axiom audit remain.
  Cell-error and summable-majorant prototype: `/tmp/leftovers_nyquist_cell_bounds.lean`
  (scratch check now active; imports `NyquistCriticalPrimitive`). Intended module name:
  `NyquistCriticalTestCellBounds`.
  Signed expansion prototype: `/tmp/leftovers_nyquist_broad_tests.lean` (not checked;
  imports planned `NyquistCriticalTestCellBounds`), intended module name
  `NyquistCriticalBroadTests`. Covers arbitrary compact Lipschitz tests and all
  positive scales, both half-line and full-line residual integrals.
  Unused guessed-name probe inventory and obsolete physical draft were removed;
  the actual primitive scratch proof checked the relevant APIs directly.
  Existing Nyquist parent olean is present. No new Nyquist umbrella import yet.
- Source-classification reuse leads: `RHTower.LogWindowPrimeNumberTheorem`
  has `RHTower.WeilOneSided.exists_autoCorr_constants` and `abs_autoCorr_sub_le`,
  proved from source Lipschitz control, with the minus-lag autocorrelation convention.
  Use `autocorr f x = WeilOneSided.autoCorr f (-x)` to transport it, rather than
  duplicate the proof. `ArithmeticCriticalityTheory.ShiftAveragedKernel` has
  `integral_Ioi_eq_half_of_even`. `UnitEnergySmallSources` has
  `autocorr_eq_zero_of_source_radius`, useful for the actual lag-4 witness.
  All three existing oleans were checked present. Source-classification prototype
  is now `/tmp/leftovers_nyquist_sources.lean` (not checked), intended module
  `NyquistCriticalSourceClassification`. It includes normalized correlation,
  source-derived Lipschitz constant, exact mean-square slope, actual rescaled-source
  residual, full quantitative expansion, finite-part and slope limits, both mean
  alternatives and vanishing normalized energy.
  Actual signed-witness prototype `/tmp/leftovers_nyquist_witnesses.lean` is now
  written (not checked), intended module `NyquistCriticalSignedWitnesses`. It proves
  smoothness for every `r : ℕ∞` (not analytic order), nonzero source values, positive
  bump mean, normalized lag-four value `-1/2`, and the connected two-source dichotomy.
- Once primitive olean succeeds: check `/tmp/leftovers_nyquist_cell_bounds.lean`,
  repair and migrate to `NyquistCriticalTestCellBounds.lean`; build its missing
  olean for the broad-test prototype. Continue in dependency order through broad
  tests, source classification and witnesses. Every final project leaf still
  requires direct source check, axiom audit and umbrella wiring before promotion.

## Later-card read-only preparation

- PM corpus search: `/tmp/leftovers-mobius-quadrature-search.json` and
  `/tmp/leftovers-pm-centered-prefix-search.json`. Actual centered prefix is
  `RHTower.pmPowerDampedCenteredDivisorPrefix` in `PMPowerDampedMobiusDiscreteEnergy`.
  Its exact floor identity is in
  `ArithmeticContinuationAndCriticalEnergy/TheEscapeIsATailPhenomenon.lean`.
  `SignedArithmeticEnergyIncidence/ShortIntervalSumsOfTheDampedDivisorCoefficients.lean`
  defines the exact harmonic `moebiusTail` and proves a related centered-prefix
  decomposition, with `density_re_eq_tsum` and the existing `sum_rpow_neg_head_le`
  mechanism. Read the first 240 lines of that leaf and the escape leaf.
  These do not yet certify the requested long-modulus integrable producer.
  No PM source edits or new paper theorem have been made.

- Nyquist cell-bound check `2836` failed only elaboration: missing `NNReal` scope,
  partially applied majorant definition, numeric tail simplification, `0+k`,
  and unspecified integral measures. Repaired in scratch; check `34323` running.
- Further PM reuse: exact `sum_Ioc_mul_natDiv_eq_sum_Icc_Ioc` in
  `BezoutValuationIncidence/HyperbolaCancellationWithDivisorBoundedCoefficients`;
  generic `HTGeometry.integrable_tsum_of_summable_integral_norm` in
  `HTGeometry/L1PeriodizationFourier`. Both statements and proofs inspected;
  existing oleans present. No duplicate generic integration lemma needed.
  Actual PM producer prototype `/tmp/leftovers_pm_integrable_producer.lean` written,
  not compiled: exact floor cutoff, pointwise indicator series, integrability,
  and full signed harmonic-tail integral. PM card remains unfinished.

- Cell check `34323` reached all declarations. Numeric bounds passed; repaired
  integral function elaboration with typed sum/difference integrability facts,
  supplied width positivity explicitly, and used `abs_add_le`. Canonical leaf
  is now `BiScaleUncertainty/NyquistCriticalTestCellBounds.lean`; missing olean
  build `48915` active for its downstream broad-test import.
- PM sampling prototype `/tmp/leftovers_pm_sampling.lean` written, not compiled;
  uses the existing exact hyperbola-swap theorem, retains every positive integer
  sample and the entire harmonic tail. Intended imports are the producer leaf
  `ArithmeticContinuationAndCriticalEnergy/LongModulusIntegrableProducer` and
  the existing hyperbola-cancellation leaf. No PM olean built or source promoted.

- PM exact-decomposition prototype `/tmp/leftovers_pm_exact_decomposition.lean`
  written, not compiled. It supplies the unconditional all-cutoff prefix identity
  and the long-sawtooth/full-tail identity when the natural cutoff lies below `n`.
  The first prototype now exposes `pmLongModulusIndicatorTerm` publicly, so its
  exact series statement does not leak a private definition. All PM drafts remain
  `/tmp` prototypes; no completion claim.

- Nyquist cell-bound olean build `48915` exited 0, empty log. The exact
  summable majorant and signed cell bound are kernel checked. Broad-test scratch
  `/tmp/leftovers_nyquist_broad_tests.lean` is now checking.
- PM short-head search found `abs_oscillatingShortSawtooth_le` and
  `pronicNorm_oscillatingShortSawtooth_le`; these use `oscillatingSmoothPower`,
  whose coefficient definition must be checked before reuse for actual Möbius.
  Their public generic bound `sum_sq_le_of_abs_le_sqrt_rpow` may discharge the
  exact pronic constant even when the oscillating coefficient is different.

- PM oscillating coefficient is `d^(-ε) cos(t log d)`, not Möbius; do not
  identify it with the actual source. Reuse only the public generic
  `sum_sq_le_of_abs_le_sqrt_rpow`, whose exact pronic constant was inspected.
  `/tmp/leftovers_pm_short_energy.lean` now supplies the actual Möbius finite-head
  bound, exact floor-square-root exponent (including `n=0`) and all-horizon
  energy. Uncompiled. It imports the existing generic majorant leaf (olean
  present), not the large oscillating-source leaf (olean absent).
  Four PM prototypes cover the complete paper statement; they remain unchecked.

- Broad-test scratch check `57515` failed only two local elaboration details:
  explicitly typed `G`'s integrability with Lebesgue measure and reduced the
  function application before the zero-kernel rewrite. Canonical leaf now
  `BiScaleUncertainty/NyquistCriticalBroadTests.lean`; missing olean build `11180`
  active for source classification. Source-classification and witness drafts
  remain uncompiled. Superseded primitive/cell scratch files removed safely.
- Later dyadic-card audit: `FiniteHorizonPositiveCoercivity.doubling_window_coercivity`
  supplies the stronger upper bound `6N` on all integer windows. Read its
  statement and relevant path/native-edge arguments, plus the entire
  `FiniteHorizonCoercivityClassification` leaf. Its cosine witness only supplies
  lower constant `N/6144` for `N≥1024`, so it does not discharge the paper's
  exact dyadic tent or `N/4096` bound on all `N=2^(h+4)-1`. No dyadic source edits.

- Dyadic read-only follow-up: native energies and `biScaleJointEnergy_eq_zero_iff_const`
  inspected in `UniversalRamanujanCovarianceAndBiScaleRigidity` (lines 575–680).
  Two long semantic queries returned partial results with semantic deadline errors;
  short rephrasings completed. Returned tent hits do not establish the requested
  integer-mantissa tent. Scoped lexical energy and variance searches are saved
  under `/tmp/leftovers-*-lexical.json`. No absence claim.
- Possible later tent proof mechanism (not yet implemented): define the normalized
  triangle on each dyadic level; prove increment bound `1/q` for `q≤n<2q`.
  Since `n(n+1)<4q²`, its squared increments are at most `4/(n(n+1))`.
  The root increment is zero; telescoping from `n=2` gives the paper's strict
  additive energy bound `<2` without reindexing every complete level. Exact
  high/low last-level counts still required for `N/4096`. This is a planning
  observation, not a new theorem certificate or replacement of the requested witness.

- The next Nyquist source prototype's half-line integral now explicitly types
  Lebesgue integrability, avoiding the same elaboration error just found in
  broad tests. `exists_autoCorr_constants` was rechecked: its constant is
  source Lipschitz bound times `∫|f|`, then normalization divides by `∫f²`.
- Dyadic common-model lead `ArithmeticEdgeSieveFamily.signal_realization` was
  inspected, but concerns prescribed arithmetic edge coordinates rather than
  arbitrary integer window values; it is not yet accepted as the requested
  common-window realization. Further inversion searches pending.

- Broad-test olean build `11180` exited 0, empty log. Exact signed expansion
  holds for every compact Lipschitz test and all positive scales, in half-line
  and full-line forms. Source prototype corrected two visible issues before
  checking: target the lag variables in `abs_sub_comm`, and supply nonzero
  squared value (rather than positivity) to the compact-integral positivity API.
  Canonical broad source and olean retained; final direct audit remains.

- Current owned Lean command: source-classification scratch check `59754`,
  log `/tmp/leftovers-nyquist-sources-check.log`; it imports the successfully
  built broad-test leaf. All search sessions from this batch have completed.
  Three checked Nyquist leaves are now wired into `BiScaleUncertainty.lean`;
  no umbrella compilation. Broad scratch removed after byte comparison with
  the canonical checked source. Final direct checks and axiom audit remain.
- PM card now labels its old significance deferral as historical and records
  current authorization and unverified prototypes. No mathematical statement
  or gate was weakened or marked complete.

## Recovered report audit

- Missing current-tree reports exist in Git history. Both were deleted by
  `80971df8c`; their latest retained text is at `727dc15d1`. Read the full
  Nyquist report there. It additionally states: primitive error is absolutely
  integrable with exponential tails; every source Lipschitz constant gives the
  explicit normalized constant `K_f ∫|f|/∫f²`; exact first-moment energy bound;
  locally uniform normalized correlation convergence; `|H|≤1`; and the signed
  witness's negative lag occurs at `4L`. Existing drafts do not yet expose all
  these statements, so Nyquist promotion remains blocked on their formalization.
  This is additional required coverage, not a weakened theorem.
- The physical report at the same commit is being re-audited against its
  completed certificate. Its stage-3 status must be reconsidered if that
  report contains an uncovered theorem. No claim of exhaustive historical
  report coverage should be made until this comparison is complete.

- Full physical report read at `727dc15d1`. Its additional explicit claims are
  not all covered by the 110 audited declarations: equation (14), separate tail
  limits, square-root norm and derivative bounds, physical-interval uniform
  convergence and combined exact-coefficient form bounds. Card moved back to
  stage 2 and status corrected. Existing checked proofs and umbrella imports
  retained. No card is now certified complete for the recovered full-report
  scope; finish these corollaries before restoring physical promotion.
- Source scratch `59754` exited 1: only missing `integral_div_const`, a lower
  neighborhood orientation and one redundant `ring`. Repaired, then expanded
  the source leaf with exact source-derived Lipschitz constants, pointwise
  normalized scaling and every-source-Lipschitz-constant error bound. Canonical
  `NyquistCriticalSourceClassification.lean` (250 lines) is building in `27290`;
  log `/tmp/leftovers-nyquist-sources-build.log`. No other Lean process owned.

- Source build `27290` exited 1 with two elaboration errors: continuous-map
  coercion prevented the autocorrelation bridge rewrite, and a beta-redex
  prevented the normalized-scaling rewrite. Both repaired by explicit `change`;
  redundant sequential tactic removed. Retry `57154` is running, log still empty.
- New unchecked Nyquist drafts: `/tmp/leftovers_nyquist_primitive_tail.lean`
  (absolute tail admission, exponential absolute-integral bound, uniqueness,
  exact width-dependent cell variation), `/tmp/leftovers_nyquist_source_quantitative.lean`
  (absolute normalized bound, exact energy identity/ceiling for every source
  Lipschitz constant, bounded-interval uniform convergence, mean-zero iff).
  Witness draft extended with support-boundary vanishing, exact mass/lag, and
  normalized negative lag `4L`; now imports planned quantitative leaf.
- Physical historical-report follow-up: existing `PhysicalBoxProfile` directly
  proves local absolute continuity, a.e. derivative, and L² membership;
  `PhysicalBoxAverage.physicalBoxDerivative_norm_le` supplies the derivative norm.
  Reuse these, do not re-prove generic box regularity. Exact two-tail draft
  `/tmp/leftovers_physical_tail_identity.lean` now contains the general interval
  identity, specified exponential truncation identity, separate squared/norm
  tail limits and complete separate-tail producer error. Unchecked.

- Source-classification canonical build `57154` exited 0, empty log; olean now
  exists and must not be rebuilt. Quantitative draft may import it. Current
  owned Lean check is primitive-tail scratch `57108`, log
  `/tmp/leftovers-nyquist-primitive-tail-check.log` (empty so far).
- Physical unchecked drafts now also include `/tmp/leftovers_physical_quantitative.lean`
  (exact square-root norm, continuous/a.e./L²/local-AC profile regularity,
  derivative norm, all-real affine norm, physical trace bound and uniform
  convergence including zero) and `/tmp/leftovers_physical_form_bounds.lean`
  (general exact combined coefficient, finiteness, explicit three-term
  approximation cost, affine cost and separate error-form limits). Both import
  checked convergence; no new olean needed unless a downstream source requires it.

- Read the complete finite-cycle recovery leaf (478 lines) and reread its card.
  Existing `EnergyCycle` uses actual signed products, a floor mesh (including
  zero radius), and source-independent recovery; its elementary scalar and
  power-difference lemmas are private. Exact card coverage still needs arbitrary
  κ, explicit observation count, derivative-energy source controls and distant
  copies. The marked singular-energy gate is not an exact-constant certificate:
  existing collar exponent is `32 max(K,0)/c`, while the card states `8E/c`.
  Prove the latter from the first-order deficit bound; do not silently substitute
  the former. Existing finite mesh can be reused; no new finite-cycle code yet.
- Refreshed nonvacuous-dictionary search found spectral-parameter arithmetic and
  Selberg-conjecture status, not the actual cofinite Selberg-zeta zero dictionary.
  This ranked search is only a lead, not an absence proof. Card's residual
  eigenvalue symmetry caveat remains material; full dictionary audit required.

- PM endpoint audit added the all-cutoff exact formula to its decomposition
  prototype: quadrature equals the long sawtooth minus the full harmonic tail
  past `max n D`. This reduces to the usual tail past `n` for `D≤n`; for `D>n`
  the floor sum is empty and the tail begins at `D`. The centered-prefix
  decomposition already covered every natural `D`. This makes the domain
  boundary explicit without adding an analytic premise.
- Primitive-tail scratch `57108` exited 1 with two local elaboration errors
  (newline field notation parsed at the wrong argument; pointwise function
  subtraction not reduced before `linarith`). Repaired and migrated to
  `NyquistCriticalPrimitiveTail.lean`; final direct check `86169` active,
  log `/tmp/leftovers-nyquist-primitive-tail-final.log`. No tail olean created.
- Source quantitative scratch now includes a trailing axiom audit for 78 public
  declarations across the existing Nyquist parent and five expansion/source
  leaves. Manifest `/tmp/leftovers-nyquist-public-names.json`; strip its marked
  audit suffix when migrating the canonical quantitative source.

- Removed superseded `/tmp/leftovers_nyquist_sources.lean`; canonical checked
  source is authoritative. A mathematical-comment wording cleanup was made
  afterward (no proof change and no olean rebuild). Final direct audit remains.
- Quantitative source draft now also states local uniform convergence for the
  literal normalized autocorrelations of `sourceRescale`, not only the equal
  scaled test `H(x/L)`. Its pending axiom manifest now has 79 declarations.
- Later finite-cycle derivative-control leads: vendor Sobolev translation bound
  `DifferentialGeometry.Analysis.Sobolev.eLpNorm_translate_sub_le_smul_eLpNorm_fderiv`
  (smooth Euclidean source, `Tools/Translation.lean:392`, proof inspected near
  lines 340–430); main-corpus `ArithmeticIncidencePositivity.hasDerivAt_autoCorrelation`
  in `LagChebyshevAbelSummation.lean:1292` (not yet inspected). A direct physical
  box-difference argument could reuse the already certified box contraction,
  but check these precise existing inputs before writing a new translation bound.

- Finite-cycle source derivative lead inspected: the main-corpus
  `ArithmeticIncidencePositivity.hasDerivAt_autoCorrelation` is for arbitrary
  real compact C¹ functions and gives exactly `∫ F(x) F'(x+t)`; its underlying
  correlation convention matches `autocorr`. Vendor translation theorem is
  specialized to `EuclideanSpace ℝ (Fin d)`, so it needs a transport to ℝ and
  is not a drop-in real-source lemma. Prefer reuse of the existing real
  derivative/cross-correlation inputs if they close the exact energy constants.
- Dyadic planning refinement, not a certificate: the exact mantissa tent can be
  represented on each closed dyadic level `q≤n≤2q` by `min(n-q,2q-n)/q`,
  with both endpoint representations zero. This handles the level boundary in
  the adjacent difference bound. For variance, pairing `q+j` and `3q/2+j`
  for `0≤j<q/8` gives value separation at least `1/4`, hence a uniform
  two-point squared-error lower bound. Summing these disjoint pairs would
  imply the required conservative `N/2048` bound without weakening the actual
  specified tent. Formal level identities and counting still required.

- Primitive-tail canonical final check `86169` exited 0, empty log. Wired its
  import into the field umbrella without compiling the umbrella. No olean
  generated. Its five public declarations still need the axiom audit.
- Current owned Lean check: quantitative source scratch `87480`. Command logs to
  `/tmp/leftovers-nyquist-quantitative-check.log` and includes the 79-declaration
  transitive axiom audit. Only one owned Lean process runs.

- Quantitative scratch `87480` exited 1 with exactly two local errors and one
  unused tactic: typed positive `x` was needed in an absolute-value rewrite,
  and a newline before `.trans_lt` parsed as function application. Fixed with
  an explicit typed fact and named bound; unused `change` removed. The 79 axiom
  lists were emitted: 75 only standard axioms; four depend on the two failed
  proof terms and are NOT certified. No placeholder occurs in source.
- Canonical `NyquistCriticalSourceQuantitative.lean` is now building (`66611`)
  solely for the witness import. No prior olean existed. After success, do not
  rebuild it. Source quantitative scratch retains its fixed proof plus audit
  suffix; canonical source excludes the suffix.
- Combined next audit `/tmp/leftovers_nyquist_witnesses_audit.lean` checks the
  witness and exact canonical primitive-tail source, and prints 96 public
  axiom lists (all 79 previous names plus witness/tail names). It is a no-olean
  audit source. Canonical witness must be migrated ONLY from the separate
  `/tmp/leftovers_nyquist_witnesses.lean`, not this combined audit source.
  The witness's obsolete UnitEnergySmallSources import was removed.
- New unchecked dyadic draft `/tmp/leftovers_dyadic_tent.lean`: actual
  Nat.log-based mantissa tent, zero at powers of two, exact closed-level
  formula, bounds `[0,1/2]`, and exact doubling invariance. No energy/variance
  proof or canonical dyadic source yet. Nat.log API statements were read
  from surfaced mathlib source; their verification awaits this scratch check.

- Dyadic tentative leaf now also bounds adjacent increments by reciprocal
  level width and squared increments by `4/(n(n+1))`. Reuses the surfaced
  mathlib `abs_min_sub_min_le_max`, instead of duplicating the minimum
  Lipschitz estimate. Still unchecked; no canonical file or certificate.
  Exact-level and energy/variance consequences remain to finish.
- Common-model read: `BezoutValuationIncidence.sieveSeq` is the actual
  truncated sum over divisors in `[1,N]`. Refreshed searches did not yet find
  a general arbitrary-window realization. Möbius inversion can supply it,
  after checking the project leads and mathlib APIs; no generic realization
  proof written yet. `FiniteHorizonIntegerVariance` concerns logarithmic
  cosine windows, not the required linear sequence's exact variance formula.

- `/tmp/leftovers_finite_sieve_realization.lean` now gives explicit finite
  Möbius-antidiagonal coefficients and the actual `sieveSeq` window identity,
  using mathlib's `sum_eq_iff_sum_mul_moebius_eq` (statement and proof inspected
  in `ArithmeticFunction/Moebius.lean`). It is unchecked, not an abstract
  realization interface. Supports both graph cards' common-model gate.
- `/tmp/leftovers_integer_linear_variance.lean` now contains the exact
  `N(N²−1)/12` variance decomposition, its minimizing mean, adjacent energy
  `N−1`, and the necessary additive coercivity coefficient `N(N+1)/12`.
  Unchecked. Generated additive interval-sum APIs were located through their
  `@[to_additive]` product declarations in `BigOperators/Intervals.lean`.

- Canonical quantitative build `66611` exited 0, empty log. Exact energy and
  local-uniform/iff statements now pass Lean. Olean exists for witness; do not
  rebuild. Wired umbrella import. Superseded quantitative scratch (same proof
  plus obsolete 79-name audit suffix) removed after byte comparison.
- Current check `84590` runs the combined witness/tail audit and 96-name axiom
  manifest. No canonical signed-witness source yet. If it fails, update both
  the plain witness draft and its combined audit copy before retrying; only
  migrate plain witness to the repository. Final direct checks remain for
  Primitive, TestCellBounds, BroadTests, SourceClassification, SourceQuantitative
  and final witness. PrimitiveTail's exact final source check already passed.

- Tent scratch now includes native doubling energy zero and telescoping
  adjacent-energy bound `A(N)≤2−4/N<2` for every `N≥2`. All this remains
  unchecked. It imports the existing positive-coercivity olean (present);
  no extra dependency build is currently needed for its eventual check.

- Dyadic tent draft now also contains exact non-root level increment and full-level energy
  identities, including the transition to the next level. Still unchecked.
  Physical supplements combined for one scratch audit of their 21 public declarations:
  `/tmp/leftovers_physical_supplements_audit.lean`; not started.
  Pair-variance corpus search running as `73739`; result file
  `/tmp/leftovers-paired-variance-search.json`.

- Dyadic exact variance and best-constant draft written:
  `/tmp/leftovers_dyadic_variance.lean`, not checked. Uses original tent and
  disjoint paired blocks, proving the exact requested N/2048 and N/4096 constants.
  Finite-mean minimum/attainment corpus search running as `54595`.

- Existing finite-block arithmetic-mean minimization located and its full proof read:
  `TransHorizonIncidenceMechanics.sum_range_sq_sub_mean_le` in
  `MultiGapFermiSchedulesPAdicTracesAndOriginBulkTightness.lean:290`.
  Its olean is absent. Checking existing mathlib equivalents before adding
  a cross-programme import. Needed to certify attainment of the best constant,
  not only bounds on its infimum.

- Added `/tmp/leftovers_finite_window_variance.lean` using the existing finite-mean
  minimization theorem, with explicit reindexing to Icc 1 N. Dyadic variance
  draft now proves the infimum constant is itself valid and controls the
  literal minimum variance. All these drafts remain unchecked. The generic
  infimum helper needs only existence of one valid constant; no boundedness
  premise is smuggled into the dyadic theorem.
- Nyquist global lint exited 1: 21 unrelated errors, 416 size warnings;
  no Nyquist diagnostic. Log `/tmp/leftovers-nyquist-lint.log`. The current
  final witness check is `89531`; all 96 axiom lists are already clean.

- Final canonical witness check `89531` exited 0, empty log. Six Nyquist
  source checks remain including the original parent (PrimitiveTail already
  passed earlier); the 96-name axiom audit covers all eight leaves.
- Weighted-incidence searches completed (both partial=false). Reused the
  surfaced binary-parent coercivity; other returned weighted continuum
  results do not give the finite all-pairs matching claim. New unchecked
  draft `/tmp/leftovers_weighted_doubling_incidence.lean` proves explicit
  weights, off-pair exclusion, exact all-pairs reduction, energy comparison,
  tent nullity, and the exact 24N/(1-6δ) coefficient.

- Finite-cycle exact-collar draft added: `/tmp/leftovers_energy_collar_exact.lean`.
  It derives the paper radius exp(-1-8E/exp(-1/2)) from the existing first-order
  deficit theorem, including the closed collar endpoint, and the exact mesh
  exponent 128 at accuracy ε/4. The previous radius used squared increments
  and exponent 32; this draft retains the required exact constant 8. Unchecked.
- Active Lean remains original Nyquist parent final source audit `86965`.
  All newly launched corpus searches have completed; no active search handle.

- Original Nyquist parent final check `86965` exited 0 without diagnostics.
  No parent source edits or olean rebuilds.

- Added exact quadratic-node prototype `/tmp/leftovers_quadratic_perturbed_nodes.lean`:
  actual positions/logs, strict ordering, physical gaps, displacements,
  2δ mismatch bound, exclusion of physical doubling and log-two separation,
  and the precise `(1+δ/N)` logarithmic gap comparison. Unchecked.
- Native joint-kernel theorem verified in source:
  `BiScaleUncertainty.biScaleJointEnergy_eq_zero_iff_const`,
  `UniversalRamanujanCovarianceAndBiScaleRigidity.lean:615`.
- Source-derivative bridge searches completed. They locate existing physical
  primitive/box infrastructure but no direct real-source derivative L²
  translation bound among returned statements. No absence inference.
  Proposed reuse: pack compact derivative into Velocity, use its FTC
  primitive identity and physical-box contraction for the exact Bt² bound.
- Active Lean is Nyquist Primitive final check `28954`.

- Dyadic scope audit additionally retains the original card's auxiliary
  assertions: exact tree comparison T≤3D+2A (existing private helper only
  exports T≤3(A+D)), original high/low level-group counts, weighted-path
  and depth-descendant statements. The paired-block proof certifies the
  desired lower constant but must not silently discard these stated
  finite-sum/counting claims. No full dyadic certificate yet.

- Nyquist card now records all exact claim-to-declaration mappings, 96-name
  axiom audit, current source hashes, and final-check status. Stage remains 2.
  Do not append a duplicate certificate section when finishing; update it.
- Current corpus searches: compact-source MemLp and FTC reuse, launched after
  the derivative-velocity bridge query. Arbitrary-collar search completed
  partial=false; it surfaced the existing half-collar scalar/recovery proof,
  whose source has been inspected. No arbitrary-kappa declaration among
  returned statements; no global absence claim.

- Primitive final canonical source check `28954` exited 0 without diagnostics.
- New unchecked finite-cycle scalar/family prototype:
  `/tmp/leftovers_cycle_scalar_recovery.lean`. Exact arbitrary positive κ,
  literal pair/spoke products, closedness, ceiling observation count and
  maximum-order bound. Whole-window/noisy-array transfer and actual
  derivative-controlled source classes remain to connect.

- Drafted `/tmp/leftovers_compact_source_derivative_energy.lean` (unchecked).
  Actual compact source and derivative are packed into physical L²; FTC
  identifies the derivative primitive, and existing box contraction proves
  the exact translation estimate ∫(f(u+t)-f(u))²≤t²∫(f′)² for every real t.
  This reuses the constructed physical operators instead of adding an
  assumed derivative-energy admission or redoing translation integration.
  Mathlib MemLp/FTC/derivative-support signatures were inspected; their
  actual usage still needs the scratch compile.
- All launched searches are terminal. Active Lean is TestCellBounds final
  source check `90003`, log `/tmp/leftovers-nyquist-cells-final.log`.

- TestCellBounds final source check `90003` exited 0 without diagnostics.

- Derivative-correlation continuation mechanism: use the existing exact
  `RHTower.ArchimedeanAnomaly.integral_sub_shift_sq` (source inspected at
  `ArchimedeanAnomalyConstantLaws.lean:228`) with the new translation draft,
  then existing `autocorr_krein_increment_sq_le` (source inspected at
  `KreinIncrementAndChordCascade.lean:381`). This gives exact normalized
  quadratic deficit and Lipschitz constant sqrt(∫(f′)² / ∫f²), with no
  separate Cauchy/translation construction. Source-mass positivity can reuse
  the already checked public `nyquistSourceMass_pos`; do not duplicate it.
- Active Lean is BroadTests final check `65625`.
  Support-diameter corpus search just launched; other searches terminal.

- BroadTests final canonical check `65625` exited 0, empty log.
  SourceClassification final check `75617` is active; Quantitative remains.
  Exact index query returns witness, primitive-tail, and quantitative energy
  declarations (`/tmp/leftovers-nyquist-final-index.json`).
- New unchecked derivative-correlation draft:
  `/tmp/leftovers_compact_correlation_derivative_bounds.lean`. It imports
  the planned CompactSourceDerivativeEnergy and checked Nyquist quantitative
  source leaf, defines actual normalized Dirichlet energy, and derives exact
  quadratic collar, sqrt-energy Lipschitz coefficient, and interval-diameter
  correlation support. No added regularity or convergence premise.
  Current corpus derivative query completed and supplied existing Krein/
  source-mass parents; no direct derivative-energy result among its leads.
  Source-interval proof follows the same literal-support mechanism as the
  existing radius lemma. All searches now terminal.

- SourceClassification final check `75617` exited 0, empty log. The final
  quantitative check is `54703`. All eight Nyquist hashes still match the
  certificate; 96-name audit log remains clean, scoped whitespace check passed.
- Added unchecked `/tmp/leftovers_cycle_controlled_recovery.lean`: literal
  separate pair/spoke error maxima, exact mesh and global modulus bounds,
  actual uniform norm bound, and a constructed common Levy-energy class
  for any two nonzero compact smooth sources. No energy ceiling is assumed
  when connecting to the original source domain. Arbitrary noisy-data
  residual transfer and derivative-conditioned recovery still remain.

- Extended exact-collar draft with the closed-radius logarithmic modulus
  and closed continuity-radius estimate. New unchecked
  `/tmp/leftovers_grid_cycle_exact_recovery.lean` connects these to exact
  grid tail radius 32E/(cε²), mesh exp(-1-128E/(cε²)), and the stated global
  max(ε, 2^n(δC+nδ2)+ε/2) bound in pointwise and uniform norms.
  Spoke indexing uses n+1 inner edges, so the paper's positive integer order
  parameter is represented by n+1.
- Removed the verified byte-identical plain Nyquist witness scratch mirror.
  Combined 96-name audit remains at `/tmp/leftovers_nyquist_witnesses_audit.lean`.

- Exact-order corpus refinement found the actual owner
  `SharpCycleDetectionOrder.lean` (not DistantCopySharpness). Read it,
  StrictCopyCycleCharge, UnitCorrelationBump and DistantCopyEnergyTopology.
  New unchecked `/tmp/leftovers_controlled_sharp_cycle_sources.lean` puts
  every separated copy into the existing fixed constructed energy ceiling,
  preserves seed correlation on |x|<1, proves support radius T+1 including
  endpoints, and transfers exact floor(T)+1 order to normalized literal
  closed values. Nonempty arbitrary-order witnesses use T=m+3, amplitude1.
  All these are actual smooth sources; no abstract source-admission premise.

- Nyquist final quantitative check `54703` exited 0 with no diagnostics.
  Revalidated all eight exact source hashes and unique imports, all 96 exact
  axiom lists, index query and scoped whitespace. Card promoted to
  `3-formalized/leftovers/nyquist-critical-finite-part-2026-10-18.md`;
  one of 14 original cards complete. No new contribution counted.
- Active Lean is physical combined supplement audit `10797`, log
  `/tmp/leftovers-physical-supplements-audit.log`. No olean produced.
- Added unchecked `/tmp/leftovers_derivative_cycle_conditioning.lean`: actual
  B R²≤n conditioning, Bernoulli power floor1/2 using existing Nyquist parent
  lemma, exact scalar2δC+2nδ2 bound, and its actual-source pair/spoke version.
  Still connect this to finite mesh/global sqrt(B) modulus and noisy-array
  residuals; actual normalized unit-source packaging also remains.

- Finite-cycle drafting now includes:
  `/tmp/leftovers_cycle_data_residuals.lean` (arbitrary measured arrays,
  exact sum-of-two-fitting-residuals bound, actual uniform recovery);
  `/tmp/leftovers_derivative_cycle_conditioning.lean` now also has the full
  finite-mesh and global uniform2δC+2nδ2+2sqrt(B)η estimate.
  ControlledClosedCycleRecovery draft gained one shared mesh-interpolation
  helper; arbitrary-collar and derivative cases reuse it. All remain unchecked.
- Exact unit-mass compact-source normalization corpus search is active
  (`83439`); no normalization code yet. Physical supplement audit remains
  `10797`, without diagnostics so far.

- Physical supplement audit `10797` exited1. Four elaboration issues:
  unreduced lambda applications in two tail squeeze inequalities, reversed
  add_le_add_right orientation, and NNReal coercion hiding the positive-
  primitive rewrite. Repaired explicitly. The fifth error was duplicate
  compact_formEnergy_ne_top; search located the existing stronger all-anchor
  theorem in CompactSourceGraphAdmission:159. Deleted duplicate proof and
  retained the existing parent in the audit. New supplement count is20,
  plus that one reused parent (131 total unique names including prior110).
  Old r1 axiom log has elaboration-generated sorryAx and is invalid.
  Combined exact source/audit regenerated; r2 check just started with -j1.
- Added unchecked `/tmp/leftovers_unit_mass_compact_sources.lean`: actual
  inverse-square-root amplitude normalization, mass1, preserved correlation
  and derivative energy, and literal smooth nonempty derivative-controlled
  class from SharpCycle.seed with exact source-derived collar parameters.
- Route-E audit resumed: read both long cards through line720. Original1.55
  statements remain required; historical1.557 retuning is not a substitute.
  Current corpus contains final cofactor/forbidden assemblers but they still
  take MTDeshouillersIwaniecBound and MTWattBound. These inputs require proof;
  no wrapper counts as unconditional completion. Search evidence under
  `/tmp/leftovers-route-e-{supply,forbidden}-search.json`.

- Physical r2 supplement audit `67801` exited0. All21 exact query names
  verified; every list uses only the standard three axioms, no diagnostics.
  Migrated the three byte-identical plain component files to TailBounds,
  Quantitative and FormBounds; wired each once. No oleans produced.
  Canonical direct checks and complete report certificate remain.

- User requested finish-and-wire of already-started Lean work, then pause.
  Frozen scope above supersedes the previous continue-all-cards instruction.
  Physical TailBounds final check remains94906; all searches terminal.
- Additional physical scratch `/tmp/leftovers_physical_smoothed_integral.lean`
  contains four unchecked report consequences: actual compact profile, finite
  restriction identity, full-line integrability and zero smoothed integral.
- FiniteHorizonPositiveCoercivity now exposes its existing exact estimate
  `binary_energy_le_doubling_additive` and reuses it in the old private joint
  wrapper. Scratch `/tmp/leftovers_binary_tree_exact_audit.lean` pending.
  Existing olean unchanged and must not be rebuilt. No dependent draft needs
  this new public name; they use the already-existing public coercivity.
- Route-E read-only search found `KuznetsovLargeSieveTheorem.large_sieve_gamma0`,
  whose entire source was inspected; actual spectral-to-short-moment connection
  remains unresolved. No new Route-E Lean work was started.

- Physical TailBounds final direct check94906 exited0 with empty log.
  Smoothed-integral four-lemma scratch check started next. PM combined initial
  audit prepared with20 public declarations; all six external oleans present.

## Paused closure: final source ledger

All rows passed direct source checks from `formal/` with `lake --old env lean -j 1`.
Only the ten marked dependency leaves produced new oleans in separate permitted
commands. Source hashes and unique imports were verified after the last check.
The cards above retain exact mathematical coverage and unstarted gaps.

| Module | SHA-256 | Required new olean | Final direct-check log |
|---|---|---|---|
| `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.LongModulusIntegrableProducer` | `362193d428b878cc4c5ae1ab1d04a1e122461d9762a16b483c73f08748b1f1f8` | yes | `/tmp/leftovers-pm-integrable-final.log` |
| `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.LongModulusQuadratureSampling` | `dd2f9abe6a6b07615bcd653b73d4f6999ff30e09d3f70eff26a182363520640d` | yes | `/tmp/leftovers-pm-sampling-final.log` |
| `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.LongModulusExactDecomposition` | `ddfa3dd0aa31cf7ac53cfcfa901d3f7f5ef918bf861bc56fd4afe5814ed34b8d` | yes | `/tmp/leftovers-pm-decomposition-final.log` |
| `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.LongModulusShortEnergy` | `90c3ceeb202d6834f4b4fdc097d5355044ad87745939ec84050d92e716802e84` | no | `/tmp/leftovers-pm-short-energy-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.DyadicMantissaTent` | `acd4ef93ae199c3bfdc4e6540eed9ebe32769291c998de416af1b8439ffe818d` | yes | `/tmp/leftovers-dyadic-tent-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.IntegerLinearVariance` | `0dccb554cd2563d43ee770a701736e7586811a933fbdb2e79f016b3dcf2ede7f` | no | `/tmp/leftovers-integer-variance-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.FiniteSieveRealization` | `c85efe0fc79eaf2434177cbae0b675d37fec3f57fd5ff2dfed9824148003eb63` | no | `/tmp/leftovers-sieve-realization-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.FiniteWindowVariance` | `ba0f8560596f92637b3e65800bf17b0d66efe28917622790dd31b64ca25d4584` | yes | `/tmp/leftovers-window-variance-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.DyadicMantissaVariance` | `49d335546715ac9f0d11e1eb737e667d7e8e6f4880f795fa209375beb97f4d7a` | no | `/tmp/leftovers-dyadic-variance-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.WeightedDoublingIncidence` | `f5431b77daf6edf45efeba4a681be25bc9874910f71d16413a97a586915cee03` | no | `/tmp/leftovers-weighted-incidence-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.QuadraticPerturbedNodes` | `ace2e3553f44f6af64eae9d1bc136f7c203009a0952389138fe8682cd0125a49` | no | `/tmp/leftovers-quadratic-nodes-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.FirstOrderEnergyCollar` | `d96b38f6be1733f17fb4178235a3a9349aa91f1e7221920aa2e133cde1849170` | yes | `/tmp/leftovers-cycle-collar-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.ClosedCycleScalarRecovery` | `6dd9cb09d8c4164977a4606d57edb6dc86cecb66f6a0a16d9d781eb199349ef2` | yes | `/tmp/leftovers-cycle-scalar-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.CompactSourceDerivativeEnergy` | `d68db0038dcdfccb63ca5ae375a5b027d5004543affc8e009f613ac2653fd427` | yes | `/tmp/leftovers-cycle-source-derivative-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.CompactCorrelationDerivativeBounds` | `c7c1b6f0e218e24f717f105da2c6560535b9da20d105a55a7ef616db5b1ed989` | yes | `/tmp/leftovers-cycle-correlation-derivative-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.ControlledClosedCycleRecovery` | `5bef47bf1618886765dda55f48368c3001e2336f6f42aaa2653617c41c33d66c` | yes | `/tmp/leftovers-cycle-controlled-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.GridFiniteCycleRecovery` | `860048b5293a00b1aa3bdcea19d636ecf6008cf30f5f044f8611a3f6d3981141` | no | `/tmp/leftovers-cycle-grid-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.ControlledSharpCycleSources` | `59bd4dde72fff6960ba69987df9aaa0041bde8a45a1d362c0821286bb2720aac` | no | `/tmp/leftovers-cycle-sharp-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.DerivativeCycleConditioning` | `a636c585ded88d88feb2cefb216c8254b412e4fbb63b016a8a3ca769a9c878e4` | no | `/tmp/leftovers-cycle-conditioning-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.ClosedCycleDataResiduals` | `2c6240f3264fa3d0268ee73e742d2d4041b7198a57d6674026967585d7b674aa` | no | `/tmp/leftovers-cycle-residuals-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.UnitMassCompactSources` | `e25513b2ddf29de14278ed9edaba87a3cac69cd4dc1bca461af8e902d307a38a` | no | `/tmp/leftovers-cycle-unit-mass-final.log` |
| `GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonPositiveCoercivity` | `847fc32a9a136cc3409d44fcb46256aec6cbd53dff642eec224837ef21be2dc6` | no | `/tmp/leftovers-tree-owner-final.log` |

Paused after finishing the authorized started work. No further mathematical
route or formalization is scheduled or started by this batch.
