# PM multiplicity signature conjecture loop

- **ID:** pm-multiplicity-signature-2026-09-29
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md` §PM; `pm-physical-model-clock-reduction.md` PM-18/19a/19b
- **Statement:** The physical alternating Nyman witness form detects zero multiplicity, not only distinct zero locations.

## Goal

Advance recorded PM-19b without assuming RH, a zero-free region, simplicity, a source positivity law, or any new axiom. No numerical computations. Literal source identities and finite-dimensional algebra must supply every claimed direction.

User updated overarching goal: continue contributing significant PM knowledge until RH is proved or falsified unconditionally in Lean. Completing the multiplicity milestone does not complete that goal; continue the conjecture loop through exact index equality and then the source-side obstruction.

## Plan

- [x] Read PM frontier, source modules, relevant memories, and current instructions.
- [ ] Exhaust corpus search for logarithmic witnesses, confluent coupling, and signature count.
- [ ] Dependency-closed paper proof and public-literature novelty audit.
- [ ] Formalize exact surviving theorem in narrowly imported leaf modules.
- [ ] Direct `lake env lean` audit, axiom audit in `/tmp`, lint, umbrella wiring, cleanup.

## Conjectures and failures

1. Reverse dyadic Haar closure: technically open in local Lean, but card already derives it from bounded equivalent Nyman weight. Classical closure theory found in public sources. Rejected as contribution satisfying requested novelty; retain as infrastructure only if necessary.
2. Multiplicity-sensitive negative index: recorded PM-19b. Candidate: a zero of order `m` gives `m` literal logarithmic witnesses, whose coupling to `m` distinct spurious witnesses is confluent Cauchy and invertible. Their neutral completions produce exact physical Gram matrix `-I_m`. Stronger survivor to investigate: simultaneous hyperbolic signature `(m,m)`.
3. Exact multiplicity index: `witnessNegIndex = rightStripMultiplicityCount`. Lower side is now reduced to the audited literal hyperbolic construction. Upper-side candidate uses correlation-Mellin jets; their common kernel cancels every possible pole of the left dyadic defect, hence is self-similar and neutral. A negative orthonormal family maps injectively into those jets. Finite-dimensional rank bounds its size by total multiplicity; infinite total multiplicity makes the extended upper bound automatic.

## Evidence and limitations

- `FermiNymanWitnessNegativeIndex.lean` constructs `-I_n` for distinct right-strip zeros via `B_lj=(2^(-rho_j)-1/2)/(rho_j-d_l)`; spurious span is neutral.
- `FermiNymanWitnessSelfSimilarityCriterion.lean` localizes non-self-similar witness defects at meromorphic poles unconditionally (PM-19a).
- `MellinIteratedDerivative.lean` identifies all logarithmic source moments with Mellin derivatives for `MellinRapid` densities.
- First broad corpus search returned no lexical AND matches; available hybrid hits had complete source inventory but substantial stale/pending compiler coverage. Narrowed searches underway; applicability requires direct Lean verification.
- No finite search certifies absence from all public literature or training data. Novelty status remains provisional until scoped searches and comparison of exact statements.

## Working log

- 2026-09-29: initialized. Existing dirty files recorded and reserved; no commits/push, no dev server, no full/umbrella build.
- Tool availability: Serena available; `update_plan` and `multi_tool_use.parallel` absent from exposed tools. Plan tracked here; independent reads batched via `Promise.allSettled`.

## Next checkpoint

Read narrow search results; verify reusable Mellin and confluent algebra APIs in `/tmp`; first close all-order literal witness admission. Do not count this ingredient alone as significant final contribution.

## Paper mechanism (candidate, not yet audited)

Write `c(z)=2^(-z)-1/2`, nonzero for `Re z<1`. For a right-strip zero `rho` of order `m`, the functions `conj(d^j/dz^j[t^(z-1)/c(z)] at rho)`, `0<=j<m`, are finite combinations of literal log-power witnesses. Their coupling to spurious witness `g_k` is

`q(g_k,h_(rho,j))=(-1)^j j!/(rho-d_k)^(j+1)`.

Reason: logarithmic Mellin differentiation identifies all source moments; the order of the nonzero eta/source unit times zeta equals the order of zeta; dividing the coupling by `c` removes its triangular jet multiplier. Distinct zero nodes and injective imaginary spurious nodes permit the corpus's complex Cauchy-jet controllability theorem. Thus finite combinations `g_s` of spurious witnesses can satisfy `q(g_s,h_t)=delta_st`, while `q(g_s,g_t)=0`.

For `Q_st=q(h_s,h_t)`, set `v_s^- = h_s - (1/2) sum_t (Q_st+delta_st) g_t` and `v_s^+ = h_s - (1/2) sum_t (Q_st-delta_st) g_t`. Sesquilinearity gives `q(v_s^-,v_t^-)=-delta_st`, `q(v_s^+,v_t^+)=delta_st`, and `q(v_s^-,v_t^+)=0`. This supplies the exact hyperbolic block, hence negative index at least the sum of zero multiplicities in every finite packet.

Audit obligations: all-order L2 log admission; analytic source order; exact conjugation convention; normalized-jet coupling; spurious controllability; no omitted zero or simplicity condition; no computation-backed axiom.

- First ingredient passed scratch Lean: `isFermiNymanWitness_logPower_of_order` admits every log-power jet strictly below zeta analytic order. Source leaf `FermiNymanLogarithmicWitness.lean` created; targeted `lake --old build` underway. No numerical experiments or evaluator-backed proofs used.
- Public comparison: Burnol, *On Fourier and Zeta(s)* (2001), Theorem 7.1, already uses zero multiplicity to characterize jet-vector orthogonality. Logarithmic admission alone is therefore not claimed novel. Exact dyadic-form hyperbolic completion is the candidate distinction.
- A duplicate scratch Lean process was accidentally launched while previous check remained active; older owned process was terminated and its exit verified. Subsequent Lean checks are strictly sequential.

- Narrow PM-jet search returned existing PM-18/19a only, with partial method coverage; exact source searches found no log-power witness or multiplicity-index bridge.
- Serena symbol lookup reports Lean path ignored by configured Python project. Source reads and new-file edits use standard tools.

- All-order admission leaf targeted build passed. Normalized-coupling scratch under audit: compactly supported spurious cuts are MellinRapid; their logarithmic Mellin derivatives compute the literal dyadic pairing. Normalize by the reciprocal of `2^(-s)-1/2` before applying confluent controllability.
- Refined construction avoids choosing an arbitrary finite square confluent matrix: the existing infinite-node complex control map is surjective, yielding finite spurious combinations dual to every finite multiplicity packet. Candidate strengthened to two mutually orthogonal signed families with exact Gram matrices `-I` and `+I`.
- Next capstone is unconditional `rightStripMultiplicityCount ≤ witnessNegIndex`, where the count is the supremum of finite sums over the actual right-strip-zero subtype. Analytic order finiteness will be discharged through the existing xi/zeta order bridge, not assumed.

- Exact normalized-jet/spurious coupling passed scratch Lean without warnings. `FermiNymanConfluentCoupling.lean` created and targeted dependency build started. Reciprocal differentiation uses the toolchain's proved iterated-derivative formula; no numerical computation, evaluator tactic, new premise, or heartbeat increase.
- Import refinement: the multiplicity capstone can prove zeta order finiteness directly by analytic continuation on the punctured complex plane and nonvanishing at `2`. This avoids importing the much broader completed-prime-flux module solely for its xi/zeta bridge.
- Public exact-statement searches (`Nyman-Beurling` with `negative index`, `inertia`, `indefinite`, `dyadic`, `multiplicity`) found no matching physical dyadic theorem. The public 2026 Weil-form inertia framework concerns a different form and compression mechanism; it does not by itself supply the literal Fermi witness construction. Absence from all public literature/training data remains uncertifiable.

## Upper-bound paper mechanism (new conjecture)

For each right-strip zero `rho` of multiplicity `m`, attach the `m` coordinates
`J_(rho,j)(w) = conj(iteratedDeriv j (correlationMellin (conj ∘ w)) rho)`, `j<m`.
The map is complex-linear on finite sums of witnesses: correlation integrates the real alternating generator against `conj(w)`; its bounded compact support makes every Mellin derivative legitimate.

If all coordinates vanish, the analytic order of the correlation Mellin transform at `rho` is at least `m`. The prefactor in the left dyadic defect is analytic, while the entire zeta denominator has order exactly `m`. Thus the quotient has no pole there. Every possible left-half-plane pole corresponds to a right-strip zero: nonvanishing on `Re s >= 1` excludes the rest. Existing unconditional removability then gives self-similarity of `w`, and its dyadic quadratic form is zero.

On a negative orthonormal family, a nonzero coefficient vector gives quadratic form `-sum |c_i|^2 < 0`. Therefore the jet-coordinate map on its span is injective. If total multiplicity is finite, the target has exactly that dimension, proving the upper index bound. If total multiplicity is infinite, the extended-natural upper bound is immediate. This is a dependency-closed paper mechanism; formal obligations remain all-order coordinate linearity, local order cancellation, and finite/infinite counting glue.

- Literal multiplicity signature scratch passed without warnings. New leaf `FermiNymanMultiplicitySignature.lean` then passed targeted `lake --old build` (192s for the new leaf; dependencies replayed). Intrinsic capstones `exists_rightStripMultiplicity_hyperbolic` and `rightStripMultiplicityCount_le_witnessNegIndex` have no hypothesis parameters. All three finished leaves are wired into `RHTower.lean`; no umbrella/full build run.
- Final direct leaf audits, axiom audits, index regeneration, lint and owned scratch cleanup remain outstanding for this milestone.
- Upper-bound scratch `/tmp/pm_upper.lean` now tests analytic local order cancellation and `selfSimilar_of_correlation_order`. No upper bound or index equality is claimed yet.

- Milestone direct audits: `lake env lean` on each of the three actual new leaves returned exit 0 without warnings. `/tmp/pm_axioms.lean` returned exit 0; four key proofs depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Ran documented index command; API, gaps and overview regenerated and search index refreshed. `lint --check-generated` returned exit 1 solely for 15 unrelated modules unreachable from their umbrella (plus existing large-file warnings). None of the PM additions was reported. Preserve concurrent scopes; rerun gate only after further source changes justify it.
- Paper/theorem card moved to `3-formalized/pm-fermi-multiplicity-hyperbolic-signature.md`; full RH goal remains active. Upper scratch now includes correlation-density rapidness and exact complex-linear correlation jet coordinates, under audit.

- Upper coordinate/order scratch passed exit 0 without warnings. New leaf `FermiNymanCorrelationJets.lean` created; targeted old-mode dependency build underway. Proved mechanism: clearing correlation order at every actual right-strip zero forces self-similarity via existing removability; conjugated jets are complex-linear on finite witness sums.
- `/tmp/pm_upper_index.lean` now contains the matching index upper-bound draft: zero jet packet is neutral, negative families inject into finite multiplicity coordinates, finite/infinite type split yields `witnessNegIndex = rightStripMultiplicityCount`. Not yet compiled; no equality claim yet.

- Correlation-jet leaf targeted build passed (252s new leaf, cached dependencies replayed), now wired into `RHTower.lean`. Upper-index scratch launched; final correlation direct audit remains outstanding.
- Next candidate to audit after index closure: algebraic rank of the literal dyadic defect `w(t/2)-w(t)` equals right-strip multiplicity; its nonneutral quotient should carry the actual dyadic Jordan action. Search corpus before accepting this as new. This is a structural candidate, not a source proof of rank zero or RH.

- Upper-index scratch passed exit 0 without warnings after correcting a sum-negation rewrite, identity scalar hom simplification and local sigma-type unfolding. `FermiNymanMultiplicityIndex.lean` now contains the unconditional equality; targeted old-mode leaf build underway. Final actual-leaf and axiom audits remain pending.
- Critique of the next candidate: self-similar witnesses need not lie in the form radical; spurious witnesses are self-similar yet have nonzero pairing with zero jets. The zero correlation-jet packet implies self-similarity, but the converse is not established and must not be assumed. A dyadic-defect rank argument needs its own exact dilation/correlation transfer, rather than identifying these two kernels.

- `FermiNymanMultiplicityIndex.lean` targeted old-mode build passed (70s leaf); wired into `RHTower.lean`. Final direct correlation-jet audit passed exit 0 without warnings. Direct multiplicity-index audit underway.
- Dyadic-difference rank paper mechanism closed without a converse kernel theorem: any negative Gram family has independent literal differences, because a vanishing difference combination is self-similar and therefore has zero quadratic form. Any independent-difference family injects into correlation-jet coordinates because zero jets imply zero difference. Thus `ind₋(q) ≤ rank(D) ≤ M`, and exact index equality closes both. Full proof recorded in `3-formalized/pm-dyadic-defect-rank.md`; draft `/tmp/pm_defect_rank.lean` awaits compiler audit.
- Broad source-cancellation search returned useful source receiver hits with `partial: true`; inventoried coverage complete but compiler coverage mostly pending/stale. No independent half-mass positivity producer surfaced. Scoped rank/public searches found classical dilation and jet work, not an exact matching alternating-Fermi difference-rank theorem. Novelty remains provisional.

- Final actual-leaf multiplicity-index audit passed exit 0 without warnings. Intrinsic equality now has both targeted build and direct `lake env lean` verification; axiom audit underway.
- Next kernel conjecture paper mechanism: continuous dyadic self-similarity makes a witness bounded on `(0,1]`, by reducing each point to the compact interval `[1/2,1]`. A bounded witness has Mellin exponent zero. The literal Fubini factorization then holds near every right-strip zero and factors correlation as zeta times an analytic function. Hence all submultiplicity jets vanish. Together with the new forward cancellation theorem, zero jet packet, boundedness and dyadic self-similarity are equivalent. Corpus search returned existing forward implications but no converse packet classification; `partial: true` limits coverage claims. This mechanism is separate from the form radical and does not produce universal boundedness or RH.

- Upper-stage axiom audit passed exit 0: local cancellation, coordinate linearity and unconditional `witnessNegIndex_eq_rightStripMultiplicityCount` depend only on `propext`, `Classical.choice`, `Quot.sound`. Exact equality recorded in the formalized theorem card and PM frontier. Difference-rank scratch now compiling; kernel paper proof recorded in `3-formalized/pm-correlation-jet-kernel.md` with draft `/tmp/pm_kernel.lean` pending.

- Difference-rank scratch reported one error solely in the generic API probe (`have := @Fintype.linearIndependent_iff` left universe levels unconstrained); every mathematical declaration elaborated without a reported error. Probe fixed with explicit universe levels. New actual leaf `FermiNymanDyadicDifferenceRank.lean` omits the probe and is in its targeted old-mode build. Actual build/direct/axiom audits are required before claiming the rank theorem complete.
- New source conjecture's arithmetic proof closed: for any continuous dyadically self-similar `w`, every literal generator pairing is `-(1/a) integral_(1/2)^1 w(t)/t dt`, `a≥1`. Half-dilation converts the first fractional-part integral to twice the lower half of the second; their difference is the upper half, where the fractional part is exactly `1/(2at)`. Bounded actual witnesses are therefore exactly continuous self-similar profiles with zero logarithmic mean. Corpus/public searches found individual spurious modes and rigidity, but no matching all-profile source identity; corpus result partial and novelty provisional. Proof recorded in `3-formalized/pm-bounded-spurious-classification.md`; implementation queued after current rank/kernel work.

- Difference-rank actual leaf targeted old-mode build passed; wired into `RHTower.lean`. Final direct actual-leaf and axiom audits remain pending. Kernel scratch `/tmp/pm_kernel.lean` now compiling. Bounded-spurious source-classification draft written to `/tmp/pm_periodic.lean`; it awaits the planned actual kernel module before compiling.

- Kernel scratch failed only at local analytic composition (`AnalyticAt.comp` takes the analytic inner-map proof directly) and a redundant argument to `zero_le`; also three unnecessary-simpa warnings. Corrected those in the draft. Actual `FermiNymanCorrelationKernel.lean` created with an unconditional intrinsic set-equality capstone `fermiMultiplicityJetKernelSet_eq_boundedFermiWitnessSet`; targeted old-mode build underway. `boundedFermiWitnessSet` lives in this kernel leaf and is reused by the queued arithmetic classification, avoiding duplicate definitions.

- Kernel leaf targeted old-mode build passed (8.6s leaf), now wired. Mean-classification scratch `/tmp/pm_periodic.lean` launched against that actual module. Final actual-leaf/axiom audits for rank and kernel remain queued; no completed-milestone claim for those stages yet.
- Future conjecture, not accepted yet: weighted dyadic signature tomography. For a weight `t^(2α)` with `-1/2<α≤0`, the matching form subtracts `2^(-1-2α)` times full weighted mass. Admission threshold is `Re rho>1/2-α`; Mellin exponent is `a=1/2+α`, matching the existing general removability receiver. Candidate exact index is the analytic-multiplicity count beyond that threshold. Corpus search initiated before any weighted implementation; no weighted theorem claimed.

- First mean-classification scratch returned formal API/inference errors: `Measure.integrableOn_of_bounded` needs global measurability, whereas continuity supplies restricted measurability. Replaced with the verified `IntegrableOn.of_bound`. Added explicit pointwise function reductions, explicit self-similarity type and the missing product inequality `(a-1)t≥0`; fixed conjugate-function rewrite matching. Revised scratch compiling. No mathematical counterexample to the source identity found.
- Weighted corpus search reported `partial: true`: hits expose existing `L^p` exclusion and general Mellin-exponent removability, plus current unweighted index, but no weighted multiplicity-index theorem. Preferred parameterization is `0<a≤1/2`, weight `t^(2a-1)`, form coefficient `2^(-2a)`, zero threshold `Re rho>1-a`. Weighted spurious coupling should be `2^(1-2a) c(rho)/(rho-(d_l+1-2a))`; this follows directly by integrating the power exponent. No weighted theorem claimed or implemented yet.

- Mean-classification scratch passed exit 0 without warnings after explicit Pi reductions and replacing a recalled unavailable name with the verified `div_lt_one`. Actual `FermiNymanBoundedSpuriousClassification.lean` created, including unconditional bounded-class and full jet-kernel set equalities. Targeted old-mode leaf build underway; then final actual-leaf/axiom audits of rank, kernel and this source classification.
- Weighted candidate now has its own `1-in-progress/pm-weighted-multiplicity-tomography.md` card. Extended parameter range `0<a<1` is proposed, with an explicit warning that `a>1/2` uses a new weighted witness class rather than ordinary `L²` membership. No weighted source file edited yet.

- Mean-classification actual leaf targeted old-mode build passed (118s leaf); wired. Direct final actual-leaf audit of `FermiNymanDyadicDifferenceRank.lean` underway, then kernel/classification audits and combined `/tmp/pm_structural_axioms.lean`. No full or umbrella build.
- Hardy search returned `partial: false`, no lexical conjunction hits but useful source candidates. Actual `HardyDyadicWindowTheorem.lean` declares unconditional `exists_riemannZeta_line_zero_dyadic` and `exists_pow_le_xiPosCriticalZeroCount`; inspected proof mechanisms and exact types. These support a proposed weighted index cliff for `a>1/2`, once weighted admission/pairing are proved and this dependency is compiler/axiom-audited. No cliff theorem claimed yet.
