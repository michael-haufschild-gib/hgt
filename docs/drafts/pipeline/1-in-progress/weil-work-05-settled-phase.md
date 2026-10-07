# WP05: canonical spectral phase settlement

- **ID:** weil-work-05-settled-phase
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/weil-work/05-settled-phase.md
- **Statement:** Every full-positive integer-supported Weil system supplies the exact atomic representation and constant-phase power settlement required by `vonMangoldt_and_riemannHypothesis_of_settled_atomic_phase`.

## Goal and active target

Constant-phase receiver only. Produce its hypotheses from the original canonical boundary measure. Full positivity is the assigned input, not an independently constructed producer. Goal stays open until all hypotheses are paid and the receiver composes in Lean.

## Plan

1. Refresh corpus and external primary-source audit; distinguish source laws from receivers.
2. State exact competing conjectures, attack them, and record dependencies and novelty verdicts.
3. Complete dependency-closed paper proofs before Lean; formalize substantive positive survivors of failed approaches.
4. Audit leaf modules with `lake env lean`, targeted dependencies with `--old`, axiom inspection in `/tmp`, umbrella wiring, lint; continue next conjecture.

The requested `update_plan` and `multi_tool_use.parallel` tools are unavailable in this session. Plan is tracked here; independent reads use parallel tool promises.

## Current frontier

- Existing Lean: canonical positive measure, exact Poisson representation, logarithmic local mass bound, smoothed Riemann--von Mangoldt count, atomic and mixed settled-phase receivers, sublinear-power fractional-mass rigidity, weighted mean-square lock receiver.
- Unpaid: atomicity; lower support restriction; phase settlement for actual measure. Smoothed counting does not determine its exponential phase.
- Existing dipole example in the settled-atomic module already allows linear fractional mass with sublinear total separation. Do not count its routine formalization as new mathematics.
- Booker, *L-functions as distributions*, Definition 1.3(A3), explicitly requires discrete support and finitely many nonintegral masses. Degree-one classification cannot produce those assumptions.

## Competing conjectures under attack

1. **Count-to-phase transfer:** a positive spectral counting function within bounded error of a rigid count inherits power settlement. Exact obstruction under investigation; rounding and smoothing can change phase by order one.
2. **Arithmetic phase concentration:** the complete integer-supported explicit formula forces dyadic phase concentration even though generic positive measures with the same count need not. `[OPEN CORE]`: derive a nonlinear phase estimate from the signed arithmetic source, without assuming quantization, a producer functional equation, or a settled lock.

## Gates

- [x] 0 → 1: exact assigned target and unpaid properties identified.
- [ ] 1 → 2: complete source-derived paper proof.
- [ ] 2 → 3: Lean proof of assigned target.
- [ ] 3 → 4: novelty/significance audit and publication artifact.

## No-go closure

- Count-only uniform phase-cost transfer: false for explicit finite positive half-mass packets. Counting discrepancy stays at most 1/2 while integrated phase error is unbounded as width grows. This is not a counterexample to settlement for a fixed arithmetic producer.
- Positive survivor: exact packet chord-length cost and finite-family transport bound, with arbitrary overlaps. Paper proof closed; Lean leaf build and final source/axiom audit passed. Seven capstones depend only on `propext`, `Classical.choice`, `Quot.sound`.
- New-insight verdict: BRIDGE / REDISCOVERED mechanism. Corpus already describes dipoles. No scientific frontier advance claimed; WP05 milestone is unmet.

## Active conjecture and source-sensitive next step

**Conjecture:** monotone fractional-mass rigidity persists for C(T)=o(T), beyond every fixed-power receiver. No proof and no counterexample known from this audit.

The existing radial-error bound epsilon^(1-nu) for fixed nu>0 does not suffice: C(T)=T/log T defeats its absolute estimate. Varying nu with epsilon requires bounds on constants that the theorem does not supply. A candidate improvement must preserve that atomic mass lies at zeros of the actual producer; the current horizontal-edge estimate takes a strip supremum and loses this incidence. First check whether exact Herglotz potential yields an averaged top-edge bound against the fractional part of the same measure. `[OPEN CORE]`: this bound is unproved. Do not assume it as a new premise and call the receiver an advance.

Cycle 2 obtained a source-wide quantitative bound: `Re producerLogZeta <= C log|t|/log log|t|`, with no extra coefficient bound. The potential normalized-producer envelope is therefore `exp(C log T/log log T)`. This still loses against `C(T)=T/log T`. A near-linear fractional class such as `C(T) <= T exp(-log T/sqrt(log log T))` is a precise next transfer candidate, but neither its transfer proof nor its production from hW is done. Do not conflate this prospect with settlement. The collective source-sensitive estimate remains the central question.

## hgtl7 self-audit

- No significant new scientific knowledge yet. New Lean content is a useful bridge, not novelty. Avoid further routine count/transport additions.
- Corpus and external audits killed a classification shortcut and a count-only shortcut; this prevented false closure but consumed the cycle.
- No work avoided for effort reasons. Main source-derived estimate remains the hard target; the next cycle must attack it directly.
- Relevant machinery and stronger receivers were searched and read. Positive survivor is being fully audited instead of left as proof debt.
- Cycle 2 anti-theatre audit: removed a real coefficient premise from a source theorem; did not manufacture fractional-mass or settlement hypotheses. Method remains classical and significance for phase detection is unproved.
- Cycle 2 anti-laziness audit: tested local zero incidence, checked collective energy interfaces, and audited converse-theorem premises. Formalized the dependency-closed source estimate. The difficult collective estimate and actual phase production remain explicitly open, not deferred under a new theorem premise.
- Cycle 3 anti-theatre audit: the actual atomic phase has a quantitative nonrigidity obstruction, not a source-derived upper bound. Atomic representation and support remain unpaid. The elementary contraposition is not claimed as scientific novelty; the source envelope is its substantive input.
- Cycle 3 anti-laziness audit: formalized the complete generic lock argument and actual-phase change of variables after paper closure. Checked the source-wide moment shortcut: coefficient and rest-weight assumptions enter the variance argument independently, so the new Littlewood theorem cannot silently remove them.

## Next falsifiable source conjecture

For every original hW, its normalized holomorphic completed producer has a finite
horizontal boundary trace almost everywhere, with reflection phase given by
`exp(2*pi*i*(mu((0,y)) + mu({0})/2))`, where `mu=boundaryMeasure hW`.
No atomicity or support-gap assumption. The trace need only be measurable, not
continuous. This is a bridge candidate toward removing the atomic representation
premise from the disorder law; it is not yet a settlement estimate.

Corpus evidence: `exists_zetaQuotient_primitive` supplies an actual holomorphic
primitive; the horizontal potential identity and positivity control the modulus;
the integrated Poisson kernel identifies cumulative boundary mass. Candidate
mechanism: normalize G from the primitive, use horizontal monotonicity to obtain
its modulus limit, and integrate Re(Phi) vertically to identify the phase limit.
The needed contour passage with only measurable boundary trace is unproved.
Do not replace it by assumed boundary continuity, or declare atomicity proved.
Complete paper and applicability audits before adding Lean for this conjecture.

## Log

- Cycle 4: previous turn classified as progress; source hash revalidated. Canonical measurable trace conjecture now has a dependency-closed paper proof in PROOF.md. It uses the exact actual primitive, monotonic modulus and canonical interval Poisson limit; no atomicity or support gap. Target includes local L1 convergence, needed for the later contour step. Classical boundary inversion, BRIDGE verdict; no settlement or scientific novelty claim. Installed API audit precedes Lean implementation.

- Cycle 3 active conjecture: the new coefficient-free Littlewood estimate yields a source-derived phase-disorder dichotomy. For a full-positive source and its exact atomic representation, either rigidity holds or every candidate constant phase has dyadic L1 defect at least `a T exp(-K log T/log log T)` at arbitrarily large heights. Atomicity/representation remain explicit unpaid inputs; no settlement-rate assumption is introduced. This is stronger than the existing contraposition of every fixed-power receiver. First prove the generic normalized-producer lock dichotomy, then instantiate the actual strict-cutoff atomic phase.
- Cycle 3 closed: source audit passed after scalar sign/rewrite repairs. No heartbeat increase. New module is wired once into RHTower; targeted `--old` build, final `lake env lean` audit and three axiom checks passed. All three declarations use only standard axioms. Latest global lint has 13 unrelated unreachable modules and no WP05 error. Search coverage, including two partial results, is retained separately. Actual atomic phase disorder is proved under its explicit representation inputs; source-derived settlement and the main goal remain open.

- Cycle 2: the single-atom model `G(x)=x^c` has horizontal integral `1/(1+c)`, so zero incidence alone gives no saving uniform in small masses. No counterexample to the source-sensitive `C(T)=o(T)` conjecture was obtained. A collective weighted estimate remains unproved.
- Cycle 2: corpus refresh found `WeilProducerLittlewoodBound.exists_re_producerLogZeta_le_littlewood`, which adds `|lam(n)| <= kappa log n`. New exact conjecture: this bound holds for every full-positive system with no extra coefficient assumption. Paper proof closed in `PROOF.md`: use `M2=sum |lam(n)|/n^2` and cutoff `L=(log log |t|)/4`. Scientific assessment: classical method; useful removal of a corpus premise, not a claimed solution or significant phase theorem. Formalization started only after paper closure.
- Cycle 2 closure: coefficient-free Littlewood source estimate formalized in `WeilWorkSettledPhaseLittlewood.lean`, wired into RHTower, leaf-built with `--old`, and finally audited with `lake env lean`. Both capstones have standard axioms only. Global lint has seven unrelated unreachable modules. Main WP05 and first phase milestone remain open; goal remains active.

- 2026-10-07: initialized hgtl7; read project instructions, relevant memories, assigned package, shared contract, exact receiver, relevant frontier/STATUS entries. No architecture/testing documents exist. Existing working-tree changes preserved.
- 2026-10-07: hybrid searches `settled atomic phase` and `fractional mass power growth` completed with `partial=false`; source inventory complete but compiler snapshots mostly pending/stale and semantic coverage not measured. Read declarations, candidate lemmas, and source arguments; direct Lean verification still required. Deep search running.
- 2026-10-07: all launched searches finished. Deep search returned no useful closing theorem; the sublinear-variation query had a semantic deadline and is explicitly partial. Source passages and exact contour statements exposed the fixed-exponent obstruction.
- 2026-10-07: wrote `RESULT.md`, `PROOF.md`, `EVIDENCE.md`, retained search coverage; created `WeilWorkSettledPhasePackets.lean` and wired it into RHTower per explicit user instruction. `lake --old build +GaloisForLFunctions.RHTower.WeilWorkSettledPhasePackets:olean` passed; only the new leaf was reported built. No umbrella/full build. Global lint exit 1: 11 unrelated unreachable modules.
- 2026-10-07: final `lake env lean` source audit passed with no output; seven `#print axioms` checks passed with standard axioms only. No significant frontier movement yet. Continue with the source-sensitive sublinear-mass conjecture; do not spend the next cycle extending the finite packet bridge.

Cycle 4 stronger survivor: the corpus's actual right-edge Gamma bound gives an
integrable majorant on all heights. The paper proof now establishes global L1
trace convergence from hW alone. The original local trace module passed its
source audit before this extension; the extended module is awaiting verification.
The exact next contour interfaces are `critical_line_inverse_mellin` and
`critical_line_even_theta_relation_defect`, both currently using closed-strip
continuity. Fresh contour search returned `partial=false` but includes stale
compiler snapshots; source inspection, not search freshness, supports these facts.

Big-picture implication of the trace survivor: a source-derived settlement law
for the full canonical cumulative measure can be formulated before proving
atomicity. If the measurable-trace rigidity transfer is completed, that law
could force lambda=Lambda and RH first; identification of the resulting measure
would then pay representation/support obligations. This is an alternative order
of proof obligations, not a completed reduction. The remaining central difficulty
is still a source-derived upper bound on the actual phase defect. Global L1
regularity alone gives no such bound, and generic diffuse measures need not settle.

## Cycle 4 checkpoint

The 411-line `WeilWorkSettledPhaseTrace.lean` now passes the targeted `--old`
leaf build and final standalone `lake env lean` audit. It is wired once into the
RHTower umbrella. It derives the actual normalized producer, a.e. canonical
boundary trace, exact reflection phase, integrability, and global L1 convergence
from the original hW alone. Global lint reports 12 unrelated unreachable modules;
no WP05 error. All nine axiom inspections passed with exactly `propext`,
`Classical.choice`, and `Quot.sound`. Evidence is retained; all owned jobs
completed and all fourteen owned cycle-4 scratch files were removed.

hgtl7 anti-theatre audit: this is a BRIDGE removing a real input from the boundary
trace construction, using a classical inversion mechanism. It is not the phase
upper bound required by WP05 and is not claimed as significant scientific novelty.
Atomicity is absent from the new theorem, but it remains present in the completed
phase-disorder theorem until the measurable-trace coefficient transfer is proved.

hgtl7 anti-laziness audit: the local trace conjecture was carried through primitive
normalization, conjugation, null exceptional sets, reflection, and L1 convergence.
The contour audit exposed a stronger global claim, which received a separate
paper proof and full Lean implementation. Source-specific compact-height and
large-height decay for the pole-subtracted producer was analyzed on paper. No
unproved contour regularity or phase estimate was smuggled into a capstone.

Immediate next conjecture: the canonical full-measure phase has the same
rigidity-or-disorder dichotomy as the atomic phase, without any representation
or support-gap premise. First implement the pole-subtracted source trace and
measurable inverse Mellin/coefficient transfer described in PROOF.md. Retain the
central mass and diffuse part. Then return to the unpaid source phase upper bound.

## Cycle 5 active proof

Revalidated the cycle-4 source hash and refreshed the assigned contract/corpus.
New quantization work supplies an everywhere measurable radial trace for exp(P);
this overlaps the primitive/trace construction, not the missing pole-subtracted
source decay and contour passage. Do not reprove that endpoint improvement here.
The current falsifiable target is a uniform C/(1+t^2) bound and global L1 trace
for bigEG(sourceCompletion hW), followed by an interior-to-trace contour shift.
Only hW may remain as a source premise. The detailed paper argument is in PROOF;
existing modules remain read-only.
