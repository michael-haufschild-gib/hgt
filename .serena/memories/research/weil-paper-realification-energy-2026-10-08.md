# Weil-first proven-paper applications: exact energy preservation

Active unbudgeted user goal, not complete. Proven OpenAI/math results are treated as proven; local new applications checked in Lean. User scope Weil-work first; no cards, corpus search/direct Lean only, no computations or extra axioms, no full/umbrella builds. One foreground build per agent. No subagents used.

## New native result: complete and audited
`formal/GaloisForLFunctions/RHTower/WeilPaperRealificationEnergy.lean` contains eight new public theorems. Production final `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilPaperRealificationEnergy.olean GaloisForLFunctions/RHTower/WeilPaperRealificationEnergy.lean` PASS first attempt, warning-free (batch45523). Wired in RHTower.lean without umbrella build.
- line20 `paperFT_reflect_complex`: f(-x) Fourier transform at z equals transform f at -z, for arbitrary complex f, no analytic premises. Proof extends existing real-input reflection using integral_neg_eq_self.
- line33 `weilArchRe_reflect`: swaps pole evaluations and changes r→-r in gamma integral. Gamma multiplier evenness already existed privately in WeilPaperPacketRealification; exposed unchanged as public packet_gammaBracket_neg (line24). That existing leaf was final-rechecked warning-free before the new one.
- line42 `weilArchRe_paperConjugateTestFn`: conjugate autocorrelation equals reflected original; energy identical.
- line52 `energy_paperRealMixture`: for every finite signed mixture c, conjugation averaging preserves FULL energy exactly. Finsupp.induction_linear, no nonnegativity assumptions.
- line64 `energy_paperRealComplexNullMixture`: canonical conversion from normalized real integer-defect-null to ComplexNullMixture preserves energy.
- line70 `defect_complexNullMixture`: converse full complex cancellation implies real integer defects zero.
- line76 `attainable_energy_real_null_eq_complex_null`: exact equality of sets of attainable full energies of normalized real-defect-null mixtures and normalized ComplexNullMixtures.
- line88 `exists_negative_energy_real_null_iff_complex_null`: negative-witness existence is equivalent. Does NOT assert a negative witness exists or settle RH.

Research interpretation: WP01 may impose full complex integer cancellation and use actual origin-representing spectral probabilities without losing any attainable energy. Generalizes prior translated-bump packet realification to arbitrary native compact-C2 test mixtures.

## Verification/bookkeeping
Combined nine-declaration axiom audit `/tmp/audit-weil-realification-energy.lean` PASS (69525); only propext/Classical.choice/Quot.sound, no added axioms/sorry. Logs under gitignored durable workspace tmp/hgt-openai-math: packet-realification-final.log, realification-energy-final.log, audit-realification-energy.log. All52 owned modules exact umbrella imports checked; scoped git diff --check PASS. Cumulative410 public theorems/52 modules, Weil335/39 (eight new plus one exposed existing helper). Count regex public theorem lines. Authoritative own-files.txt.
Index PASS. Global lint10 unrelated concurrently unfinished/unreachable modules, zero owned errors; lint-realification-energy-summary.log. Exact lexical searchback finds capstone line76. Earlier search-general-realification-energy nonpartial; later search-attainable-null-energy partial snapshot, all candidate/source arguments inspected, no duplicate generic theorem. No card reads.
Finished /tmp drafts and name probes removed. Audit scratch files retained. No heartbeat increases/full builds.

## Source port checkpoint
See mem:research/openai-seven-eighths-local-port-2026-10-07. Source ExponentialSmoothing, CompatCalculus432 and LogProfiles now checked; current inventory nine fresh/2950, historical133 artifacts lost and not counted. Two generic calculus helpers are proved and axiom-audited: smooth ratio cutoff with exact open support and closed one-set; finite common bound for all derivatives up to K, arbitrary normed spaces/field, generalizes native DeningerSplitBounded proof. Six uncompiled source callers import CompatCalculus432. LogProfiles fixes noncomputable mulCharProd plus three exact_mod_cast le_top derivative-order bounds. Canonical pinned source unchanged.
After native audit, batch46450 started serial six-leaf source continuation (source-check-after-logprofiles.log), beginning ChineseRemainder.AdditiveCharacters. Check owned process/log before further builds. Whole local7/8 endpoint remains incomplete, upstream theorem proven.

Potential next native infrastructure: prove exact idempotence/retraction of paperRealMixture via involutive paperConjugateTestFn; generic nullRepair full-energy invariance follows from energy_paperRealMixture and defect_paperRealMixture (packet-specific version already exists). Build missing interesting infrastructure instead of pivoting. Do not count private-source helpers in native public totals.


Source continuation update: batch46450 terminal: AdditiveCharacters PASS; EisensteinIdeals failed old API differences. Repaired missing Mathlib.NumberTheory.NumberField.Ideal.Basic import, removed redundant rfl after simp; swapped Ideal.mul_le_left/right at153 sites in38 uncompiled staged modules (all occurrences enumerated, mapping source-ideal-product-compatibility.json). Batch78829: EisensteinIdeals PASS without any heartbeat increase; MatrixPhases failed only ite_eq_left/right unavailable. Four conditional aliases to if_pos/if_neg/dif_pos/dif_neg verified in scratch (72024), no axioms. Added OAI.CompatConditionals432 at common EisensteinCoordinates import root, intentionally invalidating five arithmetic leaves. Batch61680 now serially checking up to8 source leaves (source-check-conditionals.log). Prepared35-declaration source audit /tmp/audit-weil-source-ideals-conditionals.lean. Native batch remains fully completed/audited.


FINAL TERMINAL checkpoint: batch61680PASSall8; source current14fresh/2951 (readonly8598), all14 source logs empty. MatrixPhases andFiniteFourier newly pass. Combined35decl source audit93936PASS (31EisensteinIdeals standard3only,4conditionalaliases noaxioms). Allownedbuilds/probes/index/search/audits terminal; completedprobes cleaned; noownedliveprocess. Nextsource GaussSum.ChineseRemainder thenArithmetic.EisensteinEmbedding. Native410/52,Weil335/39 complete audited. Wholegoal remainsACTIVE, successfulprogress, notcomplete/block/pause.
