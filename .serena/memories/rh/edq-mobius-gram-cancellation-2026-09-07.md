# EDQ complete Möbius Gram cancellation — verified progress, RH still open

Goal remains ACTIVE: unconditional closed Lean proof/falsification of RH via EDQ. No budget, no external blocker. Do not mark complete or blocked for mathematical difficulty. Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. Previous transfer memory: `mem:rh/edq-primitive-energy-transfer-2026-09-07`.

## New completed leaf
`formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusGramCancellation.lean`, namespace `RHTower.DeletionMobiusGram`, 192 lines. Imports existing EulerDeletionMobiusPrimitiveEnergy, BaezDuarteGramDiscrete, Mathlib.NumberTheory.Harmonic.Bounds. Three definitions, nine public theorems, one private helper. Wired exactly once into RHTower.lean; NO umbrella/full build.

Definitions: entry m n = (mu m:R)*(mu n:R)*bdGram(1/m,1/n); diagonal N = sum m in Icc1N entry m m; cross N = sum m in Icc1N sum n in (Icc1N).erase m entry m n. Cross counts ordered unequal pairs and retains both Möbius signs. This is the actual raw modular carrier, NOT a different divisor-channel or Euler-aperture Gram.

Public proofs:
- modular_norm_sq_eq_diagonal_add_cross: entire raw modular carrier squared norm = diagonal N + cross N. Uses actual source generator identification and full real quadratic Gram expansion; no tail discarded.
- diagonal_nonneg.
- gram_self_le_two_div (m>=1): bdGram(1/m,1/m)<=2/m. NEW stronger individual estimate, removing previous log(m) loss in GramDiagonalSandwich. Discrete summand g_n <=1/m² using residue<=n+1, and <=1/(n+1)-1/(n+2) using residue<=m. Extend finite cutoff L to m+L, split at m: head<=1/m, telescoping tail<=1/(m+1). Then existing genuine HasSum supplies full bound. No numerical certificate.
- diagonal_le_two_mul_harmonic: D_N<=2*harmonic N, EVERY N.
- diagonal_le_two_mul_one_add_log: D_N<=2*(1+log N), EVERY N, including N=0 (Real.log0=0).
- diagonal_eventually_le_four_log.
- modular_norm_sq_div_log_pow_tendsto: for ANY actual off-line zero rho and q:Nat, norm(raw_N)^2/(log N)^q→+infinity. Uses existing positive zero-dependent current-to-primitive-energy constant, E_N<=2norm², and current superlog escape.
- cross_div_log_pow_tendsto at line153: same escape for signed cross N. Apply norm escape at q+1, diagonal<=4logN, logN>=1, retain signs, derive cross/log^q >= any B.
- riemannHypothesis_of_cofinally_log_bounded_cross: source-only sufficient ceiling, exists q B forall K exists N>=K cross N<=B(log N)^q implies Mathlib RH. THIS CEILING IS NOT PROVED; NO converse RH→cross ceiling asserted. No off-line zero asserted to exist. No route retired.
Private log_tendsto only.

## Genuine gain / remaining task
Complete literal diagonal is now unconditionally O(log N), independent of any selected zero. Thus hypothetical off-line obstruction must live in aggregate constructive cross interference beyond every logarithmic power. Full Gram PSD does not give an upper bound on signed cross contribution. Remaining source producer is a cofinal polynomial-log ceiling on this full cross sum OR weaker original zero-dependent current ceiling. Do not portray this new sufficient criterion as an independent proof of RH or an established equivalence. Further work should examine literal arithmetic cross cancellation, not repeat receiver proofs.

## Validation already complete — do not repeat old audits
- API 74693 exit1 only nonexistent Filter.Tendsto.atTop_sub_const; replaced with verified Filter.tendsto_atTop. API6441 exit0; expanded API9566 exit0. No final code uses nonexistent name.
- Initial scratch54205 exit1 No goals after field_simp; fixed. Scratch6825 exit0 for initial diagonal-log² version and full cross escape. Strengthened scratch9900 exit1 only linarith treating 2/m vs 1/m+1/m separately. Fixed via explicit additive inequality then ring. Final scratch19754 exit0 with one redundant seq-focus style warning. Changed `field_simp <;> ring` to `field_simp; ring`; targeted build validates cleaned version.
- Targeted leaf build96059 exit0: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMobiusGramCancellation`. Exactly two Built lines: existing EulerDeletionPrimitiveHardy refreshed 6.9s (prior trailing-space source edit), new GramCancellation8.2s. All remaining 13108 graph jobs cached/replayed. Existing PrimitiveEnergy not rebuilt. No full/umbrella build. One owned foreground Lean at a time.
- ONE new-only axiom38239 exit0, all12 public declarations only propext/Classical.choice/Quot.sound. Closure covers private helper. Do not reaudit old declarations.
- Repository formal lint98026 ran ONCE exit0, only existing size warnings. Previously concurrent unwired modules are now wired; no unrelated fix made.
- Index ran once exit0:5 changed0removed32996files402332decl3946gaps. Exact no-refresh query retrieves cross escape line153.
- Scoped checks passed192lines, exact scratch/source equality, no forbidden declarations, single umbrella import, links, all12 axiom lists, exactly two Built lines, no owned Lean/Lake processes. Final git diff --check passed.
- All three owned Lean scratch sources REMOVED: /tmp/edq_gram.lean, /tmp/edq_gram_api.lean, /tmp/edq_gram_axioms.lean. Retained logs /tmp/edq_gram.{api,check,build,axioms,lint,index}.log. All sessions completed, no stale owned process. Imports sometimes took 2–3min under concurrent load; CPU confirmed live, never restart on timeouts.

## Documentation
Paper/card created before new Lean, now `docs/drafts/pipeline/3-formalized/edq-mobius-gram-cancellation.md`, full derivation/proof statuses/audits/cleanup. Old in-progress card removed by rename. Frontier updated current EDQ paragraph and EDQ row. Replaced stale duplicate Hardy paragraph incorrectly saying no literal-input identification existed (PrimitiveEnergy already provides it). STATUS appended route-independent MUST-LOCATE-EXCESS-IN-INTERFERENCE: superlog full growth with logarithmic complete diagonal must reside in aggregate cross contribution; head/tail diagonal improvement is not cross cancellation.

## Local API/math notes
Finset.sum_erase_add s f hm: sum erased + self = sum full; use symm.trans(add_comm) for diagonal-first. Finset.sum_range_add gives m+L splitting at m. Finset.sum_range_sub' telescopes f n-f(n+1). le_of_tendsto existing HasSum.tendsto_sum_nat plus Eventually.of_forall finite bound. Harmonic is rational; harmonic_eq_sum_Icc then Rat.cast_sum/cast_inv/cast_natCast. Sieve.abs_moebius_real_le_one verified. For arbitrary q cross escape, use q+1, max B0+4 threshold and L^q>=1, no asymptotic subtraction API required. linarith does not identify 2/m and 1/m+1/m; explicit ring equality necessary.

Exploratory BaezDuarteMobiusSeries is unrelated binomial coefficients, not raw carrier estimate. SquarefreeCounting.lean currently gives exact finite mu²/divisor-floor identity, not an already found density/window bound. No numerical experiment was necessary or run.

## Persist user computation rules
All numerical experiments only RunPod ssh root@157.157.221.29 -p27094 -i ~/.ssh/id_ed25519; multicore optimized Python; download/document under docs/drafts/pipeline/2-fully-proven/computations; only unpredictable results; no hours-long jobs. Local symbolic Lean checks and repository bookkeeping continue as authorized. No SSH connection, subagent, commit, or push this turn.
