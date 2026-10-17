# Full Weil ramp–tent Gram decoupling — 2026-10-18

Card: `docs/drafts/pipeline/3-formalized/factorial-weil-gram-decoupling-2026-10-18.md`. Follows `mem:biscale/factorial-full-weil-coercivity`.

Four new verified modules under `formal/GaloisForLFunctions/BiScaleUncertainty/`:
- `FactorialWeilGram.lean`: defines the literal spectral vonMangoldt `factorialSpanWeil n c d` for c times actual reflected factorial ramp plus d times actual tent. Every source's finite-jump domain is discharged. Exact identity Q(cL+dR)=c²A+d²D+cdM. M is minus the causal jump integral minus twice the full prime–polar pairing; no positivity assumption.
- `FactorialWeilMixedDecay.lean`: |M| <= E_N = (36 log N+26 log 5+14+2 log 1000000)/sqrt N, N=n+1. E_N and M tend to zero. `factorialWeilGramError n`=E_N²/(2N) also tends to zero.
- `FactorialTentWeilCoercivity.lean`: every prime sample of the pure tent autocorrelation vanishes exactly. Its fullPairing is nonpositive. D/N >= 6 exp(-1/2) log N - 30 |gammaBracket 0|, hence D/N tends to +infinity and eventually D>=N.
- `FactorialWeilGramDecoupling.lean`: eventually, uniformly for all real c,d, Q(cL+dR)>=c²(A-GramError)+(D/2)d². `factorialWeilMinRamp` is the actual energy at optimal tent coefficient -M/(2D). Exact square completion and minimization are verified; 0<=A-MinRamp<=GramError eventually, so the actual energy gain tends to zero.

All four direct `lake --old env lean -j 1 <leaf>` checks passed, no raised heartbeats. All 17 public theorems audited: only propext, Classical.choice, Quot.sound. Logs `/tmp/bsu-<Module>.log`, `/tmp/bsu-weil-gram-axioms.log`; scratch `/tmp/biscale_weil_gram_axioms.lean`; source-hash/audit manifest `/tmp/bsu-weil-gram-verification.json`. All new modules wired, index regenerated, no umbrella/full build. All own handles terminal.

Formal lint exited 1 for concurrent unrelated drafts: three missing area imports (ClosedCorrelationCycleRecovery, SeparatedCopyCycleCharge, SeparatedCopyCyclePolarAmbiguity) and package-root research leaf BezoutValuationIncidence.lean. No forbidden-declaration errors. Do not claim the repository lint passed.

Next OPEN conjecture: eventually GramError <= A=factorialSpanWeil n 1 0. This would imply eventual positivity of this whole two-dimensional span. Exact weaker target: MinRamp>=0, equivalently A>=M²/(4D) once D>0. Mere A>=0 is insufficient without a margin. This still does not prove all-source RW or RH. No pure-ramp zeta-kernel identification is assumed. Search ingredient set using unrelated sign4 was marked not_verified and rejected.

Current goal remains unconditional RH in Lean. Preserve user constraints: corpus-only, no numerical experiments, README/frontier map read-only, one own foreground Lean process, no full builds/commits/push. No external novelty claim.

Lean implementation lessons: integral_add/sub rewrite patterns may contain pointwise Pi.add; normalize the equality with `simp only [Pi.add_apply]` before rewriting. Specify both coefficients in `factorialSpanWeil_gram n c d`, otherwise rewrite can hit a diagonal energy first. `squeeze_zero_norm` uses argument `a` for its real majorant; open scoped Topology for 𝓝. Cast from Real.log_pow needed norm_num.