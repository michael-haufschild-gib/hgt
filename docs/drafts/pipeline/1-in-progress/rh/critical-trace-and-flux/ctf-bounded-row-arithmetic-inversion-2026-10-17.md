# CTF: bounded rows and arithmetic inversion

- **ID:** CTF-INV-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Read-only `docs/reports/rh-current-frontier-map.md`, CTF.
- **Statement:** Derive an unconditional source mechanism producing bounded chronological rows with vanishing original L2 heat error, or remove a substantive obstruction in that construction.
- **Contribution credit:** None. This turn recovered and checked existing exclusions and constructions; it did not remove a new hard obstacle.

## Goal and plan

1. Inspect exact row, dual sampling, and arithmetic rigidity results in the local Lean corpus.
2. Test competing constructions retaining the original Bose defect, coefficient budget, and full positive-time L2 norm.
3. Write a dependency-closed paper proof before adding Lean. Verify any finished module directly, audit axioms, wire imports, and remove owned scratch.

No numerical experiments, web search, novelty audit, historical research Markdown, added analytic premises, or full/umbrella builds. One owned foreground Lean process at a time. Preserve concurrent work.

## Source facts inspected

For `beta(t)=1/t-1/(exp(t)-1)`, the row error is

`r_(a,N)(t)=exp(-t)+sum_(1<=k<=N) a_k beta(k t)`.

`ChronologicalRiemannEquivalence.lean` gives the exact Mellin error `Gamma(s)(1-zeta(s) A(s))`, L2 Plancherel, and bounded-row/RH equivalence. Its constructive Riesz rows use RH; their coefficient bound alone is unconditional.

`ChronologicalDualSamplingCriterion.lean` gives the dual inequality against every L2 test whose Bose samples have bounded absolute partial sums. The hoped-for Mobius inversion must hold on that entire sampling domain, not merely on a dense smooth core.

`ChronologicalMobiusEscape.lean` gives pointwise decay of sharp Mobius errors using PNT and Lambert inversion, plus local uniform boundedness away from zero. A globally bounded L2 subsequence already implies RH through weak convergence and Banach-Saks averaging. Pointwise convergence alone does not pay the small-time boundary layer.

## Conjecture and mechanism ledger

1. **Pointwise Mobius cancellation plus bounded coefficients gives L2 decay: false.** `chronologicalRawHeat_not_convergent` in `ChronologicalRawHeatObstruction.lean` contradicts full norm decay of the very rows whose pointwise decay is proved in `ChronologicalMobiusEscape`. A critical-line zero supplies the obstruction unconditionally. The positive survivor already in the corpus is a cofinal positive raw-error floor and a cofinal nonvanishing correction required of every successful row family. This does not exclude bounded subsequences or general bounded arrays.

2. **Geometric response damping repairs raw rows: false for every vanishing schedule in [0,1/2].** `ChronologicalDampedRepair` constructs bounded arithmetic coefficients and an infinite rational response with error energy at most epsilon squared over four. Its exact finite transform retains earlier raw errors at cutoffs N/d. `ChronologicalDampingRigidity` proves equivalence of finite-row convergence with raw convergence; `chronologicalDampedHeat_no_vanishing_schedule` closes the exclusion. The small infinite-response error cannot be substituted for the finite-row norm.

3. **A near-identity Abel average suffices: excluded.** `ChronologicalArithmeticAveraging` proves that positive decreasing weights with terminal weight tending to one have the same zero-convergence condition as raw rows. For power damping, epsilon_N log N tending to zero is impossible along a successful full schedule. Its existing positive survivor is a cofinal positive scale floor. Substantial averaging remains open; the floor does not supply a schedule.

4. **Undamped nonlinear Fermi repair has a bounded arithmetic inverse: excluded at increasing depth.** `chronologicalRepairArithmetic_bounded_prefix_classification` identifies every deep repair truncation within a fixed coefficient budget: a Mobius prefix, with at most the first terminal correction. The coefficient at m+2 costs at least m-1. This exact classification already exists; it is not a new contribution.

5. **Fixed moment repair pays the boundary error: false; growing moment repair is already admitted.** `leastNormMomentRepair_fixedOrder_obstruction` gives a cofinal positive norm floor for every fixed order. `growingMomentSource_spec` already constructs unit-bounded rows with an exact half-length Mobius prefix, zero charge, and increasing exact odd moments. `growingMomentSource_jets` and convergence away from zero are established. `growingMomentSource_L2_iff_window` leaves the original shrinking window (0, log N/N) unresolved. Merely diagonalizing the number of moments supplies no bound on that window. The signed Abel formula retains the Mertens and harmonic channels; bounding each by absolute values discards the cancellation still needed.

6. **Unbounded Bose completeness supplies a bounded source: invalid.** `boseDilateL2_eq_zero_of_inner_eq_zero` already proves completeness using prime dilates alone. `exists_chronologicalL2Norm_floor_primes` and `exists_chronologicalL2Norm_floor_one_primes` show that bounded rows on those same restricted supports cannot reach zero error. No coefficient control follows from completeness.

7. **Small finite differences construct the needed tail repair: unsupported.** `exists_log_scale_dilation_freedom` supplies small-norm signed differences with binomial coefficients. Its conclusion neither constructs cancellation of the existing residual nor verifies that adding those coefficients respects a prescribed unit box. Normalizing a difference changes the displacement it produces. This freedom is useful geometry, not an approximation source.

8. **Greedy subset rounding supplies the source: unsupported.** `ChronologicalMobiusSubsetSums` removes the rounding obstacle once a suitable smooth Mobius row exists. Its successful Riesz input uses RH. The resulting subset-sum equivalence does not produce an unconditional selection of squarefree indices.

9. **Absolute summability of dual Bose samples justifies full Mobius inversion: unresolved.** Absolute convergence of the scalar sample series does not, by itself, justify exchanging its sum with an L2 pairing against pointwise-convergent raw errors. A graph-domain approximation theorem would need control of both L2 distance and the sum of absolute sample differences. Dense-core validity alone supplies neither. The second search found tail-L1 transfer results, not this domain theorem. Continuous dilation averaging from the inspected Fermi witness source uses invariance under all real dilations; the chronological sampling premise controls integer dilates only, so that argument has no established transfer here.

## Remaining positive targets

The original CTF route remains live. A useful next construction must pay the growing-moment boundary window or establish arithmetic inversion on the entire dual absolute-sampling domain. No unconditional producer for either target survived this turn. This is a location of missing work, not a new RH receiver or a claimed theorem.

Existing positive survivors were checked rather than recreated: exact bounded-prefix classification, persistent correction, the power-damping scale floor, growing-moment source admission, and subset rounding. None earns new contribution credit.

## Verification

- Two documented deep searches; mathematical evidence restricted to Lean results. First search completed with `partial=false`; second had `partial=true` because the local filter/judge returned malformed or incomplete JSON. Available hits were used. Both reported complete source inventories but extensive pending/stale compiler metadata and a running background indexer; no semantic-completeness claim.
- Ten selected source modules had existing oleans no older than their source files before the audit. This timestamp check is not a dependency rebuild.
- Name/import and axiom audit of 22 existing declarations: `lake --old env lean /tmp/hgt_ctf_audit.lean` passed, exit 0, no errors or warnings. Every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. These are existing results, not 22 new theorems.
- Direct verification from `formal`: `lake --old env lean GaloisForLFunctions/RHTower/ChronologicalRawHeatObstruction.lean` passed, exit 0, empty diagnostic output. No full or umbrella build.
- All five owned scratch files removed after verification; absence checked. Both owned Lean processes exited before cleanup.
- No repository Lean changes, added hypotheses, new axioms, numerical experiments, or new theorem claims.

## Gates

- [x] Original receiver, norm, and coefficient budget inspected.
- [ ] Independent source construction or substantive obstruction removed.
- [ ] Dependency-closed paper proof.
- [ ] Exact Lean theorem and final direct audit.
- [ ] Significant-contribution audit.

## Log

- 2026-10-17 — Selected previously unworked CTF. Started documented deep search `chronological Bose Mobius bounded rows vanishing error dual sampling arithmetic coefficient source`, budget 300 seconds.
- 2026-10-17 — Follow-up deep search `Bose sampling absolute summability Mobius inversion interchange graph domain`, restricted to modules containing `Chronological`, budget 300 seconds. Audited nine proposed mechanisms against the original coefficient box and full L2 norm. No qualifying contribution; CTF remains unresolved.
- 2026-10-17 — Existing-declaration audit and final direct source check passed. Classification: progress through verified exclusion evidence, no significant new positive contribution. Full cross-route goal remains active and incomplete.
