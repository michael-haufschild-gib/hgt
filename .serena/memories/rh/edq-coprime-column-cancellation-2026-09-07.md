# EDQ complete-column arithmetic estimate — 2026-09-07

Persistent RH/EDQ goal ACTIVE, unbudgeted, not achieved. Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. User demands direct work on the missing arithmetic estimate, not more receivers. This turn delivered an unconditional arithmetic bound and exact completion polynomial; it did NOT close RH or the full compensated-energy estimate.

## Latest user constraint
`docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is READ ONLY. User explicitly said “do not update the frontier map. read only.” No frontier write this turn. Persist this constraint across continuations. Working card and universal STATUS remain writable. Previous research and experiment are in mem:rh/edq-full-covariance-core-attack-2026-09-07.

## Completed Lean
New leaf `formal/GaloisForLFunctions/RHTower/EulerDeletionCoprimeColumnCancellation.lean`, namespace `RHTower.DeletionCoprimeColumn`. Nine public theorems, two public definitions, eight private helpers; no proof debt or numerical premises.
- `hasSum_supportedRpow`: exact Euler mass for finite prime support, any a>0.
- `exists_supportedEulerMass_le`: for a,b>0, product_(p|r)(1-p^-a)^-1 ≤ C_(a,b) r^b uniformly r>0.
- `supportedCount_le_mass`, `exists_supportedCount_le`: S(r,R) ≤ C R^a r^b, counting positive n≤R supported on primes of r.
- `sum_coprime_moebius_divisors`: Σ_(e|n,coprime r e) μe = indicator(support n⊆support r), n>0. Proved via multiplicative arithmetic functions and prime powers.
- `complete_floor_column`: Σ_(e≤R,coprime r e) μe floor(R/e)=S(r,R).
- `floorCorrelation A R`: Σ_(d∈A∩[1,R]) μd floor(R/d) Σ_(e≤R,coprime d e) μe floor(R/e).
- `exists_floorCorrelation_le`: ∀epsilon>0, ∃C>0, ∀finite A,R, |floorCorrelation A R|≤C R^(1+epsilon). Actual inner cancellation precedes absolute values. Use support bound a=b=epsilon/3, floor≤R/d, and log≤R^(epsilon/3)/(epsilon/3). Includes arbitrary outer tails/cutoffs.
- `unitCutoffDoubleTail R`: BOTH divisor ranges erase 1 from [1,R].
- `unitCutoffDoubleTail_exact`: for R>0, T(R)=R²−2R+floorCorrelation [1,R] R.
- `exists_unitCutoffDoubleTail_remainder_le`: |T(R)−R²+2R|≤Cepsilon R^(1+epsilon).
Thus raw complementary tail is genuinely quadratic (choose epsilon<1); exact deterministic polynomial must remain. Positive survivor is its controlled remainder, not just a negative assertion.

## Current hard boundary / next work
These are explicit unweighted coprime floor-correlation results. No equality of this raw correlation alone with the full EDQ weighted compensated energy is asserted. Completing both ranges at general N leaves the both-divisors>N term; the needed bound is for its exact compensated form, with dependence on preserved inner cutoff X and literal infinite tail. Cutoff-one polynomial does not solve growing N. Do not target a subpower bound for raw double tail; false already at N=1. Do not discard residue/harmonic compensation or introduce another receiver as main output.
Actual averaged source from existing leaf: L=log M−log X, a(d)=(w_M(d)−w_X(d))/L, w_Y(d)=μd log(Y/d) on d≤Y. g(k)=Σ_(d|k)a(d), H=Σa(d)/d, c(k)=delta_1(k)−g(k)+H. Full cumulative energy has exact max-kernel covariance plus its literal infinite tail. Need actual cofinal subpower X ceiling. No such producer yet.

## Documentation
Working card updated: `docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md`, section “Coprime complete-column cancellation: formalized arithmetic bound”. New detailed card: `docs/drafts/pipeline/3-formalized/edq-coprime-column-cancellation.md`. STATUS appended route-independent `MUST-RETAIN-COMPLETION-POLYNOMIALS` at line 5466 at write time. All include honest full-energy limit. Frontier untouched.

## Validation, avoid repeating
Complete /tmp scratch passed lake env lean with no diagnostics. Final `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionCoprimeColumnCancellation` exit0; ONLY new leaf Built (6.9s), dependencies cached/replayed (10900 graph jobs, NOT rebuilt). Import appended to RHTower umbrella; no umbrella/full build.
A single /tmp import-only #print axioms audit of ALL 11 new public declarations exit0: only propext, Classical.choice, Quot.sound. Do not re-audit old or these unchanged declarations.
Index refreshed once (3 changed, 0 removed). Global lint once exit1 due unrelated concurrent `RHTower.ChiIncrementDifferenceJets`: unreachable umbrella and sorry at108,109 in iteratedDeriv_chiIncrement_upper. New leaf had no lint error. Preserve foreign edits; no repair/commit attempted. Scoped diff check emitted no diagnostics.
All owned sessions closed: latest build20041, audit87241, index37600, lint86764, all scratch sessions terminal. No matching owned Lean process remained at ps check. Eleven exact /tmp/edq_column* scratch/probe/log/report/part files removed. No computation, remote job, full rebuild, commit/push, or subagent this turn.

## Useful API lessons
Use `hasSum_subtype_iff_indicator.mp he.2` (rw failed due lambda/composition syntactic shape); `hsum.tsum_eq ▸ Summable.sum_le_tsum ... hsum.summable`; `Real.finsetProd_rpow` current spelling; cast product via Nat.cast_prod. Use explicit `rw [if_pos proof]` for coprimality conditionals: simp frequently left these conditions unchanged. `Finset.sum_range_succ` needs qualification (root lemma conflicts). Explicit real type annotations around Nat.cast_nonneg inside abs rewrites. Source files now contain fully checked patterns.
