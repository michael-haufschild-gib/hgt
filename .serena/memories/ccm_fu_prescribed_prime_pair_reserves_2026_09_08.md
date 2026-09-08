# CCM-FU: prescribed-prime inclusion and uniform pair source profile

RH goal remains ACTIVE and unproved. Frontier map READ ONLY by explicit user override; neither frontier nor universal STATUS was edited. No subagents, commits, full or umbrella builds. Preserve unrelated shared worktree edits.

## Closed new Lean leaves (six public theorem closures)

1. formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimePairRatioProfile.lean:97 `exists_bound_mobiusDivisorPrime_pair_ratio_profile`. Fixed nonempty prime core P admits C>=0, for ALL distinct outside primes q>=p:
|p*(kappa_(P+p+q)-kappa_P)-2*rhoP*(p/q)*sqrt(p/q)*W_P(q/p)|<=C/sqrt(p).
Uniform entire ratio ray. Exact complete pair change, first merger and both density changes retained. Choose C=2*rhoP*(3B+D) using all-Y W bound B and uniform insertion error D. Main decomposition in paper card.

2. MobiusDivisorPrimePairSourceOrientation.lean:49 `exists_mobiusDivisorPrime_pair_tail_orientation`: exists L0>=1; EVERY L>=L0 admits c>0,T giving c/p<=(-1)^cardP*(kappaP-kappa_(P+p+q)) for p>=T and Lp<=q<=(L+1)p. Freely selectable window endpoint is essential for common source-state comparison.
:118 `exists_mobiusDivisorPrime_pair_forced_prime_incompatibility`: even nonempty P, prescribed r outside P, ONE common L,c,T makes same pairs (outside P+r) release >=c/p before r and COST >=c/p after r. No supplied analytic sign hypothesis.
:152 `exists_arbitrarily_large_mobiusDivisor_forced_prime_debt_growth`: such pairs exist beyond every N. Statement contains both inequalities; their sum raises debt kappa_(P+r)-kappaP by >=2c/p. This constrains far-ratio pairs, NOT general repair or other windows. No finite-Q debt-transfer theorem added.

3. MobiusDivisorPrescribedPrimePairReserve.lean:24 `exists_mobiusDivisorEvenCore_prescribed_prime_pair_reserve`: for each nonempty even prime core P, exists c>0,T such that EVERY prime r>=T has prime partner p<r, both outside P, even final core P+r+p and kappaP-kappa_(P+r+p)>=c/r.
:80 `exists_mobiusDivisorEvenCore_prescribed_prime_energy_reserve`: same universal prescribed-prime quantifier, actual QP(M)-Q_(P+r+p)(M)>=c*M^2/r eventually M for chosen pair. Threshold in M depends on r,p.
Positive proof: invert existing even-core reserve window Lp<=q<=(L+1)p. Fix q=r; corpus prime_between with x=r/(L+1), epsilon=1/L supplies p in (r/(L+1),r/L) for EVERY sufficiently large r. Set threshold (L+1)*max(Z,max(T,supP+1)). Complete pair release >=c/p>=c/r. Insertions commute; DOES NOT establish intermediate budget. This is stronger than prior arbitrary-large-pair existence.

## Verification and cleanup

All three leaves passed foreground scratch lake env lean and exact leaf source checks with only their olean emission. No old prerequisite rebuilt. Three imports wired after EvenCorePrimeReserve in RHTower. Six new public declarations audited ONCE via /tmp scratch: only propext, Classical.choice, Quot.sound. No computation premise, sorry or added axiom. Global formal lint passed (existing large-file warnings only), index refreshed, scoped whitespace check passed. Known lake build packaging audit remains pending because its graph expands broad stale prerequisites; don't repeat that broad preflight/build. No umbrella build.

All owned Lean sessions terminal. Process scan found no lake env lean/lake build/owned lean. Removed four exact local scratches: /tmp/ccm_pair_profile.lean, /tmp/ccm_pair_orientation.lean, /tmp/ccm_prescribed_pair.lean, /tmp/ccm_prescribed_audit.lean. New required oleans retained. No live owned local/remote process.

## Bounded RunPod experiment completed

Stage1 docs/drafts/pipeline/1-in-progress/ccm-fu-forced-prime-repair.md froze all-prescribed-prime two-step successor-envelope repair BEFORE run. Exact envelope Psi(P)=max(QP, all Q_(P+q)), original diagonal budget. From EVERY admitted proper saved state and EVERY prescribed remaining r, P+r or P+r+q must restore admission. This stronger quantifier was not predicted by earlier existential good-next tests.

RunPod only: supplied SSH endpoint; eight cutoff workers, one-thread numerical libs, internal50s/external60s deadlines. Reused full saved subset cubes at M=1..32 from ccm-fu-adaptive-prime-energy-2026-09-06 CSV and defect-reserve JSON, crosschecked all energies. No channels regenerated. Original tolerance 1e-12*max(1,B). Diagnostic energy-safe minimum restoration distance; high precision direct source audit frozen for failures only.
RESULT: all8860 states processed,39220 prescribed choices; zero failures,36765 one-step and2455 two-step repairs; no longer/infinite. Runtime0.060543984s. No failure ->80digit audit not triggered. FINITE NUMERICAL EVIDENCE ONLY, no Lean premise. No repeat/larger scan scheduled.
Downloaded script, summary.json, README under docs/drafts/pipeline/2-fully-proven/computations/ccm-fu-forced-prime-repair-2026-09-08/. Local/remote hashes matched. Remote temp /tmp/ccm-forced-prime-UAkzXC fourfiles removed and rmdir; no workers remain.

## Documentation and next hard target

Stage3 docs/drafts/pipeline/3-formalized/ccm-fu-prescribed-prime-pair-reserves.md contains exact quantifiers, dependency-closed paper proofs, orientation obstruction AND positive prescribed-prime survivor, validation and open scope. Stage1 forced-prime-repair and changing-core-dilation-renewal updated; frontier and STATUS untouched.

Full chain: actual divisor source -> renewable signed reserve -> exhaustive prime selection -> uniform signed Abel bound -> RH.
Gaps: each changing even core has a threshold T(P); least omitted prime may always lie below it. Universal coverage ABOVE threshold is proved; arbitrary prescribed small prime is not. Pair endpoint Q benefit doesn't pay initial merger or every successor in Psi. Finite-Q onset varies with selected pair/core; no single every-cutoff bound. No complete RH receiver closed.
Exact two-step finite-cutoff repair involves every Q_(P+r+q+s), hence full three-prime interaction, not just pair release. Experiment supports but doesn't prove it. Future work should directly close below-threshold forced-prime payment or full three-prime every-cutoff envelope, not repeat fixed-core limits or generic receiver/no-go lemmas.

Lean traps: typed cast sup needs ((P.sup id:Nat):Real), otherwise infers OrderBot Real. Use Finset.insert_comm (ambiguous with Set). field_simp may finish alone, extra '; ring' gives No goals. nlinarith on oriented error needs hc:0<c explicitly. Dependencies in mem:ccm_fu_changing_core_pair_reserves_2026_09_08 already checked; do not re-audit.
