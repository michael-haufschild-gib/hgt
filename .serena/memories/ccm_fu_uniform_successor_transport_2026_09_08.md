# CCM-FU: uniform polynomial quotient costs and successor-envelope transport

Goal active and unmet: unconditional RH proof/falsification via CCM-FU. Previous turn made progress (analytic successor-average counterexample); this turn adds all-cutoff source estimates. Frontier map is READ-ONLY for this task. It became dirty through concurrent work by end of turn; do NOT revert or edit it. STATUS not changed here. No subagents, no numerical experiment, no commits.

## New authoritative formal module
formal/GaloisForLFunctions/RHTower/MobiusDivisorUniformSuccessorTransport.lean
~294 lines, new and wired into RHTower immediately after MobiusDivisorSuccessorAverageObstruction.

Let Q_P be literal energy, Psi(P) max of Q_P and all available one-prime successor energies, B=Q_empty, L_p=floor(M/p).
Unconditional actual-source bounds:
- sum_R |F_P(R+p)| <= (3/5)sqrt(M)L_p.
- J_p=sum_R F_P(R+p)^2 <= (9/25)M L_p^2.
These two even allow p already processed. No prime/sign/cardinality hypothesis on P.
- |Q_(P+p)-Q_P| <= (6/5)L_p sqrt(M Q_P), and corresponding squared inequality.
- Psi(P+p)<=Psi(P)+(6/5)L_p sqrt(M Psi(P)), simultaneously over ALL alternative q, all overlaps.
- sqrt(Psi(P+p))<=sqrt(Psi(P))+(3/5)sqrt(M)L_p, including already processed p.
- For every finite T of active primes, sqrt(Psi(P union T))<=sqrt(Psi(P))+(3/5)sqrt(M)sum_(p in T)L_p. Apply to subsets to bound all ordering prefixes.
- p*(Psi(P+p)-Psi(P))<=(6/5)M sqrt(M Psi(P)).
- NEW original diagonal ceiling B<=(9/25)M^2, from the newer channel amplitude. Earlier 722M^2 bound remains true but is weaker.
- If delta>0, Psi(P)+delta*M^2<=B, and B<Psi(P+p), then delta*p<(18/25)sqrt(M).
Thus sufficiently large available primes are safe with a stated quadratic reserve. No reserve or prime availability producer has been proved.

Ten public theorems in RHTower:
sum_abs_mobiusDivisorPrimeFibre_le_quotient
sum_mobiusDivisorPrimeFibre_sq_le_quotient
sq_mobiusDivisorSelectionEnergy_insert_le_quotient
abs_mobiusDivisorSelectionEnergy_insert_le_quotient
mobiusDivisorSuccessorEnvelope_insert_le_quotient
sqrt_mobiusDivisorSuccessorEnvelope_insert_le_quotient
sqrt_mobiusDivisorSuccessorEnvelope_union_le_quotient_sum
mul_mobiusDivisorSuccessorEnvelope_insert_sub_le
mobiusDivisorSelectionEnergy_empty_le_nine_twentyFifths_sq
mobiusDivisorSuccessorEnvelope_failure_prime_bound

## Proof mechanism
Count original coefficients BEFORE aggregation. Triangle + exchange finite sums shows grouping cannot increase total absolute mass. A p-containing retained label can only receive coefficients n divisible by p. Insert-p is injective on p-free labels; reindex n=p*d and use |C_n(M)|<=.6sqrt(M) for all n. There are floor(M/p) terms including harmless zero terminal n=M. Sum squares<=square of nonnegative sum yields J bound; Cauchy with actual parent-child pairing gives signed gain.

For envelope compare at P+q: Q_(P+q)<=Psi(P), p still available there. Same universal bound controls every second successor, including overlapping pq<M. No separate exponential mixed-core factor. Taking finite maximum yields transport. Square-root costs add by induction.
B ceiling follows exact empty-energy sum and M times .36M. If failed successor has gain>delta M², multiply by p, bound floor via p*floor(M/p)<=M, and use Psi<=B<=.36M². Cost<=.72 M²sqrtM; cancel M².

This complements rather than uniformly dominates older small-core bound .36*4^(corecard-1)*M*floor((M-1)/p): sparse core can still be better. New bound is polynomial even when depth grows, independent of all processed-cardinality growth.

## Verification completed (do NOT repeat)
Full scratch49000 EXIT0, exact installed emit11259 EXIT0, no warnings.
One external axiom audit82402 EXIT0 checked ONLY the ten new public declarations, all standard propext/Classical.choice/Quot.sound. No old proof re-audited.
Indexes refreshed. Lint initially failed on concurrent HTGeometry.TiltedWeightTopConcentration (sorry and unwired), then only unwired, then passed after owner removed debt and wired it. Repeat checks were justified by observed source changes. Final lint29085 EXIT0 with existing size warnings. Current LEAN_OVERVIEW active proof debt0.
Own whitespace/doc links and git diff --check passed.
Targeted Lake packaging remains pending; do NOT repeat known expensive lake build --old prerequisite rebuild. No umbrella/full build run. Do not claim lake build passed.
All owned Lean/Lake handles terminal, ps confirmed none. Removed six exact owned /tmp ccm_fu_uniform_transport* scratch/log paths. Needed installed olean retained. No remote computation/worker this turn.

## Documentation
New card moved from1-in-progress to:
docs/drafts/pipeline/3-formalized/ccm-fu-uniform-successor-transport.md
Contains complete paper proof, exact quantifiers, batch cost, prime threshold, missing reserve production/renewal and validation.
Updated:
docs/drafts/pipeline/1-in-progress/ccm-fu-exact-successor-extension.md
docs/drafts/pipeline/1-in-progress/ccm-fu-greedy-envelope-extension.md
Frontier map read only, STATUS untouched by us.

## Remaining hard problem
Full chain: actual divisor source -> signed simultaneous selection/exhaustive compatible order -> uniform signed Abel bound -> CCM-FU RH.
Missing one actual p for every admitted P satisfying Delta_p+Delta_q+2C_pq<=B-QP for EVERY q.
New theorem closes this when some available p is large relative to inverse reserve fraction. It does not supply reserve, ensure such a prime remains, or prevent cumulative batch cost from exhausting it. Near-zero reserve and smaller primes need arithmetic signed compensation. Do not reset additive cost without proving fresh energy release; do not substitute a generic receiver or another finite repeat screen for that source law.
Possible useful next checks: localize parent energy in Cauchy to actual quotient-supported labels (whole Q can be wasteful after head correction); inspect existing head/transverse compensation producers before adding anything. Also inspect exact combination of large-original-prime two-pair ceiling with existing separated-pair theorem before inferring how many fixed prime exceptions remain; no new combined result was proved here.

## Practical Lean notes
- grouped sum with condition a n = R simplifies using Finset.sum_ite_eq (not prime version).
- RHTower shadows add_le_add_right under these imports: unqualified theorem gave addition on left. Use qualified root or linarith for a fixed added constant.
- energy_nonneg needs explicit change to sum of fibre squares before sum_nonneg to avoid stuck metavariables.
- Keep edits at repo root separate from lake env lean invocation with workdir formal. Mixed workdirs caused avoidable initial command errors, fixed.
- A bounded unsigned remainder after removing leading sqrt term was considered but NOT inferred. Existing exact expansion retains moving terminal modular residue. No experiment or no-go claim about bounded remainder was made; actual proof uses established amplitude bound.
See mem:ccm_fu_successor_average_and_prime_separation_2026_09_08 and mem:ccm_fu_global_unsigned_envelope_2026_09_07 for prior checked results.
