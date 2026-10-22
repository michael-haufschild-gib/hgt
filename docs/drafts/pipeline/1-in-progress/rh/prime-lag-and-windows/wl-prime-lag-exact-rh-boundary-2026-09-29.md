# WL prime-lag exact RH boundary

- **ID:** WL-PLB-20260929
- **Stage:** 1-in-progress
- **Type:** NOVELTY REJECTION; positive geometric survivor candidate
- **Source:** `WeilLagQuadraticInterpolation` and actual unconditional `WeilLagFunctionPrimeGap.exists_prime_short_gap` / `Sieve.InghamUniformDetectorMellinHoheiselEveryBase.exists_eventually_routeT_prime_in_every_base_window`.
- **Statement:** Actual primes form a `QuadraticLagMesh`. The proposed RH boundary is already in the corpus and is not new knowledge. Only the explicit geometric mesh and its interpolation proof remain candidates for distinct structural knowledge.

## Plan
1. [x] Corpus novelty rejected the proposed RH boundary; inspect positive geometric survivor and source axioms.
2. [x] Derive dependency-closed paper proof from the actual 71/100 supply and 3/4 mesh threshold.
3. [ ] Verify rpow APIs, formalize actual prime mesh and closed equivalence.
4. [ ] Targeted artifacts, all-public axiom audit, direct source audit, umbrella wiring, frontier and index updates.

## Paper proof
For every sufficiently large integer k, the existing lower-prime theorem gives a prime p<=k with k-p<p^(71/100). Since p>=2 and 71/100<1, k<=2p. The existing every-base theorem gives a prime q>k with q-k<=k^(71/100). Monotonicity and multiplicativity of positive real powers yield k^(71/100)<=2*p^(71/100). Hence q-p<=3*p^(71/100), and
`(q-p)^2 <= 9*p^(142/100) <= 9*p^(3/2) = 9*p*sqrt(p)`.

Choose one fixed prime above both source thresholds. Every remaining integer k>=2 is bracketed by 2 and that fixed prime; increasing the mesh constant absorbs this bounded initial segment without evaluating any lag or prime table. Thus the actual prime set has a quadratic mesh unconditionally. Apply the already audited upper-interpolation receiver. Conversely RH bounds every actual integer lag by the existing sharp constant.

No estimate of prime lag values is claimed. The new receiver identifies exactly which arithmetic ceiling remains open. No density or counting-series continuation is used.

## Log
- 2026-09-29: Source statements read directly. Both short-gap sources are explicit unconditional theorems in the current corpus. Their actual axiom audit is pending; no inference from recalled prime-gap literature. C11 finite-mean scratch remains the sole owned foreground Lean process while this paper candidate is recorded.
- 2026-09-29: Exhaustive `rg` for prime-lag names found `PrimeLagLandauPrimesOnly.riemannHypothesis_iff_primeLag_bddAbove` and `riemannHypothesis_iff_primeLag_le_sharp`, plus `PrimeLagGrowthExponent`. The frontier map's quarter-to-three-quarters sentence does not enumerate the full corpus. The proposed exact-prime RH boundary fails novelty. Positive survivor: actual primes form the newly introduced quantitative quadratic mesh, giving a local-interpolation proof independent of the existing Landau counting-series argument. This survivor has a complete paper proof above; Lean status pending. No route retirement or new RH endpoint claim.
- 2026-09-29: Complete actual-prime mesh scratch passed, no warnings; both actual lower/every-base supply dependencies audited with exactly `[propext, Classical.choice, Quot.sound]`. Production leaf `formal/GaloisForLFunctions/RHTower/WeilLagPrimeQuadraticMesh.lean` copies the verified paper survivor, exposes only `quadraticLagMesh_actual_primes`, and explicitly avoids claiming the already-existing RH boundary as new. Own umbrella import wired; targeted artifact build running. Own leaf axiom and final direct-source audits remain pending.
