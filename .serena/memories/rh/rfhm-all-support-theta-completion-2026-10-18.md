# RFHM: all-support actual Gamma–theta source (2026-10-18)

Verified producer advance; RH remains OPEN. Card: `docs/drafts/pipeline/3-formalized/rfhm-all-support-theta-completion-2026-10-18.md`.

New leaves:
- `formal/GaloisForLFunctions/BiScaleUncertainty/SquarefreeGaussianCompletion.lean`
- `formal/GaloisForLFunctions/RHTower/GammaThetaSupportWeightBounds.lean`
- `formal/GaloisForLFunctions/RHTower/GammaThetaFullSupportSource.lean`
- `formal/GaloisForLFunctions/RHTower/GammaThetaFullSupportCreation.lean`
All four wired into respective umbrellas. All four canonical `lake --old env lean <leaf> -j1 -o ... -i ...` runs exited 0, no warnings/errors. All 29 public theorem axiom checks passed with only propext, Classical.choice, Quot.sound. 38 API probes passed. No full/umbrella build, no commits. Hashes and logs: `/tmp/hgt-rfhm-source-sha256.txt`, `/tmp/hgt-rfhm-audit-manifest.json`, `/tmp/hgt-rfhm-{core,weights,source,creation,axioms,lint}.log`; final audit source `/tmp/hgt-rfhm-axioms.lean`.

Exact construction: for x>0, any z:C, tau:Primes->R, r:N, define chi_p=z exp(i tau_p) and F(P,y)=(product_(p in P) chi_p) W_x(P) exp((|P|+r)y) Phi(y), with corpus-native synchronized Gamma weight W and literal completed theta Phi. `memLp_jasGammaThetaFullSourceFun` proves F belongs to the EXISTING JASGammaThetaL2 over count(Finset Primes) x volume(R). `jasGammaThetaFullSource_section` recovers every exact support coordinate; `jasGammaThetaFullSource_ne_zero` uses the theta vacuum. `summable_jasGammaThetaFullSupport_energy` proves all-support square energy summability with actual theta grade |P|+r.

Mechanism: insertion gain <= vacuum/singleton <= 1/(p+1); inductively W_x(P)<=product 1/(p+1)<=product 1/p. General BSU theorem splits a summable nonnegative incidence family b into finite head and arbitrarily small tail to prove product_S(1+b_i u)<=C_epsilon exp(epsilon u), uniformly over ALL finite S and u>=0. This avoids a fixed formation-radius restriction from the full-trace estimate. The literal theta envelope implies integrability of exp(exp(2y))*exp(2r y)*Phi(y)^2 for every fixed r. Powerset expansion, bounded nonnegative partial sums and Fubini yield the full Hilbert source.

Native creator domain is DISCHARGED: `jasGammaThetaFullSource_mem_creationDomain` uses next actual grade r+1 to pay exp(y), with bounded Boolean gain. `jasGammaThetaFullSource_creation_covariance` proves chi_p * C_(x,p) F = 1_(p in support) F a.e., for every prime and also z=0 (no division). This is the native closed Gamma–theta creator, not a replacement bounded grade shift. `tendsto_jasGammaThetaFullSource_primeCutoffs` proves norm convergence of literal prime<=N alphabet cutoffs. Cutoff coordinate formula retains all compounds over that alphabet.

Boundary: this works at ALL positive apertures, including off wall; it does NOT orient zeros. It is not a unital C(PrimeTorus) intertwiner, prime-Poisson source-linearity, inverse-preimage covariance, or Xi reflection sewing. Existing nilpotency/gauge/inverse-covariance no-gos remain intact. r is arbitrary but fixed; do not claim unweighted summability over all independent extra grades. Exact synchronized coefficients retain their corpus-defined depth completion; no extra independent valuation carrier was constructed.

Repository formal lint ran, exit 1 solely for an unrelated untracked orphan: `GaloisForLFunctions.BezoutValuationIncidence.RenormalizedMobiusDefectAndFirstOctaveCancellation` unreachable from BVI umbrella. Existing large-file warnings remain. No new leaf flagged; unrelated files untouched. Do not call repository lint clean. Recheck external state on next turn.

Rotation after PA to RFHM candidate. Next choose a DIFFERENT family (avoid PA/JAS/RFHM by default), honoring user's 27 live + 18 candidates instruction. See `mem:research/route-rotation-rfhm-2026-10-18`.