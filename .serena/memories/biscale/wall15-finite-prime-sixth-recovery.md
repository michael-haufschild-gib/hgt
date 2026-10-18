# Wall 15 finite-prime sixth-order recovery — complete

User cleared the prior all-walls goal and requested completion of the already-started package only. Completed current C1/C2/C3 nine-leaf package; stop here. No next-topic card or new route after that instruction. No RH work, subagents, numerical period enumeration, extra analytic premises/axioms, heartbeat changes, full/umbrella build, commit or push.

Formalized card: `docs/drafts/pipeline/3-formalized/wall15-sixth-order-recovery-for-finite-odd-prime-mode-families.md`.
Exact failed route with strongest positive survivor: `docs/drafts/pipeline/5-failed/wall15-recovery-from-affine-and-one-zero-lag-sixth-moment.md`.
Both predecessor-card links/status claims were updated. Wall 15 remains open globally; no arbitrary multi-block reconstruction or stability claim.

## Exact results

Actual atoms A_p(d)=δ1−2δ2−pδp+2pδ2p have multiples coordinate Y(2p)=1, zero elsewhere, and response parity(n) R_p(n). `primeFamilyWeight_finite_support` proves the zero-extension bridge for every finite odd-prime support, including empty/zero cases.

C1: `primeFamily_sixth_iff_common_sign` proves full literal sixth-lag data alone determine finite prime-family coefficients up to one common sign. `primeFamily_readouts_iff_common_sign` gives the finite explicit Fourier protocol; affine+sixth equivalence is also proved. The readout is P^6(a_p a_q)^3, P=N!: six UNANCHORED lag variables, not the distinct anchored P^5 convention.

Stronger survivor: for arbitrary actual weights, sixth readouts recover signed coordinate products within any fixed power-of-two valuation class, including composite odd parts and odd part one. `sixthPairReadout_eq_iff`, `sixth_readouts_eq_iff_valuation_sign`, `sixth_moments_recover_valuation_block`. Full sixth data imply one sign per valuation block; do not assert converse/classification for arbitrary full data across multiple blocks.

C2: all affine data determine exactly coefficient squares. Every independent coefficient sign flip preserves all translated moments through degree five; every odd translated moment vanishes at every odd degree. Exact finite CRT, arbitrary-lag quadratic/quartic blindness, and the actual moment bridge are formalized.

C3: at cutoff N+14, fixed positive real roots u^3=5, v^3=2 produce vectors (1,u,−v), (1,−u,v) on primes 3,5,7. Same all-affine, all-through-five and zero-lag-sixth observations, no common sign. Selected prime-3/prime-5 sixth readouts differ by exactly 10*((N+14)!)^6; some literal sixth lag separates them. This retires that scalar observation route and supplies explicit positive salvage.

## Production leaves

All under `formal/GaloisForLFunctions/BiScaleUncertainty/`, namespace `GaloisForLFunctions.BiScaleUncertainty.SieveMoments`:
- SieveMomentFourier
- ValuationTripleResonance
- SixthValuationPhaseRecovery
- OddPrimeSieveFamilies
- FiniteCoprimeMomentCalculus
- PrimeFamilyTranslatedMoments
- PrimeFamilyPhaseRecovery
- ThreePrimeMomentCollision
- ThreePrimeScalarPhaseCollision

All nine original absolute named-source checks passed with zero diagnostics via `lake --old env lean -j 1 -R /Users/michael/Documents/code/hgt/formal` in verified `/tmp/bsu-two-lag-workspace`. Toolchain/source link match; all 18 olean/ilean artifacts copied back and byte-verified; nine umbrella imports exactly once.

Audit: 96 source declarations (89 named plus seven anonymous local instances); 59 public exports (46 theorems, 12 definitions, one named instance). Every public signature/axiom closure, 21 definition bodies (13 new public bodies plus eight underlying actual objects), and 150 toolchain API probes checked. Only propext, Classical.choice, Quot.sound. Final audit `/tmp/bsu_family_public_audit.lean`, `/tmp/bsu-family-public-audit-r2.log`, exit 0. Initial audit failed only on unsupported optional pp.width; removed. Final output otherwise byte-matches reviewed output.

Complete scoped discovery found all 89 named declarations/all 59 public exports. Final index refresh passed. Plain formal lint ran; after concurrent BVI import fixes, index and `lint --check-generated` reran. Final lint `/tmp/bsu-family-lint-r2.log` exited 1: unrelated BVI `ShiftedExponentAsymptoticDensityAndActiveMartingaleRate` unreachable from its umbrella; 381 size warnings outside package, no owned, proof-debt or generated-file findings. Do not claim repository gate passed. Do not chase concurrent unrelated modules.

Manifest `/tmp/bsu-family-phase-manifest.json`; state `/tmp/bsu-family-phase-session.json`; complete inventory `/tmp/bsu-family-declaration-inventory.json`; discovery validation `/tmp/bsu-family-discovery-validation.json`. Source hashes and 22 card links verified; scoped git diff check passed.

BiScale README and wall-ledger hashes unchanged. This task did not edit either field README or BVI worker counter. BVI README changed concurrently (initial fd49791f7d68e197372bfb55bf0289d3c19d24a39bfdb67eb8881d76a0b869e9; observed f7d5f06f18a850bce987cae5d297d2a1fb340ef1fbe0272d68ff33b9e00d1673); preserved, not restored. Manifest records current hashes.

Twenty owned obsolete prototypes, helpers and abandoned next-topic scratch were moved with mv -n and byte-verified into `/tmp/bsu-family-phase-archive-20261018/`. Final audit, logs, manifests, discovery results and dependency workspace retained. No owned background Lean process remains.

Useful Lean details: use Fin.cons and eta-expanded `fun i => Fin.elim0 i` for dependent Fin-indexed data, rather than fin_cases into Type; explicit congrArg avoids costly generic congr inference; separate sum-ite simplification from final constructor rfl. Polymorphic API probes work as `example := (have checked := @Name; @checked)`.