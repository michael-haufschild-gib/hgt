# Sixth-moment recovery in the even prime-pair sector

- **ID:** wall15-sixth-moment-recovery-in-the-even-prime-pair-sector
- **Stage:** 3-formalized
- **Type:** THEOREM, formalized in Lean; repository gate status recorded below
- **Wall:** 15, support versus positivity/orientation; field research only.
- **Parent:** [cubic recovery and parity obstruction](../3-formalized/wall15-cubic-odd-mode-recovery-and-parity-obstruction.md).
- **Statement:** In the concrete two-mode sector supported at 6 and 10, all translated moments through order five miss the relative sign, while the single zero-lag sixth moment recovers it from the affine quadratic data, up to one global sign.

## Why this is the next question

The parent mechanism recovers every signed odd-order coordinate, but an exact arithmetic anti-period annihilates the entire odd-moment hierarchy on a nontrivial even sector. A useful next observation must therefore have even degree and couple the separated components. The smallest possible additional degree is four; test that candidate before asserting six is minimal.

At cutoff `N+10`, define the actual two-parameter weights
`w(1)=a+b`, `w(2)=-2(a+b)`, `w(3)=-3a`, `w(5)=-5b`, `w(6)=6a`, `w(10)=10b`, zero elsewhere. Their coordinates are `Y(6)=a`, `Y(10)=b`, all others zero. Their literal response is

`g_(a,b)(n)=(2·1_(2∣n)-1)[a(3·1_(3∣n)-1)+b(5·1_(5∣n)-1)]`.

Write `M₆(a,b)=((N+10)!)⁻¹∑(0≤n<(N+10)!)g_(a,b)(n)^6`. All claims below concern this actual finite average, not an assumed spectral model.

## Conjecture loop

**C1 [PROVED; LEAN]: quartic data are still insufficient.** Changing `b` to `-b` preserves every translated fourth moment, for every four-lag vector. Together with the parent anti-period and affine classification, it preserves every translated moment of order at most five and every affine quadratic observation.

Proposed proof: the parity factor is a character, so its product across four shifted values is independent of the averaging variable. Expand the remaining product in its mod-3 and mod-5 factors. Every term that changes sign under `b↦-b` contains exactly one factor from one of these prime classes. CRT independence then gives its zero mean. This is a symbolic product decomposition, without enumerating a period. An alternative check is that a resonant quadruple cannot contain only one primitive mode from a prime denominator absent from the other three.

**C2 [PROVED; LEAN]: exact sixth-moment decoder.** The literal identity is

`M₆(a,b)=22a⁶+360a⁴b²+480a³b³+1560a²b⁴+820b⁶`.

Derive it from CRT independence and the two-valued prime rows `R_p(n)=p·1_(p∣n)-1`. Their complete-period powers have exact mean
`E[R_p^j]=((p-1)^j+(p-1)(-1)^j)/p`. The parity factor disappears at even degree. In the binomial expansion, the terms with one factor of either prime row vanish; the sole term sensitive to the relative sign is `20 a³b³ E[R_3³]E[R_5³]=480a³b³`. Thus

`M₆(a,b)-M₆(a,-b)=960a³b³`.

These constants follow from the symbolic CRT moment formula. Both the finite averaging identity and all coefficients passed paper and Lean audits; no numerical experiment or period enumeration was used.

**C3 [PROVED; LEAN]: complete recovery on this sector.** Affine quadratic data recover `a²,b²`. C2 then recovers `(ab)³`, hence the signed product `ab` by real cube injectivity. Equality of `a²,b²,ab` determines `(a,b)` up to one global sign, including cases where a coordinate vanishes. Formulate an exact equivalence on arbitrary real parameters; do not add nonvanishing assumptions.

This gives a sharp degree-six repair for this explicit obstruction. It does not reconstruct arbitrary sieve profiles. At `a=b=1`, the sixth moments differ by exactly 960 even though every lower-degree translated moment agrees.

## Dependency-closed paper audit

The concrete claims C1–C3 hold on paper. Write `E_P F=P⁻¹∑_{n<P}F(n)`, `P=(N+10)!`, and `R_p(n)=p·1_(p∣n)-1`. Both 3 and 5 divide P; coprimality implies 15 divides P. Any function of `(n mod 3,n mod 5)` is 15-periodic. Split the sum into complete blocks of length 15. The Chinese remainder bijection `Z/15 ≅ Z/3 × Z/5` then gives, for every function F on those two residue classes,

`E_P F(n mod 3,n mod 5) = (1/15) ∑_{x mod 3}∑_{y mod 5} F(x,y)`.

This is an exact finite bijection and block decomposition, not an equidistribution assumption. Translations in each residue group permute its elements. Since `∑_{x mod p}R_p(x)=(p-1)+(p-1)(-1)=0`, every shifted prime row has zero mean. Products depending on distinct residue coordinates factor under the double sum.

The weight formula follows from the already certified one-parameter weights by the literal linear combination `w_(a,b)=a·parityReal(0)+b·(parityReal(1)-parityReal(0))`. Both actual sieve response and multiples coordinates are linear finite sums. Thus their stated response and two-mode profile hold for every real a,b, including zero. Existing comparable-coordinate classification proves that equality of all affine observations is exactly equality of `a²,b²`: the only nonzero supported comparable pairs are the two diagonal pairs, since 6 and 10 are incomparable.

For four arbitrary natural lags `h_i`, the parity product is independent of n: `∏_i(-1)^(n+h_i)=(-1)^(∑h_i)`. Expand the remaining four-factor product. A term changes under `b→-b` only when it contains one or three prime-5 factors. In the first case its prime-5 factor has zero mean; in the second case its lone prime-3 factor has zero mean. CRT factorization kills every such term. This proves equality for all four-lag vectors. The same expansion proves degree-two blindness. Every odd-length product has zero average by the inherited anti-period 15. Degree zero is the constant one. Hence every translated moment of degree at most five agrees after either independent coefficient sign change.

For even zero-lag degree six, the parity factor disappears. At every nonnegative exponent j, a prime row has exactly one value p−1 and p−1 values −1, giving the displayed formula for its mean power. Apply the binomial theorem and CRT factorization. The j=1,5 cross terms vanish; j=0,2,3,4,6 give respectively the coefficients 820,1560,480,360,22 in the stated polynomial. These are rational consequences of the symbolic moment formula; no period enumeration or numerical experiment is used. The sign-sensitive term is exactly `480(ab)³`.

Given identical affine data and sixth moment, the even-power terms cancel by equality of a² and b², leaving `(ab)³=(a'b')³`. Real cube injectivity gives `ab=a'b'`. From `a²=a'²` and `b²=b'²`, each coefficient differs only by a sign. When both are nonzero, equality of products forces the signs to agree. When either is zero, the remaining coefficient alone chooses a global sign; no nonzero premise is added. Conversely, a simultaneous global sign preserves all quadratic and sixth-degree data. This proves the exact equivalence with `(a',b')=(a,b)` or `(a',b')=(-a,-b)`.

For a=b=1, the sign-flipped pair has equal affine and every translated moment through degree five, but sixth moments differ by 960. Therefore six is the least moment degree that repairs this particular obstruction. The conclusion concerns this sector and observation family, not arbitrary sieve reconstruction or Wall 15 as a whole.

Refreshed corpus evidence: `/tmp/bsu-sixth-frontier-r1.json` returned 20 candidates and 20 source arguments, all inspected; existing affine/triple/parity certificates apply, with no direct sixth decoder among returned hits. `/tmp/bsu-sixth-crt-deep-r1.json` returned 20 candidates, 20 source arguments and one unrelated cyclic-generator ingredient set, all inspected. Both report `partial=false`, older coverage snapshots, unmeasured semantic coverage and unfinished background refresh. No global absence or external novelty claim.

## Lean certificate and integration evidence

- [EvenPrimePairMomentCalculus.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/EvenPrimePairMomentCalculus.lean): 7 public exports, including exact factorial CRT averaging, centered-row power sums and arbitrary-lag quadratic/quartic blindness. Final named original-source check passed without diagnostics: `/tmp/bsu-sixth-calculus-final-r2.log`, exit 0.
- [SixthSievePhaseRecovery.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SixthSievePhaseRecovery.lean): 13 public exports on actual divisor weights and literal period averages, including the exact global-sign classification and sharpness witness. Final named original-source check passed without diagnostics: `/tmp/bsu-sixth-main-final-r1.log`, exit 0.

All 20 public signatures and axiom closures were audited in `/tmp/bsu_sixth_public_audit.lean`, exit 0, no diagnostics (`/tmp/bsu-sixth-public-audit-r1.log`). The exports comprise 18 theorems and 2 definitions. Every closure uses only `propext`, `Classical.choice`, `Quot.sound`. Printed and inspected both new definition bodies and the five underlying actual definitions: `translatedMoment`, `parityReal`, `sieveSeq`, `selbergMultiplesCoord`, `AffineSieve.affineMoment`. No hidden nonvanishing premise or proxy observation replaces the actual sieve.

Checks used `lake --old env lean -j 1`, compiling the absolute original sources with `--root=/Users/michael/Documents/code/hgt/formal` in the previously verified `/tmp/bsu-two-lag-workspace`. Toolchain and original-source link were rechecked; eight prior supporting artifacts matched byte-for-byte. Four owned new artifacts were copied back and byte-verified. No full or umbrella build ran. Serena rejected the owned Lean path as ignored; direct file edits were used for these new leaves.

Both umbrella imports occur exactly once. Scoped lexical discovery inspected all 28 declarations (12/16 by leaf), including exactly all 20 public exports, with no pagination gap. Evidence: `/tmp/bsu-sixth-discovery-{calculus,main}.json`. The protected README and wall-ledger hashes matched the initial snapshot. Certificate manifest: `/tmp/bsu-sixth-phase-manifest.json`; session state: `/tmp/bsu-sixth-phase-session.json`.

Initial repository lint exited 1 with six unrelated unreachable-module errors. After concurrent umbrella wiring changed, the final index refresh passed, exit 0 (`/tmp/bsu-sixth-index-r2.log`). Final `scripts/formal_tools.py lint --check-generated` exited 1 (`/tmp/bsu-sixth-lint-r2.log`) with one remaining unrelated error: `GaloisForLFunctions.RHTower.GammaThetaFullSupportCreation` is unreachable from its theorem-area umbrella. There are 381 existing size warnings, no owned wiring errors and no proof-debt findings. The repository gate has **not passed**; the unrelated RH module was not modified. No checked Lean source has changed.

All owned processes are terminal. Three obsolete prototype Lean files were moved without overwrite into `/tmp/bsu-sixth-phase-archive-20261018/`; final audit source, logs, manifests and the verified dependency workspace remain. Related card links were updated for the stage move. Both field READMEs and the wall ledger remained unchanged. Cross-session memory: `biscale/wall15-sharp-sixth-moment-recovery`.

The [failed through-five recovery route](../5-failed/wall15-recovery-from-affine-and-through-five-moments.md) records the exact obstruction and this strongest positive survivor. The [finite odd-prime-family follow-up](../0-backlog/wall15-sixth-order-recovery-for-finite-odd-prime-mode-families.md) remains conjectural, including its three-mode scalar-observation counterexample.

## Possible further extension (not a separate result)

For distinct odd primes `p,q`, the same argument predicts that modes `2p,2q` have sign-sensitive sixth-moment difference
`40a³b³(p-1)(p-2)(q-1)(q-2)`, with degree four still blind. Audit and prove the concrete 3/5 sector first, then determine whether the general prime-pair theorem is the exact same argument rather than count it as a separate discovery.

## Corpus evidence and constraints

Search `sixth moment minimal correlation order parity prime modes`, scoped to BiScaleUncertainty, returned no lexical hits and 20 candidates plus 20 source arguments; every inventory inspected. Hits included the current affine/triple/parity packages and older correlation bounds, with no direct sixth-moment phase decoder among them. Coverage is an older snapshot, semantic coverage unmeasured, refresh incomplete. Evidence: `/tmp/bsu-sixth-order-frontier-r1.json`. This bounded internal search does not establish external novelty; refresh it before implementation.

Use actual divisor weights and literal finite averages. No numerical experiments, hgtl7, RH work, unproved analytic hypotheses, new axioms, heartbeat increases or full/umbrella builds. Protected field READMEs and wall ledger remain read-only. Wall 15 remains open.

## Task tracker

1. [complete] Refreshed bounded corpus frontier and audited the full paper proof, including all quartic lag vectors and zero coefficients.
2. [complete] Exact actual-sieve identities, all lower-order blindness, sixth polynomial and global-sign classification formalized. Both final named original-source checks passed cleanly; one owned foreground Lean process at a time.
3. [complete] All signatures, bodies and axioms audited; owned wiring, discovery, protected hashes, memory and scratch cleanup verified. Final shared repository gate failure recorded above; no claim that the repository gate passed.

`update_plan` is unavailable. This card is the durable tracker. Owned scope: this card and stage moves, new BiScale leaves, their umbrella imports, generated index, direct predecessor links, next-conjecture/no-go cards if needed, and task memory. Both field READMEs, the wall ledger and other workers' records remain read-only.

## Gates

- [x] 0 → 1: refreshed frontier, exact weight/CRT applicability audit.
- [x] 1 → 2: dependency-closed paper proof of quartic blindness, sixth polynomial and full two-parameter recovery.
- [x] 2 → 3: exact Lean certificate, named-leaf and public-axiom audit, owned wiring and complete discovery. Repository gate status is recorded above.
- [ ] 3 → 4: publication audit.

## Log

- 2026-10-18: **Progress**. Full 20-export certificate and all seven definition-body audits passed; sharp lower-order obstruction recorded with its exact sixth-order positive survivor. Final repository lint remains red on one unrelated RH wiring error; no owned or proof-debt errors. Finite odd-prime-family recovery and a three-mode scalar-observation obstruction remain conjectural. Wall 15 and the all-walls goal remain open.

- 2026-10-18: previous goal turn classified **Progress**. Selected Wall 15, refreshed the bounded frontier and completed the dependency-closed paper proof. `EvenPrimePairMomentCalculus.lean` (7 exports) and `SixthSievePhaseRecovery.lean` (13 exports) passed final named original-source checks with no diagnostics. Full public audit and repository gate in progress. The arbitrary finite odd-prime-family follow-up is queued separately as a conjecture.

- 2026-10-18: proposed while the parent actual-object leaf's clean final check was running. No result on this card is counted as completed or Lean-certified.
