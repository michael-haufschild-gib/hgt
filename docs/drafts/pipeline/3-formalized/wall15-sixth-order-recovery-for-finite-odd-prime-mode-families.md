# Sixth-order recovery for finite odd-prime mode families

- **Stage:** 3-formalized
- **Type:** PROVED on paper and formalized in Lean; C1/C2/C3 complete
- **Wall:** 15, support versus orientation; field research only
- **Parent:** [sharp sixth-moment recovery in the even prime-pair sector](wall15-sixth-moment-recovery-in-the-even-prime-pair-sector.md)
- **Exact no-go:** [affine data and one zero-lag sixth moment](../5-failed/wall15-recovery-from-affine-and-one-zero-lag-sixth-moment.md)

## Exact objects and completed results

For a finite set S of odd primes, choose real coefficients a_p and a cutoff containing every 2p. The actual divisor weights are

`c_a(d)=Σ_(p∈S) a_p [1_(d=1)−2·1_(d=2)−p·1_(d=p)+2p·1_(d=2p)]`.

Their literal response is `s_a(n)=parity(n) Σ_(p∈S) a_p(p·1_(p∣n)−1)`. The multiples coordinates are exactly `Y(2p)=a_p`, zero elsewhere. `primeFamilyWeight_finite_support` proves the finite-support zero-extension bridge to the cutoff-indexed construction. Empty support and zero coefficients are included.

**C1, strengthened:** full sixth translated moments alone determine the coefficient family up to one common sign. The finite family of explicit sixth Fourier readouts already suffices. `primeFamily_sixth_iff_common_sign` and `primeFamily_readouts_iff_common_sign` give both directions; `primeFamily_affine_sixth_iff_common_sign` includes affine data as a redundant observation.

**C2:** every independent sign change preserves all affine data and every translated moment through degree five. All odd translated moments vanish, at every odd degree. Exact CRT averaging and arbitrary-lag quadratic/quartic blindness are proved for the actual weights. Together with the parent's two-mode witness, degree six is the sharp uniform recovery degree in this sector.

**C3:** at every cutoff N+14, the actual three-prime coefficient vectors `(1,u,−v)` and `(1,−u,v)`, with fixed positive `u³=5`, `v³=2`, have the same affine data, all through-five translated moments and the zero-lag sixth moment, but are not common-sign multiples. Their selected p=3/q=5 sixth Fourier readouts differ by exactly `10((N+14)!)^6`; some literal sixth lag separates them.

**Stronger positive survivor:** for arbitrary actual divisor weights, sixth readouts recover every signed pair product of multiples coordinates within each fixed power-of-two valuation class, including odd composite parts and the odd part one. Consequently full sixth-lag data recover each valuation block up to a common sign, without support or nonvanishing premises. This is an implication for arbitrary full sixth data, not a complete classification across different valuation blocks.

## Dependency-closed paper proof

**Unconditional readout, stronger than C1.** Let P=N!, and write d=2^k p, e=2^k q with p,q positive odd and d,e≤N. Put r=P/d and s=P/e, viewed modulo P. The order of r is exactly d. If p=1, the triple `(r,r,−r)` has three entries of order d and sum P/2^k. If p≥3, use `(r,r,(p−2)r)`. Its sum is again P/2^k; p−2 is odd and coprime to p, so it is coprime to 2^k p and the third entry has order d. The q triple has the same sum. Concatenating the p triple with the negatives of the q triple gives six frequencies of total sum zero, with orders `(d,d,d,e,e,e)`.

For the actual normalized m-lag average M_f(h)=P⁻¹Σ_n∏_i f(n+h_i), define its unnormalized Fourier transform in **all m unanchored lag variables**. Expanding finite sums gives

`DFT_m M_f(r)=1_(Σr_i=0) ∏_i DFT(f)(r_i)`.

Each lag sum contributes `χ(n r_i) DFT(f)(r_i)`; the base-point average of `χ(n Σr_i)` is exactly the zero-frequency indicator. Thus the selected six-frequency coefficient is `P^6 (Y_c(d)Y_c(e))^3`. The factor is P^6 because six unanchored variables are transformed; P^5 belongs to the distinct anchored five-variable convention. This normalization change does not change the given full sixth-lag observation family. No support or nonvanishing assumption enters this actual-sieve identity.

Equality of full sixth-lag data therefore implies equality of every signed pair product within each fixed power-of-two valuation class. Real cube injectivity removes the cube, and P>0 removes the scalar. A real vector is determined up to common sign by its outer-product matrix: if it is zero, diagonal products force the other vector to be zero; otherwise choose a nonzero coordinate, use its square to select a sign, and use its products to recover all other coordinates. This proves block recovery, including empty and zero blocks.

**Actual finite-prime family.** For each cutoff N, use the finite index set of odd primes p with 2p≤N and arbitrary real coefficients. Expanding the four divisor atoms for each p gives exactly `parity(n)Σ_p a_p R_p(n)` and the multiples profile `Y(2p)=a_p`, zero elsewhere. Consequently, sixth-lag data **alone** determine all coefficients up to common sign. The finitely many explicit pair readouts suffice; affine data are redundant for this recovery theorem. Global sign preserves every sixth moment, proving the reverse implication. This includes every finite odd-prime family by setting unused coefficients to zero.

**C2.** Exact CRT identifies averaging over one full product period with independent uniform residue coordinates at the distinct odd primes; that product divides N!, so complete factorial-period averages agree. Every shifted centered row has zero mean. Expand a four-lag product by assigning a prime to each of its four factors. Unless the assignment is one repeated prime or two repeated pairs, at least one prime appears once, and its independent centered factor kills the term. Surviving coefficient powers are all even, hence every independent coefficient sign change preserves every quartic lag. The degree-two argument is identical. The odd product of supported primes flips the common parity factor and preserves every prime row, annihilating every odd-degree moment. Degree zero is constant. All through-five data are therefore independently sign-blind. Existing affine classification also makes all affine data independently sign-blind because distinct supported indices 2p,2q are incomparable.

**C3 and its positive survivor.** At cutoff N+14, keep only p=3,5,7. Choose positive u,v with u³=5,v³=2; existence follows from the bijectivity of the real cube and positivity follows from the cube signs. Put X=R3 and W=uR5−vR7. The two literal responses are `parity·(X+W)` and `parity·(X−W)`. At degree six the parity factor disappears and

`(X+W)^6−(X−W)^6=12X^5W+40X^3W^3+12XW^5`.

CRT separates X from W. Both first moments vanish; the middle contribution also vanishes because `E[W³]=12u³−30v³=0`. Hence the scalar sixth moments agree. Coordinate squares agree, so all affine data agree; C2 and the anti-period give equality of all through-five and all odd translated data. The vectors `(1,u,−v)` and `(1,−u,v)` cannot differ by a common sign because the first coordinate is one and u>0. The explicit p=3/q=5 sixth Fourier readout differs by `10P^6`, since its signed cubes are +5 and −5. The strongest positive survivor is therefore an explicit observable separating the scalar collision, together with unconditional block recovery and complete finite-family reconstruction.

All arguments use exact finite sums, finite bijections and symbolic algebra. The fixed cube roots are constructed inside Lean, not added as hypotheses on the actual counterexample. No complete residue period was enumerated and no numerical experiment was used.

## Lean certificates and verification

All nine original named-source checks passed with exit 0 and no diagnostics. The leaves contain 96 source declarations: 89 named declarations and seven anonymous local instances. The 59 public exports comprise 46 theorems, 12 definitions and one named instance.

| Leaf | Public exports | Final source-check log |
|---|---:|---|
| [SieveMomentFourier.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveMomentFourier.lean) | 3 | `/tmp/bsu-family-fourier-final-r2.log` |
| [ValuationTripleResonance.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/ValuationTripleResonance.lean) | 6 | `/tmp/bsu-family-triples-final-r1.log` |
| [SixthValuationPhaseRecovery.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SixthValuationPhaseRecovery.lean) | 6 | `/tmp/bsu-family-block-final-r1.log` |
| [OddPrimeSieveFamilies.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/OddPrimeSieveFamilies.lean) | 10 | `/tmp/bsu-family-atoms-final-r2.log` |
| [FiniteCoprimeMomentCalculus.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FiniteCoprimeMomentCalculus.lean) | 7 | `/tmp/bsu-family-crt-final-r1.log` |
| [PrimeFamilyTranslatedMoments.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeFamilyTranslatedMoments.lean) | 10 | `/tmp/bsu-family-moments-final-r1.log` |
| [PrimeFamilyPhaseRecovery.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeFamilyPhaseRecovery.lean) | 7 | `/tmp/bsu-family-phase-final-r1.log` |
| [ThreePrimeMomentCollision.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/ThreePrimeMomentCollision.lean) | 2 | `/tmp/bsu-family-collision-calculus-final-r1.log` |
| [ThreePrimeScalarPhaseCollision.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/ThreePrimeScalarPhaseCollision.lean) | 8 | `/tmp/bsu-family-collision-final-r3.log` |

`/tmp/bsu_family_public_audit.lean` checked every public signature and axiom closure, printed all 12 new public definitions plus the named instance and eight underlying actual-object definitions, and checked 150 toolchain-specific API probes. Final audit: `/tmp/bsu-family-public-audit-r2.log`, exit 0, no errors or warnings. Every closure uses only `propext`, `Classical.choice`, `Quot.sound`. All 21 printed bodies and every signature were reviewed; no hidden nonvanishing premise, assumed pair-product observation, or proxy response replaces the literal sieve. The eight underlying bodies are `translatedMoment`, `translationMoment`, `residueRow`, `sieveSeq`, `selbergMultiplesCoord`, `AffineSieve.affineMoment`, `AffineSieve.coordinate` and `AffineSieve.residueSignal`.

Checks used `lake --old env lean -j 1` on the absolute original sources with `-R /Users/michael/Documents/code/hgt/formal` in the previously verified `/tmp/bsu-two-lag-workspace`. The Lean 4.32.2 toolchain and source link match the project. All 18 new `.olean`/`.ilean` artifacts were copied back and byte-verified. All nine umbrella imports occur exactly once. Serena ignores these Lean paths; direct edits were used. No full or umbrella build ran.

Scoped lexical discovery returned exactly all 89 named declarations and all 59 public exports, with no pagination gap. Evidence: `/tmp/bsu-family-discovery-<Leaf>.json` and `/tmp/bsu-family-discovery-validation.json`. The final generated-index refresh passed (`/tmp/bsu-family-index-r2.log`, exit 0).

The authoritative plain `scripts/formal_tools.py lint` was run. After concurrent BVI wiring changed, indexes were refreshed and `scripts/formal_tools.py lint --check-generated` was run on the changed tree. Final lint exited 1 (`/tmp/bsu-family-lint-r2.log`) with one unrelated reachability error: `GaloisForLFunctions.BezoutValuationIncidence.ShiftedExponentAsymptoticDensityAndActiveMartingaleRate` is not imported by its theorem-area umbrella. There are 381 size warnings outside this package, no owned findings, no proof-debt findings and no generated-file errors. The repository gate has **not passed**. This package did not modify the unrelated BVI module or its umbrella. Five earlier unrelated BVI missing imports were fixed concurrently; the final remaining error is recorded rather than treated as a successful gate.

Certificate manifest: `/tmp/bsu-family-phase-manifest.json`. Complete source/API inventory: `/tmp/bsu-family-declaration-inventory.json`. Durable session ledger: `/tmp/bsu-family-phase-session.json`. Cross-session memory: `biscale/wall15-finite-prime-sixth-recovery`. Obsolete owned prototypes and abandoned next-topic scratch are archived under `/tmp/bsu-family-phase-archive-20261018/`; final audit source, logs, discovery results, manifest and dependency workspace are retained.

## Frontier evidence and scope

The three current frontier searches `/tmp/bsu-family-frontier-r1.json`, `/tmp/bsu-family-fourier-r1.json` and `/tmp/bsu-family-block-frontier-r1.json` were reviewed across every returned candidate and source argument (20 of each per search). Returned applicable material covers the prior affine, cubic/parity and two-mode certificates. The searches report `partial=false`, older coverage snapshots, unmeasured semantic coverage and unfinished background refresh. These bounded results do not establish global absence or external novelty.

Wall 15 remains open. No arbitrary multi-block divisor-support reconstruction, stability theorem or positivity producer is claimed. This package did not edit either field README, the wall ledger or the BVI worker counter. The BiScale README and wall-ledger hashes match the initial snapshot. The BVI README changed concurrently; its initial and current hashes are recorded in the manifest, and that edit was preserved. No RH module was modified, no analytic premise or axiom was added, no heartbeat limit was raised, and no full or umbrella build ran.

## Closure

- [x] Refresh frontier and audit all of C1/C2/C3 and the stronger valuation-block survivor.
- [x] Complete dependency-closed paper proofs, including empty and zero cases.
- [x] Formalize all nine actual-object leaves and verify every original named source.
- [x] Audit every public signature, definition body and axiom closure; complete API probes.
- [x] Wire leaves, verify complete lexical discovery, regenerate indexes and run formal lint.
- [x] Record the exact scalar-observation no-go and its strongest proved positive survivor.
- [x] Update related cards, verify protected files, persist memory and archive owned scratch.

`update_plan` was unavailable; this card and `/tmp/bsu-family-phase-session.json` tracked the work. The user cleared the earlier goal and requested completion of this started package. No next-topic card or new research route was started. Repository lint status, including any unrelated failure, is reported explicitly above.
