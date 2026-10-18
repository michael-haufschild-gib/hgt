# Affine sieve correlations and arithmetic phase components

- **ID:** wall15-affine-sieve-correlation-phase-components
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); exact actual-sieve certificate and all public exports audited
- **Wall:** 15, support versus orientation. Field research only; no RH argument.
- **Statement:** Complete dilation–translation quadratic data of a finite divisor sieve recover exactly the products of Selberg coordinates at comparable divisor modes; residual signs are constant on components of the nonzero divisibility graph.

## Concrete objects and conjecture loop

For real weights `c` at cutoff `N`, use the existing actual response
`s_c(k)=∑(1≤d≤N,d∣k)c(d)` and coordinates
`Y_c(q)=∑(d≤N,q∣d)c(d)/d`. Put `P=N!` and define literal affine data

`A_c(a,b)=(1/P)∑(0≤k<P)s_c(k)s_c(a*k+b)`.

Representatives `0,…,P−1` are used in the implementation. This is a literal complete-period average; divisor periodicity makes it equal to the `1,…,P` convention.

No Fourier, positivity, arithmetic cancellation, or realization premise is added to the final theorem. Natural cutoffs, arbitrary real weights and natural affine parameters are the inputs. The zero cutoff is covered. Integer affine parameters reduce to these representatives modulo the period, but the exported theorem uses natural parameters. The protected field READMEs and wall ledger remain read-only.

**C1 [FALSIFIED; LEAN CERTIFIED]:** all affine data determine the finite weight up to a single global sign. Nonzero coordinates at incomparable modes 3 and 5 give a counterexample after flipping only one sign. The exact classification proves indistinguishability for every dilation and translation. The positive sample value 6 of one response exceeds the absolute bound 5 of the other, also excluding every translated global-sign identification.

**C2 [PROVED HERE] (positive survivor):** the unnormalized discrete Fourier transform in `b` satisfies

`DFT_b A_c(a,·)(r)=P Y_c(q)Y_c(q/gcd(q,a))`, where `q` is the additive order of `r` in `Z/PZ`.

This coefficientwise identity is the formal certificate. Fourier inversion gives the full frequency expansion; grouping frequencies of order `q` yields the usual Ramanujan notation

`A_c(a,b)=∑(1≤q≤N)Y_c(q)Y_c(q/gcd(q,a))R_q(b)`,

where `R_q(b)=∑(d∣q,d∣b)d μ(q/d)` is the real Ramanujan row. Thus equality of all affine data is equivalent to

`Y_c(q)Y_c(d)=Y_e(q)Y_e(d)` for every `1≤d∣q≤N`.

Slopes `1≤a≤N` already suffice: to select a divisor `d∣q`, use `a=q/d`. Translation data can be restricted to a complete period. This gives a finite exact measurement family, not an algorithmic or stable recovery claim.

**C3 [PROVED HERE]:** equivalent sign classification: there is a sign mask `σ(q)∈{−1,1}` with `Y_e(q)=σ(q)Y_c(q)` at every active mode and `σ(d)=σ(q)` whenever `d∣q` and both coordinates are nonzero. Equivalently, one sign per connected component of the nonzero divisibility graph. Zeros agree automatically from the ordinary covariance slice `a=1`.

## Symbolic proof plan and applicability audit

1. Prove the finite Fourier transform of the actual divisor indicator on a complete period. Its normalized coefficient at a frequency of additive order `q` is `1_(q∣d)/d`. Hence the unnormalized transform of the sieve is exactly `P Y_c(q)`; this is a concrete bridge, not an abstract spectral assumption.
2. For an arbitrary function on the finite cyclic group, Fourier transformation in translation `b` sends its affine correlation to the product of its coefficients at frequencies `r` and `−a*r`. For a real divisor sieve, opposite frequencies have the same real coefficient. Multiplication by `a` changes order from `q` to `q/gcd(q,a)`. Grouping frequencies of order `q` yields C2.
3. Fourier injectivity (or Ramanujan row orthogonality) recovers every displayed coefficient. With `a=q/d`, its partner is precisely `d`. Conversely every slope produces a divisor partner, so comparable products determine all affine data.
4. The `d=q` products give equal squares. Choose the pointwise sign relating the two real coordinates. Equality of a nonzero edge product forces equal signs at its two endpoints; zero endpoints impose no condition. This proves C3 in both directions without assuming a connected support.
5. Explicitly realize profiles supported at 3 and 5 with values `(1,1)` and `(1,−1)`, at every cutoff `N+5`. Directly checking the actual finite weights avoids an extra inverse dependency: `c(1)=−2,c(3)=3,c(5)=5` and `e(1)=0,e(3)=3,e(5)=−5`, zero elsewhere. Their comparable products agree. Their means vanish. The first response has value 6 at 0; the second has values only `0,3,−5,−2`, hence absolute value at most 5 everywhere. They are inequivalent under every translation followed by either global sign. No functional of the full affine data can recover even the absolute origin response.

All three original-source leaves completed their named Lean checks with empty diagnostic logs and fresh artifacts. The final leaf imports the existing real `sieveSeq` and `selbergMultiplesCoord` definitions; copied temporary definitions used for inexpensive syntax probes are absent from production. All 37 public signatures and axiom closures passed the independent import audit. All 11 public definition bodies and both underlying actual definitions were printed and inspected.

## Dependency-closed paper proof [PROVED HERE]

Let `χ_r(k)=exp(2πi rk/P)` and use the unnormalized transform `F(r)=∑k χ_r(−k)s(k)` on `Z/PZ`. Since every `1≤d≤N` divides `P`, the divisibility indicator is invariant under translation by `d`. Its Fourier coefficient therefore obeys `F_d(r)=χ_r(d)F_d(r)`. If `q=ord(r)` does not divide `d`, the character factor is not one, forcing zero. If `q∣d`, every contributing multiple of `d` has character value one, so the coefficient is exactly its count `P/d`. Summing with the actual weights gives `F_c(r)=P Y_c(q)`. This proves the arithmetic bridge without assuming a spectral representation. At `N=0`, the actual signal and every coordinate vanish.

For any finite cyclic source, reindex the translation sum by `j=a*k+b`. The character identity `χ_r(−b)=χ_r(a*k)χ_r(−j)` gives

`DFT_b A_c(a,·)(r)=P⁻¹ F_c(r)F_c(−a*r)`.

Multiplication by `a` changes additive order from `q` to `q/gcd(q,a)`; negation leaves order unchanged. Substitution gives C2, including singular dilations and `a=0`. Fourier inversion proves that equality of these coefficients is exactly equality of the full observations.

To recover a product indexed by `d∣q`, choose slope `a=q/d` and frequency `r=P/q`. This frequency has order `q`, its partner has order `d`, and `1≤a≤q≤N`. Thus equality on the finite slope set and one translation period yields every comparable product. Conversely every frequency with `q≤N` has a positive divisor partner, while every frequency with `q>N` has zero coordinate. Comparable products therefore imply equality for all natural slopes and translations. This proves both directions and finite completeness.

The diagonal comparisons `d=q` give `Y_c(q)²=Y_e(q)²`. Over the reals each coordinate is equal or opposite; choose either sign at a zero coordinate. For a nonzero comparable pair, cancellation of the edge product forces the same chosen sign at both endpoints. Conversely equal component signs preserve every edge product, including edges with a zero endpoint. This proves C3 with no connectedness assumption. A nonzero common multiple mode joins the relative signs of its nonzero divisor modes; zero intermediate coordinates do not supply such a connection.

For the explicit family `c_t(1)=−(1+t),c_t(3)=3,c_t(5)=5t`, divisibility by the primes 3 and 5 gives coordinates `Y(3)=1,Y(5)=t` and zero at every other mode. For `t=1,−1`, comparable products coincide because 3 and 5 are incomparable. The literal response is

`s_t(k)=−(1+t)+3·1_(3∣k)+5t·1_(5∣k)`.

Hence `s_1(0)=6`, while the four divisibility cases give `|s_(−1)(k)|≤5` at every integer. This proves C1 false, excludes translated global-sign recovery, and rules out any absolute-origin decoder. The strongest positive survivor is the exact componentwise phase classification, not a restatement of the counterexample. No numerical experiment enters any step.

## Corpus frontier and scope

- Both field READMEs read fully. Existing one-lag and two-lag classifications retain coordinate squares; the Wall 14 affine-shear package concerns operators modulo compact maps, not these finite period observations.
- Hybrid searches `sieve dilation covariance Ramanujan mixed phase recovery` in BiScaleUncertainty and `dilation translation sieve covariance mixed correlation` in BezoutValuationIncidence returned no lexical hit, plus 20 candidates and 20 source arguments each. All result inventories inspected. Coverage is a stale snapshot with semantic coverage unmeasured; no absence or external novelty claim.
- Evidence: `/tmp/bsu-affine-moment-frontier.json`, `/tmp/bvi-affine-moment-frontier.json`, `/tmp/bsu-affine-ramanujan-deep.json`, `/tmp/bsu-affine-ramanujan-lexical.json`. All four searches completed; all returned declaration/candidate/source-argument inventories and the one deep ingredient set were inspected. The broad lexical Ramanujan page has 392 possible hits and is not exhaustive. The deep candidates supply generic Fourier/period ingredients, not this classification. No external novelty claim.
- Preserve concurrent BVI prefix, integral-lattice, prime-tail and dilated-cell work. Owned write scope: this card, new BiScaleUncertainty leaves, their umbrella imports, generated index, and specific memory. No subagents, numerical experiments, hgtl7, full/umbrella builds, heartbeat increases, commits or external messages.

## Persistent plan

1. [complete] Exact arithmetic Fourier bridge and dependency-closed paper proof; bounded corpus audit with coverage limitations stated.
2. [complete] All three final original-source leaves checked without diagnostics, including the actual real-object bridge and explicit witness bounds. One owned foreground Lean process at a time; installed APIs verified in `/tmp`.
3. [complete] All public signatures/definitions/axiom closures audited, imports wired uniquely, all scoped declarations discovered, final lint limitations recorded, protected hashes checked, scratch archived and memory written as `biscale/wall15-affine-sieve-phase-components`.

`update_plan` is unavailable; this card is the durable tracker.

## Gates

- [x] 0 → 1: concrete state, wall, candidate mechanism and bounded corpus audit.
- [x] 1 → 2: complete paper proof with no open dependency.
- [x] 2 → 3: exact Lean certificate and public audit; direct named leaves checked, no umbrella build.
- [ ] 3 → 4: publication audit.

## No-go closure

C1 is retired in [its failed-route card](../5-failed/wall15-global-sign-recovery-from-affine-moments.md). Its strongest positive survivor is C2/C3: the complete comparable-product and sign-component classification, together with a finite complete observation family. Their dependency-closed paper proofs and exact Lean certificates are complete. Wall 15 remains open: neither stable reconstruction nor a general mechanism resolving the remaining components is proved.

## Exact Lean certificate and verification

All exports below are in `GaloisForLFunctions.BiScaleUncertainty.AffineSieve`.

- [AffineFourierCorrelation.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/AffineFourierCorrelation.lean): 6 public exports, including `dft_correlation` and `dft_divisorIndicator`.
- [DivisorSieveAffineSpectrum.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/DivisorSieveAffineSpectrum.lean): 17 public exports; exact frequency coefficients, finite completeness, sign classification and explicit 3/5 coordinates.
- [AffineSievePhaseRecovery.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/AffineSievePhaseRecovery.lean): 14 public exports on the existing real objects, notably `dft_affineMoment`, `affineMoment_eq_iff_comparable`, `affineMoment_finite_complete`, `affineMoment_eq_iff_signComponents`, `exists_same_affine_data_distinct_absolute_origin` and `no_absolute_origin_decoder`.

The 37 exports comprise 26 theorems and 11 definitions. Each has a successful `#check` and `#print axioms` in `/tmp/bsu_affine_public_audit.lean`; the audit exited 0 with no warnings. Every closure uses only `propext`, `Classical.choice`, `Quot.sound`. No new axioms or analytic hypotheses occur. The abstract cyclic lemma requires `NeZero P`; the sieve statements derive it from `N.factorial_ne_zero`, with no positive-cutoff premise. The main theorem covers `N=0`, zero coordinates and zero slopes.

Final named-source logs: `/tmp/bsu-affine-fourier-core-r3.log` and `/tmp/bsu-affine-spectrum-core-r1.log` (both observed exit 0), `/tmp/bsu-affine-main-r1.log` (empty; fresh `.olean` and `.ilean` emitted; terminal tool output was drained during compaction, so its exit code was not separately retained). The independently imported main artifact passed the complete audit, `/tmp/bsu-affine-public-audit-r1.log`, observed exit 0. Checks used `lake --old env lean -j 1`; the main and audit used the prior verified isolated dependency workspace `/tmp/bsu-two-lag-workspace`, and the main compiled the original source with `--root=/Users/michael/Documents/code/hgt/formal`. Only owned artifacts were copied back, with byte hashes checked. No final source changed after its check.

All three imports occur exactly once in the BiScaleUncertainty umbrella. Index refresh passed. Scoped lexical discovery inspected all 52 declarations, including all 37 public exports and the second spectrum page; namespace-only lexical misses were resolved by module-name queries. Evidence, exact source/artifact hashes and every axiom closure are in `/tmp/bsu-affine-phase-manifest.json`. Initial lint found four unrelated unwired modules and two generated files made stale during concurrent work; generated files were refreshed for a final lint snapshot.

Final `scripts/formal_tools.py lint --check-generated` exited 1 (`/tmp/bsu-affine-lint-r2.log`): no owned-source or proof-debt diagnostics, no stale generated files, 381 existing large-file warnings, and four unrelated unreachable modules: `RHTower.JointAncestrySquareShellFinitePowerCriterion`, `BiScaleUncertainty.EulerPoissonChiralDriftAndPrimeShiftRigidity`, `BezoutValuationIncidence.GcdOrbitProjectionAndExactTranslationPeriods`, `BezoutValuationIncidence.SawtoothBezoutSuccessorGradientAndRouteFZZPBridge`. These concurrent modules were not modified or wired by this task. This is a complete local certificate, not a claim that repository-wide lint is green.

Three owned prototype `.lean` files were moved without overwrite to `/tmp/bsu-affine-phase-archive-20261018/`; final logs, audit source, manifests and dependency workspace are retained. All owned Lean/search/index/lint processes are terminal.

This task made no writes to either field README or the wall ledger. BiScaleUncertainty README and wall-ledger hashes match the initial snapshot. The BVI README hash changed during concurrent work (`93dd937e…` to `fca0e255…`); it was left untouched, and both full hashes are preserved in the manifest.

The follow-up [cubic odd-mode recovery and parity obstruction](wall15-cubic-odd-mode-recovery-and-parity-obstruction.md) was subsequently formalized in its own 32-export package. Its signed odd-mode recovery and all-odd obstruction are separate from the 37-export certificate on this card.

## Log

- 2026-10-18: previous goal turn classified as Progress: all 24 exports of the two-lag cone package audited and card promoted. Selected Wall 15 and opened the affine-correlation phase audit.
- 2026-10-18: exact finite Fourier/divisor indicator leaf passed direct checking (`/tmp/bsu-affine-fourier-core-r3.log`, exit 0, no warnings). The complete spectrum, finite-data completeness, sign-component classification and explicit 3/5 profile leaf passed (`/tmp/bsu-affine-spectrum-core-r1.log`, exit 0, no warnings). Actual existing real-object bridge remains to be certified.
- 2026-10-18: actual bridge and witness source emitted clean final artifacts. All 37 public signatures/axiom closures and 13 definition bodies audited through the imported main artifact, exit 0. C1 has its exact positive survivor formalized; promoted to stage 3. Turn outcome: **Progress**, Wall 15 open, research goal active.
