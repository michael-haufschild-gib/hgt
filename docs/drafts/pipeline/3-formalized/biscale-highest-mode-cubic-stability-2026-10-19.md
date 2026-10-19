# Cubic stability when the highest admitted dyadic mode stays nonzero

- **ID:** biscale-highest-mode-cubic-stability-2026-10-19
- **Stage:** 3-formalized
- **Type:** NEW NATIVE RESULT; accepted package 6 of the current programme
- **Source:** [100-contribution programme](../1-in-progress/biscale-100-contribution-programme-2026-10-18.md); [global physical stability](biscale-physical-translation-stability-2026-10-19.md)
- **Statement:** At every cutoff N≥2, put P=2^floor(log₂ N). If both actual Selberg coordinates at P have magnitude at least one, complete fifth/sixth raw errors at most ε, 0≤ε≤1, imply one actual translation with uniform signal error at most `2*Σ_(1≤q≤N) φ(q)*ε^(1/3)`. Every other coordinate may vanish or have arbitrary magnitude. The exponent 1/3 is optimal already at N=3 in every positive-radius neighborhood of the pure parity source. The equivalent δ³-error form is also formalized.

## Goal and prior-work boundary

The previous theorem gives exponent 1/6 across all vanishing supports. This package identifies one specific nonvanishing coordinate that improves the rate for the entire mixed-valuation profile, without prescribing its remaining support. No new credit attaches to real cube inequalities, the existing quintic resonance, fixed-valuation Gram stability, or the known exact translation classification.

`MixedValuationQuintic.lean` and `SieveValuationPhaseRecovery.lean` have been read in full. They already give the exact product `a_d³ a_u²` whenever the two-adic depth of d is below that of u. `SixthReadoutStability.lean` already gives a nonzero-mass cube-root estimate within a single valuation block. The accepted advance is the stated uniform mixed-support stratum theorem and its actual-translation sharpness; the final audit and counting boundary are below.

## Checked paper proof

1. P is the unique admitted order of maximal two-adic depth. Indeed, `P≤N<2P`; an admitted order with at least that depth is divisible by P and hence equals P. Its coordinate is therefore the whole highest block.
2. Normalized Fourier averaging has norm one. Existing `resonant_product_error` and `coordinate_sixth_error`, together with the exact quintic frequencies, give sixth-power errors and errors in `a_q³ a_P²` bounded by δ³ for every q≠P.
3. Scalar estimate: if `|X|,|Y|≥1`, all three errors `|X⁶−Y⁶|`, `|x⁶−y⁶|`, `|x³X²−y³Y²|` are at most δ³, then `|x−y|≤2δ`. For opposite signs, the last error bounds `|x|³+|y|³`. For equal signs with `max(|x|,|y|)≥1`, sixth powers control the magnitude difference by δ³. In the remaining case both magnitudes are at most one; the anchor sixth powers imply `|X²−Y²|≤δ³`, so `|x³−y³|≤2δ³`, and `|x−y|³≤4|x³−y³|` finishes. All endpoints, including δ=0, are included.
4. Align only the sign at P, using either the identity or the existing actual canonical half-period. All lower coordinates are unchanged by this translation. The top magnitude error is at most δ³. Existing pointwise Ramanujan expansion and the totient kernel bound yield the stated actual-signal estimate.
5. Set δ=ε^(1/3) for ε∈[0,1]. Then δ∈[0,1] and δ³=ε, giving the explicit real-power conclusion, including ε=0. The formal scope uses unit anchor threshold.

## Sharpness on actual signals

At N=3 use actual weights `c_t(1)=−1−t`, `c_t(2)=2`, `c_t(3)=3t`, zero elsewhere. Their coordinates are `(a₁,a₂,a₃)=(0,1,t)` and their literal response is `R₂(n)+t R₃(n)`, where `R_p(n)=p*1_(p∣n)−1`.

Compare t and −t, with 0<t≤1. Translation by three changes the parity row and preserves the ternary row, so the negative source is minus the translated positive source; every sixth array agrees. Expand a fifth product by its ternary-factor subset S. CRT factors the period-six average. If |S| is even, the odd number of parity factors makes its average zero. If |S|=1, the ternary row has zero mean. The remaining ten subsets of size three contribute at most `10*2³*t³`, and the size-five subset contributes at most `2⁵*t⁵`. Thus each fifth moment has absolute value at most `112*t³`; the error between t and −t is at most `224*t³`, uniformly in every lag vector.

For a natural translation h, choose n=4 if h≡1 mod 3 and n=2 otherwise. Both n and n+h have nonzero ternary residue, and n is even. Therefore the difference between the negative source at n and the translated positive source is `1−R₂(n+h)+2t≥2t`. Both sources lie within `2t` of the parity source. A bound with exponent α>1/3 would force `2t≤C*(224*t³)^α` for arbitrarily small positive t. All-lag cancellation, coordinate identities, translation separation and this exponent obstruction are Lean-certified. The final statement uses `topOrder 3` explicitly and proves that it equals 2. Sharpness concerns pairs in each neighborhood, not only distance from its center.

## Search evidence

`/tmp/bsu-100-top-anchor-stability-search.json` completed with 74,317 inventoried files. All 20 candidate and 20 source statements, prose/passage inventories and generated proposals were inspected. It returns the exact quintic receiver, fixed-block Gram stability and the newly completed global threshold theorem. Its generated chain does not prove the proposed improved exponent. Semantic completeness is unmeasured and compiler refresh incomplete; this is not an absence certificate.

`/tmp/bsu-100-top-admitted-mode-search.json` returned a 74,318-file snapshot with partial results: `filter_and_judge` failed on malformed/incomplete local-model JSON. All 20 candidate and 20 source statements and all prose/passage inventories were reviewed; no proposal was generated. The results were mostly unrelated cutoff bounds. Direct inspection of the installed `Mathlib/Data/Nat/Log.lean` identifies the power/log bounds needed to prove the highest-mode fact.

The whole-corpus `/tmp/bsu-100-top-anchor-global-search.json` and sharpness `/tmp/bsu-100-top-anchor-sharpness-search.json` searches completed with 74,319 and 74,320 inventoried files. All 20 candidate and 20 source statements, prose/passage inventories and generated proposals in each were reviewed. The candidate card already appears as a self-hit; it is not independent prior evidence. Existing odd-prime parity families, quartic blindness and exact quintic recovery are reused prior work. No retrieved statement verified the proposed highest-mode criterion or its local exponent, but semantic coverage remains unmeasured and compiler refresh incomplete. Missing ranked hits are not an absence certificate.

The targeted `/tmp/bsu-100-top-anchor-fifth-cancellation-search.json` completed with 74,322 inventoried files, `partial=false`, semantic coverage unmeasured and compiler refresh incomplete. All 20 candidate and 20 source statements and all prose/passage inventories were reviewed. Its generated proposal incorrectly treats fifth/sixth equality as literal coefficient identity, discarding the companion alternative in the cited theorem; it is rejected. Existing `residue_pair_quartic_flip` and prime-family cancellation use the same finite multilinear expansion method, which earns no new credit. The new fifth bound is a supporting estimate for the actual mixed-depth sharpness family.

Bounded primary comparison: [Ehler–Kunis, §II.A](https://eurasip.org/Proceedings/Ext/SampTA2013/papers/p564-ehler.pdf) already gives classical magnitude-plus-anchor reconstruction. [Towards a bilipschitz invariant theory, Theorem 21](https://arxiv.org/html/2305.17241v3) supplies a general non-Lipschitz obstruction at nontrivial stabilizers; Lemma 24 addresses global polynomial bilipschitz behavior. Neither generic anchoring nor the existence of a singular inverse is new here. The candidate must supply the exact native stratum criterion, uniform rate, and actual-signal sharp exponent.

Two further primary comparisons match measurement models explicitly. [Amir–Bendory–Dym–Edidin, Definition 3.1 and Theorem 3.4](https://arxiv.org/html/2505.04190v2) study square roots of block Gram matrices under transversality assumptions on the signal prior. The present arithmetic family retains independent signs in its squared coordinates, and uses fifth/sixth correlations to remove them; the generic transversality theorem is not a substitute for that arithmetic step. [Kalra–Shukla, Theorems 3.2–3.3](https://arxiv.org/html/2512.16190v1) recover signals from linear Ramanujan-filter samples or from samples with sparse additive corruption. Those measurements retain information absent from translated moment arrays. These comparisons delimit the claim; they do not constitute exhaustive external priority verification.

An exhaustive `rg` scan of project Lean sources and pipeline/report prose for combinations of highest/dyadic modes, cubic stability and quintic anchors found the candidate's own card plus already-audited BVI/BSU work; other matches concerned unrelated objects. This complements the ranked corpus searches, rather than certifying semantic completeness.

## Gates

- [x] Finish corpus and bounded primary-literature comparison; distinguish the new assertion from generic polynomial inversion.
- [x] Close the paper proof, including every cutoff and zero-coordinate case.
- [x] Prove actual-source sharpness with all lag vectors and all natural translations.
- [x] Verify any required Mathlib names in a `/tmp` scratch file under this toolchain.
- [x] Named original-source/export checks, complete public-definition/axiom audit, wiring, index and scoped lint review. No full or umbrella build.
- [x] Accept the complete native sharp stability theorem as one contribution; count is 6/100.

## Formal certificate and contribution decision

Five leaves are wired exactly once in the BSU umbrella:

| Module | Public declarations | Purpose |
|---|---:|---|
| `SieveHighestDyadicCoordinate` | 7 | Unique maximal depth, actual companion action, noisy quintic products |
| `SieveCubicAnchorEstimate` | 2 | Scalar magnitude and anchored-cube estimates |
| `SieveHighestModeStability` | 2 | Actual translation bound in δ³ and ε^(1/3) forms |
| `SieveHighestModeSharpWitness` | 8 | Actual parity/ternary family, all-lag errors, uniform neighborhood and translation separation |
| `SieveHighestModeSharpness` | 1 | Failure of every larger exponent near parity |

All five original `lake --old env lean <module> -o <olean>` checks exited 0 with empty diagnostic logs, `/tmp/bsu-100-<Module>-named.log`. The imported audit `/tmp/bsu_100_top_anchor_audit.lean` exited 0. Its complete 252-line output `/tmp/bsu-100-top-anchor-audit.log` was inspected: all 20 public statement and axiom inventories match, every axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`, and all public definitions plus the actual observation/source definitions were printed. Source hashes, imports and whitespace match the certificate `/tmp/bsu-100-top-anchor-certificate.json`.

Index regeneration passed. Initial shared lint also detected generated files made stale during concurrent edits; regeneration removed those findings. Final `scripts/formal_tools.py lint --check-generated` exits 1 with 381 existing size warnings and exactly three unrelated umbrella reachability errors: BVI `CofinalMobiusAllMomentProfiles`, THIM `FermiHomogeneousEnergyAndPronicComparison`, and THIM `FermiPrimeExponentGramBounds`. No owned or proof-debt finding appears. Logs: `/tmp/bsu-100-top-anchor-index-final.log` and `/tmp/bsu-100-top-anchor-lint-final.log`. Those concurrent modules and umbrellas were left unchanged; shared lint is not reported as passing.

**Accepted unit:** the uniform improvement from exponent 1/6 to sharp 1/3 on the stated native arithmetic stratum, with arbitrary lower support and actual translation distance. The cutoff supplies a unique maximal dyadic coordinate, so one retained coordinate controls every lower sign through existing quintic resonances. Neither existing fixed-block stability nor generic anchor reconstruction provides this whole mixed-support conclusion. Scalar inequalities, Fourier averaging, CRT expansion, the exact quintic mechanism and the real-power limit argument are supporting or prior work and receive no separate credit. This is a bounded novelty assessment, not a claim of exhaustive literature priority or of optimal numerical constant 2.

## Log

- 2026-10-19 — Candidate recorded after corpus discovery of the exact quintic mechanism. No new Lean source yet; no completion or novelty claim.
- 2026-10-19 — Combined geometry, scalar and physical-translation scratch proof passes without diagnostics: `/tmp/bsu_100_top_anchor_combined.lean`, log `/tmp/bsu-100-top-anchor-combined-r2.log`. All cutoffs N≥2 and vanishing lower coordinates are included. Sharpness remains under verification; no source/export or axiom-audit gate is claimed from the scratch check.
- 2026-10-19 — Closed the paper exponent obstruction using the period-six family. The formal package now includes an explicit raw-error `ε^(1/3)` conclusion. Created five production leaves: `SieveHighestDyadicCoordinate`, `SieveCubicAnchorEstimate`, `SieveHighestModeStability`, `SieveHighestModeSharpWitness`, and `SieveHighestModeSharpness`; all are wired once. The combined scratch check is running; named-source checks and the axiom audit remain pending. Unit anchor threshold is the formal scope; the optional arbitrary-threshold scaling extension is not part of this package.
- 2026-10-19 — The complete 667-line combined scratch proof passes without diagnostics: `/tmp/bsu_100_top_anchor_full.lean`, log `/tmp/bsu-100-top-anchor-full-r1.log`. This includes the explicit cube-root modulus and the no-better-exponent theorem in every positive-radius neighborhood of parity. Five original-source/export checks are running sequentially. The prepared audit enumerates all 20 public declarations; no final certificate is claimed before its imported check.
- 2026-10-19 — All five named-source checks and the complete imported audit pass. Accepted the package after the bounded corpus/literature comparison. Final shared lint scope is recorded above. All five production bodies match their extracted drafts; nine owned proof drafts/combined scratch files were removed. API probes, audit source, logs, searches and certificate remain. The protected README retains SHA-256 `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275`. Count is 6/100; the research goal remains active.
