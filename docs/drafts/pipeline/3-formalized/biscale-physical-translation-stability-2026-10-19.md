# Uniform physical-translation stability from fifth and sixth sieve arrays

- **ID:** biscale-physical-translation-stability-2026-10-19
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); accepted native stability package 5
- **Source:** [100-contribution programme](../1-in-progress/biscale-100-contribution-programme-2026-10-18.md); [existing zero-support obstruction](../1-in-progress/biscale-mixed-stability-strata-1810.md); [existing BVI stability proposal](../1-in-progress/bvi-mixed-valuation-moment-stability-audit-2026-10-18.md).
- **Statement:** Fifth and sixth translated arrays control actual sieve signals modulo one physical translation with a uniform sixth-root modulus, across all vanishing coordinates and mixed two-adic support.

## Goal and prior ownership

The amplitude-threshold mechanism and the need for an ambient translation quotient were already proposed in the linked cards. They are prior ideas and earn no new credit. Fixed-valuation stability, prime-family noise estimates and their sharpness were already formalized. The advance here is the complete uniform theorem for every real divisor-sieve profile, using only fifth and sixth arrays, with an explicit signal bound and an optimal exponent in the actual translation metric. The predecessor mathematics and status were preserved; one incoming link was repaired after moving this card.

For any natural cutoff N, let `f=sieveSeq N c`, `g=sieveSeq N e`, with completely arbitrary real divisor weights c,e. Let `M_m(c;h)` be the existing normalized translated moment. Put `T_N=∑_{q=1}^N φ(q)`. The exact theorem is: for `0≤δ≤1`, if

`|M_m(c;h)−M_m(e;h)|≤δ^6` for m=5,6 and every lag vector h,

then there is one natural shift t such that

`|g(n)−f(n+t)|≤3*T_N*δ` for every natural n.

Equivalently, raw error ε≤1 permits a uniform `3*T_N*ε^(1/6)` bound. No upper amplitude bound, support gap, fixed nonzero stratum, affine data or quadratic/cubic observations are assumed. The comparison uses literal translated signals; the translated full signal may leave the order-constant coordinate family. For each fixed N≥10, no uniform estimate with exponent α>1/6 can hold near zero. Constants in N are not claimed optimal.

## Gates

- [x] Existing obstruction, threshold proposal, fixed-block stability and exact recovery audited before new code.
- [x] Complete the scoped corpus inventory and bounded primary-source comparison of the stronger physical-translation conclusion.
- [x] Re-audit the dependency-closed paper argument below, including normalizations and zero cases.
- [x] Formalize the exact surviving theorem; named original-source checks, full public axiom audit, wiring and lint evidence.
- [x] Decide substantive contribution separately from proof correctness. Accepted as one package; programme is 5/100.

## Paper argument

Write `a_q=Y_N(c,q)`, `b_q=Y_N(e,q)` for admitted q. The following proof uses the existing Fourier identity, actual Ramanujan inverse and canonical translation. Their general mechanisms are prior tools.

**Raw arrays control spectral products.** The m-dimensional moment Fourier transform at a resonant frequency tuple is `P^m∏_i a_(ord r_i)`, where P=N!. Dividing the transform difference by P^m averages P^m terms, each a unit-modulus character times a raw array difference. Thus every resonant product difference has absolute value at most δ^6. This normalization introduces no P-dependent loss.

The existing exact-order frequency constructions give four families of inequalities:

1. `|a_q^6−b_q^6|≤δ^6` for every admitted q, by the diagonal sixth readout.
2. `|a_q^5−b_q^5|≤δ^6` for every odd admitted q. At a frequency r of order q, the tuple `(r,r,−2r,r,−r)` is resonant and every entry has order q.
3. `|(a_q*a_r)^3−(b_q*b_r)^3|≤δ^6` when q,r have equal two-adic valuation, by the existing valuation-six tuple.
4. `|a_q^3*a_r^2−b_q^3*b_r^2|≤δ^6` when `v₂(q)<v₂(r)`, by the existing mixed quintic tuple. Both orders are admitted at the same original cutoff; the old construction's auxiliary cutoff is rewritten to N as in `lower_coordinate_of_fifth`.

These are measured polynomial readouts, not assumed abstract phase information. For x,y≥0, `|x−y|^6≤|x^6−y^6|`, since expanding `(y+(x−y))^6` when x≥y gives nonnegative remaining terms. Consequently

`||a_q|−|b_q||≤δ` for every q.

**Select significant coordinates.** First suppose 0<δ≤1. Let `S={q∈[1,N]:|a_q|>δ}`. For q∈S, `|b_q|>0`, so both signs are defined. Write `ρ_q=sign(b_q)/sign(a_q)∈{−1,1}`. If S is nonempty, choose r∈S with greatest two-adic valuation K.

For q∈S with `v₂(q)<K`, a negative ρ_q makes the two fifth-order products in item 4 have opposite signs. Their difference then has magnitude at least `|a_q|^3*|a_r|^2>δ^5≥δ^6`, contradiction. Hence every significant coordinate below K keeps its sign.

For q∈S with `v₂(q)=K`, if `ρ_q≠ρ_r`, the two sixth-order products in item 3 have opposite signs. Their difference has magnitude at least `|a_q*a_r|^3>δ^6`, contradiction. Thus the significant coordinates at K have one common relative sign. If K=0, item 2 forbids a negative sign individually, because `|a_q|^5>δ^5≥δ^6`.

**Realize one actual shift.** Truncate the source coordinate profile to S, and realize it by the existing Ramanujan inverse as weights c*, with signal `f*=sieveSeq N c*`. If S is empty, set c*=w=0 and take t=0. Otherwise its greatest active valuation is K. If the significant signs all agree, take t=0 and w=c*. In the remaining case K>0, take the already proved canonical shift of c*, and let w be its companion weights. Set `h=sieveSeq N w`. The coordinates of w flip exactly valuation K and keep lower valuations fixed; `h(n)=f*(n+t)` for every n. In every case the coordinates of w are zero outside S and have the signs of b on S, with magnitudes |a_q| there. Therefore

`|b_q−Y_N(w,q)|≤δ` on S, and `|b_q−Y_N(w,q)|=|b_q|≤2δ` outside S.

The discarded coordinates of f−f* have magnitude at most δ. No claim that translating the discarded part stays inside the coordinate family is needed: its uniform signal bound holds at every natural argument, including n+t.

**Equivalent proof using the existing exact receiver.** Set `a*_q=a_q` on S and zero otherwise, and `b*_q=sign(b_q)*|a_q|` on S and zero otherwise. Realize both by the proved inverse. For each resonant tuple of degree m=5 or 6, a coordinate outside S makes both truncated products zero. If every coordinate belongs to S, its source product A satisfies `|A|>δ^m≥δ^6`. Raw noise gives `|A−B|≤δ^6`, so A and the original competitor product B have the same sign. The rounded competitor product has that sign and magnitude |A|. Thus every resonant product agrees exactly. Existing spectral equivalence and `coefficients_eq_or_companion_of_moments` supply the actual translation of the truncated signal. This also works at δ=0, with every surviving product nonzero. This shorter proof reuses mixed-valuation recovery instead of re-proving its sign classification; generic threshold rounding earns no separate contribution credit.

**Convert to literal signal error.** The exact Ramanujan expansion is

`sieveSeq N c(n)=∑_{q=1}^N Y_N(c,q)*c_q(n)`, with `|c_q(n)|≤φ(q)`.

The first identity follows either from the existing inverse or from `d*1_(d|n)=∑_{q|d}c_q(n)` and finite summation. The second follows from the definition as a sum of φ(q) unit complex characters. Hence uniformly bounded coordinate error η gives signal error at most T_N η. Apply this to g−h and f−f*, then translate the second bound:

`|g(n)−f(n+t)|≤2*T_N*δ+T_N*δ=3*T_N*δ`.

If δ=0, the existing exact fifth/sixth recovery theorem and canonical-companion translation give equality for one actual shift. This closes the empty-support and exact-data boundary too. All input weights may have arbitrary tails beyond N; these are invisible to both the literal signal and the observations.

**Optimal exponent in the physical translation quotient.** Fix N≥10 and use the existing order-six/order-ten pair `f=u_6+u_10`, `g=u_6−u_10`. Both are actual sieve signals with absolute value at most six. Every fifth translated moment vanishes, and their zero-lag sixth moments differ by 960. Scaling both weights by λ>0 gives signals bounded by 6λ, with fifth arrays still identical and every sixth array difference at most `2*6^6*λ^6`.

For any natural shift t, translation preserves the sixth moment. The elementary inequality `|x^6−y^6|≤6*max(|x|,|y|)^5*|x−y|` therefore implies

`960*λ^6≤6*(6λ)^5*sup_n |λg(n)−λf(n+t)|`.

Thus every physical translation has uniform error at least `960/(6*6^5)*λ`. A putative uniform exponent α>1/6 would instead bound that error by `C*(2*6^6)^α*λ^(6α)` for arbitrarily small λ, contradiction. This lower bound applies to all actual translations, including ones that leave the order-constant family; a coefficient common-sign metric alone would not prove it.

The existing one-mode degeneration gives a shorter actual-metric certificate for the same conclusion. At cutoff `N+10`, take `c=evenPairReal (δ/2) 0` and `e=evenPairReal 0 0`. The proved literal response is a parity sign times `(δ/2)*residueRow 3`; its absolute value lies between δ/2 and δ at every integer. All fifth arrays vanish, and averaging products bounds every sixth-array error by δ⁶. Every translate remains at distance at least δ/2 from the zero signal, pointwise. Taking δ arbitrarily small proves the same exponent barrier near zero. This is reuse of the prior one-mode sharpness mechanism, not a new contribution on its own.

## Corpus and primary-source audit

Initial scoped deep request `/tmp/bsu-100-mixed-stability-frontier.json` completed with 74,297 inventoried files. All returned candidate/source statement entries, prose/passage inventories and generated proposals were inspected. It recovers exact valuation recovery and prime-family raw stability. Some indexed signatures stop at `let`, so those are not complete applicability reviews. The proposed transfer from the new arithmetic-edge rank theorem to mixed-support stability is invalid and rejected.

The whole-corpus query `mixed valuation stability`, excluding new ArithmeticEdge modules, completed with 74,299 inventoried files (`/tmp/bsu-100-mixed-stability-global-search.json`). All 20 candidate and 20 source statement entries and ten prose entries were inspected. Most declaration results concerned nonarchimedean valuations rather than observation stability; the generated valuation-order ingredient chain is irrelevant. The useful prose hits recover precisely the two existing proposals and prior fixed-block stability. This weak declaration retrieval cannot establish absence of an existing quantitative theorem. Semantic coverage is unmeasured and compiler freshness incomplete.

The coordinate-to-signal search `/tmp/bsu-100-coordinate-signal-norm-search.json` and BVI-scoped stability search `/tmp/bsu-100-bvi-stability-prior-search.json` completed with 74,299 and 74,300 files. All returned candidate/source statement entries, prose/passage inventories and proposals were reviewed. Existing inverse, prefix discrepancy, successor contraction, concentration, predictor and lag-recovery results are prior tools with different measurement models. The proposed damped/prefix predictor chains do not prove the required uniform literal signal bound and are rejected.

After a zero-hit lexical `momentDFT norm` query, `/tmp/bsu-100-fourier-noise-deep-search.json` rephrased the mechanism as translated-moment Fourier coefficient perturbation. It completed with 74,301 files. All 20 candidate and 20 source statement entries and ten prose/passage inventories were inspected. It recovers exact Fourier equivalence, exact fifth/sixth recovery and prime-family raw noise estimates; it supplies no generic Fourier perturbation bound among its returned statements. Its generated exact-shift/quartic chain is not a noise proof. Indexed statements and ranked retrieval are not exhaustive applicability or absence certificates.

[Bandeira et al., Lemma 6.8](https://arxiv.org/html/1712.10163v3) proves qualitative continuity of recovery toward a matching orbit fibre on compact parameter sets; its local inverse discussion covers nonsingular situations. These mechanisms and statistical moment-order arguments are prior work. The inspected lemma does not give the explicit global sixth-root estimate for arbitrary real divisor profiles here.

[Towards a bilipschitz invariant theory, Theorem 21, Example 22 and Lemma 24](https://arxiv.org/html/2305.17241v3) explains failure of lower Lipschitz bounds for smooth invariants at stabilizers and discusses bispectrum inversion on nonvanishing Fourier strata. Those obstructions and local recovery principles are not new claims here; the paper studies broader invariant embeddings, not this particular fifth/sixth arithmetic observation map.

[Dou–Fan–Zhou, Lemma 4.9](https://arxiv.org/pdf/2205.01847) bounds circular Fourier-phase errors by bispectral phase errors modulo rotation. Its raw statistical estimates use a nonvanishing bandlimited amplitude class (`r_k` comparable to `k^(-β)`). Phase-array noise under those assumptions is a different input from unnormalized raw fifth/sixth arrays across arbitrary vanishing divisor coordinates.

This bounded comparison supports the specific native theorem, without a claim of exhaustive literature priority. The accepted unit is sharp global physical-translation stability for mixed arithmetic supports; generic Fourier averaging, rounding, inverse transforms and existing exact recovery are excluded from new credit.

Further lexical requests are inventoried separately: `/tmp/bsu-100-coordinate-outside-search.json` returned 13 entries, all inspected, and located the already public BVI `selbergMultiplesCoord_eq_zero_of_notMem`. Its actual source was checked and will be reused, avoiding another cutoff-zero helper. `/tmp/bsu-100-parity-sharpness-search.json` returned four actual-response results, all inspected; the existing `sieveSeq_evenPairReal` and `evenPair_odd_zero` supply the simpler sharpness family above. Lexical `translatedMoment abs` returned no entries. The rephrased deep request `/tmp/bsu-100-moment-amplitude-deep-search.json` completed with 74,307 files; all 20 candidate and 20 source entries, ten prose entries and its generated proposal were inspected. It recovers exact translated moments, antiperiodicity and unrelated continuum moment bounds. The proposed shift/companion chain does not establish an amplitude bound. Semantic coverage remains unmeasured and compiler refresh incomplete. Lexical responses do not report those deep-search coverage fields.

That search also returned [the existing common-relator card](../1-in-progress/biscale-common-relator-structure-1810.md), which was read fully. Its character classification is explicitly classical, and it already identifies near-zero ambient translation stability as an open quantitative extension. This theorem addresses the arithmetic stability component only; it does not complete that card's joint arithmetic/continuum energy-transfer objective.

**Scope limits.** The theorem uses complete fifth and sixth lag arrays, so it provides no new efficient raw-measurement protocol. It does not claim an optimal cutoff constant, a nondegenerate-stratum rate, or an arithmetic-to-continuum energy transfer. These separate objectives remain open.

## Formal certificate and contribution decision

The formal upper bound includes N=0: both literal signals vanish by the empty divisor sum. This boundary adds no separate contribution. `exists_physical_translate_error` proves the δ-form; `exists_physical_translate_holder` proves the explicit ε^(1/6) form. Both quantify arbitrary real input weights and one actual natural shift valid at every natural argument. `physical_translation_sharp_witness` supplies the actual one-mode family. `no_improved_physical_exponent_near_zero` excludes every α>1/6 in every positive-radius uniform neighborhood of the zero signal, at every cutoff `N+10`; its global corollary is also formalized.

| Owned leaf | Public declarations | Role |
|---|---:|---|
| `SieveThresholdRounding.lean` | 5 | Scalar threshold errors and exactification of noisy products |
| `SieveRawMomentPerturbation.lean` | 3 | Raw Fourier error and sixth-root coordinate magnitudes |
| `SieveCoordinateSupNorm.lean` | 4 | Exact literal Ramanujan expansion and uniform signal bounds |
| `SievePhysicalTranslationStability.lean` | 7 | Actual inverse weights, exact rounded arrays and physical recovery |
| `SievePhysicalTranslationSharpness.lean` | 3 | Actual-translation witnesses and the local exponent barrier |

All five leaves passed their original `lake --old env lean <module> -o <olean>` checks without diagnostics. Final logs are `/tmp/bsu-100-{threshold-rounding,raw-moment-perturbation,coordinate-sup-norm,physical-translation-stability,physical-translation-sharpness}-named.log`. The imported audit `/tmp/bsu_100_physical_stability_audit.lean` checks all 22 explicit public declarations and prints the actual signal, moment, inverse and rounding definitions. Its complete output was inspected; every axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`. The source inventory exactly matches the audit inventory, source hashes match the checked files, and all five imports occur exactly once in the BSU umbrella. The manifest is `/tmp/bsu-100-physical-stability-certificate.json`.

`scripts/formal_tools.py index` passed. Shared `scripts/formal_tools.py lint --check-generated` exits 1 with 381 existing size warnings and three unrelated umbrella reachability errors: BVI `CofinalMobiusSourceAlphabet`, THIM `FermiHomogeneousEnergyAndPronicComparison`, and THIM `FermiPrimeExponentGramBounds`. There is no owned wiring or proof-debt finding. The exact output is `/tmp/bsu-100-physical-stability-lint.log`; those concurrent modules and umbrellas were left unchanged. Shared lint is not reported as passing.

**Accepted unit: one native theorem package.** The advance is the explicit uniform physical-translation bound across all arithmetic support changes, with no amplitude bound or nonvanishing hypothesis. It completes the previously open mixed-support stability question in its correct ambient metric. Generic Fourier averaging, threshold rounding, classical character structure, existing exact fifth/sixth recovery, inverse transforms and prior one-mode sharpness are supporting mechanisms, not additional contributions. The bounded corpus/primary-source comparison above does not claim exhaustive literature priority. Programme count is **5/100**, not 22/100.

## No-go closure

The completed theorem supplies a positive replacement for the previously identified discontinuity of the support-dependent coefficient quotient. That negative example remains valid. The survivor is the uniform bound in the actual translation metric; its dependency-closed paper proof and exact Lean statement are complete. No new negative result is counted.

## Log

- 2026-10-19 — Created after package 4 and explicit prior-work searches. The prior threshold idea is acknowledged. A proposed complete proof uses only fifth/sixth data, a 2δ significance threshold and the actual canonical translation of the truncated source. No new Lean file has been created. Count remains 4/100.
- 2026-10-19 — Paper audit improves the threshold to δ and the bound to `3*T_N*δ`. A rounded exact-data pair reuses the existing fifth/sixth receiver, including δ=0. Corpus and three primary-source comparisons recorded; no new contribution counted.
- 2026-10-19 — Initial scratch checks exposed only API/elaboration issues so far; no production Lean file is present yet. Five scratch leaves now draft Fourier noise, pointwise Ramanujan bounds, threshold rounding, actual translation recovery and actual-metric sharpness. The first corrected combined check is running. No correctness claim or count change before it passes and the original sources receive their own checks.
- 2026-10-19 — `SieveThresholdRounding`, `SieveRawMomentPerturbation` and `SieveCoordinateSupNorm` pass their original named-source/export checks without diagnostics. The capstone's first named check identified the missing explicit import for the already found BVI cutoff-zero theorem; that import is added and the corrected named check is running. Sharpness now has a drafted positive-radius neighborhood statement as well. Paper proof and bounded prior comparison are closed; full formal audit and substantive-count decision remain open. Count is 4/100.
- 2026-10-19 — All five original source checks and the full 22-declaration imported audit pass. All leaves are wired. Index passes; the three unrelated shared lint failures are recorded above. Accepted the complete native stability law as package 5, excluding all supporting mechanisms and prior ideas from separate credit.
- 2026-10-19 — Source hashes and all five empty diagnostic logs were revalidated against the certificate. Scoped whitespace checks pass; the protected README retains SHA-256 `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275`. Five verified extracted drafts and the obsolete combined draft were removed. Audit sources, logs and the manifest remain. The concurrent BVI card's new incoming link was redirected to this formalized card without changing its historical audit text.
