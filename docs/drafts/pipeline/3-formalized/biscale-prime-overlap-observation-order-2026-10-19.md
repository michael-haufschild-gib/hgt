# Coprime overlap and a jump in sharp observation order

- **ID:** biscale-prime-overlap-observation-order-2026-10-19
- **Stage:** 3-formalized
- **Type:** unconditional theorem package; accepted contribution 3/100
- **Parent:** [100-contribution programme](../1-in-progress/biscale-100-contribution-programme-2026-10-18.md)
- **Source:** [Field checklist, item 4](../../../reports/BiScaleUncertainty/field-todo-1810.md)
- **Statement:** For sieve spectra on the three orders 2pq, 2pr, 2qr, an active third mode lowers the sharp additional translated-moment degree from six to four.

## Theorem on actual objects

Let p,q,r be pairwise coprime odd integers greater than one. Take N=max(2pq,2pr,2qr)+n for arbitrary n≥0. Use the existing Ramanujan inverse to realize actual weights with arbitrary real coordinates a,b,c on 2pq,2pr,2qr and zero elsewhere. Labelled affine quadratic data are always supplied; the degree refers to additional translated moments through that degree. Recovery concerns actual sieve signals modulo integer translation and quantifies arbitrary competing real weights, with no support premise on those competitors.

Sharp classification, including every zero pattern:

- Three nonzero coordinates: fourth-order translated data recover one common sign; degree three is insufficient.
- Exactly two nonzero coordinates: all data through degree five retain independent signs; degree six recovers one common sign.
- At most one nonzero coordinate: affine data already give the full ambiguity modulo translation.

The contribution is the discontinuous increase in required correlation order when one realized connecting mode vanishes. Generic graph sign recovery, CRT, and renamed moment expansions do not themselves count. The exact logical criterion is `AtMostOne a ∨ (Full a ∧ 4 ≤ m) ∨ 6 ≤ m`.

## Paper mechanism

The orders form an antichain under divisibility, so affine observations give squares but no sign comparisons. All active orders have two-adic depth one, so odd translated moments vanish and the common sign is an actual translation.

A four-frequency zero-sum tuple of orders `(2pq,2pr,2qr,2qr)` gives the readout `P^4*a*b*c^2`. The two permutations produce the other pair products times a square. With all three coordinates nonzero, these fix relative signs. The exact factorial-period construction is given below and works for composite coprime blocks too.

When one coordinate vanishes, the remaining two orders are incomparable. Any nonzero fourth-order Fourier product uses each remaining mode an even number of times: a singleton order in a zero-sum quartet would divide the repeated order. Fourier inversion gives independent-sign invariance of the complete lag arrays through degree five. Existing sixth-order recovery gives the sharp upper bound. Single-coordinate flips provide actual witnesses whenever at least two coordinates remain nonzero.

The dependency-closed argument below includes exact frequency orders, the converse zero-sum obstruction, complete lower-order equality, and sharpness against all allowed data. Full lag arrays, not single scalar moments, are used. No numerical experiments.

## Prior-work audit so far

`/tmp/bsu-100-quartic-support-frontier.json` completed. All 20 candidate, 20 source, ten prose and ten source-passage inventories, the proof idea and ingredient-set inventory were inspected. It found existing `primeFamily_quartic_eq_of_sq_eq`, `primeFamily_through_five_eq_of_sq_eq`, `primeFamily_even_crt`, `independent_quartic_eq_of_sq_eq`, and the even-pair quartic sign obstruction. These are ingredients for coprime single-prime modes, not a certificate for the overlapping product modes proposed here.

The lexical quartic/sieve query returned 13 hits, all inventoried. The quartic/bridge query was fully paginated with `--per-module 0 --explore 0`: 48 unique hits across offsets 0,20,40, all inventoried; they concern other mechanisms. Files: `/tmp/bsu-100-quartic-sieve-exact.json`, `/tmp/bsu-100-quartic-bridge-all-{0,20,40}.json`. Semantic completeness remains unmeasured; no absence or novelty claim follows. Source searches found no matching triangle statement in the two native directories. `FourthMomentJumpReceiver` concerns continuum hyperbolic energy and `PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer` concerns source-graph energy; their scope differs.

Applicable CRT and product-mode realization sources and external higher-correlation literature were inspected; details follow. The separate BVI mixed-support noise-stability work remains untouched.

## Gates

- [x] Stated actual-object candidate and searched prior corpus.
- [x] Dependency-closed paper proof and bounded theorem-level novelty comparison.
- [x] Actual-object Lean statements, named-source and axiom audits, wiring and lint.
- [x] Count one substantive result beyond existing mechanisms; supporting lemmas are not separate contributions.

## Extended paper audit: coprime odd blocks

The mechanism only needs pairwise coprime odd integers p,q,r greater than one, not primality. Set P=N!, where N admits 2pq,2pr,2qr. Each of 2,p,q,r divides P. Write δ=P/2, α=P/p, β=P/q, γ=P/r in Z/PZ. Their exact orders are 2,p,q,r. Coprime-order addition gives the exact orders of

`δ+α+β, δ−α+γ, δ+β+γ, δ−2β−2γ`.

These are respectively 2pq,2pr,2qr,2qr; multiplication by −2 preserves odd order. The sum is 4δ=0. Thus the existing full moment Fourier identity gives `P^4*a*b*c^2`. Permuting p,q,r gives the other two readouts. Square data plus these three products determine a common sign when abc is nonzero. This is an actual-lag readout, not a fourth moment at one lag.

The lower bound has a stronger elementary form. For any two incomparable additive orders A,B, a zero-sum quartet supported on those orders cannot have multiplicities 1+3: multiply its sum by the repeated order B to obtain A|B, a contradiction. Therefore every surviving product is a fourth power or a product of squares. A Fourier-inversion step makes this equality of complete fourth lag arrays, not merely equality of selected readouts. The odd moments vanish because pqr is an antiperiod of every realized triangle signal. Quadratic arrays are already part of labelled affine observations. Hence a two-mode support has independent sign ambiguity through five. The existing sixth valuation-block theorem supplies its exact common-sign upper bound.

All three orders are pairwise incomparable: cancellation of common factors would force one coprime block greater than one to divide another. The existing affine comparable-product theorem therefore reduces exactly to three squares. Existing Ramanujan inversion realizes every real coefficient vector, including every zero pattern, without a new inverse. A single-coordinate sign change gives the sharp lower witnesses whenever at least two coordinates are nonzero. Such a change cannot be a translate: the existing sixth theorem distinguishes it. A common sign is the actual shift pqr. For support of size at most one, equality of squares already means a common sign.

This closes the mathematical dependency chain on paper. The stronger block-domain and the universal two-incomparable-orders obstruction are ingredients of this one package, not extra contribution counts.

The comparison class is all real sieve weights at the cutoff, not only a prescribed three-dimensional parametrization. Affine diagonal products force every competing coordinate outside the three orders to zero. Taking the three remaining coordinates and applying the existing Ramanujan inverse gives the same actual sieve signal as that arbitrary competitor. Thus the final recovery threshold can quantify arbitrary competing weights, while correctly ignoring their invisible coefficients beyond the cutoff.

Additional corpus inventories: `/tmp/bsu-100-prime-overlap-crt-search.json` (partial, text-retrieval interrupted), `/tmp/bsu-100-prime-overlap-realization-search.json` (request complete). All 20 candidate, 20 source, ten prose, ten passage and ingredient-set inventories of each were inspected. Useful hits include `frequencies_order_product`, `frequency_order`, coprime addition of element orders, and the BVI inverse. The searches include unrelated results and do not prove absence. Semantic completeness is unmeasured; background refresh is pending.

External baseline checked: [Jaming–Kolountzakis, §3.4](https://nyjm.albany.edu/j/2003/9-12.pdf) surveys the classical cyclic four-/six-deck bounds; [Grünbaum–Moore](https://journals.iucr.org/paper?buy=yes&cnor=gr0371) explicitly claims sixth-order recovery for integer-weight structures. These general bounds and Fourier reconstruction are not new claims here. The latter full text was not accessible through the checked publisher page; no comprehensive priority claim is justified. The proposed distinction is the exact native support-dependent 4→6 loss when one overlapping actual sieve mode disappears, with all affine data retained.

[Putinar, pp. 11–18, especially Theorems 3.3, 3.9, 4.4 and 4.6](https://www.smm.org.mx/boletin_anterior/v11/n1.pdf) was also read. It supplies the classical invariant-ring and tensor-Fourier framework, a general degree bound, and a rational symmetric-measure sixth-order theorem using Grünbaum–Moore. None of those mechanisms is claimed as new. It does not state the present exact support-stratum threshold with labelled affine observations. This is a theorem-level comparison to the inspected material, not an exhaustive priority assertion.

Further full inventories inspected: `/tmp/bsu-100-overlap-native-prior.json`, `/tmp/bsu-100-moment-injectivity-search.json`, `/tmp/bsu-100-quadratic-affine-bridge.json`, `/tmp/bsu-100-incomparable-quartic-prior.json`. The quadratic query was partial (text/source interruption and semantic deadline); the other requests completed but semantic completeness remained unmeasured. Own new sources appeared in the last query and were excluded as prior evidence. The existing `biscale-mixed-stability-strata-1810.md` card was read in full: its mixed valuation zero-support change concerns stability and a changing ambiguity group, whereas this family stays in one valuation class and its required observation degree changes. That separate work remains untouched.

## Lean certificates and verification

- `CoprimeOverlapQuarticReadout.lean`: named-source/export check passed, no diagnostics. Actual fourth readout and exact frequency orders.
- `CoprimeOverlapSieveFamily.lean`: named-source/export check passed, no diagnostics. Actual Ramanujan weights, incomparable orders, affine square classification, antiperiod, odd-moment vanishing, arbitrary-partner realization.
- `IncomparableSieveQuartic.lean`: named-source/export check passed, no diagnostics. Complete moment Fourier inversion and the incomparable-orders quartic obstruction.
- `CoprimeOverlapObservationOrder.lean`: named-source/export check passed, no diagnostics. `Triangle.sharp_observation_order` is the sharp classification against arbitrary competing weights. `translation_iff_common` identifies the remaining common sign with actual translation.

All four checks used `lake --old env lean -o <leaf.olean> <named original source>` from `formal`, one owned foreground Lean process at a time. Logs: `/tmp/bsu-100-overlap-readout-leaf.log`, `/tmp/bsu-100-incomparable-leaf.log`, `/tmp/bsu-100-overlap-family-leaf.log`, `/tmp/bsu-100-overlap-order-leaf.log`.

The imported audit `/tmp/bsu_100_overlap_final_audit.lean` passed. All 60 explicitly declared public definitions, structures and theorems were checked and their full axiom closures inspected; each is a subset of `propext`, `Classical.choice`, `Quot.sound`. The structure and observation definitions were printed and inspected. `Triangle` contains only the three odd blocks, their strict lower bounds, and pairwise coprimality; it assumes no recovery or analytic conclusion. Log: `/tmp/bsu-100-overlap-final-audit.log`.

All four leaves are imported exactly once by `formal/GaloisForLFunctions/BiScaleUncertainty.lean`. `scripts/formal_tools.py index` and `scripts/formal_tools.py lint --check-generated` passed, with only the existing large-file warnings. Logs: `/tmp/bsu-100-overlap-index.log`, `/tmp/bsu-100-overlap-lint.log`. Owned-source whitespace checks passed. Extracted temporary drafts were removed; final audit and search evidence remain. No full or umbrella build was run.

Field README remained unchanged: SHA-256 `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275`.

## Contribution decision

Count one package. Its mathematical content is the exact least observation degree on every support stratum of an actual overlapping arithmetic family, against arbitrary real sieve competitors. Multiplicative overlap creates a fourth-order phase comparison that disappears when its connecting mode vanishes, even though all labelled affine observations remain available. The result includes both recovery and actual nontranslation witnesses below the threshold. This resolves a native observability question beyond the reused universal sixth-order bound; Fourier inversion, Ramanujan realization, coprime order arithmetic and sign algebra receive no separate novelty credit. The comparison is bounded by the corpus coverage and inspected primary sources above, not a claim of exhaustive literature priority. Programme count: **3/100; 97 remain**.
