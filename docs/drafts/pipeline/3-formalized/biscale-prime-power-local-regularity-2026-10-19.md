# First-order arithmetic visibility and local sieve regularity

- **ID:** biscale-prime-power-local-regularity-2026-10-19
- **Stage:** 3-formalized
- **Type:** Unconditional native classification; accepted programme package 8
- **Source:** [100-contribution programme](../1-in-progress/biscale-100-contribution-programme-2026-10-18.md)
- **Parent lead:** [support-weighted phase degree](../1-in-progress/biscale-support-weighted-phase-exponent-2026-10-19.md)
- **Status:** Finished and verified; research paused at the user's request.

## Theorem

Fix N≥2, actual real divisor weights b, and their admitted coordinate support S. Suppose the highest admitted dyadic order H=`2^floor(log₂N)` belongs to S. A missing order q is **linearly visible** when a zero-sum frequency tuple of length five or six has exactly one entry of order q and all other entries with order in S. Frequencies live in the actual cyclic period N!.

The optimal pairwise local inverse exponent from full literal fifth/sixth lag arrays to the actual natural-translation sup metric is:

- 1 when every missing admitted order is linearly visible;
- 1/3 otherwise.

This supplies a complete arithmetic criterion on the highest-mode stratum within the broader weighted-phase question. No inverse estimate is assumed as input. Existing package 6 supplies the cubic upper bound; generic inverse-function or monomial facts earn no new credit.

## Native arithmetic application

Take the actual Möbius-inverse source whose admitted coordinates are two at order one and at every prime power, and zero elsewhere. For this source, a missing order q is linearly visible exactly when `q.primeFactors.card ≤ 5`. Thus the sharp exponent is 1 if every admitted order has at most five distinct prime factors, and 1/3 otherwise.

The source has least positive period `lcm(1,…,N)`, the largest possible at cutoff N. A fully supported source has the same least period and is locally Lipschitz. Whenever an admitted order has at least six distinct prime factors, the prime-power source therefore gives cubic instability despite full period and the same highest dyadic depth. This distinguishes arithmetic width from period/stabilizer information. The family theorem, dichotomy and sharpness count together as one contribution.

An explicit threshold can subsequently be expressed using the product of the six smallest primes. No numerical enumeration is needed or authorized. The first formal target uses prime-factor cardinalities directly; the explicit threshold is not yet proved here.

## Dependency-closed paper argument to audit

### Lipschitz direction

Choose a physical sup-norm ball small enough that every coordinate in S preserves its base sign and has magnitude at least η>0; take η≤1. All admitted coordinates in this ball have magnitude at most M≥1, by the normalized Fourier coordinate bound. Pure sixth-coordinate readouts and factorization of positive sixth powers give `|c_s−e_s|≤Kε` for s in S, with `K=(6η⁵)⁻¹`.

For a missing q, choose a witnessing tuple of length m=5 or 6. Its product is `c_q A` for the first source and `e_q B` for the second, where A and B are products of m−1 base-support coordinates. The raw-array error implies `|c_q A−e_q B|≤ε`. Telescoping gives `|A−B|≤5M⁴Kε`; also `|A|≥η⁵` and `|e_q|≤M`. Hence `|c_q−e_q|≤η⁻⁵(1+5M⁵K)ε`. Together with the S estimate and the existing weighted coordinate-to-signal inequality this gives a physical Lipschitz bound with translation zero. The estimate holds for every ε≥0, as required by the existing local property.

No exponent above one is possible. Compare b with `(1+t)b`, 0<t≤1. Moment homogeneity bounds every raw error by C_b t, uniformly in lag tuples and in m=5,6: a finite-period sup bound on b controls each base moment, and `|(1+t)^m−1|≤m2^(m−1)t`. At frequency of order H, reverse triangle inequality gives physical error at least `t|b_H|` under every translation. Both sources enter every positive-radius neighborhood as t decreases. The existing small-power contradiction finishes this endpoint.

### Invisible direction and sharp cubic obstruction

If q is missing and invisible, compare the actual inverse-weight profiles `b+tR_q` and `b−tR_q`, 0<t≤1. Every changed resonant product has an odd number k of order-q factors. If another order outside S∪{q} occurs, both products vanish. The case k=1 would be a visibility witness, so every nonzero difference has k≥3. With M≥1 bounding base coordinates, the product difference is at most `2M⁶t³`. Existing Fourier inversion then bounds every fifth/sixth raw-array error by `2(N!)⁶M⁶t³`.

For physical separation, write `q=2^v u` with u odd. Since H is the unique admitted order at its dyadic depth and q is missing, `v<log₂H`. Let z and w be the translation phases at orders H and q. They satisfy `z^(H/2^v)=w^u`. If D bounds the physical translated error, normalized Fourier coefficients give `|b_H|·|1−z|≤D` and `t|1+w|≤D`. The already proved phase-incompatibility estimate yields

`2t ≤ (H/(2^v|b_H|)+u)D`

for t≤1. Thus every translation leaves error at least a positive multiple of t. The two perturbed sources approach b with physical error at most `φ(q)t`. A putative exponent α>1/3 contradicts the raw O(t³) estimate. The existing highest-mode cubic theorem, after nonzero scalar normalization and choosing a small physical ball, supplies the matching upper bound. No changing-support coefficient quotient is introduced.

### Prime-power visibility and period

For necessity, remove the unique order-q entry from a visibility tuple. Its frequency is minus a sum of at most five other frequencies. Its additive order q divides the lcm of their orders. Every nonconstant base order is a prime power, so the union of their prime factors has size at most five. Hence q has at most five distinct prime factors.

For sufficiency, let `q=∏ p^(v_p(q))` have at most five distinct prime factors. Each primary factor is admitted and lies in the base support. Choose one frequency of that exact primary order for each factor. The primary orders are pairwise coprime, so their sum has order q. Use the negative of that sum for the distinguished q entry, and pad the remaining positions with zero frequencies, whose order is one. This gives a six-tuple with zero sum and exactly the required support. For a missing q, q is neither one nor a prime power, so none of the primary entries has order q.

Finally, a period h of the base must be divisible by every admitted prime power, by Fourier coefficients. Their lcm equals `lcm(1,…,N)` because each admitted integer factors into admitted prime powers. Conversely, that lcm is a period of every cutoff-N sieve signal. The resulting least-period equality uses existing spectral period machinery, not a new period theorem.

The differing-regularity case is nonempty without numerical enumeration. Choose a six-element finite set of primes using Euclid's infinitude theorem, and take its product as the cutoff. The product's prime-factor set is exactly that set, so it is an admitted order of width six. This gives an unconditional existence corollary of two actual sources with the same maximal least period and highest dyadic depth but respective sharp local exponents one and one third. The finite-prime-set and prime-factor-product facts are classical ingredients, not additional contributions.

## Prior work and scope

The broader card records corpus queries and primary comparisons for monomial inversion. The focused resonance query `/tmp/bsu-100-next-resonance-detection-search.json` is non-partial with 74,356 inventoried files; all 40 candidate/source statements and prose/passage inventories were inspected. It finds reusable raw/spectral equivalence, coordinate error and inverse-array bounds. Its generated affine-sign-to-error chain does not establish a local modulus and is rejected. Semantic coverage is unmeasured and compiler refresh incomplete.

The older [arithmetic order-relation card](../1-in-progress/biscale-order-relation-classification-1810.md) already proposes valuation feasibility and binary sign matrices for exact moments. Those proposals, classical CRT/order decomposition, the general Jacobian criterion, the highest-mode cubic upper bound and package 7 helpers are prior ingredients. The advance is the sharp native local dichotomy and its prime-power width/period separation.

Queries `/tmp/bsu-100-next-prime-power-{visibility,period}-search.json` are non-partial with 74,358 inventoried files each. All 40 candidate/source statements and prose/passage inventories from each were reviewed. Their proposed prime-pair and scalar periodicity chains do not establish the present visibility criterion or sharp exponent. The additive-order query `/tmp/bsu-100-next-primary-order-sum-search.json` is explicitly partial: `filter_and_judge` returned malformed/incomplete local-model JSON. Its available 40 candidate/source statements and prose/passage inventories were reviewed; its periodic-orbit proposal does not prove the required additive-order identity. Inventory: 74,359 files; semantic completeness remains unmeasured and compiler refresh incomplete.

The follow-up lexical period query returned seven records, all inspected, and found `sieveSeq_periodic_iff_active_divisors` and `sieveSeq_periodic_iff_leastPeriod_dvd`. Direct source review confirms these concern raw divisor support; spectral support must be connected explicitly. `SieveCanonicalTranslation.periodic_of_coordinate_orders` already contains the converse argument as a private helper. The installed Mathlib source supplies `AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime`, already used in the corpus's coprime-overlap and edge-resonance proofs. Broad semantic retrieval missed that usable ingredient. Product-error search was refined to an exact four-record result; the general normed-ring theorem in `HTGeometry/BanachTriangularExponential.lean` is suitable for reuse. Every exact result was inspected. All reused names still require scratch Lean applicability checks.

[Pozdnyakov–Zhang–Ortner–Csányi–Ceriotti, §1.4 and introduction](https://arxiv.org/pdf/2109.11440) already distinguish full-rank local inversion from global injectivity and describe sensitivity loss even at nonsymmetric configurations. This excludes generic Jacobian degeneracy and absence of symmetry as novelty claims. Together with the primary comparisons on the parent card and the classical restricted-congruence criterion, the scoped candidate distinction is the exact prime-factor-width classification for these literal arithmetic moment arrays. The searches do not prove universal literature priority.

## Gates

- [x] Recorded corpus and primary comparison with explicit coverage limits; inspected returned inventories and relevant source statements.
- [x] Paper steps and constants audited, including every noise size and nonzero signed base amplitude; Lean may expose corrections.
- [x] Formalize actual-object dichotomy and prime-power application without missing analytic inputs.
- [x] Named-source checks, complete statement/axiom audit, exact-once wiring, index/lint and cleanup.
- [x] Separate significance decision: count the complete classification and family comparison once.

## Implementation history

Intermediate statuses below are superseded by the final verification record.

The already checked product bound may use a coarser power of M than the paper's telescoping constant. Any larger finite constant preserves the claimed exponent. The highest-mode theorem is stated for ε≤1; in the local property, ε≥1 is handled by the physical-ball triangle bound. Raw and spectral least-period supports must not be conflated. No source theorem is assumed merely because it appeared in retrieval.

The follow-up deep query `/tmp/bsu-100-next-linear-visibility-search.json` completed without partial stages (74,362 inventoried files). All 40 candidate/source statements and all prose/passage inventories were reviewed. Its proposed chain supplies the already used raw/resonant equivalence, not local inversion. Semantic coverage remains unmeasured; compiler refresh is incomplete. Direct source review of `SixthReadoutStability.lean` confirms prior weighted Lipschitz and cubic estimates for the normalized prime-family Gram readout. Neither those bounds nor generic sixth-root branching count as new work here.

Scratch API checks passed for the normed-ring product estimate, additive-order coprime/lcm lemmas, prime-factor product, raw product errors, and physical local scaling. Formalization starts with a normalized base whose nonzero coordinates have magnitude at least two; a physical unit ball then preserves the signed branch. The draft bound uses `(1+6M⁷)ε` for each visible coordinate. Scalar and local proofs are under Lean checking; no new package is accepted.

The whole-corpus arithmetic query `/tmp/bsu-100-next-primary-visibility-arithmetic-search.json` also completed without partial stages (74,362 inventoried files). All 40 candidate/source statements, the generated ingredient set, and all prose/passage inventories were reviewed. It supplies `Nat.primeFactors_mul`; its proposed subgroup-cardinality/period-average chain does not prove the required frequency-sum order. The direct installed-source additive-order lemmas remain the applicable route. Semantic coverage is unmeasured and compiler refresh incomplete.

Scratch `/tmp/bsu_100_visibility_order.lean` passes (`/tmp/bsu-100-visibility-order-r1.log`), proving prime-width subadditivity, multiplication of pairwise coprime frequency orders, and zero padding. The arithmetic scratch through the necessity bound and primary-factor admissibility also passes (`/tmp/bsu-100-visibility-prime-r0.log`); the full converse using the existing `frequency_order` has since been drafted and still needs checking. Local inversion remains unverified as a whole: the first draft exposed three inference issues, corrected in the current draft; subsequent attempts encountered shared `.olean` regeneration by another build. Those external builds were left untouched.

The focused sharpness search `/tmp/bsu-100-next-visibility-sharpness-search.json` completed without partial stages, with 74,364 inventoried files. All 40 candidate/source statements, ingredient sets and prose/passage inventories were inspected. The existing private `not_holder_of_witnesses` is the applicable general sharpness transfer. Sign-count helpers and `orderCount_eq_one_witness` are prior ingredients. The generated chain does not itself supply the new visibility-to-cubic witness bound. Semantic coverage remains unmeasured and compiler refresh incomplete.

`SieveResonantVisibility.lean` now passes its original named-source/export check (`/tmp/bsu-100-resonant-visibility-source-r0.log`). It defines literal fifth/sixth visibility, proves the five-prime necessity bound and finite padding, and identifies the primary support as order one plus prime powers. `SieveVisibilitySpikeEstimate.lean` has been extracted from the passing scalar scratch (`/tmp/bsu-100-visibility-spike-r1.log`) and is under its named-source check. These are ingredients, not separately counted contributions; native converse, local recovery, sharpness, period and final audits remain.

Both ingredient leaves are wired once; the spike named-source check passes (`/tmp/bsu-100-visibility-spike-source-r0.log`). The arithmetic leaf now also proves that the primary support has exactly the full cutoff lcm; its updated named-source/export check passes (`/tmp/bsu-100-resonant-visibility-source-r1.log`). `SieveLinearVisibility.lean` and `SievePrimePowerVisibility.lean` are drafted source files awaiting named-source checks and wiring. The shared import closure has 9,442 project modules; another owned-by-others Lake build is regenerating successive dependencies. A guarded source-check launch waits for that existing build to exit; it does not interrupt it or start another full build. The actual single-coordinate inverse profiles and full-array cubic bound are drafted in `/tmp/bsu_100_visibility_perturb.lean`, still unchecked.

The lexical divisibility follow-up returned ten records, all inspected, and led to the existing THIM horizon modulus and prime-power admission theorem in `ValuationTraceCoprimeCompletionAndObservationState.lean`. The proposed full period is exactly the already defined `horizonObservationModulus N = (Icc 1 N).lcm id`; do not invent or claim a new arithmetic period object. Installed `Nat.dvd_iff_prime_pow_dvd_dvd` supplies the generic divisibility step. The lexical result omits semantic/compiler coverage fields; no completeness claim is made.

The finite-prime existence query `/tmp/bsu-100-next-prime-width-existence-search.json` completed without partial stages (74,375 inventoried files). All 40 candidate/source statements, the ingredient proposal and the prose/passage inventories were inspected. It finds `Set.Infinite.exists_subset_card_eq`; installed `Nat.primeFactors_prod` closes the exact product-support step. The generated proposal needs an infinite set of primes, not an arbitrary infinite set. The actual six-prime existence proof and its Mathlib API check pass in `/tmp/bsu-100-visibility-existence-r0.log`. Semantic coverage is unmeasured and compiler refresh incomplete.

The two completed ingredient leaves have a complete imported audit: all 14 public statements, three definition bodies and 14 axiom reports were inspected in `/tmp/bsu-100-visibility-ingredients-audit-r1.log`; only `propext`, `Classical.choice`, `Quot.sound` occur. The existing `ParityNeighborhood.not_holder_of_witnesses` has been made public without changing its statement or proof, for reuse by the new sharpness proofs; its updated source and export still require checking.

The remaining production drafts are `SieveLinearVisibility`, `SievePrimePowerVisibility`, `SieveVisibilityPerturbations`, `SieveVisibilityPhaseSeparation`, `SieveVisibilityRadialEstimates`, `SieveLocalVisibilityClassification` and `SievePrimePowerLocalRegularity`. They include actual inverse profiles, the visibility dichotomy, maximal-period identities and an unconditional same-period/same-depth sharp-exponent contrast. They are not yet certified or wired. The guarded wait expired before launching Lean (exit 124); a subsequent external dependency rebuild is still restoring the shared import closure. No external job has been interrupted. The user's final scope is to finish these started proofs, wire verified leaves, update documentation and pause; do not start another research candidate.

The external build ended with five required objects missing. Individual unchanged-source checks restored exactly those five imports, all exit zero without diagnostics; no dependency source was edited. Evidence: `/tmp/bsu-100-visibility-restore-abstract-r0.log` and `/tmp/bsu-100-visibility-restored-dependencies.json`. The local Lipschitz leaf then exposed one additive-inequality elaboration mismatch, corrected without changing its statement. Its original-source/export check now passes without diagnostics (`/tmp/bsu-100-linear-visibility-source-r3.log`), and it is wired once. Remaining checks run sequentially, stopping on any failure.

The primary-frequency converse, actual spike perturbations, radial estimates, promoted sharpness helper and full highest-stratum classification pass their named-source/export checks. `highest_stratum_sharp_exponent` is now verified; its domain is arbitrary real base weights with a nonzero highest admitted dyadic coordinate, and neighborhoods permit changing support. Phase separation also passes; one unused simplification has been removed and its clean check is rerunning. The final family module's first check found only a mismatch between two decidability instances for its exponent's `if`; an explicit split on the width condition removes that elaboration issue. No theorem statement or paper claim was weakened. Current check records: `/tmp/bsu-100-visibility-source-checks.json`.

All nine new leaves and the promoted helper's original source now pass without diagnostics. The final family theorem is `LinearVisibility.exists_same_period_depth_different_exponents` in `SievePrimePowerLocalRegularity.lean`; its conclusion has no unproved input or analytic premise. Each new leaf is explicitly wired once. The complete imported statement/definition/axiom audit and repository gates are the remaining certification steps.

## Final verification and scope

All nine original source/export checks pass without diagnostics, as does the promoted `ParityNeighborhood.not_holder_of_witnesses` in `SieveParityNeighborhoodSharpness.lean`. Each check used `lake --old env lean` on its actual source; no full or umbrella build was run. The nine leaves are `SieveResonantVisibility`, `SieveVisibilitySpikeEstimate`, `SieveLinearVisibility`, `SievePrimePowerVisibility`, `SieveVisibilityPerturbations`, `SieveVisibilityPhaseSeparation`, `SieveVisibilityRadialEstimates`, `SieveLocalVisibilityClassification` and `SievePrimePowerLocalRegularity`.

The complete imported audit `/tmp/bsu_100_visibility_final_audit.lean` passes. All 67 new public statements, the promoted helper's statement, eight owned definition bodies and ten existing native definition bodies were inspected. All 78 requested axiom reports are present; their union is exactly `propext`, `Classical.choice`, `Quot.sound`. This includes the literal signal, full moment arrays, physical neighborhood property, Möbius inverse, active support/depth and both existing period invariants. The final comparison is a closed existence theorem with no premises. Main reusable endpoints are `highest_stratum_sharp_exponent`, `prime_power_visibility_iff`, `sharp_primePower_exponent` and `exists_same_period_depth_different_exponents` in namespace `GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility`.

Every leaf is wired exactly once. `scripts/formal_tools.py index` and `scripts/formal_tools.py lint --check-generated` both exit zero; lint reports 381 pre-existing file-size warnings and no errors. Seventeen verified extracted/API scratch files were removed; audit sources, search results and logs remain. The field README SHA256 remains `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275`. No owned Lean process remains running.

Evidence: `/tmp/bsu-100-visibility-{initial-source-checks,source-checks,public-inventory,final-verification,cleanup-manifest}.json`; `/tmp/bsu-100-visibility-{final-audit,index,lint}-r0.log`. The final verification manifest records current source hashes and verifies every public audit entry and explicit umbrella import.

Significance decision: accept one native package. It determines the sharp pairwise physical inverse exponent for every real base in the highest-mode stratum, then computes the criterion as exact prime-factor width for an explicit actual-source family. The two families have equal maximal least period and dyadic depth, yet provably different sharp local exponents. This supplies an arithmetic distinction that the existing period/depth classifications and prior uniform cubic estimate do not determine. Generic monomial inversion, classical prime decomposition, the reused period machinery, Euclid's theorem and supporting declarations receive no separate credit. Literature priority is limited to the documented comparison; absent ranked hits are not proof of universal novelty. The broader support-weighted classification and an explicit numerical cutoff remain unproved here. No further candidate is started; work is paused as requested.
