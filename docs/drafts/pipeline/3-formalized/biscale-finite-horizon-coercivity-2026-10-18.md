# Quantitative coercivity for finite arithmetic dilation horizons

- **Stage:** 3-formalized
- **Type:** THEOREM; novelty unverified; no contribution counted
- **Parent:** [100-contribution programme](../1-in-progress/biscale-100-contribution-programme-2026-10-18.md)
- **Actual objects:** `additiveStepEnergy`, `multiplicativeScaleEnergy`, `biScaleJointEnergy` in `UniversalRamanujanCovarianceAndBiScaleRigidity.lean`.
- **Question:** how does distance from constants depend on the observation window N and the finite dilation horizon K? Zero-energy rigidity alone does not answer this.

## Certified result — 2026-10-19

Write E_(K,N) for the existing clipped joint energy and V_N for squared distance from constants.

- For every K≥2, every N (including 0 and 1), and every actual f:ℕ→ℝ, the anchored square sum is at most `6*N*E_(K,N)(f)`.
- For every N≥1024, an actual logarithmic cosine has error at least N/16 about every center and joint doubling energy at most 384. Hence every valid variance coercivity constant at K=2 is at least N/6144. Together these give the sharp linear order on every sufficiently large window.
- Put d=card(oddPrimeModes(2*K)). For every K,Q, at N=1024*(Q+1)^(d+2), an actual function has error about every center at least N/16 and joint energy at most (384+65536K³)*(Q+1)^d. All approximation and variance inputs are proved.
- For each fixed finite K there is no real C valid for all window sizes, even when the center may depend on f and N.

The six source leaves are `FiniteHorizonPrimeRecurrence`, `FiniteHorizonOscillationEnergy`, `FiniteHorizonIntegerVariance`, `FiniteHorizonCoercivityWitness`, `FiniteHorizonPositiveCoercivity`, and `FiniteHorizonCoercivityClassification`, all under `formal/GaloisForLFunctions/BiScaleUncertainty`. The classification leaf defines `WindowCoercivityBound` and proves `windowCoercivityBound_six_mul`, `doubling_coercivity_constant_lower_bound`, and `not_uniform_window_coercivity`.

All six named-source checks/export commands passed without warnings. The imported audit of ten principal declarations passed with only `propext`, `Classical.choice`, `Quot.sound` (`/tmp/bsu-100-coercivity-final-axioms.log`). Umbrella wiring, index regeneration, scoped whitespace checks and `scripts/formal_tools.py lint --check-generated` passed (`/tmp/bsu-100-coercivity-index.log`, `/tmp/bsu-100-coercivity-final-lint.log`). No full or umbrella build was run. The field README remains unchanged, SHA-256 `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275`.

The [uniform-bound no-go](../5-failed/biscale-uniform-finite-horizon-coercivity-2026-10-19.md) records this positive survivor. This package is **not counted** toward the 100-contribution target: generic recurrence, nonexpansion and graph bounds are established mechanisms, and the exact finite-prime theorem still needs a substantive novelty comparison. The programme remains 1/100.

The sections below retain the research record. Earlier statements about pending checks describe their historical checkpoints; this certification section is authoritative for current proof status.

## Prior-work gate

The exact-name corpus query returns six declarations, all in the original energy module or its capstone. Exhaustive source references add only `ClassicalFoundationBoundaries.joint_zero_iff_additive_zero`. The actual definitions and rigidity proof were read. The 170 distinct lexical hits for `"joint" "coercivity" "Poincare" --any --module BiScaleUncertainty --per-module 0` were paginated at offsets 0 through 160; every declaration inventory was inspected. Nearby `CompactSourceGraphCoercivity` was read fully: its diffuse source-pair kernel already controls variance; it does not establish a quantitative gain requiring the finite arithmetic dilation edges. The full theorem inventory and relevant proofs of `CoprimeShearAndMultiplicativeGraphUncertainty`, and all of `MixedEdgePathCongestion`, were then inspected: they supply additive telescoping, finite Cauchy–Schwarz, divisor-supported identities and a continuum path-congestion transfer, not the finite-window coercivity rate.

Broad deep energy and source-limit searches finished their requested stages but semantic completeness remains unmeasured. Their inventories were inspected; the long queries returned many irrelevant matches. The exact `multiplicativeScaleEnergy` deep search also finished; its complete candidate/source inventories contain the original energy definitions plus unrelated scaling statements. The exact native definitions remain the reliable starting point. No absence or novelty conclusion follows from the broad queries.

External comparison already prevents counting generic nonexpansion as new. [Hildebrand's symmetrized affine walk](https://arxiv.org/abs/2007.09126) has logarithm-squared mixing time on modular integers. The [Helfgott/Valette/Elkies discussion](https://mathoverflow.net/questions/110077/showing-non-expansion-for-x-rightarrow-x1-x-rightarrow-2x) points to primary affine-group spectral papers and gives finite-multiplier nonexpansion arguments. Modular walks and the corpus's clipped interval energy have different boundary edges and normalizations. Mere nonexpansion or a renamed canonical-path inequality will not qualify. Primary-paper comparison and any proposed transfer remain open.

## Conjectures and paper route under audit

Write V_N(f)=inf_c sum_(1≤n≤N)(f(n)-c)^2 and E_(K,N)=biScaleJointEnergy K N f.

1. For K=2, the best constant in V_N≤C_N E_(2,N) should have order N, compared with order N² for additive steps alone. Binary parent paths use one dilation edge and at most one additive edge. A geometrically weighted path estimate should give the linear upper bound. This is an unverified proof plan, not a formal theorem or a novelty claim.
2. A candidate sharpness family on N=2^L is the dyadically invariant tent: if 2^j≤n<2^(j+1), put f(n)=min(n/2^j-1,2-n/2^j). It satisfies f(2n)=f(n). The additive energy on the j-th block is at most 2^(-j), so total energy is at most 2. Two macroscopic subintervals of the final dyadic block have values separated by 1/4, giving V_N≥cN with an explicit c. Check every boundary and finite-window endpoint before Lean.
3. For any fixed finite horizon K, logarithmic oscillations may give a stronger quantitative deterioration law than generic nonexpansion. Set f(n)=cos(t log(n/N)), t=2πq/log 2. A simultaneous approximation of q log(k)/log 2 by integers makes every dilation defect small. With approximation parameter Q and d independent ratios, q≤Q^d and phase errors O(Q^(-1)) suggest E_(K,N)≤C_K(Q^d+N/Q²). At N of order Q^(d+2), this predicts a Poincaré-constant lower bound of order N^(2/(d+2)). Prime factorization may reduce d to the number of primes ≤K minus one. This rate, its actual integer witnesses, and its relation to existing affine spectral results are the candidate advance; none is yet certified.

For the last route, use the final dyadic annulus to bound variance. Under logarithmic coordinates it contains exactly q cosine periods. Weighted continuous variance is ≥N log(2)/4 for every center; a discrete quadrature estimate should lose O(t), not O(t log N). Additive increments split at n≈t to give O(t); dilation defects use the actual finite sum. All approximation, counting and quadrature inputs must be discharged, not assumed in the final theorem.

## Gates

- [x] Read actual native energy definitions and existing rigidity statement.
- [x] Inspect all 170 lexical hit inventories and all six exact-name hits.
- [ ] Finish nearby corpus and primary-literature comparison.
- [ ] Decide whether a quantitatively new theorem survives the classical comparison.
- [x] Complete paper proof, including boundary cases and explicit constants.
- [x] Formalize the actual unconditional prime-count window witnesses.
- [x] Formalize the positive 6N bound and a matching-order cosine family on every N≥1024.
- [x] Audit completed witness leaves: named-source checks, standard axioms, umbrella imports, index and lint.
- [x] Audit the positive leaves: named-source checks, imported axioms, wiring, index and lint.

All six Lean leaves are integrated and audited; the package remains uncounted. If the proposed contribution reduces to known graph theory, record that result and pursue a stronger native question; do not increment the count.

## Dependency-closed paper derivation

The following arguments sharpen the initial plans. The prime-count witness now has the Lean certification recorded below. The positive 6N theorem and sharpness family have paper proofs; their formalization and the package's novelty gate remain open.

### Positive bound from the actual arithmetic edges

For 2≤k≤N write b_k=f(k)-f(floor(k/2)) and B_N=sum b_k². Pairing children 2m and 2m+1 gives

    B_N ≤ 3 sum_(1≤m≤N/2) (f(2m)-f(m))²
          + 2 sum_(1≤m<N) (f(m+1)-f(m))² ≤ 3 E_(2,N).

For a node n at binary depth J, let k_j=floor(n/2^(J-j)), 1≤j≤J. Then f(n)-f(1)=sum_j b_(k_j). Weighted Cauchy–Schwarz with weights 2^(J-j) gives

    (f(n)-f(1))² ≤ (2^J-1) sum_j b_(k_j)² / 2^(J-j).

Each depth-j node has at most 2^(J-j) descendants in the depth-J part of [1,N], so summing at depth J bounds the result by (2^J-1) B_N. Sum J=1,…,L where 2^L≤N<2^(L+1). Since sum_J (2^J-1)<2^(L+1)≤2N,

    V_N(f) ≤ sum_(1≤n≤N)(f(n)-f(1))² ≤ 6 N E_(2,N) ≤ 6 N E_(K,N),  K≥2.

N=0 and N=1 have zero variance. All paths stay inside the actual window. The estimate retains incomplete final generations; no energy outside [1,N] is inserted.

The tent witness above makes this order sharp for K=2. For N=2^L with L≥4, M=N/2 is divisible by 8. On [M,9M/8) the tent is at most 1/8; on [11M/8,13M/8) it is at least 3/8. For any center c, either c>1/4 and the first block contributes at least M/512, or c≤1/4 and the second contributes at least M/256. Thus V_N≥N/1024. The doubling energy is exactly zero. On each complete binary block of size 2^j, including its last step into the next block, each additive increment has magnitude at most 2^(-j). Summing gives additive energy at most 2. Therefore every coercivity constant at this N is at least N/2048.

### Finite prime horizon: actual near-resonant witnesses

Let K≥2, let P be the finite primes in [3,K], and put d=|P|. Thus d+1 is the number of primes ≤K. Fix integer Q≥2. Partition [0,1)^P into Q^d equal boxes and place the Q^d+1 fractional-part vectors j*(log(p)/log(2)) in them, j=0,…,Q^d. Two share a box. Subtracting their indices gives an integer 1≤q≤Q^d and integers m_p satisfying

    |q log(p)/log(2)-m_p| < 1/Q  for every p in P.

The empty P case gives q=1. Set m_2=q. Factor each 2≤k≤K into primes, with multiplicity. Its factor list has length at most k, since every prime is ≥2 (an induction gives list length≤product). Add the factor errors and use log(product)=sum log(factors). Some integer m_k then satisfies

    |q log(k)/log(2)-m_k| ≤ K/Q.

Put t0=2π/log(2), t=t0*q and choose the fixed even positive integer

    A=1024,   N=A*Q^(d+2),
    f(n)=cos(t log(n/N))  for 1≤n≤N.

Values at n=0 or beyond N do not enter the native energy. The elementary bounds 1/2≤log(2)≤1 and 3<π<4 give 1≤t≤16q. The fixed A avoids rounding a frequency-dependent constant. The phase error and the 1-Lipschitz cosine give |f(kn)-f(n)|≤2πK/Q. There are at most K*N native dilation edges, hence

    E_dil(K,N,f) ≤ 4π² K³ N/Q².

For additive steps, |f(n+1)-f(n)|≤min(2,t/n), by the mean-value bound and log(1+1/n)≤1/n. A direct telescoping bound avoids a rounded splitting point: for x,t≥1 and |u|≤min(2,t/x),

    u² ≤ 24t²/[(x+t)(x+t+1)]
       = 24t²/(x+t) - 24t²/(x+t+1).

If x≤t, the denominator is ≤6t² and u²≤4; if t≤x, the denominator is ≤6x² and x²u²≤t². Summing actual steps gives E_add≤24t²/(1+t)≤24t. Consequently

    E_(K,N)(f) ≤ (24t0+4π²K³A) Q^d.

For the variance, any minimizing center lies in [-1,1]; clipping an arbitrary center to that interval decreases every squared distance. For c in this interval put g(x)=(cos(t log(x/N))-c)² on [N/2,N]. Its derivative has absolute value at most 4t/x≤8t/N. The left-endpoint integer sum on this annulus differs from its integral by at most 4t (using the bound separately on each unit cell).

With y=log(x/N), the Jacobian x is ≥N/2, and the y-interval [-log(2),0] contains exactly q periods. Hence

    integral_(N/2)^N g(x) dx
      ≥ (N/2) integral_(-log(2))^0 (cos(t*y)-c)² dy
      = (N log(2)/2)*(1/2+c²) ≥ N log(2)/4.

Indeed 4t≤64Q^d≤64Q^(d+2)≤N log(2)/8. The integer annulus is contained in [1,N], so every center has squared error at least N log(2)/8. In particular

    V_N(f) ≥ (A log(2)/8) Q^(d+2),
    E_(K,N)(f)/V_N(f) ≤ [8(24t0+4π²K³A)/(A log(2))] / Q².

With A=1024 these also give the simpler explicit bounds

    V_N(f) ≥ 64Q^(d+2),
    E_(K,N)(f) ≤ (384+65536K³)Q^d,
    E_(K,N)(f)/V_N(f) ≤ (6+1024K³)/Q².

This gives an explicit polynomial deterioration along N=A*Q^(d+2), with exponent 2/(d+2)=2/(π(K)+1), where π(K) counts primes at most K. Centering and dividing by sqrt(V_N) yields actual mean-zero, unit-variance witnesses. No approximation, source-existence or coercivity premise remains in this paper construction. Constants and all finite sums still require Lean verification. The exponent is a proved candidate lower bound, not a claim of optimality for K≥3.

The substantive comparison now concerns this prime-rank-dependent polynomial rate for the clipped interval energy, together with the sharp single-prime positive bound. Generic nonexpansion is only background. The primary paper on Baumslag–Solitar Markov operators was located, but its publisher endpoint was inaccessible; no claim about its exact coverage is made from the title or secondary summaries.

## Existing building blocks discovered by the corpus tool

`HTGeometry.exists_dirichlet_simultaneous` in `DirichletSimultaneousApproximation.lean` already proves the exact finite-type pigeonhole approximation, including an empty index type. Its complete source was read; reuse it rather than add a duplicate. `HTGeometry.norm_sum_smul_sub_integral_le` in `RiemannSumCell.lean` proves a stronger cellwise quadrature estimate with no global Lipschitz assumption; its source was read and it can be applied to a complex-valued embedding of the real squared cosine profile. The real right-endpoint alternative `RHTower.abs_riemannSum_sub_integral_le` was also inspected. The scratch import/API probe passed after instantiating the finite index type in a universe-polymorphic `have`: `lake --old env lean -j 1 /tmp/bsu_100_coercivity_api.lean`, exit 0, no warnings; log `/tmp/bsu-100-coercivity-api-r2.log`. Both imported theorems use only `propext`, `Classical.choice`, `Quot.sound`. The first probe failure was solely the uninstantiated universe, not an imported theorem failure.

The approximation search is partial (`filter_and_judge` unfinished), and the quadrature search is partial (`text_retrieval` unfinished). Both returned useful statements; all candidate/source inventories and proposed ingredient sets were inspected. Semantic completeness remains unmeasured. Files: `/tmp/bsu-100-simultaneous-approximation.json`, `/tmp/bsu-100-sum-integral-quadrature.json`. Their search `source_only` status was resolved for the selected two HT ingredients by the passing actual toolchain probe above. This does not verify the proposed new coercivity theorem.

## Prime recurrence checkpoint and additional prior work

`SieveMoments.oddPrimeModes (2*K)` already indexes precisely the odd primes at most K. Reusing this index and `HTGeometry.exists_dirichlet_simultaneous`, the scratch theorem `FiniteHorizon.exists_prime_horizon_recurrence` proves, without assumptions on K or Q, existence of `1≤q≤(Q+1)^card(oddPrimeModes(2*K))` controlling every dilation `2≤k≤K` to error `K/(Q+1)`. Prime-factor multiplicities are handled explicitly. `/tmp/bsu_100_prime_recurrence.lean` passed `lake --old env lean -j 1`; `/tmp/bsu-100-prime-recurrence-r2.log` records exit 0 and only the standard three axioms. It had one unused-parameter warning, since removed; that cleanup still needs its next combined check. This is supporting work, not a counted contribution.

The narrowed energy search also exposed `RHTower/FinitePrimeTwistRecurrence.lean`. Its complete 138-line source was read. It already proves cofinal quantitative simultaneous prime-clock alignment, energy collapse, and absence of a twist gap for a fixed finite prime packet. All four exact-name lexical hits were checked. Thus neither prime recurrence nor finite-packet nonexpansion is new here. The proposed remaining advance must concern actual clipped integer-window energies, positive coercivity and variance, with the stated prime-count rate. Files: `/tmp/bsu-100-log-energy-local.json`, `/tmp/bsu-100-prime-twist-existing.json`.

All inventories and ingredient proposals in `/tmp/bsu-100-dyadic-poincare-ingredients.json` and `/tmp/bsu-100-binary-parent-local.json` were inspected. The first mostly returned unrelated energy descent; the field-filtered second is partial and returned dyadic correlation/renewal estimates, not the binary parent inequality. `/tmp/bsu-100-log-energy-local.json` finished its requested stages. No semantic absence certificate follows. The existing private log-step estimates in `RHTower/PrimeClockFiniteScaling.lean` use the same elementary log inequality but do not prove the window-uniform O(t) oscillation energy bound.

`/tmp/bsu_100_log_energy.lean` now proves `logOscillation_additiveStepEnergy` (the uniform 24t bound) and `logOscillation_multiplicativeScaleEnergy` (every actual dilation edge, bounded by K*N*ε² under phase tolerance ε). Both passed the direct Lean scratch check with no warnings and only `propext`, `Classical.choice`, `Quot.sound`; log `/tmp/bsu-100-log-energy-r3.log`. The first two checks exposed proof/elaboration issues, all resolved before this checkpoint. These remain supporting scratch results; the unconditional witness/variance theorem is not yet formalized or counted.

The logarithmic-variance search `/tmp/bsu-100-log-variance.json` finished its stages; all candidate/source inventories were inspected. It located `HTGeometry/LogTrigPowerPrimitives.lean`, whose full source was read. The exact filtered lexical query has two hits, both existing cosine/sine integral formulas. They and the existing `hasDerivAt_mul_log` give positive-ray analytic ingredients. The first unquoted OR query expanded to 139702 matches and is not an exhaustive audit; the corrected quoted, exact, module-filtered query is `/tmp/bsu-100-log-primitives-exact.json`. No new mathematical credit attaches to these primitives.

The combined scratch `/tmp/bsu_100_horizon_energy.lean` passed with no warnings and standard axioms (`/tmp/bsu-100-horizon-energy-r2.log`). `exists_finite_horizon_low_energy` has no approximation hypothesis: for every K,Q it constructs one prime-count-bounded q controlling the joint energy for every N and every phase offset. It also rechecked the unused-parameter cleanup in the prime-recurrence lemma. The continuum variance scratch passed at `/tmp/bsu-100-log-variance-r2.log`: `annular_variance_lower_bound` proves the exact paper bound via a weighted primitive and pointwise comparison. Integer quadrature and final witness assembly remain open.

The integer step is now proved in `/tmp/bsu_100_log_variance.lean`, checked without warnings at `/tmp/bsu-100-log-variance-r4.log`. The existing complex quadrature theorem is applied through the real embedding; the actual error is ≤2t. `integer_window_variance_lower_bound` bounds the full sum over `Icc 1 (2*M)` below by `M*log(2)/2-2*t`, for every real center. Projection to [-1,1] and inclusion of the annular integer subset are proved. The theorem has only standard axioms. `/tmp/bsu_100_window_witness.lean` assembles these pieces with the fixed window 1024*(Q+1)^(d+2); its first check is in progress. No new production module or counted contribution yet.

The assembled witness passed without warnings at `/tmp/bsu-100-window-witness-r2.log`, with only `propext`, `Classical.choice`, `Quot.sound`. The first check needed two cast-normalization fixes. `exists_prime_count_window_witness` states, for every K,Q with no extra premises, that at N=1024*(Q+1)^(d+2) there exists an actual function on natural numbers with variance about every real center at least N/16 and joint energy at most (384+65536K³)*(Q+1)^d. Four leaves have been extracted: `FiniteHorizonPrimeRecurrence`, `FiniteHorizonOscillationEnergy`, `FiniteHorizonIntegerVariance`, `FiniteHorizonCoercivityWitness`. Their direct named-source checks and integration are in progress; they are not four contributions.

The additional tree-Hardy search `/tmp/bsu-100-tree-hardy-ingredients.json` finished its requested stages, with all candidate/source and ingredient inventories inspected. It returned continuous weighted Hardy inequalities and unrelated tree data, not the required binary-parent finite-window estimate. Semantic completeness remains unmeasured. The exact positive 6N bound and matching dyadic sharpness family still need Lean proofs; this route must not be retired or counted before that closure and the novelty audit.

Two further Mathlib-filtered searches finished: `/tmp/bsu-100-dyadic-partition-ingredients.json` and `/tmp/bsu-100-log2-ingredients.json`. Every returned candidate/source inventory was inspected. Useful statements include `Nat.geom_sum_le`, `Nat.geomSum_eq`, `Nat.log_mul_base`, `Nat.log2_eq_log_two` and `Nat.log_two_bit`. These are existing ingredients, not proposed advances; actual toolchain probes remain required before use in new proofs.

An alternative exact route to the positive 6N theorem avoids assigning a dyadic depth to every point. For n≥1, let A(n) be its proper-root ancestor chain, containing n,n/2,… down to 2 or 3. Induction gives sum_(k∈A(n))1/k≤1−1/n: if p=floor(n/2), the step follows from 2p≤n. Weighted Cauchy then gives (f(n)−f(1))²≤sum_(k∈A(n)) k*b_k². For k≥2 the descendants in [1,N] lie in the disjoint intervals [k*2^r,(k+1)*2^r); their number is ≤sum_(2^r≤N/k)2^r≤2N/k. Interchanging the finite sums gives the same 2N*B_N bound, hence 6N*E_(2,N). This is a formalization option for the already-stated paper theorem, not another contribution. The sharper reciprocal inequality and every cutoff endpoint must be retained when implementing it.

The weighted-Cauchy hybrid search returned mostly quadratic-form statements; all inventories were inspected. A source lookup found `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` in Mathlib's ordered finite sums. Its full statement/proof and nearby Titu form were read. It permits signed increments and positive weights without introducing square roots. The follow-up exact corpus query returned zero hits despite the source declaration (`/tmp/bsu-100-weighted-cauchy-exact.json`); whether this is a freshness or matching gap is unverified. The original results are `/tmp/bsu-100-weighted-cauchy-ingredients.json`. This concrete mismatch is another reason not to infer absence from search results. `/tmp/bsu_100_binary_parent.lean` now contains a draft recursive ancestor set, reciprocal-budget and pointwise Cauchy proofs. This draft has not yet been checked; do not rely on its declarations until its own Lean check passes.

## Direct source integration checkpoint

All four named-source checks completed with exit 0 and no warnings, using `lake --old env lean -j 1 -o ... <source>` and emitting the corresponding oleans:

- `FiniteHorizonPrimeRecurrence.lean`: `/tmp/bsu-100-prime-recurrence-leaf.log`.
- `FiniteHorizonOscillationEnergy.lean`: `/tmp/bsu-100-oscillation-energy-leaf.log`.
- `FiniteHorizonIntegerVariance.lean`: `/tmp/bsu-100-integer-variance-leaf.log`.
- `FiniteHorizonCoercivityWitness.lean`: `/tmp/bsu-100-coercivity-witness-leaf.log`.

All four are imported by the field umbrella; no umbrella or full build was run. Index regeneration passed (`/tmp/bsu-100-horizon-index.log`), source whitespace checks passed, and the field README hash remains `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275`. The final imported axiom audit passed with only `propext`, `Classical.choice`, `Quot.sound` for all four key declarations (`/tmp/bsu-100-horizon-final-axioms.log`). `scripts/formal_tools.py lint --check-generated` completed with exit 0 (`/tmp/bsu-100-horizon-lint.log`). This checkpoint certifies the witness implementation, not novelty or completion of the candidate package.

The five extracted scratch drafts were removed after the production source and imported axiom checks passed; their logs and search evidence remain. The active positive-bound draft `/tmp/bsu_100_binary_parent.lean` and imported audit `/tmp/bsu_100_horizon_final_axioms.lean` are retained. The broader Cauchy module-filtered phrase query also returned zero hits (`/tmp/bsu-100-cauchy-source-crosscheck.json`), so the source/toolchain check remains necessary.

The ancestor draft now passes the reciprocal-budget and pointwise weighted-Cauchy proofs, without warnings and with standard axioms (`/tmp/bsu-100-binary-parent-r2.log`). This also verified the Cauchy API missed by both search queries. A finite descendant-cardinality proof has been added to the same scratch file and is being checked. Summing the path bounds, comparing binary edges to the actual additive/dilation energies, and formalizing the sharp tent remain open. No positive-bound source has been promoted yet.

## Positive closure checkpoint and reuse of the cosine witness

The descendant-cardinality and full binary-parent window bound now pass without warnings and with standard axioms (`/tmp/bsu-100-binary-parent-r4.log`). The latter bounds the anchored square sum by `2*N` times binary-parent energy. The native-edge comparison and `6*N` bound are being checked after fixing an elaboration issue in the injectivity proof for `m ↦ 2*m`.

A second tent implementation is unnecessary for the sharp order. The already checked logarithmic cosine gives an explicit witness for **every** integer N≥1024, with joint doubling energy≤384 and square error about **every** center at least N/16. Here is the dependency-closed paper proof. Set M=floor(N/2), t=2π/log(2), and f(n)=cos(t*log(n)−t*log(2M)). The existing elementary bounds give 1≤t≤16. Exact resonance t*log(2)=2π makes every doubling difference zero. The proved additive estimate gives energy≤24t≤384. The integer variance theorem gives, for every center c, error on [1,2M] at least M*log(2)/2−2t≥M/4−32. Since M≥512 and N≤2M+1, this is at least N/16. Nonnegative extension from [1,2M] to [1,N] handles odd N without a missing endpoint. Consequently every valid variance coercivity constant is at least N/6144, while the positive bound is at most 6N. This proves the same sharp linear order, now on all sufficiently large windows. The tentative tent constant N/2048 is a separate, unformalized refinement and is not needed for this package's closure or counted separately.

The fresh deep query `/tmp/bsu-100-dyadic-tent-search.json` completed its requested stages. It also retrieves this session's newly integrated cosine-energy and integer-variance lemmas, so those hits must not be mistaken for independent prior work. Compiler coverage remains mostly pending/stale; inventory completeness is not semantic completeness. Its proposed Cayley-operator/conductor-specialization route does not establish integer doubling invariance and is not used.

`FiniteHorizonPositiveCoercivity.lean` passed its named-source check/export without warnings (`/tmp/bsu-100-positive-coercivity-leaf.log`). It includes `window_coercivity` for every K≥2. The all-N≥1024 cosine witness also passed without warnings and with standard axioms (`/tmp/bsu-100-doubling-sharpness-r1.log`). A follow-up scratch check assembles the positive bound, lower bound on every valid coercivity constant, and failure of a uniform constant for each fixed finite K.

The additional field-filtered query `/tmp/bsu-100-horizon-novelty-corpus.json` excluded the new `FiniteHorizon` modules. Its 20 candidate and 20 source inventories were inspected. All **198** lexical matches were then inventoried, with no module cap and offsets 20 through 180 (`/tmp/bsu-100-horizon-lexical-*.json`); the union has exactly 198 distinct declarations. This is exhaustive for that query, not for every equivalent theorem statement. The useful neighboring results concern physical dilation/trace defects, diffuse-kernel compact coercivity, divisor-grid closed range, and signed correlation energies. The exact native joint-energy source still supplies zero-energy rigidity rather than the new quantitative window bound. The field assessment and checklist were also read; their warnings against counting standard mechanisms remain applicable.

For external comparison, [Spielman's 2006 spectral-graph lecture](https://www.cs.yale.edu/homes/spielman/462/2006/lect5.pdf), sections 5.5–5.7, gives the complete-binary-tree gap bound and recalls planar-graph O(1/N) bounds. [Spielman–Teng's original planar-graph paper](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1996/CSD-96-898.pdf) proves O(1/N) Fiedler-value bounds for bounded-degree planar graphs. These are established neighboring mechanisms; linear scaling or a binary-tree comparison alone is not new. A precise reduction of the present graph, including boundary edges and multiplicities, has not been established by this literature check. The possible remaining novelty concerns the exact native finite-prime quantitative statement, not generic graph inequalities or nonexpansion. It remains uncounted.
