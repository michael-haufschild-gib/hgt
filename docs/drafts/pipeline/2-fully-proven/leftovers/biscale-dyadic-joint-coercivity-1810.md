# Adjacent and doubling differences: sharp linear deterioration

- **ID:** biscale-dyadic-joint-coercivity-1810
- **Stage:** 2-fully-proven; partial Lean coverage, remaining gates below
- **Type:** BRIDGE; elementary graph-energy comparison
- **Parent:** [field programme](../../1-in-progress/rh/bi-scale-uncertainty/biscale-field-development-1810.md), items 7 and 12

## Exact family and conclusion

For `h≥0`, put `N=2^(h+4)−1`. On the actual integer window `1,…,N`, define

`A(f)=Σ_(n=1)^(N−1) (f(n+1)−f(n))²`,

`D(f)=Σ_(n=1)^floor(N/2) (f(2n)−f(n))²`,

`V(f)=min_c Σ_(n=1)^N (f(n)−c)²`.

These are the existing additive energy and the multiplicative energy with cutoff `K=2`. The joint kernel is the constants. The best constant in `V≤C_N(A+D)` satisfies

`N/4096 ≤ C_N ≤ 24N`.

The lower constant is deliberately conservative; the sharp assertion is linear dependence on `N`. Additive energy alone requires a constant at least `N(N+1)/12`; doubling energy alone has a nonconstant null vector. Thus neither scale alone gives the same conclusion and parameter dependence.

## Upper bound by actual incidence

Use the complete binary tree on the same labels, with children `2n` and `2n+1`. Its energy `T` obeys

`T ≤ 3D+2A`.

Indeed, the even-child edges contribute exactly `D`. Each odd-child difference is the sum of its adjacent difference `f(2n+1)−f(2n)` and the doubling difference `f(2n)−f(n)`; squaring costs at most twice each square. Every used adjacent edge belongs to `A`.

For a root-to-vertex path, let `Δ_k` denote its edge difference at child depth `k≥1`. Weighted Cauchy–Schwarz gives

`(Σ_k Δ_k)² ≤ (Σ_k (3/4)^k)(Σ_k (4/3)^k Δ_k²) ≤ 4 Σ_k (4/3)^k Δ_k²`.

An edge at depth `k` has at most `2N/2^k` descendants. Summing the path bound over all vertices therefore charges that edge at most

`8N(2/3)^k ≤ 8N`.

Consequently `V(f)≤Σ_n(f(n)−f(1))²≤8NT≤24N(A+D)`. Descendant counts follow directly by summing the complete levels below the edge; no spectral computation is used.

## Matching family and single-scale failures

Write each positive integer uniquely as `n=2^k+j`, `0≤j<2^k`, and set

`f(n)=min(j,2^k−j)/2^k`.

Doubling sends `(k,j)` to `(k+1,2j)`, so `f(2n)=f(n)` and `D(f)=0`. Across a full level with `k≥1`, all consecutive differences, including the transition to the next level, have absolute value `2^(−k)`. Its additive energy is `2^(−k)`; the root level contributes zero. Omitting the final transition only decreases energy, hence `A(f)<2`.

In the last level, set `q=2^(h+3)`, so `N=2q−1` and `8∣q`. At least `q/2` entries have `f≥1/4`, using `q/4≤j≤3q/4`. At least `q/4` entries have `f≤1/8`, using `0≤j≤q/8` and `7q/8≤j<q`. For any real `c`, either `c≤3/16` and the first group lies at distance at least `1/16`, or `c≥3/16` and the second group does. Thus

`Σ_n(f(n)−c)² ≥ q/1024 ≥ N/2048`.

Together with `A+D≤2`, this gives `C_N≥N/4096`. The same nonconstant tent defeats coercivity to constants from `D` alone.

For the additive-only test `g(n)=n`, the exact variance is `N(N²−1)/12` and `A(g)=N−1`; their ratio is `N(N+1)/12`. The formulas follow from finite sums of first and second powers, without numerical evaluation.

## Audit and remaining gates

- Corpus query `adjacent doubling joint energy Poincare binary tree dyadic` returned dyadic packet, trace and energy identities, without this integer-window coercivity law among the returned declarations or source arguments. Coverage was a source snapshot with unmeasured semantic completeness. Existing zero-energy rigidity is insufficient for this bound.
- Binary-tree inverse spectral gaps of order `N` are classical: [Molitierno–Neumann–Shader, *Tight bounds on the algebraic connectivity of a balanced binary tree*](https://www2.math.ethz.ch/EMIS/journals/ELA/ela-articles/articles/vol6_pp62-71.pdf). The proof above is a direct weighted-path argument and does not treat the tree estimate as a novel principle.
- [x] Symbolic upper bound, explicit lower witness and single-scale comparisons.
- [ ] Formal exact integer-window models, all finite-sum/counting identities and unconditional conclusions for every `h`.
- [x] Explicit divisor-sieve realization of every finite window vector. Energy transport in the common model remains separate below.
- [x] Named-source and axiom audits, wiring, index and scoped lint. Global unrelated lint failures are recorded below.
- [ ] Perturbed-incidence theorem. Keeping adjacent-node energy is different from keeping the literal translation-by-one action on perturbed nodes.

This card does not yet close item 7 or item 12.

## Exact lower-bound formalization argument

Put `r=2^h`, so the last level starts at `8r` and `N=16r−1`.
For each `0≤j<r`, pair the distinct indices `8r+j` and `12r+j`.
Both blocks lie in `1,…,N` and are disjoint. The specified tent has values
`j/(8r)` and `(4r−j)/(8r)`, respectively. Their difference is at least
`1/4`. For every center `c`,

`(f(8r+j)−c)²+(f(12r+j)−c)² ≥ (f(12r+j)−f(8r+j))²/2 ≥ 1/32`.

Summing these disjoint pairs gives total variance at least `r/32`, hence
at least `N/2048`. This proves the exact stated bound without any lower
restriction on `h`; it uses the original tent, not a substituted witness.
The stronger intermediate estimate is a finite algebraic consequence, not
a separate novelty claim.

## Frozen Lean completion

The five started leaves passed the combined source and transitive axiom audit:
38 public declarations, using only `propext`, `Classical.choice`, `Quot.sound`.
All five final direct checks passed without diagnostics. Only Tent and
FiniteWindowVariance required new oleans, and both builds passed. Unique
umbrella imports and indexed names are verified; global lint has no diagnostic
for these leaves (20 unrelated errors and 417 size warnings).

| Exact claim | Canonical leaf and declaration |
|---|---|
| Original mantissa tent, doubling nullity, exact level increments and energy, `A<2` | `DyadicMantissaTent.lean`: `dyadicMantissaTent_two_mul`, `dyadicMantissaTent_full_level_energy`, `additiveStepEnergy_dyadicMantissaTent_lt_two` |
| Exact linear variance and additive-only lower constant | `IntegerLinearVariance.lean`: `sum_Icc_linear_centered_sq`, `additive_coercivity_constant_linear_lower_bound` |
| Actual finitely supported Möbius coefficients realizing every finite window | `FiniteSieveRealization.lean`: `exists_finite_sieveSeq_realization` |
| Mean minimizes centered energy; the infimum coercivity constant is attained | `FiniteWindowVariance.lean`: `integerWindowVariance_le_centered`, `windowCoercivityBound_sInf` |
| Original tent variance, `N/4096≤C_N≤24N`, and validity of the best constant | `DyadicMantissaVariance.lean`: `dyadicMantissaTent_variance_lower`, `dyadicWindowBestConstant_bounds`, `dyadicWindowBestConstant_valid` |

These names use `GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon`.
The existing owner `FiniteHorizonPositiveCoercivity.lean` also contains the
exact comparison `binary_energy_le_doubling_additive`; its final source check
and the axiom audit of it and both downstream coercivity theorems passed
without diagnostics. Its existing olean was preserved. The existing
unconditional window bound supplies the upper estimate.

This remains a partial card: the paper's separate weighted-path and descendant
counts, explicit high/low level counts, standalone doubling-only failure
statement, and transport of all energies through the common arithmetic model
are not claimed as separately formalized. The paired-block proof above
formalizes the exact advertised lower conclusion. Perturbed weights and node
geometry are recorded on the companion card. The resumed formalization is
active: exact path/depth estimates, high/low counts, doubling-only failure,
and common-model energy transport are drafted and undergoing individual
source and axiom checks. Current evidence and pending checks are tracked in
[the full programme](../../1-in-progress/leftovers-unconditional-formalization.md).

Evidence: `/tmp/leftovers-dyadic-perturbed-public-names.json` and
`/tmp/leftovers-dyadic-perturbed-audit-r2.log` (62 declarations across both cards).

## Final source checks for the started scope

Every row passed a direct `lake --old env lean -j 1` source check from `formal/`.
The exact tree comparison and both downstream coercivity statements additionally
passed their three-name axiom audit. No existing olean or umbrella was rebuilt.

| Leaf | SHA-256 | Final direct-check log |
|---|---|---|
| `DyadicMantissaTent` | `acd4ef93ae199c3bfdc4e6540eed9ebe32769291c998de416af1b8439ffe818d` | `/tmp/leftovers-dyadic-tent-final.log` |
| `IntegerLinearVariance` | `0dccb554cd2563d43ee770a701736e7586811a933fbdb2e79f016b3dcf2ede7f` | `/tmp/leftovers-integer-variance-final.log` |
| `FiniteSieveRealization` | `c85efe0fc79eaf2434177cbae0b675d37fec3f57fd5ff2dfed9824148003eb63` | `/tmp/leftovers-sieve-realization-final.log` |
| `FiniteWindowVariance` | `ba0f8560596f92637b3e65800bf17b0d66efe28917622790dd31b64ca25d4584` | `/tmp/leftovers-window-variance-final.log` |
| `DyadicMantissaVariance` | `49d335546715ac9f0d11e1eb737e667d7e8e6f4880f795fa209375beb97f4d7a` | `/tmp/leftovers-dyadic-variance-final.log` |
| `FiniteHorizonPositiveCoercivity` | `847fc32a9a136cc3409d44fcb46256aec6cbd53dff642eec224837ef21be2dc6` | `/tmp/leftovers-tree-owner-final.log` |
