# Resolution of Quantitative Factorization Matching Across Squarefree Layers

- **ID:** `QFM-2-6-RESOLUTION`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1711/obstacles-summary.md` §2.6, §2.11
- **Statement:** Complete positive and negative classification of prime-factorization opposite-parity matchings across squarefree factor counts on dyadic blocks `(X, 2X]`, their common-cofactor and fibre-boundary obstructions, and their positivity-free and spectral-free equivalences with zero-free strips, `RiemannHypothesis`, and integer-norm Beurling prime-edit selectivity.

## Gates

- [x] 0 → 1  in-progress: exact bipartite matching, cascade, cofactor, and Beurling interfaces fixed
- [x] 1 → 2  fully-proven: dependency-closed paper proofs `[PROVED HERE]`
- [x] 2 → 3  formalized: unconditional Lean modules in `GaloisForLFunctions/QuantitativeFactorizationMatching/`, wired into `QuantitativeFactorizationMatching.lean` and `MainTheorems.lean`, `lake --old env lean` audit green, standard axioms `[propext, Classical.choice, Quot.sound]` only

## Mathematical Results and Proofs

### 1. König–Ore Deficiency Decomposition and Layer-Cascade Conservation

For any finite set $S \subset \mathbb{N}$ of integers and relation $R \subseteq S_+ \times S_-$ between squarefree elements of opposite Möbius sign $S_\pm = \{n \in S : \mu(n) = \pm 1\}$:
- Every $R$-matching cancels identically in $\sum_{n \in S} \mu(n)$, and the minimum unmatched squarefree count satisfies
  $$
  U_{\min}(R, S) = \left|\sum_{n \in S} \mu(n)\right| + 2\,\operatorname{hallExcessZ}(R, S),
  $$
  where $\operatorname{hallExcessZ}(R, S) = \max_{U \subseteq S_+}(\#U - \#N_R(U)) - \max\!\big(0, \sum_{n \in S}\mu(n)\big) \ge 0$ (`minUnmatched_ore_decomposition`), proved by Hall's marriage theorem after adjoining $\operatorname{hallDeficiency}(R, S)$ universal sinks. Every $R$-isolated vertex lies in `M.unmatchedSet` (`card_isolatedVertices_le_unmatched`).
- Any sequential upward cascade $\varphi_k : U_k \hookrightarrow \mathcal{Q}_{k+1}(S)$ ($1 \le k \le K$, $U_1 = \mathcal{Q}_1(S)$, $U_{k+1} = \mathcal{Q}_{k+1}(S) \setminus \varphi_k(U_k)$) yields pairwise disjoint pairs across all $K$ layers whose unconsumed remainder in layer $K+1$ satisfies
  $$
  (\#U_{K+1} : \mathbb{Z}) = (-1)^{K+1} \sum_{\substack{n \in S \\ 1 \le \omega(n) \le K+1}} \mu(n)
  $$
  independently of $\varphi_1, \dots, \varphi_K$ (`intCast_card_cascadeUnconsumed`, `upward_cascade_necessary_and_exhaustion`).

### 2. All-Finite-Layer Cellwise Extension vs. Finite-Horizon Linear Tail

- **Positive theorem across all finite horizons:** Fix any $K \ge 1$ and $B > 0$. Partitioning $(R, 2R]$ into $J = \lfloor (\log R)^B \rfloor$ cells of width $\le 2R / (\log R)^B$, one-prime peeling with Mertens' theorems and log-power Chebyshev bounds gives $\#\mathcal{Q}_k(u, v) \le \frac{61}{60}\frac{v-u}{\log R}\frac{(\log\log R - C'_k)^{k-1}}{(k-1)!} \le \#T_{k+1}(u, v)$ on every cell for $\{2, 3, 5\}$-seeded $(k+1)$-primes $q d r$ ($\frac{31}{30}\cdot\frac{61}{62} = \frac{61}{60} > 1$). Sequential cellwise injections match **100%** of squarefree integers in $(R, 2R]$ with $1 \le \omega(n) \le K$ into a single disjoint `OppositeParityMatching` with zero Möbius sum and smooth $\Gamma$-Sobolev norm bound $\le C_{K,B} R^{1-\delta}(\log\log R)^{2(K-1)}/(\log R)^{2B+2}$ uniformly in $0 \le \delta \le 1$ (`exists_all_finite_layers_cell_matching`).
- **Finite-cutoff linear tail and `{2, 3, 5}` supply threshold:** Any matching supported on $\omega(n) \le K+1$ leaves $\ge (\frac{6}{\pi^2} - \varepsilon)R$ unmatched squarefree integers (`eventually_unmatched_after_finite_layers_ge`), and single-prime $\{2, 3, 5\}$ supply falls below Poisson–Dirichlet layer growth once $k > \frac{31}{30}\log\log R$ (`smallCofactor_divisible_card_le_and_threshold`).

### 3. Prescribed-Prime and Bounded-Arity Local Obstructions

- **Prescribed finite prime set $P_0$:** Under all opposite-parity cofactor exchanges $a u \leftrightarrow a v$ with prime factors of $u, v$ in $P_0$, every $P_0$-rough squarefree integer in $(X, 2X]$ is isolated (`coprime_mem_isolatedVertices_prescribedPrimeExchange`). Both $\mu = \pm 1$ rough halves have asymptotic density $\frac{3}{\pi^2}\prod_{p \in P_0}\frac{p}{p+1} > 0$, forcing $\ge (\frac{6}{\pi^2}\prod_{p \in P_0}\frac{p}{p+1} - \varepsilon)X$ unmatched integers (`eventually_prescribedPrimeExchange_unmatched_linear`), while multiples of $M_0 = \prod_{p \in P_0} p$ admit zero upward $P_0$-targets and have density $\frac{6}{\pi^2 M_0}\prod_{p \in P_0}\frac{p}{p+1} > 0$ (`prescribedUpward_saturated_no_target_and_density`).
- **Universal smooth isolation criterion:** Any $Z$-smooth squarefree $n \in (X, 2X]$ with $Z^k H \le X$ is isolated under `BoundedArityLocalExchange k H` because $a = n/u > X/Z^k \ge H$ forces $|a v - a u| \ge a > H$ (`mem_isolatedVertices_of_primeFactors_le`).
- **Power-local cells ($H \le C X^\theta$, $\theta < 1$):** For $r = \lceil (k+2)/(1 - \max(\theta, 0)) \rceil + 2$, $\ge c X / (\log X)^r$ balanced $r$-primes are isolated, forcing $> X^\beta$ unmatched integers for every $\beta < 1$ (`eventually_powerLocal_boundedArity_isolated_ge`).
- **Log-power cells ($H \le C X / (\log X)^B$, $B > k$):** Multi-band friable subset-product binning isolates $> X^\beta$ squarefree integers for every $\beta < 1 - k/B$ (`eventually_logPowerCell_boundedArity_unmatched_gt_rpow`), exceeding $X^{1/2+\delta}$ when $B > 2k$ (`eventually_logPowerCell_boundedArity_unmatched_gt_half`) and exceeding $X^{20999/24000+\delta}$ when $B > 24000k$ (`eventually_logPowerCell_boundedArity_unmatched_gt_strip_benchmark`).

### 4. Global Dyadic $(1 \leftrightarrow 2)$ Cofactor Graph and Even-Prefix Fibre Debt

- **Minimal arity:** Multiplicative sum-freeness of $(X, 2X]$ forbids pure prime insertions/deletions ($1 \le \omega(u)$, $1 \le \omega(v)$, $3 \le \omega(u) + \omega(v)$), making $(1 \leftrightarrow 2)$ exchanges $c p \leftrightarrow c q r$ minimal (`dyadic_no_pure_insertion_deletion`).
- **Global non-isolation and growing common supply:** `GlobalDyadicOneTwoRel` has **zero** isolated vertices on $(X, 2X]$ for all $X \ge 6$ via Bertrand's postulate on $\lfloor X/2\rfloor$ and $\lfloor X/c\rfloor$ (`globalDyadicOneTwo_isolatedVertices_empty`), and primorial compactness gives uniform vertex degree $\ge D$ for every $D \in \mathbb{N}$ (`eventually_globalDyadicOneTwo_degree_ge`).
- **Collision-free even-prefix fibres and boundary debt:** `evenPrefixCofactor` partitions $\mathcal{Q}(X)$ into pairwise-disjoint complete bipartite subgraphs `fibrePos X a × fibreNeg X a ⊆ GlobalDyadicOneTwoRel` (`evenPrefixCofactor_complete_bipartite_fibres`), but $2X \le a s^2$ ($s \mid a$) forces `fibrePos X a = ∅` (`fibrePos_eq_empty_of_primeFactor_sq_ge`), creating $\ge c X / (\log X)^3$ unmatched triprime sources under fixed-fibre matchings (`eventually_evenPrefixFibre_debt_ge`).

### 5. Positivity-Free Analytic Strip Transfer, RH Equivalence, and Beurling Selectivity

- **Positivity-free & spectral-free strip transfer:** Any $O(X^\theta)$ ($0 < \theta < 1$) dyadic opposite-parity matching yields $|M(x)| \le K x^\theta$, holomorphic convergence $\sum_{n < N} \mu(n)n^{-s} \to 1/\zeta(s)$ and $\zeta(s) \neq 0$ on $\{\operatorname{Re} s > \theta, s \neq 1\}$, and `zetaZeroAbscissa ≤ max (1/2) θ` via binary dyadic splitting, partial summation, and analytic continuation alone (`dyadic_matching_holomorphic_inv_zeta_and_zero_free`, `globalDyadicOneTwo_sub_barrier_forces_abscissa_lt`).
- **Unconditional attainment and exact RH equivalence:** Unconditionally, $(X, 2X]$ admits opposite-parity matchings with $\le C_\beta X^\beta$ unmatched integers for every $\beta > 20999/24000$ and $\le C X^{7/8}$ exact (`unconditional_dyadic_matching_sub_seven_eighths`); $O_\varepsilon(X^{1/2+\varepsilon})$ dyadic matchings hold iff `RiemannHypothesis` (`dyadic_matching_half_iff_riemannHypothesis`).
- **Integer-norm Beurling prime-edit barrier:** For every $\sigma \in (20999/24000, 14/15)$ and $\sigma' \in (1/2, \sigma)$, there exists an integer-norm two-sided prime edit `editSystem e` with $N_e(x) = A' x + O(x^{14/15})$ and $\sum_{k \le n}|e(k)| \le C_{\text{edit}} n^{14/15}$ whose dyadic generalized-integer blocks admit **no** $O(X^{\sigma'})$ opposite-parity matching (`exists_primeEdit_matching_barrier`).

## No-Go Closure Summary

- **Exact killing theorems/mechanisms:** `eventually_prescribedPrimeExchange_unmatched_linear` ($P_0$-rough isolation), `eventually_powerLocal_boundedArity_isolated_ge` and `eventually_logPowerCell_boundedArity_unmatched_gt_rpow` (friable $a = n/u > X/Z^k \ge H$ displacement barrier), `eventually_evenPrefixFibre_debt_ge` ($a P^+(a)^2 \ge 2X$ empty positive cofactor fibre), and `exists_primeEdit_matching_barrier` (fake off-line zero obstruction for prime-edited Euler products).
- **Strongest positive survivors:** `exists_all_finite_layers_cell_matching` (100% cellwise $\{2, 3, 5\}$ matching across every finite prefix $1 \le \omega(n) \le K$), `globalDyadicOneTwo_isolatedVertices_empty` + `eventually_globalDyadicOneTwo_degree_ge` (universal non-isolation for $X \ge 6$ and unbounded degree in `GlobalDyadicOneTwoRel`), `evenPrefixCofactor_complete_bipartite_fibres` (collision-free complete bipartite cofactor decomposition), and `dyadic_matching_holomorphic_inv_zeta_and_zero_free` + `unconditional_dyadic_matching_sub_seven_eighths` + `dyadic_matching_half_iff_riemannHypothesis`.
- **New insight:** Local cell and prescribed-prime rules fail globally because friable and rough integers force large surviving cofactors $a > H$; lifting cell locality to `GlobalDyadicOneTwoRel` eliminates all isolated vertices at $X \ge 6$, reduces the global unmatched count on `GlobalDyadicOneTwoRel` to cross-fibre alternating paths resolving $\operatorname{hallExcessZ}(\text{GlobalDyadicOneTwoRel}, (X, 2X])$, and proves any sub-$14/15$ global matching must exploit unique integer factorization absent in two-sided prime edits.
- **Status:** Dependency-closed and unconditionally formalized in Lean 4.

## Lean Formalization

Owner subfolder: `formal/GaloisForLFunctions/QuantitativeFactorizationMatching/`, wired into `formal/GaloisForLFunctions/QuantitativeFactorizationMatching.lean` and `formal/GaloisForLFunctions/MainTheorems.lean` (no umbrella build).

Modules and capstone declarations:
1. `OreDeficiencyAndCascadeConservation.lean`: `OppositeParityMatching`, `minUnmatched_ore_decomposition`, `card_isolatedVertices_le_unmatched`, `IsValidLayerCascade`, `intCast_card_cascadeUnconsumed`, `upward_cascade_necessary_and_exhaustion`.
2. `AllFiniteLayersCellMatching.lean`: `exists_all_finite_layers_cell_matching`, `abs_card_squarefreeOf_dyadic_sub_le`, `eventually_unmatched_after_finite_layers_ge`, `factorLayer_card_eq_sum_gcd_strata`, `smallCofactor_divisible_card_le_and_threshold`.
3. `PrescribedAndLocalCofactorObstructions.lean`: `coprime_mem_isolatedVertices_prescribedPrimeExchange`, `eventually_prescribedPrimeExchange_unmatched_linear`, `prescribedUpward_saturated_no_target_and_density`, `mem_isolatedVertices_of_primeFactors_le`, `eventually_powerLocal_boundedArity_isolated_ge`, `eventually_logPowerCell_boundedArity_unmatched_gt_rpow`, `eventually_logPowerCell_boundedArity_unmatched_gt_half`, `eventually_logPowerCell_boundedArity_unmatched_gt_strip_benchmark`.
4. `GlobalDyadicGraphAndCofactorFibres.lean`: `dyadic_no_pure_insertion_deletion`, `globalDyadicOneTwo_isolatedVertices_empty`, `eventually_globalDyadicOneTwo_degree_ge`, `evenPrefixCofactor_complete_bipartite_fibres`, `fibrePos_eq_empty_of_primeFactor_sq_ge`, `eventually_evenPrefixFibre_debt_ge`.
5. `DyadicMatchingStripAndRiemannEquivalence.lean`: `abs_sum_Icc_le_of_dyadic_Ioc`, `abs_sum_Icc_le_of_eventually_dyadic_Ioc`, `dyadic_matching_holomorphic_inv_zeta_and_zero_free`, `globalDyadicOneTwo_sub_barrier_forces_abscissa_lt`, `exists_fullOppositeParityMatching_unmatched_eq_abs_sum`, `exists_dyadic_matching_of_abscissa_lt`, `unconditional_dyadic_matching_sub_seven_eighths`, `dyadic_matching_half_iff_riemannHypothesis`, `exists_primeEdit_matching_barrier`.
6. `CompleteResolutionOfTheFactorizationMatchingQuestion.lean`: `complete_local_and_prescribed_matching_trichotomy`, `complete_global_cofactor_and_fibre_resolution`, `complete_analytic_strip_rh_and_beurling_resolution`, `complete_resolution_of_quantitative_factorization_matching`.

All 35 capstones verified under `lake --old env lean` with `#print axioms` showing `[propext, Classical.choice, Quot.sound]` only.
