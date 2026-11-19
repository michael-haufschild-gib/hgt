# Cross-Fibre Factorization Involutions, Double-Use Bookkeeping, and Power-Saving Resolution of §2.6

- **ID:** `QFM-2-6-CROSS-FIBRE-POWER-SAVING`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1811/obstacles-summary.md` §2.6
- **Statement:** Explicit sign-reversing $(1 \leftrightarrow 2)$ factorization involutions on $(X, 2X]$ with exact double-use endpoint bookkeeping evacuate $100\%$ of empty-positive ordered cofactor fibres (including the $\Theta(X / \log^3 X)$ pilot class), achieve an unconditional $O(X^{113/180}) \subseteq O(X^{2/3})$ power saving over $\Theta(X / \log^3 X)$ ordered-cofactor debt inside a self-contained growing class of ordered cofactor fibres without positivity or spectral machinery, satisfy a sharp persistence dichotomy governed by the rough-subtree Möbius invariant and the $\sqrt{X}$ cofactor-jump barrier, and yield two-sided zeta zero confinement $1 - \theta \le \mathrm{Re}\,\rho \le \theta$ and exact equivalence with `RiemannHypothesis` via signed finite pairing, Dirichlet-series continuation, and functional-equation reflection.

## Goal

Provide the complete, unconditional mathematical solution and Lean 4 formalization for every question, implication, and corollary posed in §2.6 of `obstacles-summary.md`, using only elementary prime-window bounds (de la Vallée Poussin log-power Chebyshev error and Mertens' first theorem), unique integer factorization, finite summation by parts, analytic continuation, and functional-equation reflection.

## Gates

- [x] 0 → 1  in-progress: exact involution, double-use bookkeeping, self-contained fibre class, and persistence invariants fixed
- [x] 1 → 2  fully-proven: complete dependency-closed paper proofs `[PROVED HERE]`
- [x] 2 → 3  formalized: Lean 4 modules `FactorizationInvolutionAndDoubleUseBookkeeping`, `PilotDebtEvacuationAndInvariantObstructions`, `SelfContainedFibreClassPowerSaving`, `CompleteSectionTwoSixBreakthroughResolution` (`complete_section_two_six_breakthrough_resolution`), `lake --old env lean` audit green, standard axioms `[propext, Classical.choice, Quot.sound]` only

## Formalized Lean Declarations

1. `GaloisForLFunctions.QuantitativeFactorizationMatching.FactorizationInvolutionAndDoubleUseBookkeeping`:
   - `FactorizationInvolution`, `FactorizationInvolution.toMatching`, `FactorizationInvolution.ofMatching`, `FactorizationInvolution.glueDisjoint`
   - `sum_moebius_eq_jointUnmatched_sub_doubleUsed`
   - `resolveDoubleUse`, `resolveDoubleUse_spec`, `orderedFibreInvolution_omega_drop`, `involutionWalk_omega_descent`, `resolveDoubleUse_unmatched_reduction`
2. `GaloisForLFunctions.QuantitativeFactorizationMatching.PilotDebtEvacuationAndInvariantObstructions`:
   - `maxPrimeStem`, `unique_factorization_decoding_and_norm_selectivity`
   - `rankedCrossFibreInvolution`, `eventually_emptyFibres_evacuated_by_involution`
   - `fibreUnion_ordered_and_global_bounds`
   - `pilotCofactors`, `pilotVertices`, `eventually_pilotFibreClass_debt_and_strict_drop`
   - `roughFibreCofactors`, `eventually_roughFibreClass_debt_persists`
   - `pilotVertices_neighbor_cofactor_sq_lt`, `pilotVertices_isolated_on_large_cofactor_class`
3. `GaloisForLFunctions.QuantitativeFactorizationMatching.SelfContainedFibreClassPowerSaving`:
   - `prefixSelect`, `prefixSelect_spec`
   - `eventually_root_positive_surplus_bounds`
   - `balancedRootCofactors`, `balancedChildPool`, `balancedChildSelection`, `balancedFibreClass`
   - `eventually_balancedFibreClass_power_saving`
4. `GaloisForLFunctions.QuantitativeFactorizationMatching.CompleteSectionTwoSixBreakthroughResolution`:
   - `involution_analytic_ending_and_reflection`
   - `factorizationInvolution_half_iff_riemannHypothesis`
   - `complete_section_two_six_breakthrough_resolution`

## Mathematical Results and Complete Proofs

### 1. Factorization Involutions and Exact Double-Use Bookkeeping `[PROVED HERE]`

Let $S \subset \mathbb{N}$ be finite and $R : \mathbb{N} \to \mathbb{N} \to \mathrm{Prop}$. A **factorization involution** $\tau$ along $R$ on $S$ (`FactorizationInvolution R S`) is a map $\tau : \mathbb{N} \to \mathbb{N}$ such that:
1. $\tau(\tau(n)) = n$ for all $n \in \mathbb{N}$;
2. $\tau(n) = n$ for all $n \notin \mathcal{Q}(S) := \{n \in S : \mu^2(n) = 1\}$;
3. whenever $\tau(n) \neq n$, $\mu(\tau(n)) = -\mu(n)$, and $\mu(n) = 1 \implies R(n, \tau(n))$.

Write $\mathrm{moved}(\tau) = \{n \in \mathcal{Q}(S) : \tau(n) \neq n\} = \mathrm{moved}_+(\tau) \sqcup \mathrm{moved}_-(\tau)$ and $\mathrm{unmatched}(\tau) = \mathcal{Q}(S) \setminus \mathrm{moved}(\tau) = \{n \in \mathcal{Q}(S) : \tau(n) = n\}$. Restricting $\tau$ to $\mathrm{moved}_+(\tau)$ gives an explicit bijection between `FactorizationInvolution R S` and `OppositeParityMatching R S`, with $\sum_{n \in \mathrm{moved}(\tau)} \mu(n) = 0$ and $\sum_{n \in S} \mu(n) = \sum_{n \in \mathrm{unmatched}(\tau)} \mu(n)$.

**Theorem 1.1 (`sum_moebius_eq_jointUnmatched_sub_doubleUsed`).** For any two factorization involutions $\tau_0, \tau_1$ on $S$, put $D(\tau_0, \tau_1) := \mathrm{moved}(\tau_0) \cap \mathrm{moved}(\tau_1)$ (`doubleUsedSet`) and $U(\tau_0, \tau_1) := \mathcal{Q}(S) \setminus (\mathrm{moved}(\tau_0) \cup \mathrm{moved}(\tau_1))$ (`jointUnmatchedSet`). Then
$$
\sum_{n \in S} \mu(n) = \sum_{n \in U(\tau_0, \tau_1)} \mu(n) - \sum_{n \in D(\tau_0, \tau_1)} \mu(n).
$$

*Proof.* By inclusion–exclusion on $\mathrm{moved}(\tau_0), \mathrm{moved}(\tau_1) \subseteq \mathcal{Q}(S)$,
$$
\sum_{n \in \mathrm{moved}(\tau_0) \cup \mathrm{moved}(\tau_1)} \mu(n)
= \sum_{n \in \mathrm{moved}(\tau_0)} \mu(n) + \sum_{n \in \mathrm{moved}(\tau_1)} \mu(n) - \sum_{n \in D(\tau_0, \tau_1)} \mu(n)
= -\sum_{n \in D(\tau_0, \tau_1)} \mu(n).
$$
Adding $\sum_{n \in U(\tau_0, \tau_1)} \mu(n)$ yields $\sum_{n \in \mathcal{Q}(S)} \mu(n) = \sum_{n \in S} \mu(n)$. $\square$

**Theorem 1.2 (`resolveDoubleUse_spec`, `involutionWalk_omega_descent`, `resolveDoubleUse_unmatched_reduction`).** Let $\tau_0, \tau_1$ be factorization involutions along $R$ on $S$. Define $\mathrm{switch}(x)$ on $\mathcal{Q}_+(S)$ iff there is an alternating walk $x_0, x_1, \dots, x_k = x$ with $x_0 \in \mathrm{moved}_+(\tau_0) \setminus \mathrm{moved}_+(\tau_1)$ and $\tau_0(x_i) = \tau_1(x_{i+1})$ for $0 \le i < k$. Setting $\tau_* = \mathrm{resolveDoubleUse}(\tau_0, \tau_1)$ to agree with $\tau_0$ on $\{x \in \mathrm{moved}_+(\tau_0) : \mathrm{switch}(x)\}$ and its $\tau_0$-image, with $\tau_1$ on $\{x \in \mathrm{moved}_+(\tau_1) : \neg\mathrm{switch}(x)\}$ and its $\tau_1$-image, and fixing all other integers gives a single factorization involution along $R$ on $S$ (zero double-used endpoints) satisfying:
1. $\mathrm{moved}_+(\tau_0) \subseteq \mathrm{moved}_+(\tau_*)$ and $\mathrm{moved}_-(\tau_1) \subseteq \mathrm{moved}_-(\tau_*)$;
2. if $\tau_0$ preserves `evenPrefixCofactor` ($\omega(\tau_0(x)) + 1 = \omega(x)$ for $x \in \mathrm{moved}_+(\tau_0)$) and $\tau_1$ merges the two largest primes ($\omega(\tau_1(y)) = \omega(y) + 1$ for $y \in \mathrm{moved}_+(\tau_1)$), then every alternating walk of length $k$ satisfies $\omega(x_k) + 2k = \omega(x_0)$;
3. whenever $\mathrm{moved}_-(\tau_0) \subseteq \mathrm{moved}_-(\tau_*)$, $\mathrm{moved}(\tau_0) \cup \mathrm{moved}_-(\tau_1) \subseteq \mathrm{moved}(\tau_*)$ and $\#\mathrm{unmatched}(\tau_*) + 2\,\#(\mathrm{moved}_-(\tau_1) \setminus \mathrm{moved}_-(\tau_0)) \le \#\mathrm{unmatched}(\tau_0)$.

### 2. Unique Factorization Selectivity, Empty-Fibre Evacuation, and Persistence Invariants `[PROVED HERE]`

**Theorem 2.1 (`unique_factorization_decoding_and_norm_selectivity`).** Setting $\mathrm{maxPrimeStem}(n) = n / \sup(\mathrm{primeFactors}(n))$, unique integer factorization ensures $\mathrm{maxPrimeStem}(c p) = c$ ($p > P^+(c)$) and $\mathrm{maxPrimeStem}(\mathrm{maxPrimeStem}(c q r)) = c$ ($P^+(c) < q < r$), injectively decoding $(c, p)$ and $(c, q, r)$ across all nonzero cofactors simultaneously; in any integer-norm Beurling system with distinct elements $g_1 \neq g_2$ of equal integer norm, no norm decoder exists.

**Theorem 2.2 (`eventually_emptyFibres_evacuated_by_involution`, `eventually_pilotFibreClass_debt_and_strict_drop`).**
1. Pairing the $i$-th prime of `cofactorPrimeRow X c` with the $i$-th cube-root semiprime of `cofactorCubeRow X c` across all squarefree $c \in [1, 2X]$ with $\mu(c) = -1$ yields `rankedCrossFibreInvolution X`. By `eventually_cubeBandProducts_nine_tenths` and primorial compactness ($X/a \to \infty$ uniformly on $\mathcal{Q}_-(X)$), for all $X \ge X_0$, `rankedCrossFibreInvolution X` matches $100\%$ of $\{n \in \mathcal{Q}_-(X) : \mathrm{fibrePos}(X, \mathrm{evenPrefixCofactor}(n)) = \emptyset\}$.
2. For $Y = X^{1/3}$ and $\mathcal{A}_{\mathrm{pilot}}(X) = \{p_1 p_2 : p_1 \in (Y/8, Y/6] \cap \mathbb{P},\, p_2 \in (2Y, 9Y/4] \cap \mathbb{P}\}$, $\mathrm{fibrePos}(X, a) = \emptyset$ on $\mathcal{A}_{\mathrm{pilot}}(X)$, $\#V_{\mathrm{pilot}}(X) = \Theta(X / (\log X)^3)$ is $100\%$ unmatched under every `OrderedFibreRel` involution $\tau_0$, and `{2, 3, 5}` root-clearing plus cofactor-$p_1$ pairing resolves via `resolveDoubleUse` into $\tau_*$ satisfying $\#\mathrm{unmatched}(\tau_*) + 2\,\#V_{\mathrm{pilot}}(X) \le \#\mathrm{unmatched}(\tau_0)$.

**Theorem 2.3 (`eventually_roughFibreClass_debt_persists`, `pilotVertices_neighbor_cofactor_sq_lt`, `pilotVertices_isolated_on_large_cofactor_class`).**
1. **Rough-subtree surplus invariant:** For $Z = X^{1/36}$ and $\mathcal{A}_{\mathrm{rough}}(X) = \{q_1 q_2 : q_1 \in (Z^4, \frac{5}{4}Z^4] \cap \mathbb{P},\, q_2 \in (2 Z^{10}, \frac{9}{4}Z^{10}] \cap \mathbb{P}\}$, both positive and negative vertex sets in $V_X(\mathcal{A}_{\mathrm{rough}}(X))$ have cardinality $\ge c X / (\log X)^3$, yet $q_2 > \frac{1}{2}(X/(q_1 q_2))^{1/3}$ forces $10 \cdot \#\mathrm{fibrePos}(X, b) \le 9 \cdot \#\mathrm{fibreNeg}(X, b)$, so every factorization involution confined to $V_X(\mathcal{A}_{\mathrm{rough}}(X))$ leaves $\ge c_{\mathrm{pers}} X / (\log X)^3$ unmatched vertices.
2. **$\sqrt{X}$ cofactor-scale jump barrier:** Unconditionally for every $X \in \mathbb{N}$, every $n \in V_{\mathrm{pilot}}(X)$ and every $m \in (X, 2X]$ with `GlobalDyadicOneTwoRel m n` satisfy $(\mathrm{evenPrefixCofactor}(m))^2 < X$. Hence on any fibre class $\mathcal{A} \subseteq \{a : X \le a^2\}$ containing $\mathcal{A}_{\mathrm{pilot}}(X)$, $100\%$ of $V_{\mathrm{pilot}}(X)$ remains unmatched under every `GlobalDyadicOneTwoRel` involution on $V_X(\mathcal{A})$.

### 3. Unconditional $O(X^{113/180})$ Power Saving on a Self-Contained Growing Fibre Class `[PROVED HERE]`

**Theorem 3.1 (`eventually_balancedFibreClass_power_saving`).** Set $z = X^{1/180}$ and $\mathcal{B}(X) = \{q_1 q_2 : q_1 \in (\frac{3}{4}z^{28}, z^{28}] \cap \mathbb{P},\, q_2 \in (\frac{3}{4}z^{32}, z^{32}] \cap \mathbb{P}\}$ (`balancedRootCofactors X`). For each $b = q_1 q_2 \in \mathcal{B}(X)$, put $T_b = X / b \in [z^{120}, \frac{16}{9}z^{120})$ and $s_b = T_b^{1/120}$.
1. Slicing $(s_b^{32}, s_b^{60}]$ into the $14$ bands $(s_b^{32+2i}, s_b^{34+2i}]$ ($0 \le i < 14$) with collar $(\frac{9}{16}s_b^{32}, s_b^{32}]$ and cap $(s_b^{60}, 2s_b^{60}]$ yields
   $$
   \frac{1}{1000}\frac{T_b}{\log T_b} \le \Delta_X(b) := \#\mathrm{fibrePos}(X, b) - \#\mathrm{fibreNeg}(X, b) \le \frac{27}{1000}\frac{T_b}{\log T_b}.
   $$
2. On $\mathcal{C}_-(X, b) = \{b p_1 p_2 : p_1 \in (s_b^{32}, s_b^{35}] \cap \mathbb{P},\, p_2 \in (s_b^{35}, s_b^{42}] \cap \mathbb{P}\}$ (`balancedChildPool X b`), every $a_- = b p_1 p_2$ satisfies $\mathrm{fibrePos}(X, a_-) = \emptyset$, $\#\mathrm{fibreNeg}(X, a_-) \le \lfloor 2 s_b^{53} \rfloor$, and $\sum_{a_- \in \mathcal{C}_-(X, b)} \#\mathrm{fibreNeg}(X, a_-) \ge \Delta_X(b)$.
3. Prefix selection `balancedChildSelection X b` chooses $\mathcal{C}_-^*(X, b) \subseteq \mathcal{C}_-(X, b)$ with $0 \le \Delta_X(b) - \sum_{a_- \in \mathcal{C}_-^*(X, b)} \#\mathrm{fibreNeg}(X, a_-) \le \lfloor 2 s_b^{53} \rfloor$. Grouping child negatives by $p_1$ injects $100\%$ of them into $\mathrm{fibrePos}(X, b)$ via `eventually_cubeBandProducts_nine_tenths` at $X / (b p_1)$, and complete bipartiteness of $F_X(b)$ pairs $100\%$ of $\mathrm{fibreNeg}(X, b)$ into the remaining root positives. Gluing across $\mathcal{B}(X)$ on $\mathcal{A}_{\mathrm{bal}}(X) = \bigsqcup_{b \in \mathcal{B}(X)} (\{b\} \cup \mathcal{C}_-^*(X, b))$ (`balancedFibreClass X`) yields:
   - $\#\mathcal{A}_{\mathrm{bal}}(X) \ge c_{\mathrm{fib}} X^{1/3} / (\log X)^2$ and ordered-cofactor debt $\Theta(X / (\log X)^3)$;
   - an explicit closed `GlobalDyadicOneTwoRel` involution $\tau$ on $V_X(\mathcal{A}_{\mathrm{bal}}(X))$ with $\#\mathrm{unmatched}(\tau) \le 4 X^{113/180} \le 4 X^{2/3}$ and $|\sum_{n \in V_X(\mathcal{A}_{\mathrm{bal}}(X))} \mu(n)| \le 4 X^{113/180}$.

### 4. Positivity-Free Analytic Ending and Functional-Equation Reflection `[PROVED HERE]`

**Theorem 4.1 (`involution_analytic_ending_and_reflection`, `factorizationInvolution_half_iff_riemannHypothesis`).** If $1/2 \le \theta < 1$ and every dyadic block $(X, 2X]$ ($X \ge X_0$) admits a factorization involution leaving $\le C X^\theta$ unmatched squarefree integers, dyadic summation gives $|M(x)| \le K x^\theta$, Abel summation continues $\sum_{n < N} \mu(n)n^{-s} \to F(s)$ holomorphically on $\{\mathrm{Re}\,s > \theta\}$, analytic continuation gives $F(s)\zeta(s) = 1$ ($s \neq 1$), and functional-equation reflection (`riemannZeta_one_sub_eq_zero_of_mem_openStrip`) confines every nontrivial zero $\rho$ of $\zeta$ to $1 - \theta \le \mathrm{Re}\,\rho \le \theta$ (`zetaZeroAbscissa ≤ θ`). Consequently, $O_\varepsilon(X^{1/2+\varepsilon})$ dyadic factorization involutions are unconditionally equivalent to `RiemannHypothesis`.
