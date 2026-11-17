# E-Q2: Finite-Layer Critical States, Off-Line Krein Faithfulness, Model Separation, and B13 in ECS Coordinates

- **ID:** ecs-q2-finite-layer-krein-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1611/route-ecs.md §6 (E-Q2)
- **Lean Module:** `GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity`
- **Lean Declarations:**
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.satisfiesNormalisedStar_of_nullVector`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.nullVector_zeroParseval_of_finiteOffLine`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.orthogonalNullSpan_zeroParseval_of_finiteOffLine`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.orthogonalNullSpan_eval_upperRight_injective`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.orthogonalNullSpan_eval_upperLeft_injective`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.existsUnique_singlePair_leftZero_isolator_of_finiteOffLine`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.soft_finiteLayer_does_not_force_zero_states`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.overRegular_finiteLayer_nonnegPrimes_has_offLineZero`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.beurling_levy_rigidity_forces_zeta`
  - `GaloisForLFunctions.ExclusionOfTheCriticalState.finiteLayer_ecs_b13_tfae`
- **Statement:** (1) At the soft / single-input model level, a finite off-line layer ($N > 0$), $N$ orthogonal critical states, the zero Parseval identity, $(\star)$, and the beyond-the-wall prime-head identity do **not** force $N = 0$, witnessed unconditionally by `hidingDatum M` (exact FE, $2M$ unitary on-line roots + finite off-line pair $\{2, 1/2\}$, Hodge-positive on all windows $< n$, unit critical ground state, Parseval, $(\star)$, prime-head formula, $N = 1 > 0$) and by `overRegularZeta (2/5) (1/10) 1` (continuous $\Lambda \ge 0$, integer count error $o(1)$, off-line zero $\frac{3}{5} + i$, no FE); (2) adjoining both countable $\Lambda_B \ge 0$ and the $\Gamma_{\mathbb{R}}$ functional equation up to $L^2$ strip defect uniquely forces $\zeta_B = \zeta$ (`beurling_levy_rigidity_forces_zeta`); (3) for $\zeta$ under `FiniteOffLine`, every confined null vector and every combination $H = \sum_{i < k} c_i F_i$ of $W_8$-orthogonal confined null vectors has square-summable on-line zero values and exact zero Parseval, evaluation on upper-half-plane right or left zeros is $\mathbb{R}$-linearly injective (bounding $k \le \# Z_{\text{right}}$ without multiplicity and uniquely isolating single conjugate pairs of left-zero obstructions when $k = \# Z_{\text{right}}$), and finite-layer exclusion (`N = 0`) is unconditionally equivalent (`TFAE`) to B13, absence of confined null vectors, `ZetaBeyondTheWallPrimeContinuation`, thick-lag boundedness, and `realPacketNegIndex ∈ {0, ⊤}`.

## Goal
Settle E-Q2 completely and unconditionally: prove model refutation when either atomic $\Lambda_B \ge 0$ or the $\Gamma_{\mathbb{R}}$ Lévy functional equation is dropped, bridge Beurling–Lévy rigidity, establish the full finite-layer Krein faithfulness / multiplicity-free dimension bound / single-pair pole isolation calculus for higher critical states of $\zeta$, and prove the 6-way ECS equivalence of B13.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof below `[PROVED HERE]`
- [x] 2 → 3  formalized: `GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity`

## Dependency-Closed Paper Proof `[PROVED HERE]`

### 1. Normalised $(\star)$ and zero Parseval on orthogonal spans of confined null vectors
For any `IsConfinedNullVector R F` ($R > 0$), `nullVector_alias_mul_laplace` and `tendsto_tsum_sub_left` give `SatisfiesNormalisedStar R F`. By `tendsto_zeroPairing_of_normalisedStar`, $\lim_{\varepsilon \to 0^+} \sum_q \mathcal{L}F(z_q)\mathcal{L}G(-z_q)e^{\varepsilon z_q^2} = -a(R) W_8(F, G)$ for every $G \in \mathcal{H}$.
Under `BacklundConverse.FiniteOffLine`, for any $W_8$-orthogonal family $(R_i, F_i)_{i < k}$ ($R_i > 0$) and $H = \sum_{i < k} c_i F_i$, finite off-line convergence and monotone/dominated convergence on `onLineCopies` give square-summability of $\|\mathcal{L}H(z_q)\|^2$ on `onLineCopies` and
$$\sum_{q \in \text{onLineCopies}} \|\mathcal{L}H(z_q)\|^2 + \sum_{q \notin \text{onLineCopies}} \mathcal{L}H(z_q)\mathcal{L}H(-z_q) = -\sum_{i < k} c_i^2 a(R_i) \int_{-\infty}^0 F_i(u)^2 e^{-8u}\,du.$$

### 2. Off-line faithfulness, multiplicity-free bound, and single-pair pole isolation
Since $\xi(\frac{1}{2} + x) > 0$ on $\mathbb{R}$ (`XiGlobalKummer.xi_real_pos`) and $\xi(1 - s) = \xi(s)$, conjugation partitions $Z_{\text{right}} = Z_{\text{right}}^+ \sqcup \overline{Z_{\text{right}}^+}$ and $Z_{\text{left}} = Z_{\text{left}}^+ \sqcup \overline{Z_{\text{left}}^+}$ with $\# Z_{\text{right}} = 2\,\# Z_{\text{right}}^+ = 2\,\# Z_{\text{left}}^+ = \# Z_{\text{left}}$.
If $H = \sum_{i < k} c_i F_i$ ($c_i \in \mathbb{R}$) vanishes on $Z_{\text{right}}^+$ (or on $Z_{\text{left}}^+$), conjugation symmetry makes $\mathcal{L}H$ vanish on all of $Z_{\text{right}}$ (or $Z_{\text{left}}$), killing every off-line product $\mathcal{L}H(z_q)\mathcal{L}H(-z_q)$ and forcing $0 \le \sum_{\text{on}} \|\mathcal{L}H(z_q)\|^2 = -\sum_i c_i^2 a(R_i) W_8(F_i) \le 0$, hence $c = 0$.
Thus both $\mathbb{R}$-linear evaluation maps $E_{\text{right}}^+$ and $E_{\text{left}}^+$ are injective, giving $k \le \# Z_{\text{right}}$ (without multiplicity). When $k = \# Z_{\text{right}}$, $E_{\text{left}}^+$ is an isomorphism, uniquely isolating any single conjugate pair $\{z_*, \overline{z_*}\} \subset Z_{\text{left}}$ (`not_wallPrimeBalance_continues_of_seen_zero`).

### 3. Model separation, Beurling–Lévy rigidity, and 6-way B13 TFAE
- **Soft / single-input refutations:** `hidingDatum M` (`M = n 2^n + n + 1`) satisfies `InFourStrip`, Hodge positivity on all windows $< n$, $2M$ unitary on-line roots + outer root $2 > 1$, unit critical ground state, Parseval, $(\star)$, and rational prime-head formula with $N = 1 > 0$; `overRegularZeta (2/5) (1/10) 1` satisfies $w(t) \ge 0$, integer error $o(1)$, and vanishes at $\frac{3}{5} + i$.
- **Beurling–Lévy rigidity:** Adjoining countable $\Lambda_B \ge 0$ and the $\Gamma_{\mathbb{R}}$ functional equation up to $L^2$ strip defect uniquely forces $\zeta_B = \zeta$ (`beurlingSystem_rigidity_of_finiteEnergy_defect`).
- **6-way ECS TFAE:** Combines `zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis`, `zetaBeyondTheWallPrimeContinuation_iff_no_criticalState`, `isConfinedNullVector_of_groundState`, `card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine` at $k = 1$, `InfiniteRankWeilTheory.b13_iff_thick_lag_bounded`, and `ArithmeticCastelnuovoSeveri.finiteOffLine_imp_rh_iff_packetIndex_zero_or_infinite`.
