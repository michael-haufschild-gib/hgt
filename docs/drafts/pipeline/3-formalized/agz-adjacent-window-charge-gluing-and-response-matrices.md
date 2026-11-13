# Adjacent Window Charge Gluing, Certified Susceptibilities, and Multi-Charge Response Matrices

- **ID:** agz-adjacent-window-charge-gluing
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.21 (B189, A156)
- **Statement:** For cutoff $Q \ge 3$ and block size $R \ge 1$, the dyadic halves $(R, 2R]$ and $(2R, 4R]$ of a window of ratio four admit charge vectors $u, v$ below the inter-window couplings with lowered halves nonnegative on $\ker u, \ker v$ and susceptibility product $\alpha \beta \ge 1$ if and only if $R = 1$, while the raised-potential model has negative index $1$ for every $R \ge 1$; on narrow windows $16(J_1 + J_2) \le R$ same-sign admissible charges have nonnegative susceptibilities whereas general admissible charges achieve arbitrarily large susceptibility products; extending rank-1 charges to rank-$r$ charge matrices yields two-sided potential brackets and an exact Haynsworth response-matrix inertia law that glues $(2, 4]$ and $(4, 8]$ at rank $r = 2$.

## Lean Declarations (`GaloisForLFunctions.AbsoluteGeometryOfSpecZ`)
- `TwoCoupledWindowsAreBracketedByLoweredAndRaisedPotentialsAndGluedThroughResponseMatrices`:
  - `hermNegIndex_glued_le_coupled`, `hermNegIndex_coupled_le_gluedMatrix`, `hermNegIndex_gluedMatrix_le_coupled`
  - `hermNegIndex_glued_eq_one_of_exists_neg`, `susceptibility_mul_le_of_fin_one`
  - `hermNegIndex_gluedMatrix_schur`, `hermNegIndex_gluedMatrix_response`
- `OnANarrowWindowThePotentialIsPositiveAndThereAreNoBoundStates`:
  - `xLogXStep_le_log_add_half`, `log_add_half_sub_le_xLogXStep`, `blockJet_lt_of_lt`
  - `one_lt_blockPotential_of_narrow`, `hermNegIndex_neutralWindow_eq_zero_of_narrow`, `bilin_neutralWindow_pos_of_narrow`
  - `chargeOf_nonneg_of_narrow_same_sign`, `exists_admissible_susceptibility_mul_ge_of_posDef`, `exists_narrow_admissible_susceptibility_mul_ge`
- `TheHalvesOfAWindowOfRatioFourGlueThroughTheirChargesOnlyOnUnitBlocks`:
  - `hermNegIndex_raised_left_ratio_four_eq_zero`, `hermNegIndex_raised_right_ratio_four_eq_one`, `hermNegIndex_glued_raised_zero_eq_one`
  - `exists_unit_blocks_gluing_ratio_four`, `susceptibility_mul_le_unit_blocks_ratio_four`
  - `sav_ratio_four_ge_of_four_le`, `two_le_hermNegIndex_glued_lowered_of_four_le`, `two_le_hermNegIndex_glued_lowered_ratio_four_of_two_le`, `not_exists_gluing_ratio_four_of_two_le`
  - `halves_of_ratio_four_glue_iff_eq_one`
  - `exists_sub_unit_gluing_two_blocks_ratio_four`, `hermNegIndex_gluedMatrix_two_blocks_ratio_four_eq_one`

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions.AbsoluteGeometryOfSpecZ`, single-module `lake --old env lean` audit PASS

## Proofs (`[PROVED HERE]`)

### 1. Two-sided potential brackets and multi-charge response-matrix inertia
For symmetric matrices $A \in \mathbb{R}^{J_1 \times J_1}$, $B \in \mathbb{R}^{J_2 \times J_2}$, coupling $K \in \mathbb{R}^{J_1 \times J_2}$, and rank-$r$ charge matrices $U \in \mathbb{R}^{J_1 \times r}$, $V \in \mathbb{R}^{J_2 \times r}$ satisfying $\sum_{k=1}^r U_{i k} V_{j k} \le K_{i j}$, let $F_{i j} := K_{i j} - \sum_{k=1}^r U_{i k} V_{j k} \ge 0$, $d^L_i := \sum_j F_{i j}$, $d^R_j := \sum_i F_{i j}$. From $F_{i j}(x_i \mp y_j)^2 \ge 0$,
$$\operatorname{bilin}(\operatorname{gluedMatrix}(A - \operatorname{diag} d^L, B - \operatorname{diag} d^R, U, V), (x, y)) \le \operatorname{bilin}(\operatorname{coupled}(A, B, K), (x, y)) \le \operatorname{bilin}(\operatorname{gluedMatrix}(A + \operatorname{diag} d^L, B + \operatorname{diag} d^R, U, V), (x, y)),$$
hence $\operatorname{hermNegIndex}(\operatorname{gluedMatrix}_{\text{high}}) \le \operatorname{hermNegIndex}(\operatorname{coupled}(A, B, K)) \le \operatorname{hermNegIndex}(\operatorname{gluedMatrix}_{\text{low}})$.
When $A$, $B$, and $\mathcal{A} := U^T A^{-1} U$ are invertible, applying Haynsworth inertia additivity twice to $\bigl(\begin{smallmatrix} \mathcal{A}^{-1} & V^T \\ V & B \end{smallmatrix}\bigr)$ and once to $\operatorname{gluedMatrix}(A, B, U, V)$ yields
$$\operatorname{hermNegIndex}(\operatorname{gluedMatrix}(A, B, U, V)) + \operatorname{hermNegIndex}(\mathcal{A}) = \operatorname{hermNegIndex}(A) + \operatorname{hermNegIndex}(B) + \operatorname{hermNegIndex}(\mathcal{A}^{-1} - \mathcal{B}), \qquad \mathcal{B} := V^T B^{-1} V.$$

### 2. Automatic sign elimination and exact single-block global maximum
- **Sign elimination:** If $A, B$ are symmetric, each takes a strictly negative value on some vector, $A \succeq 0$ on $\ker u$, $B \succeq 0$ on $\ker v$, $A a = u$, $B b = v$, and $1 \le (u \cdot a)(v \cdot b)$, then necessarily $u \cdot a < 0$ and $v \cdot b < 0$, so $\operatorname{hermNegIndex}(\operatorname{glued}(A, B, u, v)) = 1$.
- **Exact global maximum for $J_1 = 1$:** Suppose $A = (a_{00})$ with $a_{00} < 0$, $B \in \mathbb{R}^{J_2 \times J_2}$ is symmetric, $B b_0 = K_0$ with $b_{0, j} \le 0$ for all $j$, and $\alpha_0 \beta_0 := a_{00}^{-1}(K_0 \cdot b_0) \ge 1$. Rescaling $u_0 \ne 0$ to $u_0 = 1$ writes $v = K_0 - \delta$ with $\delta \ge 0$. For $\beta(\delta) = v \cdot \psi < 0$, testing $B_{\text{low}} \succeq 0$ on $\beta(\delta) b_0 - (v \cdot b_0)\psi \in \ker v$ gives $(-\beta(\delta))(B_0 + T_2) \le (B_0 - T_1)^2$ where $A_0 = -a_{00} > 0$, $B_0 = -(K_0 \cdot b_0) \ge A_0$, $S_1 = \sum \delta_j$, $T_1 = -\sum \delta_j b_{0, j} \ge 0$, $T_2 = \sum \delta_j b_{0, j}^2$. By Cauchy–Schwarz $T_1^2 \le S_1 T_2$ and $A_0 \le B_0$, $A_0(B_0 - T_1)^2 \le (A_0 + S_1)(B_0 + T_2)B_0$, yielding $\alpha(\delta)\beta(\delta) \le B_0 / A_0 = \alpha_0 \beta_0$.

### 3. Certified narrow windows ($16 J \le R$): positive potential, zero bound states, and unbounded opposite-sign susceptibilities
- Using $\log(n + \frac{1}{2}) + 1 - \frac{1}{(4n+1)(4n+3)} \le \Delta(n) \le \log(n + \frac{1}{2}) + 1$ ($n \ge 1$, $\Delta(0) = 0 \le \log\frac{1}{2} + 1$) and AM–GM on $(j + \frac{1}{2}) + (J - 1 - j + \frac{1}{2}) = J$, for $16 J \le R$ every block satisfies $\operatorname{blockPotential}(Q, R, J, j) > 1$, so $\operatorname{hermNegIndex}(\operatorname{neutralWindow}(Q, R, J)) = 0$ and `neutralWindow` dominates the Euclidean norm square.
- For two narrow windows with $16(J_1 + J_2) \le R$, same-sign charges $0 \le u_i v_j \le K_{i j}$ keep $A_{\text{low}}, B_{\text{low}} \succ 0$, so $u \cdot a \ge 0$ and $v \cdot b \ge 0$. Opposite-sign spike charges $u = -p e_0$, $v = f_0$ ($p > 0$) satisfy $u_i v_j \le 0 \le K_{i j}$, leave $\ker u$ and $\ker v$ strictly positive definite, and produce $u \cdot a < 0$, $v \cdot b < 0$, and $(u \cdot a)(v \cdot b) \to +\infty$ as $p \to \max(1/c_A, 1/c_B)^+$.

### 4. Ratio-four windows $(R, 2R]$ and $(2R, 4R]$ ($Q \ge 3$): complete equivalence
- **Cutoff stabilization:** For $a, b < 4R$ and $k \ge 4$, $\lfloor b / k \rfloor < R$, so $\operatorname{neutralBlock}(Q, a, b) = \operatorname{neutralBlock}(4, a, b)$ for all $Q \ge 3$.
- **Raised model ($R \ge 1, Q \ge 3$):** At $u = v = 0$, $\operatorname{hermNegIndex}(A_{\text{high}}) = 0$ and $\operatorname{hermNegIndex}(B_{\text{high}}) = 1$, giving $\operatorname{hermNegIndex}(\operatorname{glued}_{\text{high}}) = 1$.
- **$R = 1$ ($Q \ge 3$):** Zero-excess charges $u = (1)$, $v = K_0$ give $A_{\text{low}} = A$, $B_{\text{low}} = B \succeq 0$ on $\ker v$, $\alpha_0 \beta_0 = N_{11}^{-1}(K_0^T B^{-1} K_0) > \frac{8}{5} > 1$, attaining the global maximum over all admissible pairs.
- **$R \ge 2$ ($Q \ge 3$):** Contact savings from $\lfloor b / 2 \rfloor = a$ and $\lfloor b / 3 \rfloor = a$ force $\operatorname{hermNegIndex}(\operatorname{glued}(A_{\text{low}}, B_{\text{low}}, u, v)) \ge 2$ for every admissible pair ($R \ge 4$ and near-dyadic windows via row-maximum savings $> 0.27 R$; $R = 3$ on the coarse $3 \times 3$ subspace; $R = 2$ by splitting at $4 u_0 \le 5 u_1$). At $R = 2$, $u = (1, 1), v = (\frac{2}{3}, \frac{3}{10}, \frac{1}{2}, \frac{1}{2})$ achieves $0 < \alpha \beta < \frac{1}{2} < 1$, while rank-two charges $U = 1, V_{j i} = K_{i j}$ glue $(2, 4]$ and $(4, 8]$ with zero excess and exact negative index $1$.

## No-go closure
- **Exact killing theorem/mechanism:** `two_le_hermNegIndex_glued_lowered_ratio_four_of_two_le` and `not_exists_gluing_ratio_four_of_two_le` (`R ≥ 2, Q ≥ 3`).
- **Strongest positive survivor:** `hermNegIndex_gluedMatrix_response`, `susceptibility_mul_le_unit_blocks_ratio_four`, and `hermNegIndex_gluedMatrix_two_blocks_ratio_four_eq_one`.
- **New insight:** Across ratios $> 2$ at block sizes $R \ge 2$, gluing is governed by the multi-charge response operator $\mathcal{A}_{\text{low}}^{-1} - \mathcal{B}_{\text{low}}$ at coupling rank $r > 1$ rather than scalar susceptibility products.
- **Status:** Unconditionally proved and formalized in Lean 4; all three modules audited with `lake --old env lean`.
