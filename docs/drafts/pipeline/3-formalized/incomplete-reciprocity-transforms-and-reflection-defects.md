# Incomplete Reciprocity Transforms, Reflection Defects, and Family-Continuation Walls

- **ID:** incomplete-reciprocity-transforms-and-reflection-defects
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1411/obstacles-summary.md §2.5 (`[DECOMPLETE]`, `[GAUSS]`, `[AVERAGE]`)
- **Statement:** An exact doubly-incomplete Eisenstein cube-Gauss reciprocity transform retains the Möbius target and all row root-number phases and achieves a genuine uniform reflection-defect power saving below $X^{1/2}$ across the entire super-conductor reflection box $N(c) \le X^{1-\delta}$ for every sub-cubic cutoff $Y_0 = X^\eta$ with $\frac{1}{6} < \eta < \frac{1}{3}$, fails in the sub-conductor `RawMoment` regime $N(c) \ge X^{1+\kappa}$, and is unstable under the detector's row-family Poisson continuation, which restores the $2/3$ uncoupled and $3/5$ coupled walls at every local or global truncation scale.

## Goal
Resolve §2.5 completely and unconditionally across all three milestones:
1. Construct the exact prime/ideal incomplete reciprocity identity `source(s, w) = phase(s, w) · dualSource(1 - s, w') + boundaryDefect(s, w)` retaining the reciprocal target and all local root-number phases without reducing to full monomial completion, and classify the exact conductor regimes where `boundaryDefect` achieves a uniform power saving.
2. Determine whether the defect saving survives the detector's row-family Poisson continuation at `z = 1/6`, both for arbitrary local prime-exponent cutoffs `l < L` (`L ≥ 1`) and for global ideal-norm cutoffs `N(J) < Z^η` (`η < 1/3`).
3. Determine the exact resulting zero-free thresholds relative to `7/8`, `2/3` (uncoupled), and `3/5` (coupled).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules `GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.IncompleteReciprocityRetainsPhasesWithSubcubicSaving` and `GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.FamilyContinuationRestoresTheGaussWallsUnderTruncation`, foreground `lake --old env lean` green

## Lean Formalization

### Module 1: `GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.IncompleteReciprocityRetainsPhasesWithSubcubicSaving`
- `incompleteIdealT_eq_incompleteCuspDual_add_defect`: exact polar-free doubly-incomplete cusp reciprocity identity splitting `completedIdealT` at $N(J) < Y_0$ and the finite-cusp dual at $N(J') < Y_0'$.
- `incompleteIdealSummand_principal_cube_eq`: exact retention of the $J = (1)$ Möbius target for every cutoff $Y_0 > 1$.
- `incompleteCuspDual_retains_unit_gauss_root_numbers`: exact retention of unit-modulus local Gauss root-number phases $\varepsilon_i = Q_i^{-1} G(\chi_6, \psi^{-1}) G(\chi_6^3, \psi)$ ($\|\prod_i \varepsilon_i\| = 1$) times the quadratic residue twist $\prod_i \chi_{P_i}^{(2)}$.
- `exists_infinitely_many_nonzero_subcubic_directCubeTail`: infinite explicit coprime family $(c_m, \Psi_m, X_m)$ for every $\eta \in (0, 1/3)$ with `directCubeTail (X_m^η) ≠ 0`, proving non-reducibility to full monomial completion.
- `norm_directCubeTail_le_uniform` and `norm_dualCubeTail_le_uniform`: uniform bounds $O_{\mathcal{R}, W_0}(X Y_0^{-3})$ and $O_{\mathcal{R}, W_0, N}(|O/(9c)| (X / Q_c^2)^{-N} (Y_0')^{-(3N - 9/2)})$ ($N \ge 2$) over compact $s$-rectangles $\mathcal{R}$ for `twistWindow W_0 s`.
- `exists_uniform_subcubic_reflection_defect_power_saving`: for every $\delta \in (0, 1)$ and $\eta \in (1/6, 1/3)$, choosing $\eta' = \max(\delta/3, (1-\delta)/3) \in (0, 1/3)$ bounds `reciprocityBoundaryDefect (X^η) (X^η')` by $C \cdot X^{1/2 - \min(3\eta - 1/2, 1/2)}$ uniformly for all $c \ne 0$ with $N(c) \le X^{1-\delta}$ and $s \in \mathcal{R}$.
- `subconductor_dual_smoothing_obstruction`: in the sub-conductor `RawMoment` regime $N(c) \ge X^{1+\kappa}$ ($\kappa > 0$), for every sub-cubic $\eta' \le 1/3$, $d_i.\operatorname{smoothingScale}(X) \cdot (X^{\eta'})^3 \le (4 / (2187 \sqrt{3})) X^{-2\kappa} \to 0$.

### Module 2: `GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.FamilyContinuationRestoresTheGaussWallsUnderTruncation`
- `singleRow_vs_rowPoisson_amplification_dichotomy`: single-row $l = 2$ summability of $\sum_v N(v)^{1 - 6\sigma}$ for every $\sigma > 1/2$ versus divergence of the row-Poisson $Q^2$-amplified series $\sum_v N(v)^{3 - 6\sigma}$ throughout $\sigma \le 2/3$.
- `localTerm_odd_cube_eq_zero`, `hasSum_localTerm_lt_cutoff`, `truncated_principal_factor_eq`, and `truncatedPrincipalLocalFactor_eq_geom_mul_regular_add`: exact local closed form for every finite cube-exponent cutoff $l < L$ ($L \ge 1$, $M = \lfloor(L+1)/2\rfloor \ge 1$) without assuming $\|R\| < 1$:
  $$\operatorname{truncatedPrincipalLocalFactor}_M(Q, A, \eta_p, s) = \left(\sum_{r=0}^{M-1} R^r\right) \operatorname{regularLocalFactor}(Q, A, \eta_p, s) + (1 - Q^{-2}) \frac{Q^{-1} R^M}{1 - D}.$$
- `exists_truncatedPrincipalCorrection_one_cutoff`: for $L \in \{1, 2\}$ ($M = 1$), `truncatedPrincipalCorrection 1 A η S = principalCorrection 0 η S`, holomorphic and within $1/2$ of $1$ on $\operatorname{Re} s > \sigma > 1/2$.
- `truncatedFullPrincipalCorrection_mul_grossen_eq` and `exists_continuedTruncatedCorrection_properties`: for every $L \ge 3$ ($M \ge 2$), with an $M$-independent prime cutoff $N_{\text{cut}} \ge 160$, `truncatedFullPrincipalCorrection M 𝔪 η S` continues holomorphically to $\operatorname{Re} s > 7/12$, is nonvanishing on $\operatorname{Re} s \ge 2/3$, and every holomorphic continuation $G$ on $\operatorname{Re} s > \sigma_0$ ($\sigma_0 < 2/3$) has exact zero locus $G(s) = 0 \iff \operatorname{continuedProbeCorrection}(s) = 0$ on $\operatorname{Re} s > \max(\sigma_0, 41/72)$ with $\operatorname{Re} s \ge 7/12$ — hence infinitely many zeros with unbounded ordinates in $7/12 \le \operatorname{Re} s < 2/3$ whenever $\sigma_0 < 7/12$ and no nonvanishing continuation below $7/12$.
- `exists_subcubic_sixthPower_defect_lower_bound`: for every global cutoff $\eta < 1/3$ (including all $\eta \in (1/6, 1/3)$), the $l = 2$ squarefree shell $N(T)^6 \le Z$ lies strictly inside the omitted tail $N(J) = N(T)^2 \ge Z^\eta$ and carries row-continued sixth-power Möbius norm $\ge c \cdot Z^{2/3}$ ($c > 0$).
- `coupled_tower_iterates_eq_and_tendsto` and `incomplete_reciprocity_producer_classification`: joint end-to-end synthesis of Milestones 1, 2, and 3, including exact $K$-fold coupled tower contraction $\sigma_K = \frac{3}{5} + (\sigma_{\text{base}} - \frac{3}{5}) 6^{-K} \to \frac{3}{5}$ from $\sigma_{\text{base}} = 7/8$ and $\sigma_{\text{base}} = 2/3$.

## Complete Mathematical Proof `[PROVED HERE]`

### 1. Doubly-Incomplete Cusp Reciprocity Identity and Super-Conductor vs. Sub-Conductor Regimes
For $O = \mathbb{Z}[\omega]$, $c \in O \setminus \{0\}$ ($Q_c = N(c) = \|c\|^2$), $\Psi : (O/(c)) \to^* \mathbb{C}$ ($\|\Psi\| \le 1$), $W_0 \in C_c^\infty([a, b])$ ($0 < a < b$), and $W_s(y) = y^{1/2 - s} W_0(y)$, splitting `completedIdealT` at $N(J) < Y_0$ and `completedT_finite_cusp_full_reflection` at $N(J') < Y_0'$ gives
$$\operatorname{incompleteIdealT}_{Y_0}(\Psi_c, W_s, X) = \operatorname{incompleteCuspDual}_{Y_0'}(c, \Psi, d, W_s, X) + \operatorname{reciprocityBoundaryDefect}_{Y_0, Y_0'}(c, \Psi, d, W_s, X),$$
with $\operatorname{reciprocityBoundaryDefect}_{Y_0, Y_0'} = \operatorname{dualCubeTail}_{\ge Y_0'} - \operatorname{directCubeTail}_{\ge Y_0}$.
- For $Y_0 > 1$, $J = (1)$ lies inside $N(J) < Y_0$, preserving the Möbius target identically; on good prime factors $P_i$, the dual preserves unit-modulus Gauss root-number phases $\varepsilon_i$ times $\chi_{P_i}^{(2)}$.
- On any compact rectangle $\mathcal{R}$, dyadic summation of `finite_ideal_count_real` bounds $\|\operatorname{directCubeTail}_{\ge Y_0}\| \le C_{\text{dir}} X Y_0^{-3}$, while iterated Mellin integration by parts on $V^*(W_s)$ bounds $\|\operatorname{dualCubeTail}_{\ge Y_0'}\| \le C_{\text{dual}, N} |O/(9c)| (X / Q_c^2)^{-N} (Y_0')^{-(3N - 9/2)}$ ($N \ge 2$).
- For $Q_c \le X^{1-\delta}$ and $1/6 < \eta < 1/3$ with $\eta' = \max(\delta/3, (1-\delta)/3) < 1/3$, $(X/Q_c^2)(X^{\eta'})^3 \ge X^\delta$, so choosing $\delta N \ge 2$ gives $\|\operatorname{reciprocityBoundaryDefect}\| \le C X^{1/2 - \min(3\eta - 1/2, 1/2)} = o(X^{1/2})$.
- For $Q_c \ge X^{1+\kappa}$ ($\kappa > 0$) and $\eta' \le 1/3$, $d_i.\operatorname{smoothingScale}(X) \cdot (X^{\eta'})^3 \ll X^{-2\kappa} \to 0$, obstructing sub-cubic dual decay.

### 2. Instability Under Row-Family Continuation and Persistence of `2/3` and `3/5`
- Single-row $l = 2$ weights $N(v)^{1 - 6\sigma}$ converge on $\sigma > 1/2$, whereas row-Poisson continuation at $z = 1/6$ multiplies by $N(v)^2$ to produce $R_v = \kappa_v^6 N(v)^{3 - 6s}$.
- Truncating locally to $l < L$ ($M = \lfloor(L+1)/2\rfloor$) eliminates $l = 2$ when $L \in \{1, 2\}$ ($M = 1$) and, for every $L \ge 3$ ($M \ge 2$), factors `truncatedFullPrincipalCorrection M` on $\operatorname{Re} s > 2/3$ as $\operatorname{continuedProbeCorrection}(s) \cdot \widetilde{\mathcal{E}}_M(s)$ divided by $L_{\mathfrak{m}}(6Ms - 3M, \psi_6^M \eta^{6M}) \cdot \operatorname{deleted/residual}$, where the denominator is nonvanishing on $\operatorname{Re} s \ge 7/12$ (`Re(6Ms - 3M) \ge M/2 \ge 1`). Thus every zero of `continuedProbeCorrection` in $7/12 \le \operatorname{Re} s < 2/3$ persists for every $L \ge 3$.
- Truncating globally to $N(J) < Z^\eta$ ($\eta < 1/3$) omits the squarefree $l = 2$ shell $\frac{c_1}{36} Z^{1/6} \le N(T) \le Z^{1/6}$, which satisfies $N(J) = N(T)^2 \ge Z^\eta$ and carries sixth-power Möbius norm $\ge c \cdot Z^{2/3}$. Consequently, uncoupled continuation remains bounded by $2/3$, and $K$-fold coupled continuation contracts $\sigma_{\text{base}} > 3/5$ via $b \mapsto (3+b)/6$ to $3/5$.

## No-go closure
- **Exact killing theorem/mechanism:** Row-Poisson summation at $z = 1/6$ multiplies the $l = 2$ cube shell by $N(J) = N(T)^2$ (`singleRow_vs_rowPoisson_amplification_dichotomy`), placing $\ge c \cdot Z^{2/3}$ sixth-power Möbius mass inside the omitted tail $N(J) \ge Z^\eta$ for every $\eta < 1/3$ (`exists_subcubic_sixthPower_defect_lower_bound`) and preserving all zeros of $L(6s - 3, \psi_6 \eta^6)$ in $[7/12, 2/3)$ for every local cutoff $L \ge 3$ (`exists_continuedTruncatedCorrection_properties`).
- **Strongest positive survivor:** (1) Constructive polar-free doubly-incomplete cusp reciprocity retaining the Möbius target and all unit-modulus Gauss root-number phases with uniform defect bound $\ll X^{1/2 - \min(3\eta - 1/2, 1/2)}$ on $N(c) \le X^{1-\delta}$ for $1/6 < \eta < 1/3$ (`exists_uniform_subcubic_reflection_defect_power_saving`); (2) exact all-depths local closed form and holomorphic continuation to $\operatorname{Re} s > 7/12$ for every finite cutoff $L \ge 3$ (`truncatedPrincipalLocalFactor_eq_geom_mul_regular_add`, `continuedTruncatedCorrection`).
- **New insight:** Compatibility of incomplete completion with reflection holds unconditionally row-by-row on $N(c) \le X^{1-\delta}$ for $1/6 < \eta < 1/3$ because single-row cube weights decay like $N(J)^{-1}$, and fails specifically at two-sided sub-conductor reflection ($N(c) \ge X^{1+\kappa}$) and at row-family Poisson continuation ($Q^2$ congruence amplification at $l = 2$).
- **Status:** Unconditionally formalized in Lean 4 (`IncompleteReciprocityRetainsPhasesWithSubcubicSaving.lean`, `FamilyContinuationRestoresTheGaussWallsUnderTruncation.lean`), audited cleanly with `lake --old env lean`.

## Log
- 2026-11-14 — paper proof and unconditional Lean 4 formalization completed and verified
