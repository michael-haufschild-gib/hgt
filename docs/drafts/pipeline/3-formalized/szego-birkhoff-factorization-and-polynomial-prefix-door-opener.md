# Canonical Birkhoff–Szegő Factorization, Sharp Strip-Zero Growth, and Separation-Free Polynomial-Prefix Stabilization of the Integer-Theta Collision Operator

- **ID:** szego-birkhoff-factorization-and-polynomial-prefix-door-opener
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** docs/reports/review-0111/fable.md · §5.4 (Route WD → Q4.4; obstacles A17, B22, B25, Π13)
- **Lean Modules:**
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.ArithmeticRealityAndBirkhoffSzego`
    - `conj_integerThetaWindowPowerSum_eq`
    - `integerThetaDifferencePoly_real_and_loop_symmetric`
    - `IsDiskUnit`, `IsOuterPolynomial`
    - `fredholmIndex_eq_zero_of_diskUnit_re_pos`
    - `isUnit_wienerHopfLift_of_re_pos`
    - `hankelPlus_circlePolyInv_eq_zero`
    - `exists_birkhoffSzego_factorization_integerTheta`
    - `integerTheta_szego_positivity_tfae`
    - `riemannHypothesis_iff_szego_positivity_at_stoppingPrefix`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.SharpStripZeroGrowthAndSqrtLowerBound`
    - `seamSlope_gaussian_lower_bound`
    - `norm_finiteThetaAmplitude_cusp_remainder_gaussian_le`
    - `finiteThetaAmplitude_ne_zero_above_quadratic_horizon`
    - `prefixGlobalStripZeroBound_theta_growth`
    - `firstArtifactFreePrefix_sqrt_lower_bound`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.PolynomialPrefixStabilization`
    - `zhukovskyEllipseForm_second_diff_ge`
    - `card_filter_zhukovskyEllipseForm_near_one_le_two`
    - `exists_natStage_avoiding_zhukovsky_ellipses`
    - `norm_zhukovskyLoop_sub_ge_of_ellipse_gap`
    - `norm_pairDiffPoly_eval_sub_le_on_zhukovsky`
    - `pairDiffPoly_rouche_stabilization_core`
    - `integerThetaCollisionOperator_polynomial_stabilization`
    - `centeredThetaDifferencePoly_real_and_loop_symmetric`
    - `centeredTheta_szego_positivity_tfae`
    - `centeredTheta_sqrtPrefix_stabilization`
  - `GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.HeckeDefectCorridorAndRHDoorOpener`
    - `exists_prefix_zero_in_ball_of_xi_zero`
    - `logStage_sqrtPrefix_szego_iff_invLog_corridor`
    - `heckeDefect_log_bound_implies_szego_corridor_and_lindelof`
    - `heckeDefect_log_O1_implies_szego_corridor_and_lindelof`
    - `riemannHypothesis_door_opener_tfae`
    - `burnolUnit_subexp_sqrtPrefix_szego_of_rh`
- **Statement:**
  1. **Unconditional Arithmetic Reality & Canonical Birkhoff–Zhukovsky–Szegő Factorization:** For all $(T, n, N)$ (and all centered windows $[y_1, y_2]$), `integerThetaDifferencePoly T n N` (`centeredThetaDifferencePoly y₁ y₂ N`) has real coefficients and its squared Zhukovsky Laurent loop satisfies $\overline{\Lambda(\bar u)} = \Lambda(u)$ on $S^1$. At every boundary-regular, ellipse-nondegenerate $(T, n, N)$, $\Lambda_{T,n,N}(u) = G_+(u) u^{2k} \overline{H_+(u)}$ for explicit outer polynomial units $G_+, H_+$ nonvanishing on $\overline{\mathbb{D}}$ and $2k = \operatorname{ind}(W_{T,n,N})$. Consequently, the unnormalized Wiener–Hopf lift $T_{\Lambda_{T,n,N}}$ is Fredholm and surjective with $\dim\ker T_{\Lambda_{T,n,N}} = 2k$, and $\operatorname{ind}(W_{T,n,N}) < 2 \iff \operatorname{ind}(W_{T,n,N}) = 0 \iff W_{T,n,N}\text{ invertible} \iff T_{\Lambda_{T,n,N}}\text{ invertible} \iff \Lambda_{T,n,N} = G_+ \overline{H_+} \iff \exists F \in C(\overline{\mathbb{D}}, \mathbb{C}^\times),\; \operatorname{Re}(F \Lambda_{T,n,N}) > 0$ on $S^1$.
  2. **Sharp Strip-Zero Growth & $\Omega(\sqrt{T})$ Prefix Lower Bound (A17):** Every strip zero of $\mathcal{A}_N$ in $\{|\operatorname{Re} z - 1/2| \le 1\}$ satisfies $|\operatorname{Im} z| \le C_{\mathrm{hor}}(N + 2)^2$; the global strip-zero multiplicity satisfies $c_0(N + 1)^2\log(N + 2) \le \mathrm{prefixGlobalStripZeroBound}(N) \le C_1(N + 2)^2\log(N + 3)$; and `firstArtifactFreePrefix T n ≥ c_* √T` unconditionally for all $T \ge T_0$ and $n \ge \mathrm{thetaAnnihilationScale}(T)$.
  3. **Separation-Free Polynomial-Prefix Stabilization, $\ge\mathrm{qRH}$ Corridor Equivalence, and Master 9-Way $\mathrm{RH}$ Door Opener (B25, Π13, B22):** Discrete strict convexity $E_{n-1}(d) - 2 E_n(d) + E_{n+1}(d) \ge 16(\operatorname{Re} d - 1/2)^2 / n^3 + 2(\operatorname{Im} d)^2$ implies at most $2$ integer stages in $[S_0, S_{\max}]$ satisfy $|E_n(d) - 1| < (8 S_{\max}^3)^{-1}$, eliminating all zero-separation hypotheses: cumulative windows $[0, T_{\mathrm{win}}]$ stabilize `integerThetaCollisionOperator` at $N = O(m\log^2(m + S))$, and Burnol-bracketed unit windows $[y_1(m), y_2(m)]$ stabilize `centeredThetaCollisionOperator` at optimal prefix $N = C_{\mathrm{unit}}(\lfloor\sqrt{m}\rfloor + 1) = \Theta(\sqrt{m})$ across all $(S : \mathbb{R}) \le \exp(\sqrt{m})$ (and at `doorUnitPrefix m S` unconditionally for every $S \in \mathbb{N}$). At deterministic logarithmic stage `logDoorStage c m = max 6 ⌈c log(m + 5)⌉₊`, local $\Theta(\sqrt{m})$ Hurwitz–Rouché zero capture plus Vinogradov–Korobov vertex closure yields a 6-way equivalence between $\Theta(\sqrt{m})$-prefix Szegő positivity (index $< 2$) and the $A/\log|\gamma|$ zero-free corridor, linking $E_\gamma(c_0\log T) = O(1)$ unconditionally to Szegő positivity, `ZerosApproachLine`, `OffLineSparse`, `LindelofCriticalLine`, and `XiZeroHalfPlaneBound β` ($\beta < 1/2$), while across all $(m, S) \in \mathbb{N}^2$ Szegő positivity at `doorCumulPrefix m S` and `doorUnitPrefix m S` is 9-way equivalent to `RiemannHypothesis`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, corpus audit completed
- [x] 1 → 2  fully-proven: dependency-closed paper proof completed
- [x] 2 → 3  formalized: Lean modules in `ConjugateDiagonalGeometry/SzegoCollision/`, `lake --old env lean` green, `#print axioms` `[propext, Classical.choice, Quot.sound]` only

## Proof Summary
1. **Arithmetic Reality & Canonical Birkhoff–Zhukovsky–Szegő Factorization (`ArithmeticRealityAndBirkhoffSzego.lean`):**
   Quartet symmetry $g_N(1 - \bar z) = -\overline{g_N(z)}$ yields $\overline{s_{T,n,N}(r)} = \sum_{j=0}^r (-1)^j \binom{r}{j} s_{T,n,N}(j)$, cancelling every cross-term in $p_K$ so $P_{T,n,N} \in \mathbb{R}[X]$ and $\overline{\Lambda(\bar u)} = \Lambda(u)$ on $S^1$. Radial contraction on $\overline{\mathbb{D}}$ and orthogonal $P_+ \oplus (1 - P_+)$ contraction prove index $0$ and $L^2(\mathbb{R})$ invertibility under $\operatorname{Re}(F \Lambda) > 0$. Splitting each factor $J_n(\rho_n u) - d$ via quadratic Zhukovsky roots ($|z_+ z_-| = 1$) separates $E_n(d) > 1$ into outer units and $E_n(d) < 1$ into $u^2$ times a conjugate outer unit, proving $\Lambda = G_+ u^{2k} \overline{H_+}$ and the 6-way `TFAE`.
2. **Sharp Strip-Zero Growth & $\Omega(\sqrt{T})$ Lower Bound (`SharpStripZeroGrowthAndSqrtLowerBound.lean`):**
   Positivity of the $N+2$ cusp derivative gives $J_{N+1,1}(0) \ge 2\pi^2(N + 2)^6 e^{-\pi(N+2)^2}$, dominating the third-order cusp remainder above $|\operatorname{Im} z| \ge C_{\mathrm{hor}}(N + 2)^2$ and dominating $\|\xi(z)\|$ on $\{|\operatorname{Re} z - 1/2| \le 1\}$. Uniform order-$1$ Jensen upper bounds and Burnol-height Rouché lower bounds give $\mathrm{prefixGlobalStripZeroBound}(N) = \Theta(N^2\log N)$, which against Riemann–von Mangoldt forces `firstArtifactFreePrefix T n ≥ c_* √T`.
3. **Discrete-Convexity Avoidance, Polynomial-Prefix Stabilization, and Corridor/RH Equivalences (`PolynomialPrefixStabilization.lean`, `HeckeDefectCorridorAndRHDoorOpener.lean`):**
   Discrete second-difference positivity $E_{n-1}(d) - 2E_n(d) + E_{n+1}(d) \ge 16(\operatorname{Re} d - 1/2)^2/n^3 + 2(\operatorname{Im} d)^2$ limits near-$1$ hits in $[S_0, S_{\max}]$ to at most $2$, selecting an integer stage avoiding all $d^2$ zero-differences by $\ge (8 S_{\max}^3)^{-1}$ without zero-separation hypotheses and giving quantitative Rouché bounds on `pairDiffPoly`. On Burnol unit windows ($d_m \ll \log m$), `thetaStripTailBound N` enters the Rouché basin at $N = \Theta(\sqrt{m})$ across $(S : \mathbb{R}) \le \exp(\sqrt{m})$. Local $\Theta(\sqrt{m})$ Hurwitz–Rouché zero capture (`exists_prefix_zero_in_ball_of_xi_zero`) plus `exists_vk_carrier_depth_profile` closes the deterministic 6-way `logDoorStage c m` ↔ $A/\log|\gamma|$ corridor `TFAE`, the `heckeDefect` $O(1)$ implication, and the 9-way `RiemannHypothesis` `TFAE`.
