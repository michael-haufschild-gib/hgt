# Arithmetic Lorentzian Geometry (ALG)

Namespace `GaloisForLFunctions.ArithmeticLorentzianGeometry`; umbrella `ArithmeticLorentzianGeometry.lean`; 46 modules.
All results are unconditional. RH appears only as one side of an equivalence
(`riemannHypothesis_iff_intersectionGram_isHyperbolicHerm`, `riemannHypothesis_iff_cayleyLadder_nonpos`,
`riemannHypothesis_iff_cayleyLadder_nonneg`) or as the hypothesis of a lemma that is used inside an unconditional
contradiction (`isLorentzian_cayleyLadder_of_rh`, used for `not_tendsto_xiLiPaired_re_zero`). Finite-field statements take
a curve datum as input; `frobeniusGram_isHyperbolic_of_unitary` takes `|β_i| = 1` as a hypothesis, and the hyperelliptic
case proves it (Stepanov, via ArithmeticEffectivityTheory). `PolarGluingAndDispersion`,
`TheHalfDefectIsTheOptimalHodgeRepair` and `ThePoleIsInfinitesimalRelativeToThePrimeDefect` end with `#print axioms` lines.

## 1. Motivation

RH is the Hodge index of the scaling surface: every finite Gram of the intersection form has at most one positive square.
Brändén–Huh's Lorentzian theory proves exactly this kind of statement, one positive square, by **trickle-down**: local
signature of the links plus a sign hypothesis (nonnegative entries) gives global signature. Over `𝔽_q` Weil's theorem has
this shape: Bézout makes the Frobenius Gram Metzler, Frobenius is conformal with factor `q`, and the Hodge index is a
trickle-down inequality. ALG transfers the theory to `ζ`. It asks where the sign hypothesis comes from (a gauge-fixing by
the archimedean place), where the positive square lives (pole plane or conformally growing couplings), and how far
trickle-down holds for `ζ`'s atomic intersection form (proved up to a fixed fraction of the atomic spacing).

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Hyperbolic form | `IsHyperbolic`, `IsHyperbolicHerm` | `Q[x]Q[y] ≤ (xᵀQy)²` when `Q[x] > 0`; ⇔ at most one positive square |
| Lorentzian form | `IsLorentzian` | symmetric, entries `≥ 0`, hyperbolic |
| Metzler form | `IsMetzler`, `IsConnectedSupport` | off-diagonal `≥ 0`; support graph connected |
| Conditionally negative definite | `IsCND` | `Q ≤ 0` on `Σx = 0`; the sum-closed hyperbolic class |
| Row sums, weights | `rowSum`, `diagConj` | `D = Q·1`; congruence by a positive weight `π` |
| Trickle-down inequality | `TrickleDownIneq`, `WeightedTrickleDown` | `Q[v] ≤ Σ(Qv)_i²/D_i`; weighted `Σπ_i(Qv)_i²/(Qπ)_i` |
| Links | `HasHyperbolicLinks` | symmetric hyperbolic `T_i`, `ΣT_i = Q`, `T_i·1 = Qe_i` |
| Pole plane, polar defect | `realPolePlane`, `polarDefect` | `H² = V² = 0`, `H·V = 1`; `δ(d) = 2(d·H)(d·V) − L[d]` |
| Nef shift | `nefShift` | `f_i ↦ f_i + t(H + V)`: entries `≥ 0`, inertia unchanged |
| Frobenius Gram | `frobeniusGram`, `frobeniusWeight` | `H, V, Γ_0..Γ_K` of a curve datum; weight with positive image |
| Twin, gauge | `IsTwin`, `coupledKernel`, `archAtomKernel`, `twinPrimeKernel`, `HasNonnegGauge`, `archChar` | unimodular completely multiplicative twin; archimedean + twisted prime kernel on atoms; phases `g_n` |
| Ladders | `toeplitzLadder`, `conformalLadder`, `ladderGram` | `c_{|i−j|}`; `λ^{min(i,j)}a_{|i−j|}`; prime kernel on `1, p, …, p⁵` |
| Cayley ladder | `liCoupling`, `cayleyLadder`, `cayleyPoly`, `xiCayley`, `xiMult` | Toeplitz ladder of `Re Σm_a(2 − w_a^n − w_a^{−n})`, `w = 1 − 1/ρ` |
| Lorentzian polynomial | `IsLorentzianPoly`, `quadDeriv`, `IsMConvex`, `IsLorentzianPolynomial` | coefficients `≥ 0`, M-convex support, hyperbolic quadratic derivatives |
| Hessians | `hess`, `mixHess`, `dval`, `hessAt`, `hess0` | `∇²f(x) = Σ(x^α/α!)Q_α`; mixed Hessians of `∂_{v_1}⋯∂_{v_m}∂^γ f` |
| Mixed-Lorentzian | `IsMixedLorentzian`, `dirDerivs`, `linSub` | signature along all nonneg directions; nonneg substitution |
| Euler product closure | `eulerHessian`, `esymm2Form`, `disjointProd` | Hessian of `∏⟨L_p, X⟩`; `Σ_{p≠q}M_pM_qᵀ`; factors in disjoint variables |
| Ramanujan datum | `ramanujanDatum`, `quadFactor` | genus-one datum of `1 − aT + qT²`, `|a| ≤ 2√q` |
| Markov pairing | `markovPair`, `primePair` | polar form of the Markov form `2θ'(0)‖·‖² + Lévy − prime` |
| Atomic intersection Gram | `atomicIntersectionGram`, `atomicMarkovGram`, `atomPoleRow`, `poleWeight` | pole plane, pole rows `(∫g_ne^{−u/2}, ∫g_ne^{u/2})`, atom block `−M(g_m, g_n)` |
| Tilted margin | `atomMargin`, `fixedWidthRatio` | per-atom stability margin `μ_m`; `c★` |
| Pole/V-rows | `poleFunctional`, `vRowFunctional`, `upRow`, `edgePart` | `p(x) = Σx_n/√n`; `Σ√n x_n` split along prime edges |
| Hardy constants | `hardyConstant`, `poleConstant`, `psiConstant`, `crossConstant` | `C_H = 48B² + 51`; `c_P = √(2C_H)`; `B_ψ = log 4 + 4/e`; `L_{λ,κ}` |
| Window tests | `windowTest`, `windowNorm`, `pairCorr` | `Σ_n G_n(· − log n)`, any `C²` profile per atom; `y_n = ‖G_n‖₂` |
| Fractions of the spacing | `defectFraction`, `windowFraction`, `sharpFraction`, `quarterFraction` | explicit `K★` thresholds |
| Covers | `atomCover`, `adaptedTest`, `adaptedCover` | support of atomic tests; adapted widths `c log(1 + 1/n)` |
| Margin model | `marginModel` | pole plane, pole rows, atom block `−m·1` |
| Twin atomic Gram | `twinAtomicIntersectionGram`, `twinMarkovPair`, `liouvilleTwin` | same pole data, prime place twisted by `ω` |
| Tower matrix | `towerMatrix` | `2γ_p + log p` diagonal, `−log p·q^{|i−j|}` off it |
| Polar gluing | `anchorReserve`, `polarDispersion`, `polarGluingCorrection`, `polarGlue` | reserve `(xᵀQe)²/Q[e] − Q[x]`; weighted variance of polar rows |
| Tilted model | `tiltedModel`, `atomPiece`, `tiltedResidual`, `poleAnchor` | atomic Gram = tilted diagonal model + NSD residual |
| Half-defect repair | `halfDefectRepair`, `frobeniusEven`, `frobeniusOdd`, `hodgeCompletion` | odd-reflection Gram of Frobenius evaluation; pole-preserving completion |
| Pole cost | `poleRelativeCost` | `ε + 2C_He·K²/ε` |

External: `poleDefect` `D_N(x) = Σ_{mt≤N}Λ(t)(x_{mt} − x_m/√t)²` (RenormalizedArithmeticPotentialTheory); `atomicTest`,
`atomSpacing` `δ_N = log(1 + 1/N)` (ArithmeticElectrostatics); `CurveDatum`,
`goldenDatum`, `intersectionGram` (ArithmeticCastelnuovoSeveri); `succConn`, `PrimeGauge` (BiarithmeticGaugeGeometry).

## 3. Language

- **Hyperbolic** = one positive square (reverse Cauchy–Schwarz), not real-rootedness. **Lorentzian** adds entrywise
  nonnegativity, which is coordinate-dependent.
- **Trickle-down**: links (local hyperbolic pieces) plus Metzler sign plus connectivity ⇒ global hyperbolicity. The
  carried quantity is the NSD form `Q − QD⁻¹Q`, which adds where hyperbolicity does not.
- **Stability regime** `Qπ ≤ 0` (form is NSD outright) vs **trickle-down regime** `Qπ > 0` (hyperbolic ⇔ `TD_π`).
- **Overlap ratio** `K = w/δ_N` (`wN` up to constants): bump width over atomic spacing. **Robin–Euler threshold**
  `K_RE ≈ exp(2θ'(0) + κ_L(φ) + γ)` ≈ 0.43: where stability ends.
- **Gauge**: unimodular phases on atoms; **Euler gauge** `g ≡ 1`. **Twin**: `ζ` with the prime place twisted by a
  completely multiplicative `ω`.
- **Isometric / conformal ladder**: Gram of translates under a symmetry with factor 1 / factor `λ`.
- **Pole complement**: `p(x) = 0`; the H-row of an atomic test is `p(x)` times a profile moment at every width.

## 4. Mechanisms

**A. Degree-two calculus.**
1. Hyperbolic ⇔ no PD plane ⇔ `Q ≤ 0` on some hyperplane (`isHyperbolic_iff_exists_nonpos_on_ker`); domination preserves it
   (`IsHyperbolic.of_le`); pullback preserves it; sums do not (`not_isHyperbolic_add_rankOne`); CND forms add (`IsCND.add`).
2. `2 × 2`: hyperbolic ⇔ `det ≤ 0`; bivariate Lorentzian ⇔ ultra-log-concave with interval support
   (`isLorentzianPoly_bivariate_iff`).
3. Hermitian bridge `hermPosIndex_le_one_iff`; RH ⇔ every finite scaling-surface Gram hyperbolic; the nef shift makes any
   Gram with a hyperbolic pole plane entrywise nonnegative without changing inertia (`isLorentzian_nefShift_iff`).
4. Block Hodge index: a Gram with pole plane is hyperbolic ⇔ its polar defect is `≥ 0` (`isHyperbolic_fromBlocks_iff`).

**B. Trickle-down.**
1. Connected Metzler, positive row sums: one positive square ⇔ `(TD)` ⇔ hyperbolic links (rank one + NSD)
   (`isHyperbolic_iff_hasHyperbolicLinks`). Proof: maximizer on the `D`-sphere of `{ΣD_iv_i = 0}` is a generalized eigenvector;
   `(TD)` gives `m ≤ m²`, the graph Laplacian `m ≤ 1` with equality only on constants. Quantitative: `qf_le_of_approxTrickleDown`.
2. Both side conditions necessary (`trickleDown_disconnected`, `trickleDown_not_metzler`).
3. Metzler dichotomy: `Qπ ≤ 0` ⇒ NSD (`qf_nonpos_of_mulVec_nonpos`); `Qπ > 0` ⇒ hyperbolic ⇔ `TD_π`
   (`isHyperbolic_iff_weightedTrickleDown`).
4. Polar gluing: with a common positive anchor, reserve of a sum = sum of reserves − polar dispersion (`anchorReserve_sum`);
   sum hyperbolic ⇔ dispersion ≤ Σ reserves (`isHyperbolic_sum_iff_dispersion_le`). `polarGlue` subtracts the dispersion and is
   hyperbolic for hyperbolic pieces (a new form, not a theorem about a given form).
5. Exchange: `Q ≥ 0` hyperbolic, `Q_ai, Q_jk > 0` ⇒ `Q_aj > 0` or `Q_ak > 0` (`IsHyperbolic.exchange`); this forces M-convexity.

**C. Finite-field calibration.**
1. Frobenius Gram Metzler ⇔ point counts `≥ 0` (Bézout = sign); always connected and in the TD regime
   (`frobeniusGram_isMetzler_iff`). Golden fake datum: Metzler, connected, violates `TD_π` (`golden_not_weightedTrickleDown`).
2. `TD_π` on every ladder ⇔ `|β_i| = 1` ⇔ `N_k ≥ q^k + 1 − Cq^{k/2}` (`forall_weightedTrickleDown_iff_exists_pointCount_ge`);
   hyperelliptic curves have hyperbolic links (`hyperelliptic_hasHyperbolicLinks`). The input is a count, not a surface.
3. Depth `2g − 1` decides (`unitary_of_isHyperbolic_frobeniusGram`); genus one: depth one ⇔ `|a| ≤ 2√q`
   (`frobeniusGram_one_isHyperbolic_iff`); Kloosterman factors trickle down by Weil's bound (`kloosterman_trickleDown`).
4. Local polynomials: Lorentzian forces `a_1 ≥ d√q`; with Ramanujan `a_1 = d√q` (`ramanujan_lorentzian_rigid`); never at a
   prime (`not_isLorentzianPoly_at_prime`); `1 + tT + qT²` Lorentzian ⇔ `t² ≥ 4q` (reverse Hasse).
5. Half-defect repair: span Gram + odd-reflection Gram is PSD; minimal rank `#outer eigenvalues`; sharp scalar `t ≥ 1`;
   pole-preserving Hodge completion for every pole row (`optimal_frobenius_hodge_repair`, `exists_positive_repair_iff`).

**D. Gauge and sign.**
1. Each kernel alone is gauge-trivial; `A + t·P_χ` (`t ≥ 2`, `N ≥ 6`) has a nonneg gauge ⇔ `χ(p) = 1` for `p ≤ N`
   (`exists_nonneg_gauge_iff`): the archimedean kernel fixes the gauge along the successor (`P(m, m+1) = 0`), then `(1, p)`
   fixes `χ(p)`. With the kernel of `ζ(s − iτ)`: ⇔ `χ(p) = p^{iτ}` (`exists_nonneg_gauge_shifted_iff`).
2. Successor connection = archimedean gauge field: flat ⇔ `ω(p) = 1` (`gaugedArch_succ_nonneg_iff`); periodic holonomy ⇔
   Euler point (`succConn_periodic_iff_euler`); periodic `f ≢ 1` vanishes somewhere (`exists_eq_zero_of_periodic`).
3. Atomic level: positive H-row fixes the gauge; `ω(p) = −1` ⇒ no Metzler gauge
   (`not_exists_nonneg_gauge_twinAtomicIntersectionGram`). Hyperbolicity is twin-blind, the sign is not
   (`liouville_isHyperbolic_and_not_metzler`).
4. Beyond the spacing: overlapping atoms meet positively (`markovPair_shift_ge`), separated ones strictly negatively
   (`markovPair_atom_neg`); odd/negative triangles frustrate every gauge. Metzler threshold of the overlap ratio is exactly 1
   (`metzlerThreshold_overlapRatio`).

**E. Symmetry and ladders.**
1. Frobenius is conformal `TᵀG_{K+1}T = qG_K` (`frobeniusPullback_conformal`). Over `ℤ`: Hecke dilations preserve every
   coupled kernel and act on the pole plane by an isometric boost (`coupledKernel_mul_left`, `boost_isometry`); power maps and
   the successor are not conformal (`not_conformal_powerMap`, `not_conformal_succShift`).
2. Decaying isometric ladder: hyperbolic at every depth ⇔ NSD at every depth (`forall_isHyperbolic_toeplitzLadder_iff`);
   conformal ladders reduce to normalized couplings `λ^{−k/2}a_k` (`forall_isHyperbolic_conformalLadder_iff`). The positive
   square must come from the pole plane or growing couplings.
3. A single `p`-ladder of the prime kernel has two positive squares (`not_isHyperbolic_ladderGram`); the archimedean jump form
   is NSD (`qf_jumpForm_nonpos`).
4. Cayley ladder: reflection formula `Q_K[c] = Re Σm_a(2(Σc)² − 2p_c(w_a)p_c(w_a⁻¹))`; unitary points are reflection positive.
   RH ⇔ every Cayley ladder NSD on primitive vectors ⇔ entrywise `≥ 0` (Li). Unconditionally `Re 2λ_n ↛ 0`
   (`not_tendsto_xiLiPaired_re_zero`). Over `𝔽_q`: `ℓ(n) ≥ 0` ⇔ sharp Weil lower bound (`unitary_iff_cayleyLadder_nonpos`).

**F. Lorentzian polynomials.**
1. Hessian of a Lorentzian polynomial is hyperbolic at every `x ≥ 0`, by trickle-down on degree using Euler's identity as
   the link condition (`isHyperbolic_hess`, `isHyperbolic_hess_of_nonneg`). Mixed Hessians too (`isHyperbolic_mixHess`) ⇒
   Alexandrov–Fenchel and Khovanskii–Teissier (`alexandrov_fenchel`, `khovanskii_teissier`).
2. Closure: differentiation, nonneg substitution (`IsMixedLorentzian.subst`), products (disjoint variables + merge,
   `isMixedLorentzian_prod`); strong log-concavity (`IsMixedLorentzian.logConcave`). Mixed class = coefficient class
   (`isMixedLorentzian_iff_isLorentzianPolynomial`, M-convexity forced by exchange).
3. Euler product of Lorentzian local factors after any nonneg substitution is Lorentzian
   (`isLorentzianPolynomial_prod_subst`, `isLorentzian_eulerHessian_of_nonneg`) — for every nonneg datum, hence blind.
4. Closure Hessians are exactly the Lorentzian forms (`isLorentzian_iff_exists_hessAt`).
5. Turán layer: Jensen polynomials of `ξ` are Lorentzian (`xi_jensen_isLorentzianPoly`) and satisfy Laguerre on `s ≥ 0`
   (`xi_jensen_laguerre_halfLine`).

**G. `ζ`'s atomic form at the spacing scale.**
1. Below the spacing the Euler-gauge atomic Gram is Metzler, connected, in the TD regime; Weil ≥ 0 on atomic tests ⇔ `TD_π`
   (`weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown`).
2. Tilted margin `μ_m ≥ 1 + (m/8N) log m` grows along the pole; weighted C–S pays `2|AB|` ⇒ Weil ≥ 0 at `w ≤ c★δ_N` for all
   `N` and every sign twin (`weilQuad_atomicTest_nonneg`, `twin_markov_add_pole_nonneg`); hence Hodge index, `TD_π`, links
   (`hasHyperbolicLinks_atomicIntersectionGram`). A uniform margin fails by `K√log N` (`not_isHyperbolic_marginModel_eventually`).
3. Multiplicative Hardy: `(Σ√n x_n)² ≤ C_H(N²/log N)(D_N + |x|²)` (`sq_vRow_le`); the pole defect pays the pole
   (`two_mul_abs_poleMoments_le_defect`) ⇒ Weil ≥ 0 at `K★` eventually (`eventually_weilQuad_nonneg_at_fraction`), for window
   tests and for every `C²` test supported near the logarithms (`eventually_weilQuad_nonneg_of_support`).
4. Constants: one-sided Lévy cross energy (`levyEnergy_windowTest_ge_sharp`), sharp Hardy split at `N^b`
   (`sq_vRow_le_split`), Fubini halving (`levyEnergy_windowTest_ge_fubini`), PNT for up-rows ⇒ `≈ 0.108` of the spacing for
   plateau profiles, `≈ 0.072` for all (`eventually_weilQuad_windowTest_nonneg_quarter`). With `|AB|` the method stays below
   `≈ K_RE/2`.
5. Pole cost is infinitesimal relative to the defect: `2|AB| ≤ ‖g‖²(εD_N + poleRelativeCost(K,ε)|x|²)`
   (`two_mul_abs_poleMoments_le_relative_defect`).
6. Beyond `K_RE` the atom block has a positive square along the pole vector (`eventually_not_stability_atomBlock`).
   Rank-two reduction: Weil ≥ 0 on atomic tests ⇔ `M ≥ 0` on `p = 0` and one scalar on `p = 1`
   (`forall_weilQuad_atomicTest_nonneg_iff`, `eventually_markovEnergy_pole_neg_and_gap`).
7. Atomic tests of ratio `K` live on measure `≤ K`; exhaustion needs `K ≥ log N − ε²` (`le_overlap_of_setIntegral_sq_le`);
   adapted families below Nyquist are Metzler (`markovPair_adapted_nonpos`).
8. Tower forms: `−F_p` Metzler, row sums `≤ 2d_p`; `F_p + c ≥ 0` ⇔ row-sum law (`towerFinitePart_add_nonneg_iff_rowSum`).
9. Tilted decomposition: atomic Gram = tilted model + NSD residual (`atomicIntersectionGram_eq_tiltedModel_add`); the tilt
   pays the polar dispersion of the atom pieces (`polarDispersion_le_sum_anchorReserve`).

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Metzler Hodge index: hyperbolic ⇔ `(TD)` ⇔ links | `isHyperbolic_iff_hasHyperbolicLinks` | proved |
| Metzler dichotomy | `qf_nonpos_of_mulVec_nonpos`, `isHyperbolic_iff_weightedTrickleDown` | proved |
| RH ⇔ scaling-surface Grams hyperbolic | `riemannHypothesis_iff_intersectionGram_isHyperbolicHerm` | equivalence |
| Sign = archimedean gauge-fixing; Lorentzian locus = archimedean characters | `exists_nonneg_gauge_iff`, `exists_nonneg_gauge_shifted_iff` | proved |
| Over `𝔽_q`: trickle-down = square-root count | `forall_weightedTrickleDown_iff_exists_pointCount_ge`, `golden_not_weightedTrickleDown` | proved |
| Ramanujan–Lorentzian rigidity | `ramanujan_lorentzian_rigid`, `not_isLorentzianPoly_at_prime` | proved |
| Optimal half-defect Hodge repair | `optimal_frobenius_hodge_repair` | proved |
| Frobenius conformal, Hecke isometric; isometric ladders carry no positive square | `frobeniusPullback_conformal`, `boost_isometry`, `forall_isHyperbolic_toeplitzLadder_iff` | proved |
| RH ⇔ Cayley ladder reflection positive ⇔ Li sign; `Re 2λ_n ↛ 0` | `riemannHypothesis_iff_cayleyLadder_nonpos`, `not_tendsto_xiLiPaired_re_zero` | equivalence; unconditional |
| Lorentzian Hessians, mixed Hessians, AF/KT | `isHyperbolic_hess`, `isHyperbolic_mixHess`, `alexandrov_fenchel` | proved |
| Euler product closure is Lorentzian and blind | `isLorentzianPolynomial_prod_subst`, `isLorentzian_iff_exists_hessAt` | proved |
| Atomic Weil positivity ⇔ `TD_π` below the spacing | `weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown` | proved |
| Weil ≥ 0 and Hodge index at `c★δ_N`, all `N` | `weilQuad_atomicTest_nonneg`, `atomicIntersectionGram_isHyperbolic` | proved |
| Weil ≥ 0 on all `C²` tests near the logarithms | `eventually_weilQuad_nonneg_of_support` | proved (eventually in `N`) |
| Quarter of the Robin–Euler threshold | `eventually_weilQuad_windowTest_nonneg_quarter` | proved (uses PNT) |
| Metzler threshold of overlap ratio = 1 | `metzlerThreshold_overlapRatio` | proved |
| Hyperbolicity blind, sign selective | `liouville_isHyperbolic_and_not_metzler` | proved |
| Hodge index = gap on pole complement + one scalar | `forall_weilQuad_atomicTest_nonneg_iff` | proved; gap open beyond `K_RE` |
| `TD_π` for `ζ` from `c★`/`K_q` up to the spacing | — | open |

## 6. Tools

**Developed**
- Degree-two calculus, Hermitian bridge, block Hodge index, nef shift (`LorentzianFormsAtDegreeTwo`,
  `TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity`, `TheFrobeniusLadderIsMetzler`).
- Trickle-down engine: variational eigenvector `exists_max_generalizedEigen`, active-variable reduction
  `isHyperbolic_of_weightedTrickleDown_active`, link construction `hasHyperbolicLinks_of_trickleDownIneq`, `mconvex_path`.
- Polar gluing law and `polarGlue` (`PolarGluingAndDispersion`); rank-two reduction `forall_add_two_mul_nonneg_iff`.
- Frustration lemmas `not_nonneg_gauge_of_neg_triangle`, `not_nonneg_gauge_of_odd_triangle`; unimodular rigidity
  `eq_of_conj_mul_nonneg`.
- Lorentzian polynomial calculus: `hess`, `mixHess`, closure under substitution/products/renaming, M-convexity.
- Atomic analysis: `markovPair` bilinearity, `markovPair_shift_ge`, `windowTest_of_support`, multiplicative Hardy
  (`sq_vRow_le`, `sq_vRow_le_split`), `sum_top_le_poleDefect_param`, `two_mul_sum_cross_le`, `sum_mul_upRow_sq_le_pnt`.
- Margin model `marginModel_isHyperbolic_iff`; covered-measure bounds; tower row-sum law; tilted decomposition.
- Half-defect repair and `hodgeCompletion` with exact rank budget.

**To build**
- A non-atomic basis (differences, Hecke orbits, wavelets) in which the overlapping form is Metzler, or a direct primitive gap
  `Q ≤ (1 − g)D` at fixed `K > 1`.
- Renormalized links from source pieces (tower forms, archimedean jump Laplacian, pole plane) with the `2d_p` row sums paid.
- A conformal correspondence over `ℤ` (factor `≠ 1`), or a source-built reflection-positive functional whose Cayley ladder is
  the Li ladder.
- A signed estimate that keeps the sign of `AB` (absolute payment caps at `≈ K_RE/2`).
- Transfer from bounded-overlap families to exhaustive ones (overlap `≍ log N`).

## 7. Open questions

1. `TD_π` for `ζ`'s atomic Gram between `K_q ≈ 0.108` and the spacing; equivalently the gap of `M` on the pole complement
   plus the scalar condition. Beyond `K_RE` the atom block alone is not NSD.
2. Who pays the tower deficits `2d_p` at small primes in a link decomposition (archimedean jump form, pole plane)?
3. Polar compatibility of atom pieces beyond the stability regime.
4. A Lorentzian lift of the Weil pairing (not of the Euler product) through the polynomial closure with Γ-term, pole plane
   and diagonal identified.
5. Is there a Metzler gauge in a non-atomic basis at overlap `K > 1`?
6. Exhaustion: atomic families of bounded overlap cover measure `≤ K`; can positivity at bounded `K` be assembled across
   scales into an exhaustive family?

## 8. Traps

| Trap | Fact |
|---|---|
| Local positivity at every prime ⇒ global Hodge index | Hyperbolicity is not closed under sums; the dispersion must be paid (`isHyperbolic_sum_iff_dispersion_le`) |
| `polarGlue` proves the Hodge index | It constructs a different form |
| Nonneg entries + connectivity ⇒ Hodge index | Golden datum has both and fails; trickle-down is the content |
| Nef-shift nonnegativity is information | It changes coordinates; Lorentzian in a nef basis ⇔ hyperbolic |
| Stability-regime positivity carries arithmetic | Holds for every sign twin, Liouville included |
| Better constants reach the spacing | `|AB|` payment caps near `K_RE/2`; beyond `K_RE` the pole vector is a negative direction of `M` |
| A better gauge restores Metzler beyond the spacing | Odd triangles frustrate every unimodular gauge for `K > 1` |
| Positive Euler product gives the arithmetic sign | Closure is Lorentzian for every nonneg datum (Beurling, fakes) |
| Local L-factors are Lorentzian by RH over `𝔽_p` | Lorentzian forces `a_1 ≥ d√q`; never at a prime |
| A Hecke dilation plays Frobenius | Dilations are isometries (boost); decaying isometric ladders carry no positive square |
| Li positivity is a weak sign | On the Cayley ladder the Metzler sign is RH |
| A uniform margin pays the pole | Fails by `K√log N`; the margin must grow along `n^{1/2}` |
| Positivity on tests near `log n` is exhaustive | Covered measure `≤ K`; exhaustion needs `K ≳ log N` |
| Jensen polynomials Lorentzian ⇒ real-rooted | Lorentzian is the log-concavity layer; Laguerre proved only on `s ≥ 0` |
| Successor gives a monotone transfer | Successor lowers and raises the prime form on the nonneg cone |

## 9. Context

**Uses**

| Programme | Imports | For |
|---|---|---|
| RHTower | 8 | Li criterion, ξ zeros, Kloosterman bound, ξ Taylor log-concavity, archimedean Lévy density, PNT inputs |
| ArithmeticCastelnuovoSeveri | 8 | scaling-surface Gram, `CurveDatum`, span defect, Pontryagin law, golden datum |
| SpacingScaleHarmonicAnalysis | 6 | Markov/Lévy form, stability law at the spacing, tilted prime rows, self-energy, diamagnetism |
| HTGeometry | 5 | inertia, Schur complements, Jacobian/derivation lemmas, integral Cauchy–Schwarz |
| RenormalizedArithmeticPotentialTheory | 4 | pole defect, finite part of the Markov form, tower finite part |
| BiarithmeticGaugeGeometry, ArithmeticIntersectionTheory, ArithmeticElectrostatics, ArithmeticEffectivityTheory, ArithmeticCriticalityTheory | 1 each | gauge torus, Hecke cocycle, atomic prime form, hyperelliptic calibration, Markov scaling |

**Used by**

| Programme | Modules | For |
|---|---|---|
| RenormalizedArithmeticPotentialTheory | 8 | full Weil matrix at the spacing, tower deficit payment, pole moments |
| TransMetzlerWeilPositivity | 3 | trans-Metzler decomposition, Liouville selectivity, plateau parameters |
| SelectiveMultiscaleArithmeticPositivity | 3 | pole hyperplane, twin-blind Haar floor |
| CriticalArithmeticCorrelationTheory | 3 | defect retention under signed sources and directed rows |
| HeckeKreinToeplitz, AdelicKreinGeometry, SuccessorShellArithmetic, RHTower | 1 each | outer Frobenius eigenvalues, separable assembly signature, shell cost, confinement as square-root count |

| Neighbour | Relation |
|---|---|
| ArithmeticCastelnuovoSeveri | owns the target (Hodge index of the scaling surface) and finite-field calibration data |
| SpacingScaleHarmonicAnalysis | owns the stability law; ALG converts it into Hodge index, `TD_π`, links |
| RenormalizedArithmeticPotentialTheory | mutual: supplies pole defect and finite parts; consumes ALG's atomic Gram and tower row sums |
| TransMetzlerWeilPositivity | continues the programme beyond the Metzler threshold |
| BiarithmeticGaugeGeometry | gauge torus and successor connection, read here as the archimedean gauge field |

## 10. Big picture

ALG asks whether the Hodge index of the scaling surface can be produced the way Lorentzian theory produces it: local
signature, a sign hypothesis, and trickle-down. The answer splits the problem cleanly. The sign hypothesis is real for
`ζ`: it is a gauge-fixing performed by the archimedean place along the successor, it selects the Euler point among all
twins, and it holds exactly up to atomic resolution. The positive square cannot come from any symmetry over `ℤ`, because
every available symmetry is an isometry; it comes from the pole plane. The multiplicative closure (Euler products) is
Lorentzian but blind, so arithmetic cannot enter there. What is left is the trickle-down inequality itself, which over
`𝔽_q` is the square-root count of points.

For `ζ`, trickle-down is a theorem on a fixed fraction of the spacing, and the hyperbolicity there is twin-blind: it holds
at the Liouville point. The programme therefore locates the RH content precisely: between the Robin–Euler threshold and the
spacing, on the pole complement, where a positive square of the Markov form along the pole vector has to be absorbed by the
pole plane. Absolute-value payment of the pole cannot reach it; the sign of the pole term and a non-atomic basis are needed.
The constructive tools (trickle-down engine, polar gluing, Hardy inequality with the prime defect) are the parts other
programmes reuse.
