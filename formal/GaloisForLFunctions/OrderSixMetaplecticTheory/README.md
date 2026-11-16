# Order-Six Metaplectic Theory over ℚ(ω) (OSM)

Namespace `GaloisForLFunctions.OrderSixMetaplecticTheory`; umbrella `OrderSixMetaplecticTheory.lean`.
Source: review-1511, obstacles summary §2.9 ("unbuilt programme: order-six metaplectic theory over ℚ(ω)").

## 1. Why this field

The only producer of a zero-free half-plane in the corpus is the cubic-theta probe over `K = ℚ(ω)`
(`Re s > 20999/24000`, MetaplecticMobiusDescent). Its budget is read in the twist exponent θ
(FamilyContinuationTheory): the half-plane is `½ + (1 − 1/n)θ/2` at `n = 6`. The room below `7/8` is
decided by one object, the **floor bin**, and CoherenceTheoryOfReciprocityFamilies (CRF) reduced its
binding part, the long columns, to a first moment: over the rows `u ∈ ℤ[ω]` of the probe, the root
number of the row character against a dual column `n`. The root number of a squarefree row is a
normalized **sextic** Gauss sum,

`Φ(c) = g_c^{(1)}(1)/|c| = G(c) γ₂(c)²`   (`rowRootNumber_eq_thetaPhase_mul_sq`),

with `γ₂(c)` the normalized cubic Gauss sum (the theta coefficient of the probe) and `G(c)` a phase of
conductor `4`. So the long columns are the **order-six Kubota series**

`Z(w; n) = Σ_c g_c^{(1)}(n) |c|^{−1} N(c)^{−w}`

and the floor bin is read on the curve of FCT by its row exponent `R₀`:

| `R₀` | origin | half-plane |
|---|---|---|
| `1` | triangle inequality | `13/15` |
| `5/6` | cubic large sieve, cross term `(MN)^{2/3}`; every square stops here | `5/6` (the free floor) |
| `2/3 = ½ + 1/6` | coherent main term of the order-six Kubota series | `7/9` (the bifurcation) |
| `(1 + Θ)/3` | main term evaluated, remainder from the zero-free region `Θ` of `ζ_K` | broken branch |
| `½` | main term evaluated, square-root remainder | `2/3` (the wall of the frame) |

OSM is the theory of `Z(w; n)`: its structure, its continuation, its main term and its remainder,
uniformly in the column. It decides how far the probe's floor bin can go below `5/6`.

**Thesis: order six is order three times order two.** Hasse–Davenport at the rows (CRF) and at the
columns (OSM) says that a sextic Gauss sum is a quadratic Gauss sum times a product of two cubic theta
coefficients. Every first moment of the floor bin is therefore a Rankin–Selberg series of the cubic theta
function `θ` with a dilate of itself, twisted by quadratic data, on the *cubic* cover, where the spectral
theory exists (SpectralTheoryOfTheCubicCover, STCC). The six-fold cover, its Eisenstein series and its
theta function — none of which is in the corpus, and whose theta coefficients are not determined by Hecke
theory — are replaced by cubic objects with quadratic characters; what the six-fold cover adds is exactly
the quadratic Gauss sum of the row at the odd part of the column.

## 2. Objects

| Object | Meaning | Lean |
|---|---|---|
| sextic symbol `χ_c(x)` | `(x/c)₃² (x/c)₂` for primary `c` prime to `6`; `χ_c² = (·/c)₃`, `χ_c³ = (·/c)₂` | `sexticSymbol` (FCT) |
| Gauss sums `g_c^{(j)}(h)` | `Σ_{d mod c} χ_c(d)^j ψ_c(hd)` | `sexticGaussPow` (FCT) |
| row root number `Φ(c)` | `g_c^{(1)}(1)/|c|` on squarefree rows | CRF |
| theta coefficient `G̃(c) = γ₂(c)` | normalized cubic Gauss sum; `G̃(ab) = \overline{(a/b)₃}G̃(a)G̃(b)`; `G̃³ = μ(c)c/|c|` | `normalizedCubicUnitGauss` (MMD), `thetaGauss` |
| Weil index `Γ(c)` | the normalized quadratic Gauss sum `g_c^{(3)}(1)/|c|`, a function of `c` modulo `4`, `= 1` on `c ≡ 1 mod 4` | `fixedDualAverage` |
| conductor phase `G(c)` | `\overline{χ_c(4)}Γ(c) = (c/−2)₃²Γ(c)` | `thetaPhase`, `conj_sexticSymbol_four` |
| column `n = n₁n₂²k³` | the cube-free and odd-exponent decomposition of a column | `rowRoot_column_hasseDavenport` |
| shifted theta product | `G̃(−2n₁n₂c)G̃(n₁c)`: the cubic content of the row at a column | `rowRoot_column_shift_actual` |
| order-six Kubota series `Z(w; n)` | the row-root-number series at column `n`; absolutely convergent on `Re w > 1`; Kubota pole at `½ + 1/6` | — |
| sixth-power-free rows | `u = a·b²c³d⁴e⁵`; the root number on the conductor `a·bcde` | `rowConductorGauss` |
| cubic theta `θ`, coefficients `T(ν)` | residue of the cubic Eisenstein series at `4/3`; `T(ab³) = C|b|\overline{(δ/a)₃}G̃(a)` | MMD, STCC |
| theta-square weight `σ(A)` | `((9/a)₃\overline{G̃(a)})²`, `T(a)² = C̄²σ(a)`; `Φ = G(9/c)₃²σ̄` | `thetaSquareWeight` (STCC) |
| Rankin–Selberg series | `D(w) = Σ T(ν)² N(ν)^{−w} = C̄² Z₀(3w − 1) Σ_{u,m}(…) S_{uλ^m}(w)`; `S₁` the untwisted squarefree series | STCC |
| completed unramified theta square `Λ₀` | the continuation of `M(s)·D₀(s)` on `1 < Re s < 13/3` | `completedUnramified` (STCC) |
| sextic large-sieve norm `B₆(M, N)` | the norm of `(χ_m(n))` on squarefree `N(m) ≤ M`, `N(n) ≤ N` | — |

## 3. Language

- **Rows and columns**: rows `u` carry root numbers `Φ(u)`; a column `n` twists them by `\overline{χ_u(n)}`.
- **Main term, remainder**: `Σ_{N(u) ≤ U} Φ(u) ξ_n(u) = ρ(n) U^{2/3} + E(U; n)`; the **remainder exponent**
  is the infimum of `β` with `E ≪ U^{β+ε}` (sharp or smoothed).
- **Uniform in the column / on average over columns**: the remainder bound with constants independent of
  `n`, or for `Σ_n |b(n)||E(U; n)|` — the form the floor bin uses.
- **Shift**: a column's cubic content `G̃(pc)G̃(qc)` — a Rankin–Selberg product of `θ` with a dilate.
- **Quadratic content**: the normalized quadratic Gauss sum of the row at the odd part of the column.
- **Cube convolution**: `D = C̄² Z₀(3w − 1) S`, the passage between all frequencies and squarefree ones; it
  divides by `ζ_K` at `3w − 1`.
- **Layers of a row**: `u = a·b²c³d⁴e⁵`; the squarefree layer `a` and the higher layers `b, c, d, e`.

## 4. Mechanisms

1. *Hasse–Davenport at the rows* (CRF). `χ_c(4) N(c) g^{(1)} = g^{(3)} (g^{(2)})²`: `Φ = Gγ₂²`.
2. *Hasse–Davenport at the columns* (OSM). Twisted multiplicativity of `G̃` turns the cubic character of a
   column into a shift: `(c/n₁)₃(c/n₂)₃²G̃(c)² · G̃(n₁n₂)G̃(n₁) = G̃(n₁n₂c)G̃(n₁c)`. The cubic part of the
   conductor phase is the shift by `−2`. Quadratic reciprocity turns `(c/q)₂Γ(c)` into the quadratic Gauss
   sum `r(q, c)g_c^{(3)}(q)/|c|`.
3. *Layer peeling* (OSM). CRT on the conductor of a sixth-power-free row splits off the squarefree layer;
   sextic reciprocity turns the cross factor into the column `b³c²d` of that layer.
4. *Rankin–Selberg on the cubic cover* (STCC). Unfolding `θ²` against the cubic Eisenstein series, a
   bounded renormalization and the `L²` resolvent give the continuation of `M(s)D(s)` to
   `1 < Re s < 13/3` with a double pole at `4/3` (`108π³r³`); opposite translations by `±ω` isolate the
   unit layer `S₁`.
5. *Real spectral poles* (OSM). At a real `μ = s₀(2 − s₀) ∈ [0, 1)` the resolvent has a simple pole with
   residue the eigenprojection; the seed defect only sees the constant term, so only `8/9` (`s = 4/3`) is
   seen by the cusp and the continued correction is holomorphic across the real axis.
6. *Cube convolution in both directions* (OSM, STCC). The squarefree series is `D/Z₀(3w − 1)`. The seed
   `Θ ≤ 7/8` continues it to `Re w > (1 + Θ)/3` (STCC: smoothed main term with remainder `X^a`, `a > 5/8`).
   Conversely a remainder `O(X^β)` makes `S₁ − main` holomorphic on `Re w > β` (Abel summation or the
   Laplace transform of the smoothing), so every zero `ρ` of `ζ_K` with `Re ρ > 3β − 1` must be a zero of
   `Λ₀(2(1 + ρ)/3)`.
7. *Heath-Brown recursion* (MMD, order three). Poisson in the long variable turns a character matrix of
   order `k` into Gauss sums of order `k`; principal dual frequencies give the cross term.
8. *Hecke at a primary prime* (OSM), first at the inert prime 2. The correlation `θ(Aw)θ(A⁻¹w)` lives on the level-2 subgroup `Γ_A`
   because the 2-adic nebentypus of the two Hecke points cancels; its trace back to `Γ(3)` runs over
   `P¹(𝔽₄)` and its constant term is a shifted square plus a cubic twist at `2`, produced by the Gauss sum
   of `𝔽₄`. No Eisenstein series of level `2` is needed: the trace lives where `E_{Γ(3)}` already does. At a
   general primary prime `p` the cosets are the pairs of distinct points of `P¹(O/p)`, the dilate cosets give the
   shifted square at `p²`, and the phased cosets give the Gauss sum `g(χ², 9k)`, which Patterson's relation turns
   into the dilate correlation `|p|T(k)T(kp)`. Patterson again reduces the shifted square to the dilate correlation,
   so one trace isolates the cubic twist at `p`.
9. *Subtract the square, keep the remainder bounded* (OSM). `Tr F − 8θ²` has no growth; a bounded remainder
   with `O(v^{−7/3})` decay unfolds against `E(s)` to the Mellin transform of its constant term and has at
   most a simple pole at `4/3`, so the double pole of the twisted combination equals that of `D`.

## 5. Pillar theorems

**From the corpus** (inputs, Lean).

| Theorem | Lean |
|---|---|
| sextic symbols, reciprocity, twisted multiplicativity of the sextic Gauss sums, Gauss CRT | `sexticSymbol_reciprocity`, `sexticGaussPow_mul`, `sum_crt_mul_traceChar` |
| Hasse–Davenport at the rows; `Φ = Gγ₂²`; `γ₂³ = μ(c)c/|c|` | `rowHasseDavenport`, `rowRootNumber_eq_thetaPhase_mul_sq`, `thetaGauss_cube` |
| the reflected Gram is twisted by `Φ`; rank one at sixth-power frequencies | `gramCoeff_eq_thetaSquares`, `gramCoeff_sixthPower` |
| the cubic theta function, its coefficients on squarefree × cube indices, twisted multiplicativity of `G̃` | `normalized_sourceFourier_squarefree_cube`, `normalizedCubicUnitGauss_coprime_product` |
| Rankin–Selberg of `θ²`, the double pole, the nine twists, the unit layer `S₁` and its pole | `thetaSqDirichlet_double_pole`, `thetaSqDirichlet_eq_zeta_mul`, `untwistedSquarefreeSeries_simple_pole` |
| the smoothed main term of `S₁` | `gaussianSmoothedUntwistedTheta_main_term` |
| the cubic large sieve `(M + N + (MN)^{2/3})(MN)^ε` | `CubicSieve.sieveNorm_sharp` |
| the floor-bin curve and its bifurcation at the Kubota exponent `½ + 1/n` | `signedGramBrokenTheta`, `kubota_pole_eq_signedGram_bifurcation` |
| the seed | `riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`, `hecke_ne_zero_of_sub_seven_eighths_lt_re` |

**Of this programme** (Lean).

| Theorem | Content | Lean |
|---|---|---|
| The bridge | the additive normalizations of FCT/CRF and MMD agree; `γ₂ = G̃`; `Φ = G(9/c)₃²σ̄`; the column law `g_c(n) = r̄(n,c)(c/n)₃(c/n)₂g_c(1)`; the tower law `\overline{(c/|c|)}^{6k}Φ = Gγ₂²γ̄₂^{18k}` | `rowRootNumber_eq_conj_thetaSquareWeight`, `rowRoot_column`, `rowRoot_tower` |
| Hasse–Davenport at the columns | at `n = n₁n₂²k³`: `g_c(n)/|c| · G̃(−2n₁n₂)G̃(n₁) = r̄(n, c) r(n₁k, c) · g_c^{(3)}(n₁k)/|c| · G̃(−2n₁n₂c)G̃(n₁c)`; square columns are cubic, cube columns are quadratic twists | `rowRoot_column_hasseDavenport`, `rowRoot_column_shift_actual`, `rowRoot_square_column_shift`, `rowRoot_cube_column` |
| The conductor phase is a shift | `\overline{χ_c(4)} = (c/−2)₃²`, `Φ(c)G̃(−2) = Γ(c)G̃(−2c)G̃(c)` | `conj_sexticSymbol_four`, `rowRootNumber_shift_neg_two` |
| Layers of a row | `g(χ_{a·b²c³d⁴e⁵}) = r(a, M) · g_a(b³c²d) · g(χ_M)`, `M = b²c³d⁴e⁵`: the squarefree layer sits at the column `b³c²d` | `rowConductorGauss_layers`, `rowConductorGauss_peel` |
| Real spectral poles | at real `μ ∈ [0, 1)`: `R(z) = ((μ+1)/(μ−z))Π_μ + R_reg(z)`; the pencil is invertible off its eigenvalues | `resolvent_eventually_eq`, `spectralForm_eventually_isUnit` |
| Only `8/9` is seen by the cusp | the seed defect reads the constant term; `Π_μ defect(s₀) = 0` for real `1 < s₀ ≤ 2`, `s₀ ≠ 4/3`; the correction continues to `Re s > 1`, `s ≠ 4/3`, with `‖Corr(s)‖ ≤ ‖defect(s)‖/(2|Im s|(Re s − 1))` | `integral_star_defect_mul`, `eigenProjection_seedDefect_eq_zero`, `correctionExt_analyticOnNhd`, `norm_correction_le` |
| The remainder reads the zeros of `ζ_K` | if the sharp or Gaussian-smoothed sums of `σ` are `c·X^{2/3} + O(X^β)`, every zero `ρ` of `ζ·L(·, χ₋₃)` with `Re ρ > max(½, 3β − 1)`, `Im ρ > 0` is a zero of `Λ₀` at `2(1 + ρ)/3` | `remainder_forces_thetaSquare_zero`, `smoothedRemainder_forces_thetaSquare_zero`, `smoothedRemainderExponent_ge` |
| Conjugation | `(x̄/c̄)₃ = \overline{(x/c)₃}`, `G̃(c̄) = \overline{G̃(c)}`; the theta-square weights, the Gauss-sum Dirichlet series at both cusps, and the Whittaker factor at rational rows are conjugation symmetric | `symbol_conjO`, `normalizedCubicUnitGauss_conj`, `thetaSquareWeight_conj`, `arithmeticDirichletSeries_conj`, `unramifiedCubicGaussSeries_conj`, `cuspWhittakerHeightFactor_star` |
| The cubic theta function is conjugation symmetric | the continued cusp coefficients satisfy `K_{h̄}(s̄) = \overline{K_h(s)}` off the real axis (identity theorem from `Re s > 4` in the lower half-plane); residues at `4/3` conjugate: `T(h̄) = \overline{T(h)}`; `C` is real; `T(ω²λ²)` is real | `reflection_of_initial`, `residue_star_of_reflection`, `rationalSourceResidualFourierCoefficient_conj`, `rationalSourceThetaScalar_star` |
| Positive main term | `G(X) = κX^{2/3} + O(X^{13/20})` with `κ > 0`: `C² > 0`, `r > 0`, `L(1, χ₋₃) > 0` (the cleared cube zeta is positive on the real ray), `M(4/3) > 0`; the smoothed sum is real for every `X` | `gaussianSmoothedUntwistedTheta_positive_main_term`, `LFunction_chi3D_one_isPosReal`, `star_gaussianSmoothedUntwistedTheta` |
| The order-six family is 2-ramified | `Φ(c) = Γ(c) χ₂(c) G̃(c)²` with `χ₂ = (·/−2)₃²`; `Γ(ωc) = Γ(c)` and `χ₂(ω) ≠ 1`, so `χ₂` is orthogonal to every `ω`-invariant function modulo `4`: at every column the 2-adic phase `\overline{r(n, c)}Γ(c)χ₂(c)` has mean zero, and the family contains no untwisted theta square and no twist unramified at `2`, at every column and in every layer; `ω₆(c̄) = \overline{ω₆(c)}`, so the smoothed order-six first moment is real | `rowRootNumber_eq_weil_mul_cubicTwo`, `sum_mul_cubicTwoChar_eq_zero`, `sum_column_phase_mul_cubicTwoChar`, `sum_layer_phase_mul_cubicTwoChar`, `star_gaussianSmoothedOrderSix` |
| The order-six family twists the plain squares | `(ω²λ²)² = 9`, so the coefficient of the 3-adic twist `S_{ω²λ²}` is `\overline{G̃(c)}²`, and `ω₆(c) = Γ(c)χ₂(c)\overline{(ω²λ²/c)₃²σ(c)}`: the family is the 2-adic Weil twist of `\overline{S_{ω²λ²}}`, the plain mean of the squared Gauss sums; its Rankin–Selberg weight `(T(ω²λ²)/T(1))²` is nonnegative real | `twisted_coefficient_eq_plain_square`, `orderSixWeight_eq_conj_plain`, `plain_square_weight_nonneg` |
| The Hecke-at-four trace | `F = θ(A·)θ(A⁻¹·)`, `A = diag(√2, 1/√2)`, has multiplier `κ²` on `Γ_A = Γ(3) ∩ {2 ∣ b, 2 ∣ c}`; `Γ(3)/Γ_A` is the set of ordered pairs of distinct points of `P¹(𝔽₄)`; the trace `Tr F` is `κ²`-automorphic on `Γ(3)`, `SL₂(ℤ)`-invariant, and a phased sum of products of `θ` at Hecke points | `heckeFourCorrelation_automorphy`, `heckeFourTrace_automorphy`, `heckeFourTrace_eq_hecke`, `heckeFourTrace_rational` |
| The trace reads the cubic twist at 2 | `∫_P Tr F(z + jv) = 8|P|(Σ_h b(2v, h)b(v/2, −4h) + Σ_h χ(h)b(v/2, h)b(v/2, −h))`, `χ(h)` the cube root of unity `≡ h mod 2` (the Gauss sum `Σ_u uψ(hu²) = 2χ(h)` of `𝔽₄`) | `integral_sourceFourTrace`, `gaussFour` |
| The trace is eight theta squares up to a bounded remainder | `G' = Tr F − 8θ²` is bounded, `O(v^{−7/3})` above any height, and decays at the ramified cusps (Hecke points of a ramified cusp are ramified) | `fourRemainder_bounded`, `norm_fourRemainder_strip`, `sourceTheta_hecke_ramified` |
| Bounded remainders have at most a simple pole | the Rankin–Selberg integral of a bounded `κ⁻¹`-automorphic function with `O(v^{−7/3})` decay is the Mellin transform of its constant term on `2 < Re s < 13/3`, continues to `1 < Re s < 13/3`, and `(s − 4/3)²Λ_G → 0` | `RemainderData`, `pairing_eq`, `pairing_near_four_thirds` |
| The 2-adic cubic twist has the double pole of `θ²` | with `D₄(s) = Σ T(h)T(−4h)(4π|ξ_h|)^{−s}` and `L_χ(s) = Σ χ(h)T(h)²(4π|ξ_h|)^{−s}`: `M(s)(2^{−s}D₄(s) + 2^{s−2}L_χ(s))` continues to `1 < Re s < 13/3` and `(s − 4/3)²` times it tends to `108π³r³ ≠ 0`, the double pole of `D` | `twoAdicCubicTwist_double_pole` |
| Patterson at two separates the twist | `T(h)T(−4h)` vanishes unless `v₂(h) ≡ 1 mod 3`, so `D₄ = 2·2^{−s}\overline{G̃(−2)}(1 − 4·2^{−3s})^{−1}L_χ`, and `χ(h) = (h/−2)₃`; hence `(s − 4/3)²M(s)L_χ(s) → 108π³r³/c(4/3)`, `c(4/3) = 2^{−2/3}(1 + ⅔\overline{G̃(−2)}) ≠ 0`: the cubic twist at 2 of the theta square keeps the double pole | `besselDirichlet_fourShiftCoeff`, `cubicTwistCoeff_eq_symbol`, `cubicTwistAtTwo_double_pole` |
| The Hecke trace at every primary prime | for primary `p`, `F = θ(A_p·)θ(A_p⁻¹·)`, `A_p = diag(√p, 1/√p)`, has multiplier `κ²` on `Γ_p = Γ(3) ∩ {p ∣ b, p ∣ c}`; `Γ(3)/Γ_p` = ordered pairs of distinct points of `P¹(O/p)`; the trace is `SL₂(ℤ)`-invariant and `Tr_p − 2N(p)θ²` is a bounded remainder; its constant term is `N(p)|P|(2c²v^{4/3} + 2|p|^{−2}R_{p²}(|p|v) + |p|R_{dil}(v/|p|))`: the twisted cosets carry the Gauss sum `g(χ², 9k)`, which Patterson's relation turns into `|p|T(k)T(kp)` | `heckeTrace_eq_hecke`, `heckeTrace_rational`, `remainder_remainderData`, `twistedCoeff_eq_gauss`, `integral_sourceHeckeTrace_bessel` |
| Every cubic twist keeps the double pole | for every primary prime `p` (`ρ = |p|`): `(s − 4/3)²M(s)Σ_{p∤k}T(k)T(kp)(4π|ξ_k|)^{−s} → 216π³r³/c_p(4/3)` and `(s − 4/3)²M(s)Σ_k(k/p)₃T(k)²(4π|ξ_k|)^{−s} → 216π³r³/(c_p(4/3)(9/p)₃\overline{G̃(p)}) ≠ 0`, `c_p(4/3) = ρ^{1/3}(N(p) + 1)/(N(p) − 1)` | `dilateCorrelation_double_pole`, `cubicTwistAtPrime_double_pole`, `dilateFactor_four_thirds` |

## 6. Questions

| # | Question |
|---|---|
| Q1 | **Bridge.** Is the row-root-number series at every column a combination, with coefficients of bounded conductor, of Rankin–Selberg series of the cubic theta function? Pointwise the answer is Hasse–Davenport at the columns: a shifted theta product times the quadratic Gauss sum at the odd part of the column. Open: the series-level statement in the theta coefficients `T` (the 3-adic twist `(9/c)₃` between `G̃` and `T`) and the class restriction modulo `4` of the Weil index. |
| Q2 | **Residues.** The residue at `2/3` of the actual row family at column `n` and under bounded reweighting: the order-six theta coefficients. By Q1 they are residues of shifted cubic theta products with quadratic twists. Closed form? Which reweightings kill them? Known: `S₁` (the family reweighted by `\overline{G}(9/·)₃`) has a nonzero residue (STCC); it is a positive real number and the theta scalar `C` is real (conjugation symmetry). The actual family is orthogonal to `S₁` and to every twist unramified at `2` (its 2-adic phase has mean zero modulo `4`): its residue is a combination of residues of theta squares twisted by characters ramified at `2`. Its 3-adic part is the twist `S_{ω²λ²} = Σ \overline{G̃(c)}² N(c)^{−w}` (the plain mean of the squared Gauss sums), not `S₁`. Every cubic twist keeps the double pole: for every primary prime `p`, `L_{χ_p} = Σ(k/p)₃T(k)²(4π|ξ_k|)^{−s}` has leading coefficient `216π³r³/(c_p(4/3)(9/p)₃\overline{G̃(p)})`, `c_p(4/3) = |p|^{1/3}(N(p) + 1)/(N(p) − 1)`, and the dilate correlation `Σ_{p∤k}T(k)T(kp)` has `216π³r³/c_p(4/3)` (Hecke trace at `p` plus Patterson at `p`); at `p = −2` this is the 2-ramified twist `L_χ`. Open: the Klein twists `η` and the 3-adic layer `ω²λ²` of this twist. |
| Q3 | **Remainder.** The remainder exponent of the first moment, for one column and on average over columns. At the unit layer it is the zero-free region of `ζ_K` read at `3w − 1`, from both sides: `(1 + Θ)/3` is reached through the seed, and a zero `ρ` with `Λ₀(2(1 + ρ)/3) ≠ 0` forbids every exponent below `(1 + Re ρ)/3`. Open: the actual family and the columns. |
| Q4 | **Functional equation** of `Z(w; n)` with explicit column dependence: needs the continuation of the cubic Eisenstein series across `Re s = 1`. |
| Q5 | **Sextic large sieve** `B₆(M, N)`. A square stops the floor bin at `5/6` whatever its cross term; the sieve matters for the mean over columns of the remainders, not for the main term. |
| Q6 | **Layers.** Every sixth-power-free row is a squarefree row at a column (`rowConductorGauss_layers`); open: the analytic summation over the higher layers with column-dependent remainders. |
| Q7 | **Tower.** The same statements along `k ↦ 6k + 1` (Grössencharacters of infinity type `6k`): non-spherical Eisenstein series of the cubic cover. |
| Q8 | **Decision.** Success (remainder `U^{½+ε}` uniform in the column: the curve reaches `2/3`) or kill (a main term of order `U^{2/3}` that no admissible reweighting removes). At the unit layer the success criterion is RH for `ζ_K` up to coincident zeros of `Λ₀`; the attainable target is the main term plus the remainder `(1 + Θ)/3`, and below `5/6` the decision is the coherence of the main terms across columns. |

## 7. Traps

| Trap | Truth |
|---|---|
| `μ(c)·c/|c|` in the root number is a twist that kills the metaplectic main term | it is `γ₂(c)³`: the root number is a sextic Gauss sum, coherent at `2/3` |
| The six-fold theta coefficients need the six-fold cover | they are residues of cubic theta products with quadratic twists (Hasse–Davenport at the columns) |
| The conductor phase is a bounded nuisance | its cubic part is the shift by `−2`; only the Weil index `Γ(c)` (conductor `4`) is quadratic |
| A double pole of `D` at `2/3` is a pole of the squarefree series | the cube frequencies alone give a simple pole; the squarefree part needs the double pole (STCC) |
| The nine twisted squarefree series separate from `D` and the rotations | every coefficient at ramified layers is an undetermined `T(uλ^m)`; rotated correlations weight `T(ωh)T(h)` |
| `G̃` and `T` are the same coefficients | `T(a) = ±C̄(9/a)₃\overline{G̃(a)}`: Rankin–Selberg series in `T` carry the 3-adic twist `(9/c)₃` relative to the row family |
| Squarefree extraction is free | it divides by `ζ_K(3w − 1)` and inherits its zeros, in both directions |
| A square-root remainder for the squarefree rows is a spectral question | it forces every zero of `ζ_K` right of the critical line onto the zeros of `Λ₀(2(1 + ·)/3)` |
| The sextic matrix is the Hadamard product of a quadratic and a cubic matrix, so its norm is bounded by theirs | the Hadamard bound needs a bounded factorization of one factor, which the quadratic matrix lacks |
| A remainder uniform in a single column is what the probe needs | the floor bin sums columns with weights; the usable statement is a mean value over columns |
| Kubota's pole is at `1 + 1/n` | for normalized Gauss sums it is at `½ + 1/n` |
| The fifth-power layer of a row twists the squarefree layer | it is invisible to it: `χ_a(e⁶) = 1` |
| The phase of the theta scalar `C` is an analytic unknown | conjugation conjugates both Gauss-sum series behind `ρ(1)`, so reflection makes their residues real: `C ∈ ℝ`, and the `S₁` residue is positive |
| Reflecting a continued coefficient needs its values on the real segment | the resolvent identification holds at every nonreal spectral parameter; the initial region in the lower half-plane and the identity theorem suffice |
| The positive main term of `S₁` is the main term of the order-six family | the 2-adic phase `Γ(c)(c/−2)₃²` of the family has mean zero modulo `4`; only theta squares twisted by characters ramified at `2` contribute, and the 3-adic partner is `S_{ω²λ²}` (plain squares), whose weight in `D` is `(T(ω²λ²)/T(1))²` |

## 8. Tools this programme develops

1. The bridge between the root numbers of the rows (FCT/CRF normalization) and the coefficients of the
   cubic theta function (MMD/STCC normalization). (Lean)
2. Hasse–Davenport at the columns and the layer peeling: every row at every column as a shifted theta
   product times a quadratic Gauss sum. (Lean)
3. Real-axis spectral theory of the cubic cover: simple real poles of the resolvent, the seed defect as a
   constant-term functional, holomorphy of the continued Eisenstein correction across the real axis. (Lean)
4. The cube convolution in both directions: Abel summation and the Laplace transform of the Gaussian
   smoothing turn remainders into holomorphy and force the zeros of `ζ_K`. (Lean)
5. Conjugation and reflection: `c ↦ c̄` on symbols, Gauss sums, both cusp Dirichlet series and the Whittaker
   factors; reflection of continued cusp coefficients across the real axis; reality of residues. (Lean)
6. Hecke correlation traces at every primary prime: `θ(A_pw)θ(A_p⁻¹w)` traced from `Γ_p` to `Γ(3)`, its coset geometry
   over `P¹(O/p)`, Bezout factorization of the Hecke points, invariance under `SL₂(ℤ)`, the constant term with the
   Gauss sum of `χ²`, the bounded-remainder Rankin–Selberg lemma, and Patterson's reduction. (Lean) Composite
   moduli and cubic Eisenstein series of `Γ(3) ∩ Γ₀(m)` with nebentypus. (open)
   Concretely: the spectral theory of MMD (energy graph, resolvent, Eisenstein series) on `L²(H\ℍ³)` for
   finite-index `H ≤ Γ_ker`; the 2-adic covers only see `θ`'s expansion at `∞` and the four rational cusps.
7. Quadratic twists of `θ` (translates by `(1/q)O`, level `q²`) and the 3-adic layer `(ω², 2)` (translates by
   `λ^{−1}O`, level `3λ`). (open)
8. A sextic large sieve over `ℤ[ω]`. (open)

## 9. Position in the corpus

| Programme | Relation |
|---|---|
| CoherenceTheoryOfReciprocityFamilies | the consumer: owns the floor bin, the long columns and the reflected Gram |
| SpectralTheoryOfTheCubicCover | the spectral engine: Rankin–Selberg of `θ²`, double poles, nine twists, the unit layer `S₁`, its vertical growth and smoothed main term |
| MetaplecticMobiusDescent | the cubic cover, Kubota character, Eisenstein series, residue `θ`, `L²` resolvent, cubic large sieve, the seed |
| FamilyContinuationTheory | sextic symbols and Gauss sums, Gauss CRT, the frame, the budget curve in `R₀`, the tower |
| ExponentDynamicsOfTheCriticalStrip | the rungs as tensor powers of cubic Gauss sums (O3), Gauss pairings |
| TensorPowerProgramme | frames and the sign line; the Gauss-pairing classification |

Obstacle map (review-1511): the classical part of this programme is J6, the open part is O2 (signed
evaluation before Cauchy–Schwarz); Q7 is O3.

## 10. Success criteria

1. Q1: the row-root-number series at every column as Rankin–Selberg data of the cubic cover (pointwise:
   done; series level in `T`: open).
2. Q2: the main term of the actual row family with its residue in closed form, and the reweightings that
   kill it.
3. Q3: the remainder exponent of the first moment — at the unit layer pinned to the zero-free region of
   `ζ_K`; for the actual family and on average over the columns the floor bin uses.
4. Q8 decided: the coherence of the main terms across the columns, and the floor-bin exponent it leaves.

## 11. What a contribution must be

- It is a statement about the actual sextic Gauss sums of `ℤ[ω]` and the actual cubic cover, not a model.
- It moves Q1–Q8: a structure identity, a continuation, a residue, a remainder exponent, a sieve bound, or
  a refutation.
- Its exponents are stated in the variable `w` of the row norm and translated to `R₀` and the
  half-plane of the probe.
- It is calibrated: a statement that would also hold for random unimodular phases, or for order two,
  is not a statement about order six.
- Unconditional in Lean; an implication counts only when the implication is the content and its premise
  is named as open.

## 12. Open research topics

1. **The core analytic object.** `Σ_c ψ(c) T(−2n₁n₂c)T(n₁c) N(c)^{−w}` with `ψ` the quadratic Gauss sum at
   `n₁k` and `(9/c)₃`: continuation to `Re w > (1 + Θ)/3`, residue at `2/3`, dependence on the column.
   At column `1` it is a combination of the residues of `Σ_c ψ(c) G̃(c)² N(c)^{−w}` over the characters
   `ψ = ηχ₂` of `(O/4)^×` (`χ₂ = (·/−2)₃²`, `η` on `(1 + 2O)/(1 + 4O)`), with the coefficients of `Γ` on the
   Klein group (all nonzero). `S₁` gives one relation: splitting off the rows divisible by `−2` (twisted
   multiplicativity) ties the odd untwisted residue to the odd `χ₂`-twisted residue. Products `T(c)T(pc)` reduce
   to cubic twists of `T(c)²` by the prime recurrence, so the 2-ramified twists are the new objects.
2. The Rankin–Selberg series of `θ(w)θ(A_m w)`: done at every primary prime `m = p` (the dilate correlation and the
   cubic twist `L_{χ_p}` have explicit double poles). Open: composite columns `n` (twists by `(·/n)₃`, Hecke traces at
   products of primes) and the coherence of `c_p(4/3)` across columns.
3. Quadratic twists of `θ` and their cusp growth: does a quadratic twist keep the double pole?
4. The 3-adic theta coefficients `T(uλ^m)` and the layer `(ω², 2)` that carries `(9/c)₃`. Known: `T(uλ) = 0`,
   `T(u) = 0` for `u ≠ ±1` (STCC); conjugation pairs `T(uλ^m)` with `T(ū(−ω²)^mλ^m)`, so `T(ω²λ²)` is real.
5. The Weil index `Γ(c)` on classes modulo `4`: class-restricted residues and their signs (the unrestricted
   `S₁` residue is positive).
6. Mean over columns: a spectral or sextic large sieve for the column remainders.
7. Higher layers of sixth-power-free rows with column-dependent remainders (Q6).
8. Non-spherical twists along the tower (Q7).
