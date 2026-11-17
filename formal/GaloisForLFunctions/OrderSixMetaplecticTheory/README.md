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
| order-six Kubota series `Z(w; n)` | the row-root-number series at column `n`; absolutely convergent on `Re w > 1`; Kubota pole at `½ + 1/6` | `columnSeries`, `orderSixSeries` (column `1`) |
| Klein characters `κ_s` | `κ_s(1 + 2t) = (−1)^{tr(st)}` on `(1 + 2O)/(1 + 4O) ≅ 𝔽₄`, read on `c³`; `Γ = ½(1 + κ₁) + (i/2)(κ_{ω²} − κ_ω)` | `kleinChar`, `fixedDualAverage_eq_klein` |
| layers `S^ψ_{h₀}` | `Σ_{A squarefree}ψ(gen A)(h₀/gen A)₃²σ(A)N(A)^{−w}` for a multiplicative twist `ψ`; nine of them (`h₀ = uλ^m`) make `Q_ψ` | `twistedSquarefreeSeriesG` |
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
- **Grade and pole order**: a twist `ψ` of `θ²` factors as `L_ψ(s) = C̄²Z_{ψ³}(3s/2 − 1)Q_ψ(s)`. The cube factor
  `Z_{ψ³}(z) = Σ_Bψ(gen B)³N(B)^{−z}` collects the cube frequencies; the **squarefree combination**
  `Q_ψ = Σ_{u,m}ψ(uλ^m)(T(uλ^m)/T(1))²(4π|ξ_{uλ^m}|)^{−s}S^ψ_{uλ^m}(s/2)` collects the nine 3-adic **layers** `S^ψ_{uλ^m}`. In
  the cubic grade (`ψ³ = 1`) the cube factor is `Z₀` without its Euler factor at `q`, with its pole: a **double** pole of `L_ψ`
  is a **simple** pole of `Q_ψ`. In the quadratic grade (`ψ³ = λ_q`, `N(q) ≡ 1 mod 4`) it is the Hecke `L`-function
  `L(·, λ̃)`, entire and nonzero at `1`: `L_ψ` and `Q_ψ` have the same pole order. The family itself is one layer
  (`S_{ω²λ²}`); `L_ψ` sees the layers only through `Q_ψ`, but every layer is the unit layer of the unramified theta square `D₀^{ψ'}` of a twist `ψ' = ψξ_{h₀}` (times `η₃` if `ψ` is odd), with no 3-adic weights.

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
10. *Opposite fractional translations* (OSM). A translation by `3t/q` is not in `Γ(3)`: under `δ ∈ Γ(3) ∩ Γ₀(q²)` it moves
   `θ(T_t·)` to `κ(M_t)θ(T_{td²}·)`. The product `θ(T_tw)θ(T_{−t}w)` has the multiplier `κ(δ)²`, because the two
   denominators multiply to `a² − (3tc/q)²`. The trace
   reads three kinds of pairs: the `q`-divisible frequencies at `∞`, Jacobi phases `χ(1 − s²)` over the middle cusps,
   and low points of low points with phases `χ(−9t²)` over `0`, whose Gauss sums `Σ_tχ(9t²)ψ(c/t)` produce the
   **conjugate** character `χ̄_q` — unreachable by Hecke traces, which only see `χ_q`. The main coefficient
   `N² + N + (N − 1)J` carries the cubic–quadratic Jacobi sum: order six enters through the trace geometry.
   Weights on `t` must be invariant under squares (`t ↦ td²`): the constant `1` and the quadratic character `λ`.
   The weight `λ` removes the `θ²` main term (`Σλ = 0`) and turns the Gauss sums of the cusp `0` into sextic ones.

11. *The quadratic grading* (OSM). Characters modulo `q` split into the cubic grade `{1, χ, χ̄}` and the quadratic
   grade `{λ, λχ, λχ̄}`. A trace weighted by `λ` sees only the quadratic grade: orthogonality removes every term of
   the cubic grade, including `θ²`. Its relations among double poles are therefore homogeneous; the cubic grade has
   the inhomogeneous anchor `D`. A single translate already carries `κ(M_t) = κ(δ)`: the symbol `(c/b)₃` only sees
   `b` modulo `q` and modulo `9c/q²`, and `3tc/q` vanishes modulo both. So every ratio pair sum
   `Σ_tλ(t)θ(T_tw)θ(T_{ct}w)` traces to `Γ(3)`. At level `q²` they all give the relation of `G_λ`: completing the square,
   `Σ_s(λχ)((1 + s)(1 + cs)) = (χλ)(−(1 − c)²/(4c))J₆`.
12. *The grade factorization* (OSM). `T(ab³) = |b|T(a)` (squarefree `a`, unramified `b`) moves the cube frequencies
   onto `ψ(gen B)³`, so the nine-twist split of `D` (STCC) holds for every twist with the cube factor `Z_{ψ³}`. For cubic `ψ`
   it is `(1 − N(q)^{−z})Z₀(z)`: removing the ideals divisible by `(q)`. For `ψ³ = λ_q` with `λ_q(−1) = 1` every unit is
   `±` a square, so `λ_q` is trivial on `O^×`, and `B ↦ λ_q(gen B)` is a Hecke character of modulus `(q)(λ)`.
13. *The ω-shift* (OSM). Shift both opposite fractional translations by `±ω`. Conjugation by `T_b` changes `κ(γ) = (c/a)₃`
   into `(c/(a + bc))₃`, and the two changes cancel in every pair: for equal lower-left entries, and for `c`, `qc` by
   reciprocity. Each coset keeps both points at `∞`-class cusps, so the constant term is the unshifted one with the phase
   `φ(k) = e(2ωξ_k)` in every frequency. Away from `∞` the column determinant moves by the norm, `D(a ± ωc, c) = D(a, c) ∓ N(c)`:
   one factor of every pair is ramified, and its exponential decay beats the polynomial growth of the other. STCC's
   selector `φ(k) + φ(−k) ∈ {2, −1}` then cuts out the frequencies prime to `3`. So a trace whose cosets stay at
   `∞`-class cusps reaches the unit layer of its twist, without the 3-adic coefficients `T(uλ^m)` and without `SL₂(ℤ)`-invariance.
   The same works for the Hecke trace at `p`: the two conjugates of `γ ∈ Γ_p` have lower-left entries `c`, `p²c` (reciprocity,
   `3 ∣ p² − 1`), the dilate pairs carry `e(ξ_h(1 + p²)b) = φ(h)`, and the Hecke points of a point off `∞` have columns
   `(pa, c)/g`, `(a, pc)/g` with the residues of `(a, c)`, so one of them is ramified after `±ω`.

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
| The fractional trace | for an odd primary prime `q`, `G = Σ_{t ∈ O/q}θ(T_tw)θ(T_{−t}w)` (`T_t`: translation by `3t/q`) has multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)`; its trace to `Γ(3)` is `SL₂(ℤ)`-invariant (`S⁻¹T_tS = δ_tT_tγ₀` with one `γ₀` for all `t`); the cosets are `P¹(O/q²)`: the cusp `∞`, the `N − 1` middle cusps `3qx` (Jacobi phases `χ(1 − s²)`, cubic reciprocity), and the `N²` classes over `0` (low points of low points) | `fracSum_automorphy`, `fracTrace_rational`, `fracTrace_eq`, `fracCorrelation_lowerThree`, `fracSum_sO` |
| The fractional trace is a Jacobi multiple of `θ²` | `Tr G − (N² + N + (N − 1)J)θ²` is a bounded remainder, `J = Σ_sχ(1 − s²) = −χ(4)q` the Jacobi sum of the cubic and the quadratic character of `O/q`; its constant term is `|P|(−NJ R_{cop}(v) + N²χ(−4)χ(9)⁻¹R_g(v/N))`, `g(k) = χ(k)⁻¹g_χ` | `fracRemainder_remainderData`, `integral_sourceFracTrace`, `cuspConstantTerm_fracRemainder`, `fracJacobi_eq_primary` |
| The conjugate cubic twist keeps the double pole | for every odd primary prime `q`, `(s − 4/3)²M(s)Σ_kχ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s} → g_χ⁻¹A(4/3)⁻¹NJ(1 − N⁻¹)·108π³r³ ≠ 0`, `A(s) = N²χ(−4)χ(9)⁻¹N^{s−2} + NJρ^{−s}χ(9)⁻¹g_{χ²}²ρ⁻²g_χ⁻¹` (non-vanishing on `Re s > 2/3`); the Euler identity `(1 − ρ^{2−3s})D = D_{cop} + ρ^{−s}D_q` puts the `q`-divisible part of `θ²` on the conjugate twist | `conjugateCubicTwist_double_pole`, `conjugateTwist_relation`, `thetaSq_euler`, `conjFactor_ne_zero` |
| The quadratic fractional trace | for the quadratic character `λ` of `O/q`, `G_λ = Σ_tλ(t)θ(T_tw)θ(T_{−t}w)` has multiplier `κ²` on `Γ(3) ∩ Γ₀(q²)` (the weight is invariant under squares); its trace is `SL₂(ℤ)`-invariant and is itself a bounded remainder: every main value cancels against `λ`. The cusp `∞` and the middle cusps read the quadratic twist with weight `g_λλ(2k)J₆`, `J₆ = Σ_s(χλ)(1 − s²) = J(λ, χλ) ≠ 0`; the cusp `0` reads the sextic Gauss sums `g_{χλ}(k) = (χ̄λ)(k)g_{χλ}` | `fracSumW_automorphy`, `fracTraceW_rational`, `sourceFracTraceW_remainderData`, `integral_sourceFracTraceW`, `lamJacobi_eq`, `sexticGaussAt_eq` |
| The sextic twist is the quadratic twist | `(s − 4/3)²M(s)(g_λJ₆λ(2)L_λ(s) + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}L_{χ̄λ}(s)) → 0`, `L_ψ = Σ_kψ(k)T(k)²(4π|ξ_k|)^{−s}`; every factor is nonzero, so `M·L_{χ̄λ}` continues past `4/3` with leading coefficient `cL` if and only if `M·L_λ` does with `L`, `c = −g_λJ₆λ(2)/(N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{−2/3})` | `sexticTwist_relation`, `sexticTwist_double_pole_iff`, `sexticRatio_ne_zero` |
| The main term of the quadratic grade is a theta period | the residue at `4/3` of a bounded remainder is its pairing with the residue vector `θ_{res}` of the cubic Eisenstein series; so `(s − 4/3)M(s)(g_λJ₆λ(2)L_λ + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}L_{χ̄λ}) → |P|⁻¹⟨Tr G_λ, θ_{res}⟩` | `RemainderData.pairing_residue`, `sexticTwist_residue` |
| Every layer is the unit layer of an even twist | `D₀^ψ = Σ_{λ∤h}ψ(h)T(h)²(4π|ξ_h|)^{−s} = C̄²Z_{ψ³}(3s/2 − 1)(ψ(1) + ψ(−1))(4π|ξ₁|)^{−s}S^ψ_1(s/2)` (only `T(±1)` survive on units); `S^ψ_{h₀} = S^{ψξ_{h₀}}_1` with `ξ_{h₀} = (h₀/·)₃²`; so for every bounded multiplicative `ψ` and every layer `uλ^m` some even `ψ'` (`ψξ` or `ψξη₃`) has `D₀^{ψ'} = 2C̄²Z_{ψ³}(4π|ξ₁|)^{−s}S^ψ_{uλ^m}`: the unknown weights `T(uλ^m)` drop out | `unramifiedChar`, `cubeSign`, `layerChar`, `unramifiedTwist_eq`, `twistedSquarefreeSeriesG_layer`, `twistDirichletG_eq_zero_of_odd`, `layer_eq_unramifiedTwist` |
| The family layer is the unramified dilate correlation at nine | for `λ ∤ h`: `T(h)T(9h)T(1) = (9/h)₃T(9)T(h)²` (source mask and twisted multiplicativity at `9 = ωλ⁴`); so for even `ψ`, `T(1)Σ_{λ∤h}ψ(h)T(h)T(9h)(4π|ξ_h|)^{−s} = 2T(9)C̄²Z_{ψ³}(3s/2 − 1)(4π|ξ₁|)^{−s}S^ψ_{ω²λ²}(s/2)`: the family's layer is read by `θ(3w)θ(w/3)` on unramified frequencies, with weight `T(9)` | `thetaNine_identity`, `unramifiedDilateNine_eq`, `unramifiedTwist_layer`, `unramifiedDilateNine_eq_layer` |
| Opposite translations by thirds | `θ(w + β/3)θ(w − β/3)` has multiplier `κ²` on `Γ_Z = {27 ∣ c, 9 ∣ d − a}`: the translation by `β/3` conjugates `Γ_Z` into `Γ(3)` without moving the translate, and `(a + 9βc₂)(a − 9βc₂) ≡ a²` modulo `9` and `c` | `thirdShift_mul`, `thirdConj_character_mul`, `thirdCorrelation_automorphy` |
| The twisted remainders read the zeros of the cube factor | on `V = {1 < Re s < 13/3, Im s > 0}`: if the squarefree combination continues holomorphically to `V` (a square-root remainder, `Re w > 1/2`), the trace continuation vanishes at `2(1 + ρ)/3` for every zero `ρ` of the cube factor in the image of `V` — of `ζ·L(·, χ₋₃)` in the cubic grade, of the Hecke `L(·, λ̃_q)` in the quadratic grade | `eqOn_traceStrip`, `cubicGrade_remainder_forces_zero`, `quadraticGrade_remainder_forces_zero` |
| Rigidity of the quadratic pair traces | a single fractional translate moves with `κ` on `Γ(3) ∩ Γ₀(q²)`; for every ratio `c ≠ 0, 1` the trace of `Σ_tλ(t)θ(T_tw)θ(T_{ct}w)` is `SL₂(ℤ)`-invariant, and its constant term is `C_c/C_{−1}` times that of `Tr G_λ`, `C_c = χ(9c)λ(M)χ(M)²`, `M = (1 − c)/(9c)`; the middle cusps carry `J_c = (χλ)(−(1 − c)²/(4c))J₆` | `theta_fracShift_automorphy`, `ratioTrace_rational`, `ratioJacobi_eq`, `ratio_coefficients_proportional`, `integral_sourceRatioTrace_eq` |
| The grade factorization | for every completely multiplicative `ψ : O → ℂ` with `|ψ| ≤ 1` (characters of `O/q`, of `O/4`, products) and `Re s > 4`: `L_ψ(s) = C̄²Z_{ψ³}(3s/2 − 1)Q_ψ(s)`; for cubic `ψ`, `Z_{ψ³}(z) = (1 − N(q)^{−z})Z₀(z)`; for `ψ³ = λ_q`, `λ_q(−1) = 1`, `Z_{ψ³} = L(·, λ̃)` with `λ̃` a nonprincipal Hecke character of modulus `(q)(λ)`, entire and nonzero on `Re z ≥ 1` | `twistDirichletG_eq_zeta_mul`, `twistDirichlet_eq_zeta_mul`, `cubeZetaW_cubic`, `cubeZetaW_eq_LFunction`, `quadHecke_residue_ne_one`, `twistDirichlet_eq_quadCubeFactor` |
| The cubic twists of the squarefree combination have simple poles | a double pole `c` of `M·L_ψ` (cubic `ψ`) is a simple pole of `M·Q_ψ` with residue `c/(C̄²(2/3)Z̃(4/3)(1 − N(q)^{−1}))`; so for every primary `q` (`χ_q`) and every odd primary `q` (`χ̄_q`), `(s − 4/3)M(s)Q_ψ(s)` tends to a nonzero limit: neither cubic twist at a prime kills the residue at `w = 2/3` of the squarefree combination | `twistCombination_simple_pole_of_double_pole`, `cubicTwistCombination_simple_pole`, `conjugateTwistCombination_simple_pole` |
| Pole orders agree in the quadratic grade | for `ψ³ = λ_q`, `λ_q(−1) = 1`, and every `k`: `M·L_ψ` continues to `{4/3 < Re s < 13/3, Im s > 0}` and a punctured neighbourhood of `4/3` with `(s − 4/3)^kM(s)L_ψ(s) → c` iff `M·Q_ψ` does with `c/(C̄²L(1, λ̃))` | `quadraticGrade_pole_transfer`, `quadraticGrade_pole_transfer_symm` |
| The family is one cubic layer and three Klein layers | `Γ(c) = ½(1 + κ₁(c)) + (i/2)(κ_{ω²}(c) − κ_ω(c))` on odd classes (`Γ = 1, 1, i, −i` at `1, −1, 1 + 2ω, 1 + 2ω²`); every column is `Σ_s γ_s\overline{S^{Ξ_s}_{ω²λ²}(w̄)}`, `γ = (½, ½, i/2, −i/2)`; at column `1`, `Σ_A ω₆(gen A)N(A)^{−w}` is the `χ₂`-layer with weight `½` plus the three Klein layers `κ₁χ₂` (`½`), `κ_{ω²}χ₂` (`i/2`), `κ_ωχ₂` (`−i/2`) | `fixedDualAverage_eq_klein`, `kleinChar`, `phaseTwist`, `columnSeries_eq_klein`, `orderSixSeries_eq_klein` |
| The long columns are layers of twisted theta squares | `g_c(n)/|c| = \overline{r(n, c)}(c/n)₃(c/n)₂ω₆(c)` at every squarefree row; the 2-adic weight `\overline{r(n, c)}Γ(c)χ₂(c)` depends only on `c` mod `4` and expands over the characters of `(O/4)^×`; the column twist `(·/n)₃(·/n)₂` is completely multiplicative; so the `n`-th column series is `Σ_η a_η(n)\overline{S^{Ξ_{η,n}}_{ω²λ²}(w̄)}` | `columnRootNumber_eq_columnWeight`, `twoAdicWeight_congr`, `twoAdicWeight_expansion`, `columnTwist`, `columnCoefficient_eq`, `columnSeries_eq_layers` |
| The unit layers of the cubic twists | for every odd primary prime `q`: the shifted fractional trace `Tr G^ω` (translations by `±(ω + 3t/q)`) has the multiplier `κ²` on `Γ(3)`, its constant term is the fractional trace's with `φ(k) = e(2ωξ_k)` inserted, and `Tr G^ω − (N² + N + (N − 1)J)θ_s(T_ω·)θ_s(T_{−ω}·)` is a bounded remainder; the phased conjugate twist `Σ_kφ(k)χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s}` has a quarter of the double pole of `L_{χ̄_q}`, its part on `3 ∤ k` has half; so `S^{χ̄_q}_1(w) = Σ_Aχ_q(gen A)⁻¹σ(A)N(A)^{−w}` has a simple pole at `w = 2/3` with an explicit nonzero residue; for every primary prime `p` the shifted Hecke trace `Tr_pF^ω` (`F^ω = θ_s(T_ωA_p·)θ_s(T_{−ω}A_p⁻¹·)`) minus `2N(p)θ_s(T_ω·)θ_s(T_{−ω}·)` is a bounded remainder, the phased cubic twist has a quarter of the double pole of `L_{χ_p}`, its part on `3 ∤ k` half, and `S^{χ_p}_1` has a simple pole; the residues are `Res S^{χ_p}_1 = 2N(p)^{5/6}/(N(p) + 1)·\overline{(9/p)₃}G̃(p)·Res S₁` and `Res S^{χ̄_q}_1 = N(q)J_q/(g(χ_q)A_q(4/3))·Res S₁` | `shiftSum_automorphy`, `shiftTrace_eq`, `integral_sourceShiftTrace`, `shiftRemainder_remainderData`, `phasedConjugateCubicTwist_double_pole`, `unramifiedConjugateCubicTwist_double_pole`, `conjugateUnitLayer_simple_pole`, `heckeShiftTrace_eq_hecke`, `heckeShiftRemainder_remainderData`, `phasedCubicTwist_double_pole`, `cubicUnitLayer_simple_pole`, `twistUnitResidue_closed`, `conjUnitResidue_eq_mul` |
| The cubic layer of the first column | `ω₆(c)ξ(c) = Γ(c)χ₂(c)σ̄(c)` (`ξ = (ω²λ²/·)₃²`): the `ξ`-reweighted column `n` is the Klein combination `Σγ_s\overline{S^{Ξ_s}_1(w̄)}` of unit layers; at column `1` the cubic layer is `Ξ₀ = (·/−2)₃` and `S^{Ξ₀}_1` has a simple pole at `w = 2/3` with residue `(2·2^{5/3}/5)\overline{(9/−2)₃}G̃(−2)·Res S₁ ≠ 0` | `gauss_sq_mul_xi`, `unitColumnSeries_eq_of_expansion`, `unitColumnSeries_one_eq_klein`, `cubicKleinLayer_eq`, `unitColumnCubicLayer_simple_pole` |
| The unit layer over the cubic classes | for every odd primary prime `q` the unit layer of the principal character modulo `q` has a simple pole with `Res S^{1_q}_1 = N^{4/3}χ(−4)χ(9)⁻¹/A_q(4/3)·Res S₁` (selector on the `q`-coprime squares), and each cubic class `χ_q(gen A) = c` has `Res S^{[c]}_1 = ⅓(Res S^{1_q}_1 + c̄ Res S^{χ_q}_1 + c̄² Res S^{χ̄_q}_1)` in closed form | `coprime_sub_phased`, `unramCoprime_double_pole`, `principalUnitLayer_simple_pole`, `classSeries_eq`, `classSeries_simple_pole`, `classUnitResidue_eq` |
| The cubic grade lives on the square columns | on classes prime to `2n`, the layer characters of column `n` satisfy `Ξ_{s,n}(c)³ = r(n, c)κ_s(c)(c/n)₂`; at a square column `m²` the Klein-trivial layer is cubic (`Ξ³ = 1`) and the three Klein layers are quadratic; at a column with an odd power of a prime every layer is quadratic (`Ξ³ = −1` on a primary class) | `layerTwist_cube`, `square_cubicLayer_cube`, `square_kleinLayer_quadratic`, `nonsquare_layer_quadratic` |
| Smoothed main terms of the twisted unit layers | for every primary prime `p` and odd primary prime `q`, the unit layers of `χ_p`, `χ̄_q`, the principal character modulo `q` and every cubic class `χ_q(gen A) = c` have Gaussian-smoothed sums `Σ_A a(A)g(log(N(A)/X)) = e^{4/9}α(4/3)Res S₁·X^{2/3} + O(X^a)` for every `5/8 < a < 2/3`, with `α(4/3)` the closed-form residue ratio; each layer is `α(2w)S₁(w) + (2w − 4/3)β(2w)(Λ̃₁ − Λ̃₂)(2w)` with regularized remainder pairings of the traces at the prime, bounded on vertical strips | `gaussianSmoothedSum_main_term`, `regPairing_vertical_bound`, `cubicUnitLayerCont_eq_series`, `cubicUnitLayer_smoothed_main_term`, `layerCont_smoothed_main_term`, `conj_key`, `principal_key`, `conjugateUnitLayer_smoothed_main_term`, `principalUnitLayer_smoothed_main_term`, `classUnitLayer_smoothed_main_term` |
| Uniform prime-factor normalization | `c_p(4/3)N(p)^{−1/6}(1 − N(p)^{−1})² = 1 − N(p)^{−2}`. Equal norms determine primary primes up to conjugation, so each norm occurs at most twice: `1/4 < C(S) = ∏_{p∈S}(1 − N(p)^{−2}) ≤ 1` for every finite primary-prime set. The unordered infinite product converges to a constant in `[1/4, 1]`. Normalized dilate and cubic-twist prime residue products have modulus in `[1, 4)`; the Gauss phases have modulus one. | `PrimaryPrime.eq_or_conj_of_conductorNorm_eq`, `normalizedDilateProduct_eq`, `normalizedDilateProduct_bounds`, `conductorSquare_multipliable`, `conductorSquareConstant_bounds`, `normalizedCubicTwistResidueProduct_bounds` |
| Composite cubic phase and dilate bridge | For `m = ∏_{p∈S}p`, put `κ_m = (9/m)₃\overline{G̃(m)}`. The coprime dilate series equals `κ_m` times the cubic-twist series, coefficient by coefficient; `‖κ_m‖ = 1` and `(κ_m/∏_{p∈S}κ_p)³ = 1`. Adding a new prime `p` multiplies this phase correction by `(p/m)₃`. Twisted coefficient magnitudes are bounded by `‖T(k)‖²`, uniformly in `S`, giving weighted absolute summability for `σ > 4`. | `compositeDilateCoeff_eq_twist`, `compositeDilateDirichlet_eq`, `cubicConductorPhase_norm`, `compositePhaseCorrection_cube`, `compositePhaseCorrection_insert`, `summable_compositeDilateCoeff` |

Composite analytic continuation and residue factorization remain open.

## 6. Questions

| # | Question |
|---|---|
| Q1 | **Bridge.** Is the row-root-number series at every column a combination, with coefficients of bounded conductor, of Rankin–Selberg series of the cubic theta function? Pointwise the answer is Hasse–Davenport at the columns: a shifted theta product times the quadratic Gauss sum at the odd part of the column. At the series level (Lean): for every primary column `n` prime to `2` and `Re w > 1`, `Σ_A g_{gen A}(n)/|gen A| N(A)^{−w} = Σ_η a_η(n)\overline{S^{Ξ_{η,n}}_{ω²λ²}(w̄)}` over the twelve characters `η` of `(O/4)^×`, `Ξ_{η,n} = \overline{η·(·/n)₃(·/n)₂}`, `a_η(n)` the coefficients of the 2-adic weight `\overline{r(n, c)}Γ(c)χ₂(c)` (a function of `c` modulo `4`); each `S^Ξ_{ω²λ²}` is one of the nine layers of `L_Ξ = C̄²Z_{Ξ³}(3s/2 − 1)Q_Ξ`. The 3-adic twist is absorbed by the layer `ω²λ²` (`(ω²λ²)² = 9`). The coefficients are explicit (Lean): on odd classes `Γ = ½(1 + κ₁) + (i/2)(κ_{ω²} − κ_ω)` with the Klein characters `κ_s(1 + 2t) = (−1)^{tr(st)}` read on `c³`, and `r(n, ·)` is multiplicative, so each column is four layers `½\overline{S^{Ξ₀}} + ½\overline{S^{Ξ₁}} + (i/2)\overline{S^{Ξ_{ω²}}} − (i/2)\overline{S^{Ξ_ω}}`, `Ξ_s = \overline{r(n, ·)κ_sχ₂(·/n)₃(·/n)₂}`. |
| Q2 | **Residues.** The residue at `2/3` of the actual row family at column `n` and under bounded reweighting: the order-six theta coefficients. By Q1 they are residues of shifted cubic theta products with quadratic twists. Closed form? Which reweightings kill them? Known: `S₁` (the family reweighted by `\overline{G}(9/·)₃`) has a nonzero residue (STCC); it is a positive real number and the theta scalar `C` is real (conjugation symmetry). The actual family is orthogonal to `S₁` and to every twist unramified at `2` (its 2-adic phase has mean zero modulo `4`): its residue is a combination of residues of theta squares twisted by characters ramified at `2`. Its 3-adic part is the twist `S_{ω²λ²} = Σ \overline{G̃(c)}² N(c)^{−w}` (the plain mean of the squared Gauss sums), not `S₁`. Every cubic twist keeps the double pole: for every primary prime `p`, `L_{χ_p} = Σ(k/p)₃T(k)²(4π|ξ_k|)^{−s}` has leading coefficient `216π³r³/(c_p(4/3)(9/p)₃\overline{G̃(p)})`, `c_p(4/3) = |p|^{1/3}(N(p) + 1)/(N(p) − 1)`, and the dilate correlation `Σ_{p∤k}T(k)T(kp)` has `216π³r³/c_p(4/3)` (Hecke trace at `p` plus Patterson at `p`); at `p = −2` this is the 2-ramified twist `L_χ`. The conjugate twist `L_{χ̄_q}` keeps the double pole at every odd primary prime `q` (fractional trace, leading coefficient with the Jacobi sum `J = −χ(4)q`). Neither cubic twist at a prime kills the residue of the squarefree combination: `Q_{χ_q}` and `Q_{χ̄_q}` have simple poles at `w = 2/3` with nonzero residues. At a prime column the family carries the sextic symbol `χ̄_qλ_q`, which lies in the quadratic grade. Its main term is the residue at `w = 2/3` of the single layer `S^{χ̄λ}_{ω²λ²}`; `L_{χ̄λ}` has the pole order of `Q_{χ̄λ}`, which combines the nine layers. The double poles of `L_{χ̄λ}` and of the quadratic twist `L_λ` determine each other, with an explicit nonzero ratio (quadratic fractional trace). For `N(q) ≡ 3 mod 4` both twists vanish identically (`λ(−1) = −1`, `T` even): the layers `u` and `−u` cancel; a single layer is the unit layer of the even twist `ψη₃ξ` and stays visible. Single layers of twists unramified at `3` are reachable (Lean): the unit layers `S^{χ̄_q}_1` (odd primary `q`) and `S^{χ_p}_1` (every primary `p`) of the two cubic twists — the `S₁`-type reweightings of the family at the columns `q²` and `p⁴` — have simple poles at `w = 2/3` (shifted fractional and Hecke traces), with residues local multiples of `Res S₁`: `Res S^{χ_p}_1 = 2N(p)^{5/6}/(N(p) + 1)·\overline{(9/p)₃}G̃(p)·Res S₁`. The phase of the main term at the column `p⁴` is the normalized cubic Gauss sum at `p`. At column `1` the family reweighted by `ξ = (ω²λ²/·)₃²` is `½\overline{S^{(·/−2)₃}_1}` plus three Klein layers (Lean), and its cubic layer has the nonzero residue `(2·2^{5/3}/5)\overline{(9/−2)₃}G̃(−2)·Res S₁`: this reweighting leaves a cubic main term, and the decision at column `1` rests on the Klein layers. On each cubic residue class modulo an odd primary prime `q` the unit layer has an explicit residue (Lean); its dependence on the class is carried by `G̃(q)` and the Jacobi sum `J_q`. Open: the simple poles of the quadratic grade (`L_λ`, `L_{χ̄λ}`, the Klein twists `η` at `2`), which bounded-remainder pairings do not see; the 3-adic layer `ω²λ²`; and twists of composite conductor (`4q`, `q₁q₂`). |
| Q3 | **Remainder.** The remainder exponent of the first moment, for one column and on average over columns. At the unit layer it is the zero-free region of `ζ_K` read at `3w − 1`, from both sides: `(1 + Θ)/3` is reached through the seed, and a zero `ρ` with `Λ₀(2(1 + ρ)/3) ≠ 0` forbids every exponent below `(1 + Re ρ)/3`. Twisted (Lean): the squarefree combination of a cubic twist reads the zeros of `ζ_K` the same way, and in the quadratic grade at a prime column (`N(q) ≡ 1 mod 4`) it reads the zeros of the Hecke `L(·, λ̃_q)`: a continuation to `Re w > 1/2` forces every such zero with `Re ρ > 1/2` onto a zero of the λ-trace continuation at `2(1 + ρ)/3`. At the reachable layers the exponent is attained (Lean): the unit layers of `χ_p`, `χ̄_q`, the principal character modulo `q` and every cubic class modulo `q` have smoothed main terms with remainder `O(X^a)` for every `a > 5/8 = (1 + 7/8)/3`, the exponent of `S₁`; the remainder part of each layer is a pair of regularized trace pairings, holomorphic at `2/3`. Open: the actual family (one layer) and the mean over columns. |
| Q4 | **Functional equation** of `Z(w; n)` with explicit column dependence: needs the continuation of the cubic Eisenstein series across `Re s = 1`. |
| Q5 | **Sextic large sieve** `B₆(M, N)`. A square stops the floor bin at `5/6` whatever its cross term; the sieve matters for the mean over columns of the remainders, not for the main term. |
| Q6 | **Layers.** Every sixth-power-free row is a squarefree row at a column (`rowConductorGauss_layers`); open: the analytic summation over the higher layers with column-dependent remainders. |
| Q7 | **Tower.** The same statements along `k ↦ 6k + 1` (Grössencharacters of infinity type `6k`): non-spherical Eisenstein series of the cubic cover. |
| Q8 | **Decision.** Success (remainder `U^{½+ε}` uniform in the column: the curve reaches `2/3`) or kill (a main term of order `U^{2/3}` that no admissible reweighting removes). At the unit layer the success criterion is RH for `ζ_K` up to coincident zeros of `Λ₀`; at a prime column in the quadratic grade a square-root remainder of the squarefree combinations needs GRH for `L(·, λ̃_q)` up to coincident zeros of the λ-trace continuation; the attainable target is the main term plus the remainder `(1 + Θ)/3` (reached in Lean for the `S₁`-reweighted family at the columns `p⁴`, `q²` and on the cubic classes modulo `q`), and below `5/6` the decision is the coherence of the main terms across columns. The main terms split by grade. In the cubic grade (`χ_q`, `χ̄_q`, the cubic twist at `2`) they are double poles with explicit coefficients, reached by traces. In the quadratic grade (`χ̄_qλ_q` at prime columns, the Klein characters at `2`) they are simple poles, which bounded remainders do not see. The grade of every layer of every column is known (Lean): the cubic grade occurs only at the square columns `m²`, in the Klein-trivial layer; all other layers of all columns are quadratic. So the double-pole main terms reached by traces live on a sparse set of columns, and the decision outside them is the vanishing of quadratic-grade simple poles. For `N(q) ≡ 3 mod 4` the prime-column sextic twist vanishes identically, by cancellation of the layers `±u`, not of the family layer. |

## 7. Traps

| Trap | Truth |
|---|---|
| `μ(c)·c/|c|` in the root number is a twist that kills the metaplectic main term | it is `γ₂(c)³`: the root number is a sextic Gauss sum, coherent at `2/3` |
| The six-fold theta coefficients need the six-fold cover | they are residues of cubic theta products with quadratic twists (Hasse–Davenport at the columns) |
| The conductor phase is a bounded nuisance | its cubic part is the shift by `−2`; only the Weil index `Γ(c)` (conductor `4`) is quadratic |
| A double pole of `D` at `2/3` is a pole of the squarefree series | the cube frequencies alone give a simple pole; the squarefree part needs the double pole (STCC) |
| The nine twisted squarefree series separate from `D` and the rotations | every coefficient at ramified layers is an undetermined `T(uλ^m)`; rotated correlations weight `T(ωh)T(h)` |
| `G̃` and `T` are the same coefficients | `T(a) = ±C̄(9/a)₃\overline{G̃(a)}`: Rankin–Selberg series in `T` carry the 3-adic twist `(9/c)₃` relative to the row family |
| Squarefree extraction is free | it divides by `ζ_K(3w − 1)` and inherits its zeros, in both directions; twisted, by the cube factor `Z_{ψ³}`: in the quadratic grade by the Hecke `L(3w − 1, λ̃_q)`, whose zeros a square-root remainder at the prime column `q` must meet with zeros of the trace continuation |
| A square-root remainder for the squarefree rows is a spectral question | it forces every zero of `ζ_K` right of the critical line onto the zeros of `Λ₀(2(1 + ·)/3)` |
| The sextic matrix is the Hadamard product of a quadratic and a cubic matrix, so its norm is bounded by theirs | the Hadamard bound needs a bounded factorization of one factor, which the quadratic matrix lacks |
| A remainder uniform in a single column is what the probe needs | the floor bin sums columns with weights; the usable statement is a mean value over columns |
| Kubota's pole is at `1 + 1/n` | for normalized Gauss sums it is at `½ + 1/n` |
| The fifth-power layer of a row twists the squarefree layer | it is invisible to it: `χ_a(e⁶) = 1` |
| The phase of the theta scalar `C` is an analytic unknown | conjugation conjugates both Gauss-sum series behind `ρ(1)`, so reflection makes their residues real: `C ∈ ℝ`, and the `S₁` residue is positive |
| Reflecting a continued coefficient needs its values on the real segment | the resolvent identification holds at every nonreal spectral parameter; the initial region in the lower half-plane and the identity theorem suffice |
| The positive main term of `S₁` is the main term of the order-six family | the 2-adic phase `Γ(c)(c/−2)₃²` of the family has mean zero modulo `4`; only theta squares twisted by characters ramified at `2` contribute, and the 3-adic partner is `S_{ω²λ²}` (plain squares), whose weight in `D` is `(T(ω²λ²)/T(1))²` |
| The Hecke traces at primes give the column dependence of the order-six family | they reach the twists `χ_q = (·/q)₃`; the fractional traces reach `χ̄_q`; the family at column `q` carries the sextic symbol `χ̄_qλ_q`, whose twist is tied to the quadratic twist `L_λ` |
| A second `λ`-weighted trace decides the quadratic twist | every `λ`-weighted trace is homogeneous in the quadratic grade. At level `q²` every ratio pair trace has the constant term of `Tr G_λ` up to a constant. Traces fix the ratio of the double poles of `L_λ` and `L_{χ̄λ}`, not their value |
| The sextic relation decides the main term at a prime column | it ties the double poles; in the quadratic grade the cube factor `L(·, λ̃)` is regular and nonzero, so `L_{χ̄λ}` and `Q_{χ̄λ}` share their pole order, and the main term is a simple pole. A bounded remainder only bounds the pole order: its residue at `4/3` is its pairing with the Eisenstein residue vector (Lean), for `Tr G_λ` a triple theta period |
| Parity kills the prime-column main term when `N(q) ≡ 3 mod 4` | an odd twist kills its theta square (`T(−h) = T(h)`), but not a layer: the sign `η₃` (`c³ ≡ η₃(c) mod λ²`) is trivial on primary elements and odd, so `ψη₃` has the same layers and the opposite parity. Every layer of every twist is the unit layer of an even unramified twisted theta square (Lean) |

## 8. Tools this programme develops

1. The bridge between the root numbers of the rows (FCT/CRF normalization) and the coefficients of the
   cubic theta function (MMD/STCC normalization). (Lean)
2. Hasse–Davenport at the columns and the layer peeling: every row at every column as a shifted theta
   product times a quadratic Gauss sum. (Lean)
3. Real-axis spectral theory of the cubic cover: simple real poles of the resolvent, the seed defect as a
   constant-term functional, holomorphy of the continued Eisenstein correction across the real axis. (Lean)
4. The cube convolution in both directions: Abel summation and the Laplace transform of the Gaussian
   smoothing turn remainders into holomorphy and force the zeros of `ζ_K`. (Lean)
   The converse direction: a Gaussian-smoothed sum over ideals with a bounded coefficient reads the residue of a
   continuation with Gaussian-dominated growth, with remainder `O(X^a)` (contour shift); continuations through the
   untwisted layer `α(2w)S₁(w) + (2w − 4/3)β(2w)(Λ̃₁ − Λ̃₂)(2w)`, the trace remainders paired against the regularized
   Eisenstein correction and bounded on vertical strips, pass the main term and the remainder exponent of `S₁` to every
   twisted unit layer reached by a trace. (Lean)
5. Conjugation and reflection: `c ↦ c̄` on symbols, Gauss sums, both cusp Dirichlet series and the Whittaker
   factors; reflection of continued cusp coefficients across the real axis; reality of residues. (Lean)
6. Hecke correlation traces at every primary prime: `θ(A_pw)θ(A_p⁻¹w)` traced from `Γ_p` to `Γ(3)`, its coset geometry
   over `P¹(O/p)`, Bezout factorization of the Hecke points, invariance under `SL₂(ℤ)`, the constant term with the
   Gauss sum of `χ²`, the bounded-remainder Rankin–Selberg lemma, and Patterson's reduction. (Lean) Fractional
   traces at every odd primary prime: opposite translations by `3t/q` on `Γ(3) ∩ Γ₀(q²)`, cosets over `P¹(O/q²)`,
   `SL₂(ℤ)`-invariance through one `γ₀ ≡ S mod q²`, Jacobi and Gauss phases, the Euler identity at `q`. (Lean)
   Shifted fractional traces: the same cosets with the translations shifted by `±ω`, the cusp-`0` classes through
   `g_t = δ_t⁻¹M_{−t} ∈ Γ(3)` instead of `S`, the bound away from `∞` by the column determinant, and the selector to the
   unit layer; shifted Hecke traces at every primary prime with the same three steps. (Lean)
   Composite moduli (`4q`, `q₁q₂`) and cubic Eisenstein series of `Γ(3) ∩ Γ₀(m)` with nebentypus. (open)
   Concretely: the spectral theory of MMD (energy graph, resolvent, Eisenstein series) on `L²(H\ℍ³)` for
   finite-index `H ≤ Γ_ker`; the 2-adic covers only see `θ`'s expansion at `∞` and the four rational cusps.
7. The grade factorization `L_ψ = C̄²Z_{ψ³}(3s/2 − 1)Q_ψ`: the cube factor as `Z₀` without the Euler factor at `q`
   (cubic grade) or as the Hecke `L`-function `L(·, λ̃)` (quadratic grade), and the transfer of poles between `L_ψ` and
   the squarefree combination `Q_ψ`. (Lean) Quadratic twists of `θ`: `λ`-weighted and ratio-pair fractional traces at level `q²` (Lean); an input that reaches
   the simple poles of the quadratic grade (open). Every layer as the unit layer of an even unramified twist, and the
   family layer `(ω², 2)` as the unramified dilate correlation at `9` (Lean); the Hecke correlation `θ(3w)θ(w/3)` at the
   ramified prime and the value `T(9)` (open).
8. A sextic large sieve over `ℤ[ω]`. (open)
9. [Polynomial filters of the ramified cubic channel](CharacterChannels/WeilPolynomialFilters.lean).
   For the actual character projector $E$, $p(E)f=p(1)Ef+p(0)(f-Ef)$; the signed Weil-phase
   pairing changes by exactly $p(1)$ (`cubicProjector_polynomial`, `weightedSum_polynomial`).
   Every Chebyshev order preserves the finite row sum with arbitrary weights
   (`finite_row_sum_chebyshev`). (Lean)
10. [Cubic unit rotation calculus](CharacterChannels/CubicRotationCalculus.lean).
    For $Uf(c)=f(\omega c)$, the three character projectors sum to the identity and
    $p(U)$ acts by evaluating $p$ at the corresponding eigenvalues (`unitRotation_polynomial`).
    Writing $z=\chi_2(\omega)$, the actual signed Weil pairing satisfies
    $W(p(U)f)=p(z^2)W(f)$, including finite arithmetic row sums
    (`finite_row_sum_rotation_polynomial`). Cancellation occurs exactly when $p(z^2)=0$
    or the original pairing vanishes. (Lean)
11. [Minimum-energy phase carrier](CharacterChannels/MinimumEnergyPhaseCarrier.lean).
    With $v=\overline{\mathrm{phase}}$ and $C=\|v\|^2>0$, the vector $W(f)v/C$ is the
    unique minimum-norm class vector with signed pairing $W(f)$
    (`coherentClassVector_minimum_eq_iff`). The residual has zero pairing and
    $|W(f)|^2+C\|f-W(f)v/C\|^2=C\|f\|^2$; this identity holds for the literal finite
    arithmetic row sum (`finite_row_sum_phase_energy`). (Lean)

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

1. Q1: the row-root-number series at every column as Rankin–Selberg data of the cubic cover (pointwise and
   series level: done; each column is twelve `ω²λ²`-layers of twisted theta squares).
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
   `ψ = ηχ₂` of `(O/4)^×` (`χ₂ = (·/−2)₃²`, `η` on `(1 + 2O)/(1 + 4O)`), with the coefficients `½, ½, i/2, −i/2`
   of `Γ` on the Klein group (Lean: `orderSixSeries_eq_klein`). `S₁` gives one relation: splitting off the rows divisible by `−2` (twisted
   multiplicativity) ties the odd untwisted residue to the odd `χ₂`-twisted residue. Products `T(c)T(pc)` reduce
   to cubic twists of `T(c)²` by the prime recurrence, so the 2-ramified twists are the new objects.
2. The Rankin–Selberg series of `θ(w)θ(A_m w)`: done at every primary prime `m = p` (the dilate correlation and the
   cubic twist `L_{χ_p}` have explicit double poles). Open: composite columns `n` (twists by `(·/n)₃`, Hecke traces at
   products of primes) and the coherence of `c_p(4/3)` across columns.
3. The quadratic grade. The main term of the family at a prime column (`χ̄_qλ_q`) and the Klein part at column `1`
   are simple poles at `4/3` with `ψ³ ≠ 1`. In the quadratic grade the cube factor `L(3s/2 − 1, λ̃)` is entire and nonzero
   there (Lean), so `L_ψ` and the squarefree combination `Q_ψ` share pole order and residue up to `C̄²L(1, λ̃)`. The family
   is one layer of `Q_ψ`; `L_ψ` reaches it only together with the other eight. Bounded-remainder pairings
   see these residues only as triple theta integrals `Σ_tλ(t)∫θ(T_tw)θ(T_{−t}w)θ(w)`. Double poles in this grade are tied
   in pairs (Lean) and are expected to vanish. Candidate inputs: the residual spectrum of `Γ(3) ∩ Γ₀(q²)` (it contains
   `θ_λ = Σ_tλ(t)θ(T_t·)`, which has no constant term at `∞`); the Kubota series twisted by a character of order prime
   to `3`.
4. The 3-adic theta coefficients `T(uλ^m)` and the layer `(ω², 2)` that carries `(9/c)₃`. Every layer is the unit layer of an
   even unramified twist (Lean), so a single layer needs either these coefficients (dilate by `9`: weight `T(9)`; rotations:
   `T(uλ^m)T(u'λ^m)`) or the expansions of `θ` at the ramified cusps: opposite translations by `β/3` (`κ²` on `Γ_Z`, Lean)
   average the 3-adic character away on the classes over `∞`. Known: `T(uλ) = 0`,
   `T(u) = 0` for `u ≠ ±1` (STCC); conjugation pairs `T(uλ^m)` with `T(ū(−ω²)^mλ^m)`, so `T(ω²λ²)` is real. The ω-shift
   isolates the unit layer of every twist unramified at `3` that a trace with `∞`-class cosets reaches (Lean for `χ_p`
   and `χ̄_q`; the principal character modulo `q`, and with it the cubic residue classes, needs the selector on the
   coprime squares). It does not reach `ξ_{ω²λ²}`: a character of the frequency modulo `9` needs translations by
   ninths or a Hecke trace at the ramified prime, and there one point of the non-rational cosets sits at a ramified
   cusp, whose expansion is the 3-adic datum.
5. The Weil index `Γ(c)` on classes modulo `4`: class-restricted residues and their signs (the unrestricted
   `S₁` residue is positive).
6. Mean over columns: a spectral or sextic large sieve for the column remainders.
7. Higher layers of sixth-power-free rows with column-dependent remainders (Q6).
8. Non-spherical twists along the tower (Q7).
