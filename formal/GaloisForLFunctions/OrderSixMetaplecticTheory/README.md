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
bounded conductor. So the long columns are the **order-six Kubota series**

`Z(w; n) = Σ_c g_c^{(1)}(n) |c|^{−1} N(c)^{−w}`

and the floor bin is read on the curve of FCT by its row exponent `R₀`:

| `R₀` | origin | half-plane |
|---|---|---|
| `1` | triangle inequality | `13/15` |
| `5/6` | cubic large sieve, cross term `(MN)^{2/3}` | `5/6` (the free floor) |
| `2/3 = ½ + 1/6` | coherent main term of the order-six Kubota series | `7/9` (the bifurcation) |
| `½` | main term evaluated, square-root remainder | `2/3` (the wall of the frame) |

Nothing in the corpus evaluates `Z(w; n)`: its continuation, its main term and its remainder, uniformly
in the column `n`. OSM is the theory of that series and of the large sieve that controls it on average
over columns. It decides whether the probe's floor bin reaches the wall `2/3` (success) or stops at a
coherent main term that the probe cannot remove (kill; the survivor is the main term in closed form).

**Thesis: order six is the square of order three.** Hasse–Davenport at the rows (Lean, CRF) says that
the sextic root number is a bounded phase times the *square* of a cubic theta coefficient. The
programme tests the consequence: every first moment of order six is a twisted Rankin–Selberg
convolution of the cubic theta function `θ` with a translate of itself, on the *cubic* cover, where
the spectral theory exists (SpectralTheoryOfTheCubicCover, STCC). The six-fold cover, its Eisenstein
series and its theta function — none of which is in the corpus, and whose theta coefficients are not
determined by Hecke theory — are then replaced by objects the corpus has. Where the thesis fails, the
failure names exactly what the six-fold cover adds.

## 2. Objects

| Object | Meaning | Lean |
|---|---|---|
| sextic symbol `χ_c(x)` | `(x/c)₃² (x/c)₂` for primary `c` prime to `6`; `χ_c² = (·/c)₃`, `χ_c³ = (·/c)₂` | `sexticSymbol` (FCT) |
| Gauss sums `g_c^{(j)}(h)` | `Σ_{d mod c} χ_c(d)^j ψ_c(hd)` | `sexticGaussPow` (FCT) |
| row root number `Φ(c)` | `g_c^{(1)}(1)/|c|`, supported on squarefree `c` | CRF |
| theta coefficient `γ₂(c)` | `g_c^{(2)}(1)/|c|`, normalized cubic Gauss sum, `γ₂³ = μ(c)c/|c|` | `thetaGauss` |
| phases `Γ(c)`, `G(c)` | normalized quadratic Gauss sum (a function of `c mod 4`), `G = \overline{χ_c(4)}Γ` | `fixedDualAverage`, `thetaPhase` |
| column twist | `g_c^{(1)}(n) = \overline{χ_c(n)} g_c^{(1)}(1)` for `(n, c) = 1`; by sextic reciprocity a character of `c` of conductor dividing `4n` up to bounded phases | `sexticSymbol_mul_sexticGauss`, `sexticSymbol_reciprocity` |
| order-six Kubota series `Z(w; n)` | the Dirichlet series of the row root numbers at column `n`; absolutely convergent on `Re w > 1`; classical pole at `½ + 1/6` | — |
| sixth-power-free rows | `u = a b² c³ d⁴ e⁵`; root number of `χ_u` = product of the root numbers of the five layers (orders 6, 3, 2, 3, 6) times reciprocity cross factors | — |
| cubic theta `θ`, coefficients `T(ν)` | residue of the cubic Eisenstein series at `4/3`; `T(ab³) = C|b|\overline{(δ/a)₃}G̃(a)` | MMD, STCC |
| Rankin–Selberg series | `D(w) = Σ_ν T(ν)² N(ν)^{−w} = \overline{C}² Z₀(3w − 1) Σ_{u,m}(…) S_{uλ^m}(w)`, nine twisted squarefree series `S_{h₀}` | `thetaSqDirichlet_eq_zeta_mul` (STCC) |
| order-six residue `ρ(n; ξ)` | the residue at `w = 2/3` of the row-root-number series at column `n`, twisted by a character `ξ` of bounded conductor: the order-six theta coefficient | — |
| sextic large-sieve norm `B₆(M, N)` | the norm of `(χ_m(n))` on squarefree `N(m) ≤ M`, `N(n) ≤ N` | — |
| six-fold Kubota character | `κ₆ = κ₂ · \overline{κ₃}`: the six-fold cover is the fibre product of the double and the triple cover | cubic `κ₃` in MMD |

## 3. Language

- **Rows and columns**: rows `u` carry root numbers `Φ(u)`; a column `n` twists them by `\overline{χ_u(n)}`.
- **Main term, remainder**: `Σ_{N(u) ≤ U} Φ(u) ξ_n(u) = ρ(n) U^{2/3} + E(U; n)`; the **remainder exponent**
  is the infimum of `β` with `E ≪ U^{β+ε}`.
- **Uniform in the column**: the remainder bound holds with a constant independent of `n`; **on average
  over columns**: the bound holds for `Σ_n |b(n)| |E(U; n)|` or its square — the form the floor bin uses.
- **Square of order three**: a statement of order six obtained from the cubic theta function through
  Hasse–Davenport and Rankin–Selberg.
- **Cube convolution**: the passage between all frequencies and squarefree frequencies, `D = \overline{C}² Z₀(3w − 1) S`;
  it divides by `ζ_K` at `3w − 1`.
- **Layers of a row**: the five orders `6, 3, 2, 3, 6` of a sixth-power-free modulus.
- **Coherent direction**: a column or a reweighting along which the main term survives.

## 4. Mechanisms

1. *Hasse–Davenport squaring* (CRF, Lean). `χ_c(4) N(c) g^{(1)} = g^{(3)} (g^{(2)})²` and `g^{(3)} = |c|Γ(c)`:
   `Φ = G γ₂²`; the Möbius sign and the angular character are `γ₂³`, so `γ₂² = μ(c)(c/|c|)\overline{γ₂}`.
2. *Columns are multiplicative twists.* `χ_c(u) g_c(uh) = g_c(h)`; sextic reciprocity
   `χ_c(d) = r(c, d) χ_d(c)` turns the column twist into a character of the row.
3. *Rankin–Selberg on the cubic cover* (STCC, Lean). Unfolding `θ²` (multiplier `κ⁻¹`) against the cubic
   Eisenstein series, a bounded renormalization `θ² − H` and the `L²` resolvent of MMD give the
   continuation of `M(s)D(s)` to `1 < Re s < 13/3` (`Im s > 0`) and the double pole at `s = 4/3` with
   leading coefficient `108π³r³`; products of translates `θ(g·)θ(g'·)` give other combinations
   (rotations: `54π³r³`).
4. *Cube convolution.* `T(hb³) = |b|T(h)` factors the cube frequencies out as `Z₀(3w − 1)`. The squarefree
   series is `D/Z₀(3w − 1)`: its continuation left of `2/3` needs the zeros of `ζ_K = ζ·L(χ₋₃)` at
   `3w − 1`. The seed `Θ ≤ 20999/24000` covers `Re w > (1 + Θ)/3 = 44999/72000 < 2/3`: the corpus seed
   isolates the order-six main term.
5. *Heath-Brown recursion* (MMD for order three, Lean). Poisson in the long variable turns a character
   matrix of order `k` into Gauss sums of order `k`; the principal dual frequencies (`k`-th powers) produce
   the cross term; reciprocity swaps the roles of `M` and `N`.
6. *Layer separation.* The root number of a sixth-power-free row is multiplicative across its five layers
   up to reciprocity cross factors; only the squarefree layer has a series that is not absolutely
   convergent on `Re w > ½`.

## 5. Pillar theorems

**From the corpus** (inputs, Lean).

| Theorem | Lean |
|---|---|
| sextic symbols, reciprocity, twisted multiplicativity of the sextic Gauss sums | `sexticSymbol_reciprocity`, `sexticGaussPow_mul`, `sexticSymbol_pow_mul_sexticGaussPow` |
| Hasse–Davenport at the rows; `Φ = Gγ₂²`; `γ₂³ = μ(c)c/|c|` | `rowHasseDavenport`, `rowRootNumber_eq_thetaPhase_mul_sq`, `thetaGauss_cube` |
| the reflected Gram is twisted by `Φ`; rank one at sixth-power frequencies | `gramCoeff_eq_thetaSquares`, `gramCoeff_sixthPower` |
| the cubic theta function, its constant term, its coefficients on squarefree × cube indices | MMD: `TheCubicResidueIsNonzero`, `normalized_sourceFourier_squarefree_cube` |
| Rankin–Selberg of `θ²`, the double pole, the nine twists, the rotated correlations | `thetaSqDirichlet_double_pole`, `thetaSqDirichlet_eq_zeta_mul`, `twistedSquarefreeCombination_simple_pole`, `rotatedCorrelation_double_pole` |
| the cubic large sieve `(M + N + (MN)^{2/3})(MN)^ε` | `CubicSieve.sieveNorm_sharp` |
| the floor-bin curve and its bifurcation at the Kubota exponent `½ + 1/n` | `signedGramSymmetricTheta`, `signedGramBrokenTheta`, `kubota_pole_eq_signedGram_bifurcation` |
| the seed | `riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`, `hecke_ne_zero_of_sub_seven_eighths_lt_re` |

**Of this programme.** Filled as the pillars are proved; the targets are the questions of §6.

## 6. Questions

| # | Question |
|---|---|
| Q1 | **Bridge.** Is the row-root-number series at every column a finite combination, with explicit coefficients of bounded conductor, of twisted Rankin–Selberg series of the cubic theta function? (thesis) |
| Q2 | **Residues.** The residue at `2/3` of the row-root-number series at column `n` and under bounded reweighting `ξ`: the order-six theta coefficients at the frequencies of the reflected Gram (rank one at sixth powers). Closed form in the cubic data `c = 3πr`, `C = T(1)`? Which reweightings kill it? |
| Q3 | **Remainder.** The remainder exponent of the first moment, for one column and on average over columns. Does the cube convolution tie it to the zeros of `ζ_K` at `3w − 1`? |
| Q4 | **Functional equation** of `Z(w; n)` with explicit dependence on the column. |
| Q5 | **Sextic large sieve.** `B₆(M, N)`: the analogue of Heath-Brown's bound; a cross term below `(MN)^{2/3}`? |
| Q6 | **Layers.** The first moment over sixth-power-free rows: which layers reach right of `½`? |
| Q7 | **Tower.** The same statements along `k ↦ 6k + 1` (Grössencharacters `ψ₆^k η`, the rungs of the cubic probe). |
| Q8 | **Decision.** Success (main term + remainder `U^{½+ε}` usable in the floor bin: the curve reaches `2/3`) or kill (a main term of order `U^{2/3}` that no admissible reweighting of rows removes; the survivor is the main term in closed form). |

## 7. Traps

| Trap | Truth |
|---|---|
| `μ(c)·c/|c|` in the root number is a twist that kills the metaplectic main term | it is `γ₂(c)³`: the root number is a sextic Gauss sum, coherent at `2/3` |
| The six-fold theta coefficients have a closed form like the cubic ones | for the double cover of `GL₂` only orders `2, 3` are determined by Hecke theory; order six is not. Closed forms can only come through the cubic square |
| A double pole of `D` at `2/3` is a pole of the squarefree series | the cube frequencies alone give a simple pole; the squarefree part needs the double pole (STCC) |
| The nine twisted squarefree series separate from `D` and the rotations | every coefficient at ramified layers is an undetermined `T(uλ^m)`; rotated correlations weight `T(ωh)T(h)`, not `T(h)²` |
| Squarefree extraction is free | it divides by `ζ_K(3w − 1)` and inherits its zeros |
| The sextic matrix is the Hadamard product of a quadratic and a cubic matrix, so its norm is bounded by theirs | the Hadamard product bound needs a bounded factorization of one factor, which the quadratic matrix lacks |
| A remainder uniform in a single column is what the probe needs | the floor bin sums columns with weights; the usable statement is a mean value over columns |
| Kubota's pole is at `1 + 1/n` | for normalized Gauss sums it is at `½ + 1/n` |
| Even order carries the Möbius sign | at even order the sign is the parity `χ(−1)`; the sign of the rows enters through `γ₂³` (odd order three) |

## 8. Tools this programme develops

1. The bridge between the root numbers of the rows (FCT/CRF normalization) and the Fourier coefficients
   of the cubic theta function (MMD/STCC normalization).
2. Twists of `θ` by characters of bounded conductor as automorphic functions on the cubic cover
   (translates by `(1/9)O`), and their Rankin–Selberg products: one series per twist.
3. Growth on vertical lines of the continued Rankin–Selberg series (resolvent bound) and the contour
   shift to smoothed first moments.
4. The cube convolution with the seed: continuation of the squarefree series to `Re w > (1 + Θ)/3`.
5. The root number of a sixth-power-free row, layer by layer.
6. A sextic large sieve over `ℤ[ω]`.

## 9. Position in the corpus

| Programme | Relation |
|---|---|
| CoherenceTheoryOfReciprocityFamilies | the consumer: Q1 (B175), Q6 (coherence exponent of Gauss sums); owns the floor bin and the long columns |
| SpectralTheoryOfTheCubicCover | the spectral engine: Rankin–Selberg of `θ²`, double poles, nine twists |
| MetaplecticMobiusDescent | the cubic cover, Kubota character, Eisenstein series, residue `θ`, cubic large sieve, the seed |
| FamilyContinuationTheory | sextic symbols and Gauss sums, the frame, the budget curve in `R₀`, the tower `ψ₆^k η` |
| ExponentDynamicsOfTheCriticalStrip | the rungs as tensor powers of cubic Gauss sums (O3), Gauss pairings |
| TensorPowerProgramme | frames and the sign line; the Gauss-pairing classification |

Obstacle map (review-1511): the classical part of this programme is J6, the open part is O2 (signed
evaluation before Cauchy–Schwarz); Q7 is O3.

## 10. Success criteria

1. Q1 in Lean: the row-root-number series as Rankin–Selberg data of the cubic cover, at every column.
2. Q2: the main term of the actual row family (not only a combination) with its residue in closed form,
   and the set of reweightings that kill it.
3. Q3: a remainder exponent below `2/3` for the first moment, first for one column, then on average
   over the columns the floor bin uses; its consequence on the floor-bin curve.
4. Q5: a sextic large sieve in Lean.
5. Q8 decided.

## 11. What a contribution must be

- It is a statement about the actual sextic Gauss sums of `ℤ[ω]` and the actual cubic cover, not a model.
- It moves Q1–Q8: a continuation, a residue, a remainder exponent, a sieve bound, or a refutation.
- Its exponents are stated in the variable `w` of the row norm and translated to `R₀` and the
  half-plane of the probe.
- It is calibrated: a statement that would also hold for random unimodular phases, or for order two,
  is not a statement about order six.
- Unconditional in Lean; an implication counts only when the implication is the content and its premise
  is named as open.

## 12. Open research topics

1. The bridge `γ₂ ↔ T` and the row-root-number series as `S`-data (Q1).
2. Isolation of the nine twists: twisted theta functions as combinations of translates, their cusps and
   constant terms; the residues `ρ(1; ξ)` for all `ξ` mod `9` (Q2).
3. Columns: `θ(w)·θ(A_n w)` and the conjugated multiplier; the residue at column `n` (Q2).
4. Growth of the continued series on `1 < Re s < 2` and the smoothed first moment with remainder
   `(1 + Θ)/3 + ε` (Q3).
5. The quadratic factor of the column twist: twisting `θ` by quadratic characters (Q1, Q2).
6. The sextic large sieve: Poisson, sextic Gauss sums of non-squarefree moduli, sixth-power frequencies (Q5).
7. Layers of sixth-power-free rows (Q6).
8. Non-spherical twists (infinity type `6k`) along the tower (Q7).
