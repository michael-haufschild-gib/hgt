# Order-six metaplectic theory over ℚ(ω) (OSM)

- **ID:** osm
- **Stage:** 1-in-progress
- **Type:** programme card (goal loop)
- **Source:** docs/reports/review-1511/obstacles-summary.md §2.9 ("unbuilt programme: order-six metaplectic theory over ℚ(ω)"); J6, O2, O3
- **Statement:** develop the order-six Kubota series of the row root numbers `Φ = Gγ₂²` (continuation, functional equation, residue, remainder uniformly in the column), the sextic large sieve, the tower; decide success (curve reaches 2/3) or kill (irremovable main term `U^{2/3}`).

## Goal
README: `formal/GaloisForLFunctions/OrderSixMetaplecticTheory/README.md` (questions Q1–Q8). Lean in
`formal/GaloisForLFunctions/OrderSixMetaplecticTheory/`, umbrella `OrderSixMetaplecticTheory.lean`.

## Gates
- [x] 0 → 1 in-progress: README draft, questions, thesis "order six is the square of order three"
- [ ] 1 → 2 fully-proven: per conjecture below
- [ ] 2 → 3 formalized: per module

## Approach
Thesis: Hasse–Davenport makes every first moment of order six a twisted Rankin–Selberg convolution of
the cubic theta function on the cubic cover (STCC engine). Order of attack:
1. Bridge `γ₂ = normalizedCubicUnitGauss`; row-root series = conjugate twisted squarefree theta-square
   series (column 1). Transfer of STCC's simple pole: a coherent main term at `2/3`.
2. Columns: `Φ_n(c) = (n/c)₃(n/c)₂Φ(c)`; cubic part = shift `T(nc)T(1) = (n/c)₃T(n)T(c)`.
3. Isolation of the untwisted squarefree series: `O/3O` translates of θ_s normalize `Γ(3)` and keep κ;
   `(1/9)Σ_τ C_τ` projects onto `ν ∈ 3O` (layers `m ≥ 2`, constant term included); `D − (1/9)Σ_τ C_τ`
   is the unit layer `2Σ_I T(gen I)²…` = `S_1` times `Z₀(3w−1)`. Double poles of `C_τ` from the cusps fixed by
   the translation.
4. Smoothed first moments: incomplete Eisenstein series with entire rapidly decaying Mellin transform,
   polynomial growth of the resolvent pairing (`‖R(λ)‖ ≤ 1/|Im λ|`), contour shift to `Re s = 1 + ε`;
   squarefree part through `1/Z₀(3w − 1)` and the seed.
5. Sextic large sieve (Heath-Brown recursion at order six).

## Paper notes

**N1 [D] Bridge.** `residueAdditive 3 c d = tracePhase(d/(traceLambda·c))` and `principalTraceChar c d =
exp(2πi Tr(d/(traceLambda c)))`: the two additive normalizations agree, so `γ₂(c) = normalizedCubicUnitGauss c`.
With `σ(A) = ((9/a)₃ \overline{γ₂(a)})²` (STCC `thetaSquareWeight`): `Φ(a) = G(a)(9/a)₃²\overline{σ(A)}`, i.e.
`σ(A) = G(a)(9/a)₃²\overline{Φ(a)}` on odd squarefree `A`.

**N2 [D] Budget readings at `n = 6`.** Broken branch `θ(R) = (96R − 34)/(5(12R + 1))`, half-plane
`½ + (5/12)θ`. `R = 2/3 ↦ 7/9`, `R = 5/8 ↦ 77/102`, `R = ½ ↦ 2/3`. If the squarefree first moment has
remainder `(1 + Θ)/3` (cube convolution, zeros of `ζ_K` at `3w − 1`) uniformly in the columns and the main
term is harmless, the map `Θ ↦ ½ + (16Θ − 1)/(6(5 + 4Θ))` has the fixed point `(√337 − 1)/24 ≈ 0.7232`
(model only: both premises open).

- The 2-ramified twists (C12) are additive twists of `θ²` by `β ∈ (1/2)·(period lattice)`: the Rankin–Selberg series of `θ·θ(· + β)` on `H = Γ_ker ∩ T_β^{-1}Γ_ker T_β`. As for `S₁` (STCC), each twisted squarefree residue is the double-pole coefficient of that series divided by `Res Z₀`, and the double pole is a constant-term invariant: it needs the constant terms of `θ` at all cusps of `H` (via `SL₂(K) = SL₂(O)·B(K)`, the constant terms of `θ` at all cusps of `SL₂(O)`). At non-rational cusps these are residues of Kubota series restricted to classes mod 3, i.e. the undetermined 3-adic data `T(uλ^m)`. Next infrastructure: `θ` at every cusp of `SL₂(ℤ[ω])` (Patterson's ramified computation at `λ`), then Rankin–Selberg on the cover `H`.
## Conjecture ledger
- C1 (PROVED, Lean, pointwise): bridge `Φ = G(9/c)₃²σ̄` (module 1). Series-level transfer pending; main term of `S_1` is being isolated by a peer in STCC (translated correlations, card `the-unramified-theta-square-has-a-nonzero-pole.md`) — do not duplicate.
- C7 (PROVED, Lean): the continued cubic Eisenstein correction has no singularity on the real segment `s>1` except `4/3` (the residual spectrum seen by the cusp ∞ is `{8/9}`).
- C8 (PROVED, Lean): a power remainder `O(t^β)` — sharp cutoff or the Gaussian smoothing of STCC's main-term theorem — for the untwisted squarefree theta-square moment forces every zero of `ζ_K` right of `max(½, 3β−1)` (upper half-plane) to be a zero of `Λ₀(2(1+·)/3)`. With STCC's `β > 5/8 = (1+7/8)/3`: the remainder exponent is the zero-free region of `ζ_K` at `3w−1` from both sides; the §2.9 success criterion (square-root remainder) is RH for `ζ_K` up to coincident zeros of the theta square.
- C2 (PROVED, Lean, pointwise): column `n = n₁n₂²k³` of the actual family = shifted theta product `G̃(−2n₁n₂c)G̃(n₁c)` times `(c/n₁k)₂Γ(c)` (Γ the quadratic Weil index, a function of `c` mod 4, `=1` on `c ≡ 1 mod 4`) and `r̄(n,c)`. The cubic part of the conductor phase is the shift by `−2`. So the order-six content of every long column is quadratic: `(c/n₁k)₂Γ(c) = r(n₁k,c)g₂(n₁k,c)/|c|`, the normalized quadratic Gauss sum of the row at the odd part of the column. Open: main terms of cubic shifted products with quadratic twists (need cubic Eisenstein series with cubic nebentypus at level `n₂`, quadratic twists of `θ`, and the 3-adic twist `(9/c)₃` between `G̃` and `T`).
- C9 (PROVED, Lean): layers — `g(χ_{a·b²c³d⁴e⁵}) = r·g_a(b³c²d)·g(χ_{b²c³d⁴e⁵})`: every sixth-power-free row is a squarefree row at the column `b³c²d`.
- C10 (open, the core): continuation and residues of the shifted products with quadratic twists `Σ_c ψ(c)·T(−2n₁n₂c)T(n₁c)N(c)^{−w}` (`ψ` = normalized quadratic Gauss sum at `n₁k` and `(9/c)₃`), uniformly in the column. Needs cubic Eisenstein series of `Γ(3)∩Γ₀(n₂)` with cubic nebentypus `(d/n₂)₃`, quadratic twists of `θ` (level `n₁k`), and the 3-adic layer `(ω², 2)` (translations by `λ^{−1}O`, level `3λ`); none is in the corpus.
- C11 (PROVED, Lean): conjugation symmetry and the sign of the unit-layer main term. `c ↦ c̄` conjugates the cubic symbols, the Gauss sums, the theta-square weights and the Gauss-sum Dirichlet series at both cusps; the Whittaker factor is symmetric at rational rows. The resolvent identification holds at every nonreal spectral parameter, so the continued cusp coefficients satisfy `K(s̄) = \overline{K(s)}` off the real axis and residues at `4/3` of reflected pairs are conjugate: `ρ(h̄) = \overline{ρ(h)}` for every row (the cubic theta function is conjugation symmetric); `C` is real, `T(ω²λ²)` is real. With `r, L(1,χ₋₃), M(4/3) > 0`: `G(X) = κX^{2/3} + O(X^{13/20})`, `κ > 0`.
- C12 (PROVED, Lean): the order-six family at column `1` is 2-ramified. `Φ(c) = Γ(c)χ₂(c)G̃(c)²`, `χ₂ = (·/−2)₃²`; `Γ(ωc) = Γ(c)`, `χ₂(ω) = ω² ≠ 1` ⇒ `Σ_{c mod 4} Γ(c)χ₂(c) = 0`. The trivial character of `(O/4)^×` has coefficient `0` in `Γχ₂`: `S₁` (positive main term) and the nine 3-adic twists do not occur in the family; Q2 at column `1` = residues of theta squares twisted by characters ramified at `2` (C10's level-4 objects). Same at every column `n`: the column law multiplies the phase by `\overline{r(n,c)}`, which is `ω`-invariant (`sum_column_phase_mul_cubicTwoChar`). Every layer `u = a·b²c³d⁴e⁵` too (`sum_layer_phase_mul_cubicTwoChar`). The order-six weight is conjugation symmetric; the smoothed first moment is real (`star_gaussianSmoothedOrderSix`).
- C14 (PROVED, Lean): the 3-adic partner. `(ω²λ²)² = 9` ⇒ `(ω²λ²/c)₃²σ(c) = \overline{G̃(c)}²`: `S_{ω²λ²}` is the plain mean of squared Gauss sums and `ω₆ = Γχ₂·\overline{coeff(S_{ω²λ²})}`. Its weight `(T(ω²λ²)/T(1))²` in `D` is `≥ 0` real. At layer `λ²` integral translations do not separate `u ∈ {1, ω, ω²}` (`uλ²c ≡ uλ² ≡ λ² mod λ³`), so `R(S_{ω²λ²})` needs translations by `λ^{−1}O`.
- C15 (mechanism, paper): the 2-adic twisted residues need the Eisenstein series `E_H` of `H = Γ_ker ∩ T_β^{−1}Γ_kerT_β` (`β ∈ ½L`) at `∞`. Two facts make the double-pole computation constant-term-only: (i) `T_βδ∞` (`δ ∈ Γ_ker`) stays in the `∞`-class of `Γ(3)` (β is 3-adically integral), so only `θ`'s expansion at `∞` and its constant terms at the four rational cusps enter (STCC's partial-subtraction framework then gives the double pole); (ii) at the non-rational cusp `1/ω` the Kubota character is nontrivial on the parabolic subgroup (`κ(γT₃γ^{−1}) = (2/(1+3ω))₃ = ω² ≠ 1` in `F₇`), so `θ` has no constant term there. Dead ends recorded: the trace of `θ_β` to `Γ_ker` is a Hecke image of `θ` (Patterson's relations), so Rankin–Selberg against the pulled-back `E_{Γ_ker}` returns only the known `D`; `T(c)T(pc)` reduces to cubic twists by the prime recurrence. Missing input: the resolvent/Laplacian theory of MMD on `L²(H\ℍ³)` (MMD is specific to `Γ_ker`).
- C16 (PROVED, Lean): the Hecke-at-four mechanism reaches the 2-ramified twists without `E_H`. `F(w) = θ_s(Aw)θ_s(A⁻¹w)` (`A = diag(√2, 1/√2)`) has multiplier `κ²` on `Γ_A = Γ(3) ∩ {2 ∣ b, 2 ∣ c}` (the 2-adic nebentypus `(2/a)₃^{±1}` cancels); its trace to `Γ(3)` is automorphic; `Γ(3)/Γ_A ≅` ordered pairs of distinct points of `P¹(𝔽₄)` (column pair mod 2), twenty representatives with `κ = 1`; `Tr F = Σ_t θ^{(∞)}θ^{(t)} + Σ_t θ^{(t−1)}θ^{(∞)} + Σ_{u,t} u θ^{(t−u²)}θ^{(t)}` (`κ(L₊(u)) = (−3u/−2)₃ = u`). Constant term: `∫_P Tr F = 8|P|(Σ_h b(2v,h)b(v/2,−4h) + Σ_h χ(h) b(v/2,h)b(v/2,−h))`, `χ(h) ≡ h mod 2` a cube root of unity (Gauss sum of `𝔽₄`: `Σ_u u ψ(hu²) = 2χ(h)`). Growth `8c²v^{4/3}` from the shifted square only. Next: `G' = Tr F − 8θ_s²` has no growth; if bounded with `O(v^{−7/3})` decay, its Eisenstein pairing has at most a simple pole, so `(s−4/3)²M(s)[2^{−s}D₄(s) + 2^{s−2}L_χ(s)] → 108π³r³` (same as `D`). Needs: rationalExtension-equivariance of `Tr F` (generators `S`, `T²`, `Γ(3)`), Hermite decomposition of determinant-2 matrices, ramified-class smallness at Hecke points.
- C13 (conjecture): `R(ηχ₂) = 0` for the three nontrivial Klein characters `η` of `(1+2O)/(1+4O)` (quadratic twists are invisible to the cubic theta: the local factor at `2` of an odd row is the Haar measure on units). Then the order-six main term at column `1` is `½` the residue of the `χ₂`-twist of `\overline{S_{ω²λ²}}`, the cubic twist by `(−2/c)₃²` (a frequency twist by reciprocity, so not expected to vanish). Test: the Rankin–Selberg of `θ` with its `η`-twist on the level-4 cover.
- C3 (open): isolation of `S_1` by the `O/3O` translation correlations; residue in closed form.
- C4 (open): smoothed asymptotic for `Σ T(ν)² W(N(ν)/X)` with remainder `X^{½+ε}`.
- C5 (open): smoothed squarefree first moment with remainder `X^{(1+Θ)/3+ε}`.
- C6 (open): sextic large sieve `(M + N + (MN)^{2/3})(MN)^ε`; below `(MN)^{2/3}`?

## Lean modules
| Module | Content | State |
|---|---|---|
| `TheRowRootNumbersAreConjugateThetaSquares` | additive characters agree (`residueAdditive_eq_principalTraceChar`); `χ_c² = (·/c)₃`; `γ₂ = G̃` (`thetaGauss_eq_normalizedCubicUnitGauss`); `Φ = G(9/c)₃²σ̄`, `σ = G(9/c)₃²Φ̄`; column law `g_c(n) = r̄(n,c)(c/n)₃(c/n)₂g_c(1)`, square columns; tower `\overline{(c/|c|)}^{6k}Φ = Gγ₂²γ̄₂^{18k}` | clean |
| `TheCubicResolventHasSimplePolesOnTheRealSegment` | pencil coercive for real `x<0`; at real `μ∈[0,1)`: `T(z)⁻¹ = ((μ+1)/(μ−z))P + B(z)⁻¹(1−P)` (shifted pencil `T+P` invertible); `L²` resolvent `= ((μ+1)/(μ−z))Π_μ + R_reg`; `⟨F,Π_μF⟩ = ‖P m*F‖²` | clean; olean |
| `TheSeedDefectReadsTheConstantTerm` | `⟨defect(s₀),F⟩ = K∫_5^6 d̄(v)(∫_P F)v^{−3}` for continuous `F` of multiplier κ; constant term of `E(s)−seed(s)` | clean; olean |
| `TheEisensteinCorrectionIsHolomorphicOnTheRealSegment` | Mellin integrals over `[a,b]` entire; `⟨defect(s₀),Corr(s)⟩ = Ψ(s)` on `Re s>1, Im s>0`; **`Π_μ defect(s₀) = 0`** for `1<s₀≤2`, `s₀≠4/3`; **`correction_removable`**: Corr has removable singularities on the real segment `s>1` except `4/3` | clean; olean |
| `TheEisensteinCorrectionContinuesToTheStrip` | removable singularities ⇒ analytic extension by punctured limits; `Corr` analytic on `Re s>1`, `s≠4/3`; `‖R(z)F‖ ≤ ‖F‖/|Im z|`; `‖Corr(s)‖ ≤ ‖defect(s)‖/(2|Im s|(Re s−1))` | clean; olean |
| `TheSquarefreeRemainderReadsTheZerosOfTheCubeZeta` | `S₁` as an `L`-series by norms; Abel summation `S₁(w) = w(c/(w−2/3)+J(w))`, `J` holomorphic on `Re w>β`; **`remainder_forces_thetaSquare_zero`**: `Σ_{N(A)≤t}σ(A) = ct^{2/3}+O(t^β)` ⇒ every zero `ρ` of `ζ·L(·,χ₋₃)` with `Re ρ>max(½,3β−1)`, `Im ρ>0` has `Λ₀(2(1+ρ)/3)=0`; square-root and exponent corollaries | clean |
| `TheSmoothedRemainderReadsTheZerosOfTheCubeZeta` | Laplace transform of the Gaussian-smoothed sum `= e^{w²}S₁(w)`; one-sided Laplace transforms holomorphic; **`smoothedRemainder_forces_thetaSquare_zero`**: the converse of STCC's smoothed main term — `O(X^β)` forces zeros of `ζ_K` right of `3β−1` into `Λ₀(2(1+·)/3)` | clean |
| `TheColumnsAreShiftedThetaProducts` | **`rowRoot_column_hasseDavenport`**: `Φ_n(c)·G̃(−2n₁n₂)G̃(n₁) = r̄(n,c)r(n₁k,c)·g³_c(n₁k)/|c|·G̃(−2n₁n₂c)G̃(n₁c)`; `quadSymbol_mul_fixedDualAverage`: `(c/q)₂Γ(c) = r(q,c)g³_c(q)/|c|`; twisted multiplicativity `G̃(ab) = \overline{(a/b)₃}G̃(a)G̃(b)`; column `n = n₁n₂²k³`: `Φ_n(c)·G̃(n₁n₂)G̃(n₁) = r̄(n,c)(c/n₁k)₂G(c)·G̃(n₁n₂c)G̃(n₁c)`; square columns cubic, cube columns quadratic twists; **conductor phase** `\overline{χ_c(4)} = (c/−2)₃²`, `Φ(c)G̃(−2) = Γ(c)G̃(−2c)G̃(c)`; **`rowRoot_column_shift_actual`**: `Φ_n(c)·G̃(−2n₁n₂)G̃(n₁) = r̄(n,c)(c/n₁k)₂Γ(c)·G̃(−2n₁n₂c)G̃(n₁c)` | clean |
| `TheSixthPowerFreeRowsSplitIntoLayers` | Gauss sum of `χ_u` on its conductor; **`rowConductorGauss_peel`**: `g(χ_{au'}) = χ_a(m)χ_{u'}(a)g_a·g(χ_{u'})`; **`rowConductorGauss_layers`**: `u = a·b²c³d⁴e⁵`: `g(χ_u) = r(a,M)·g_a(b³c²d)·g(χ_M)` | clean |
| `ComplexConjugationActsOnTheCubicSymbols` | conjugate ideals (maximal, good, primary generators, squarefree, norms); Euler's criterion under conjugation; **`symbol_conjO`** `(x̄/c̄)₃ = \overline{(x/c)₃}`; `cubicUnitGaussSum_conj`, `normalizedCubicUnitGauss_conj`, **`thetaSquareWeight_conj`** | clean; olean |
| `TheUntwistedThetaMainTermIsReal` | `untwistedSquarefreeCoefficient_conj`; the smoothed untwisted sum is real; `thetaGaussianMainCoefficient_im`, `untwistedThetaResidue_im`; `M(4/3)` real | clean; olean |
| `TheGaussSumSeriesAreConjugationSymmetric` | `arithmeticResidueSum_conj` (residues mod `3c`, `row_symbol_shift`); **`arithmeticDirichletSeries_conj`**, **`unramifiedCubicGaussSeries_conj`**; source kernel and **`cuspWhittakerHeightFactor_star`** at rational rows | clean; olean |
| `TheCubicThetaFunctionIsConjugationSymmetric` | resolvent identification for `Im s ≠ 0`; both cusp families `= series × W` in both half-planes; **`reflection_of_initial`**, **`residue_star_of_reflection`** (pairs `K, K'`); residues at both cusps conjugate under `h ↦ h̄`; **`rationalSourceResidualFourierCoefficient_conj`**: `ρ(h̄) = \overline{ρ(h)}`; **`rationalSourceThetaScalar_star`**; `T(ω²λ²)` real (`T(uλ) = 0` is STCC's) | clean; olean |
| `TheUntwistedThetaMainTermIsPositive` | `Z₀(x) ≥ 1` on `x > 1`; `r > 0`; **`LFunction_chi3D_one_isPosReal`**; `M(4/3) > 0`; `C² > 0`; **`gaussianSmoothedUntwistedTheta_positive_main_term`** | clean; olean; axioms standard |
| `TheOrderSixFamilyIsOrthogonalToTheUntwistedSquare` | `χ₂(c) = (c/−2)₃²`; `(ω/−2)₃ = ω` (`N(2) = 4`); `Γ(ωc) = Γ(c)` from `fixedDualAverage_formula`; **`sum_mul_cubicTwoChar_eq_zero`** (orthogonality to `ω`-invariant functions mod 4); `Σ_{c mod 4} Γχ₂ = 0`, and with `\overline{r(n,c)}` at every column, and in every layer (`sum_layer_phase_mul_cubicTwoChar`); **`rowRootNumber_eq_weil_mul_cubicTwo`**: `Φ = Γχ₂G̃²` | clean |
| `TheOrderSixFirstMomentIsReal` | `Γ(c̄) = \overline{Γ(c)}` from the explicit formula; `χ₂(c̄) = \overline{χ₂(c)}`; **`orderSixWeight_conj`**; order-six coefficients on ideals; **`star_gaussianSmoothedOrderSix`** | clean |
| `TheOrderSixFamilyTwistsThePlainSquares` | `(ω²λ²)² = 9`; `(9/c)₃ = (ω²λ²/c)₃²`; **`twisted_coefficient_eq_plain_square`**; **`orderSixWeight_eq_conj_plain`**, on ideals; **`plain_square_weight_nonneg`** | clean |
| `TheHeckeAtFourCorrelationHasTheSquareMultiplier` | `Γ_A` (`fourCorrelationGroup`); **`heckeFourCorrelation_automorphy`**: `F_Θ = Θ(A·)Θ(A⁻¹·)` has multiplier `κ²` on `Γ_A` for any `Θ` of multiplier `κ` | clean; olean |
| `TheHeckeAtFourCorrelationReadsTheShiftedSquare` | cross-Parseval `∫_P S_a(4u)S_b(u) = |P|Σ a_h b_{−4h}`; constant term of `F` for `θ_s`; `b(2v,h)b(v/2,−4h) = T(h)T(−4h)v²K_{1/3}(8π|ξ_h|v)²` | clean; olean |
| `TheHeckeAtFourTraceIsAutomorphicOnTheCubicCover` | generic coset trace (`cosetTrace_smul`); `Γ_A` finite index; **`heckeFourTrace_automorphy`** on `Γ(3)` | clean; olean |
| `TheHeckeAtFourTraceHasTwentyCosets` | reduction mod 2 (`red`, `two_dvd_iff`); column pairs in `P¹(𝔽₄)`; twenty representatives, `κ = 1`; **`heckeFourTrace_eq_sum`** | clean; olean |
| `TheHeckeAtFourTraceIsAPhasedSumOverHeckePoints` | `−1` acts trivially; Euler at `2` (`symbol_root_neg_two`); **`heckeFourTrace_eq_hecke`**: trace = phased sum of Hecke-point products | clean; olean |
| `TheHeckeAtFourTraceReadsTheCubicTwistAtTwo` | doubling on `P` (`integral_periodDomain_two_mul`); trace character of `𝔽₄` (`tracePhase_half`); Gauss sum `gaussFour`; **`integral_sourceFourTrace`** | clean |

## Log
- 2026-11-16 — created; README first draft; modules 1–4 (bridge, real-segment resolvent, defect unfolding, real-segment holomorphy); module 5 (strip continuation, resolvent bound); module 6 (remainder reads the zeros of `ζ_K`). The cutoff transfer `[5,6] → [2,3]` was done by STCC (`TheThetaCorrectionHasOnlyTheCubicPole`).
- 2026-11-16 — modules 7–9 (smoothed remainder, columns, layers); modules 10–14 (conjugation, reality of the residues, `C` real, positive main term): C11.
