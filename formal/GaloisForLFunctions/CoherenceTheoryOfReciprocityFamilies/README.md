# Coherence Theory of Reciprocity Families (CRF)

Namespace `GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies`; umbrella
`CoherenceTheoryOfReciprocityFamilies.lean`. Source: review-1111, obstacles summary §2.9.

## 1. Why this field

The corpus has one producer of a pointwise theorem about the zeros of ζ: the continuation of the
reciprocals of a family of Hecke `L`-functions over `ℚ(ζ₃)` from two estimates for one completed
sum, the cubic-theta probe. It gives `Re s > 7/8` (the external theorem `[X]`). Its frame, its
budget and its arithmetic are in Lean in `FamilyContinuationTheory` (FCT) and
`MetaplecticMobiusDescent` (MMD). Every other route of the corpus is a receiver of this scale.

The producer has three limits above the line, and two of them come from one step:

| Limit | Value | What sets it |
|---|---|---|
| room of the estimates | `[13/15, 7/8]` | the row count of the binding bin |
| floor of the squares | `13/15`, then `5/6` | every bound that takes absolute values across the rows, or Cauchy–Schwarz between rows and columns |
| wall of the frame | `2/3` (`3/5` with a tower) | the correction `H_η` of the target contains a second `L`-function |

The probe bounds a law (a mean square over a twist family) by squares and converts it to a point
because the target occurs among its own twists. Everything the class does with squares is mapped
in Lean. What none of the programme folders contains is **an estimate of a family that is not a
square**: an evaluation of the phases between the amplitudes of a family of rows and the columns
of a reciprocity kernel.

CRF is the theory of those phases. It asks when arithmetic amplitudes **align** with a column
(coherence) and when they **cancel** (incoherence), it evaluates instead of bounding, and it treats
the correction of a family as a family of the same theory.

## 2. Objects

| Object | Meaning |
|---|---|
| row family | the Poisson frequencies `u` of the probe (sixth-power-free elements of `ℤ[ω]`), each with the row character `χ_•(u) : p ↦ χ_p(u)` and the row quotient `ζ(6z) L(w, χ_•(u)) H_{η,u}/L(x, ηχ_•(u))` |
| row local series | at a good prime `π ∤ u` the complete local series of row `u`; it depends on `u` only through `ρ = χ_π(u) ∈ μ₆` |
| mode | the Fourier component of the row local series in `ρ`: `ρ^k`, `k mod 6` |
| average row | mode `0`: the mean of the row local series over `μ₆`, the coherent part of the family along the principal twists |
| column | a periodic function of the row variable; a character modulo `q`; its conductor |
| short / long column | conductor below / at least the row scale |
| floor bin | the rows whose `L`-functions have no zero right of `51/100`; their row quotients summed on the floor contours |
| signed Gram | `Q_M(α) = Σ_m ‖Σ_u α(u) Φ(u, m)‖²`, diagonal plus signed off-diagonal |
| row exponent `R₀` | the exponent of the floor-bin sum relative to one row: `½` square-root cancellation, `1` the triangle inequality |
| saving before Cauchy–Schwarz `s` | the gain of a bilinear estimate over its squared form, in the twist exponent |
| correction `H_η` | the Euler product between the principal row and `L(s, η)⁻¹` |
| phase `L`-function | `L_A(w) = Π (1 − A_v N(v)^{−w})⁻¹`; for the probe `A_v = κ_v⁶ = ψ₆(v) η(v)⁶`, `ψ₆(π) = (π̄/|π|)⁶` |
| wall | the abscissa below which the frame reads a second `L`-function |
| row root number | the normalized Gauss sum of the row character, the amplitude of the dual side of `L(w, χ_•(u))` |

## 3. Language

- **Coherent / incoherent**: the sum over the rows has the size of the triangle bound / cancels to a
  power.
- **Mode, average row**: Fourier analysis of the row family in the residues `χ_π(u)`.
- **Short and long columns**: a column is short if Poisson summation in the rows sees no dual
  frequency on the lattice.
- **Evaluation before Cauchy–Schwarz**: a statement about a sum itself, not its square.
- **Wall, transport**: below the wall the frame proves that zeros of the target are zeros of the
  correction.
- **The twist exponent** `θ`, the common ruler: the half-plane is `½ + (1 − 1/n)θ/2`; at `n = 6` the
  thresholds `s = 1/12, 1/6, 1/3` are `¾`, the wall `2/3`, the line.

## 4. Mechanisms

1. *The frame* (FCT). Two estimates for one sum compared with the signal of
   `exp((s − c)²) H_η(s)/L(s, η)` give the half-plane where `H_η` is holomorphic and nonzero.
2. *The source identity* (MMD). The cube of the composite cubic Gauss sum is the ideal Möbius value
   times the angular part of the modulus; odd orders carry the Möbius sign, even orders the parity.
3. *The signed Gram* (FCT). Interchanging rows and columns before absolute values leaves the column
   energy times the exact signed Gram of the rows; matched phases saturate it.
4. *The wall is a phase `L`-function* (here). The denominator `1 − A Q^{3−6s}` of the principal local
   factor is the local factor of `L_A` at `w = 6s − 3`; the numerator is within `9Q^{−e}` of one on
   all of `Re s > ½`. In the three variables of the probe the factor is `L(6x + 6z − 4, ψ₆η⁶)` and
   is common to every row; on the floor contours (`Re z ≥ 17/50`) it is absolutely convergent, and
   it becomes the wall only at the signal, the residue `z = 1/6`.
5. *Modes of the row family* (here). The row local series is
   `P(ρ) = (1−V)⁻¹ + ρY(1−ρY)⁻¹ + (1−R)⁻¹(R(1−Q⁻¹)(1−V)⁻¹ + ρYR − ηρ⁻¹X − η(Q−1)XYV(1−V)⁻¹)`.
   The target `1/L(x, η)` sits in the mode `ρ⁻¹`; the plain columns `L(w, ·)` in the modes `ρ^k`,
   `k ≥ 1`. The average over `μ₆` keeps mode `0` only.
6. *Poisson in the rows* (here). A column is a combination of phases `e(⟨u, θ⟩)`; its row sum is
   the dual lattice sum `|det B|⁻¹ Σ_m f̂(B^{−*}(m − θ))`. Off the lattice the dual sum decays to
   every order in (row scale)·(distance of `θ` to `ℤ^d`).
7. *Hasse–Davenport on the rows* (here). For squarefree `c`,
   `χ_c(4) g_c^{(1)} g_c^{(2)} = μ(c) c g_c^{(3)}` and `χ_c(4) N(c) g_c^{(1)} = g_c^{(3)} (g_c^{(2)})²`:
   the cross factors of the sextic, cubic and quadratic Gauss sums cancel (`X·X² = X³`, `X³X⁴ = X`).
   With `g_c^{(3)} = |c| Γ(c)` the root number of a row is `G(c) γ₂(c)²`, the square of the theta
   coefficient `γ₂(c) = g_c^{(2)}/|c|` of the probe times the phase `G(c) = \overline{χ_c(4)} Γ(c)` of
   bounded conductor; `γ₂(c)³ = μ(c) c/|c|`.

## 5. Pillar theorems

**From FCT and MMD.**

| Theorem | Lean |
|---|---|
| frame with reciprocal kernels and corrections | `zetaZeroAbscissa_le_of_two_reciprocal_estimates`, `exists_cutoff_zetaZeroAbscissa_le_of_probe_estimates` |
| the cube identity; the sign law at odd and even order | `compositeCubicGauss_cube`; `exists_gaussSum_pow_orderOf_eq_of_odd`, `…_of_even` |
| signed Gram identity; saturation; the curve in `R₀` | `norm_sq_bilinearFloorSum_le_mul_signedGram`, `exists_matched_phase_saturation`, `signedGramSymmetricTheta` |
| every Cauchy–Schwarz row sieve stops at `θ = (n − 2)/(n − 1)`; escape needs `s > 0` | `free_floor_le_probeThetaHybridFree`, `escape_below_free_floor_bound` |
| the complete local identity of a row | `hasSum_localTerm` |
| the correction as a Grössencharacter `L`-function (A139) | `principalCorrection_eq_euler_mul_residual`, `primeKappa_tower_pow_six` |
| the tower `L`-functions continue; the correction has zeros in `7/12 ≤ Re s < 2/3` | `infinite_zeros_continuedProbeCorrection_in_strip`, `no_nonvanishing_continuation_of_probeCorrection_below_seven_twelfths` |

**Of this programme.**

| Theorem | Lean | Answers |
|---|---|---|
| the wall: `H = L_A(6s−3)·E`, `E` holomorphic and nonzero on `Re s > ½` | `principalCorrection_eq_phaseLFunction_mul`, `exists_regularCorrection_cutoff` | Q4 |
| the frame premise at `½ < σ ≤ 2/3` is a zero-free half-plane `Re w > 6σ − 3` of `L_A` | `framePremise_iff` | Q4 |
| below the wall the frame is a transport law: a zero `ρ` of `L(s, η)` forces a zero `6ρ − 3` of `L_A` | `heckeLFunction_transport`, `heckeLFunction_transport_phase` | Q5 |
| the row local series is `P(χ_π(u))`; its `μ₆`-average has no target term | `hasSum_localTerm_rowLocalSum`, `average_rowLocalSum` | Q1, Q2 |
| the average row is an absolutely convergent Euler product, holomorphic and without zeros in `x` on the floor region | `exists_averageRowCorrection_cutoff` | Q1 |
| reflection of a row sum; decay off the lattice; short columns are incoherent | `tsum_phase_mul_comp_eq`, `tsum_norm_le_of_far`, `norm_tsum_column_le` | Q2, Q3 |
| over `ℤ[ω]`: a column of mean zero modulo `c` has row sum `O((μ√(2/(3N(c))))^{−M})`; the dual frequencies of `ψ_c(h·)`, `c ∤ h`, lie at distance `≥ √(2/(3N(c)))` from `ℤ²` | `norm_tsum_eisensteinColumn_le`, `sqrt_le_norm_sub_thetaH`, `card_mul_eq_sum_dual` | Q2, Q7 |
| the Möbius sign of the row modulus in its Gauss sums | `rowGauss_product`, `rowGauss_defect_mul` | Q1, Q6 |
| the Gram entry of two rows is a completed sum: `G(u₁,u₂) = |O/(u₁u₂)|⁻¹|det B|⁻¹ χ_{u₁}(u₂)χ_{u₂}(u₁)⁵ Σ_h g_{u₁}^{(1)}(−h) g_{u₂}^{(5)}(−h) Σ_m f̂(B^{−*}(m − θ_h))`; reflection of any column | `gramEntry_eq_completedSum`, `tsum_column_eq_dualOf`, `sum_pairColumn_traceChar` | Q3 |
| the reflected Gram is twisted by the root numbers: at a dual frequency `h` prime to `u₁u₂` the coefficient is `r(u₂,u₁) χ_{u₂}(−1) \overline{χ_{u₁}(−h)} χ_{u₂}(−h) |u₁||u₂| Φ(u₁)\overline{Φ(u₂)}`, `Φ = G γ₂²`, `r` the quadratic bicharacter modulo four; at `−h = k⁶` it is rank one | `gramCoeff_eq`, `gramCoeff_eq_thetaSquares`, `gramCoeff_sixthPower`, `sexticGaussPow_one_mul_five` | Q3, Q7 |
| the short sextic Gram is diagonal: distinct squarefree rows give a pair column of mean zero (`g_c^{(j)}(0) = 0`), so their Gram entry is `O((μ√(2/(3N(u₁u₂))))^{−M})` | `norm_gramEntry_le`, `sum_pairColumn_eq_zero`, `sexticGaussPow_zero_prod` | Q7 |
| the root number of a row: `g̃⁽¹⁾ = μ(c)·(c/|c|)·χ̄_c(4)·g̃⁽³⁾·\overline{g̃⁽²⁾}`, with `|g⁽ʲ⁾_c| = |c|` | `rowRootNumber_eq_angularTwist`, `normSq_sexticGaussPow_prod` | Q1, Q2 |
| the root number of a row is the square of the theta coefficient: `g̃⁽¹⁾ = G(c) γ₂(c)²`, `g⁽³⁾ = |c| Γ(c)`, `γ₂(c)³ = μ(c) c/|c|`, so `μ(c)(c/|c|)\overline{γ₂(c)} = γ₂(c)²` | `rowRootNumber_eq_thetaPhase_mul_sq`, `rowHasseDavenport`, `thetaGauss_cube`, `moebius_angular_mul_conj_thetaGauss` | Q1, Q2, Q6 |
| the wall is the price of completion: the local series on cube-free indices is `R`-free, every `R`-term is a joint sixth power of index and frequency, and the uncompleted correction has no wall on `Re s > ½` | `hasSum_localTerm_uncompleted`, `rowLocalSum_sub_uncompleted`, `exists_uncompletedCorrection_cutoff` | Q4 |

## 6. Questions

| # | Question | State |
|---|---|---|
| Q1 (B175) | For the actual floor bin: is `R₀ < 1`, is there `s > 0` before Cauchy–Schwarz, or do the amplitudes saturate? | reduced (§7): the average row and the short columns are settled (Lean); the long columns are the first moment of `Gγ₂²`, coherent at `R₀ = 2/3` [C]/[D], so an evaluation lands the floor bin on the endpoint `7/9` of its curve; open: the remainder uniformly in the column |
| Q2 | Which directions of amplitude space are coherent besides the principal twists? | the principal twists (mode 0) are target-free; short columns are incoherent; the long columns are read by the squares `γ₂(u)²` of the theta coefficients (Lean), the normalized sextic Gauss sums of the rows, coherent along the sextic theta coefficients of the columns [C] |
| Q3 | Is the signed Gram of two rows a completed sum with its own reflection? | yes (Lean): a sum over the dual frequencies `h mod u₁u₂` at dual length `N(u₁u₂)` over the row scale, whose coefficient is the same kernel at `h` times the root numbers `Φ = Gγ₂²` of the two rows times the bicharacter `r` modulo four; the reflected Gram of `α` is the Gram of `αΦ`, and its sixth-power frequencies are rank one |
| Q4 (B184) | Do the families `ψ₆^k η` close under correction; their common abscissa; a form whose correction converges on `Re s > ½`? | closure `k ↦ 6k + 1` and the continuation of the tower `L`-functions (FCT); the wall is the zero abscissa of `L(·, ψ₆η⁶)` at `6s − 3` (here), and it is real: the continued correction has infinitely many zeros in `7/12 ≤ Re s < 2/3` and no nonvanishing continuation below `7/12` (FCT, `no_nonvanishing_continuation_of_probeCorrection_below_seven_twelfths`); without completion there is no wall, and completion is what the reflection needs; the common abscissa is a half-plane for the tower uniform in the infinity type: open |
| Q5 | What does the frame prove below the wall? | a transport of zeros into the phase `L`-function |
| Q6 | The coherence exponent of normalized Gauss sums of odd order against a column | for the rows of the probe the Gauss sums are of order six (Lean: `G γ₂²`), with the sextic Kubota residue `½ + 1/6` [C]; the remainder uniformly in the column: open |
| Q7 | Which reciprocity families cancel inside the mean square? | the sextic family cancels completely off the diagonal for pairs with `N(u₁u₂)` below the row scale (Lean); above it the entry is the completed sum of Q3; the quadratic family cancels in every range (sharp quadratic sieve over `ℤ[ω]`); for odd orders the long range is the large-sieve conjecture |
| Q8 | The analogue over `𝔽_q[T]` | open |

## 7. The floor bin as a first moment (state of Q1)

The floor bin is not a Gram problem but a first moment over the row family of the row quotients
`L(w, χ_•(u)) H_{η,u}/L(x, ηχ_•(u))` on the floor contours. Its parts:

| Part | Content | State |
|---|---|---|
| mode 0 (average row) | coherent along the principal twists, so `R = 1` is sharp for it; but it carries no reciprocal of the target: an absolutely convergent Euler product times `ζ(6z)ζ(6w)L(6x+6z−4)`. Its contribution to the high side is the residue of the row sum at `z = 1`, of size `Z^{Re x}` on the floor | Lean (local and Euler product); size [D] |
| short columns | conductor below the row scale: the full-family row sum is `O((q/λ)^M)` for every `M` | Lean (Poisson tool) |
| selection | the floor bin is chosen by zeros; its complement is counted by moments of the zero-detector polynomials, as the row counts of B174 | [D] |
| long columns | the dual side of `L(w, χ_•(u))`, weighted by the root number `G(u) γ₂(u)²`: a first moment over the rows of the normalized sextic Gauss sums of the row moduli, the squares of the theta coefficients of the probe | identity in Lean; main term `U^{½+1/6}` [C]; remainder open |

The binding part is the last one. It is not a Möbius-signed family: the Möbius value and the angular
character of infinity type one in the root number are the cube of the theta coefficient
(`γ₂(u)³ = μ(u) u/|u|`), so the root number is `G(u) γ₂(u)²`, a sextic Gauss sum. Its first moment
over the rows against a dual column `n` is the sextic Kubota series, whose pole at `½ + 1/6` has the
sextic theta coefficient of `n` as residue [C]. The long columns are coherent along the sextic theta
directions, with row exponent `½ + 1/6 = 2/3`, and that main term is evaluable.

**The Rankin–Selberg square of the cubic theta function [D].** The Fourier coefficients of the cubic
residue `θ` (MMD) satisfy `\overline{T(ab³)} = C |b| \overline{(δ/a)₃} G̃(a)`, `C = \overline{T(1)} ≠ 0`, on
squarefree `a` and arbitrary `b` (`normalized_sourceFourier_squarefree_cube`), with `G̃` the normalized
cubic Gauss sum (`γ₂` up to the normalization of the additive character). Unfolding `θ²` (multiplier
`κ²`) against the cubic Eisenstein series (multiplier `κ`, `κ³ = 1`) writes
`D(w) = Σ_ν T(ν)² N(ν)^{−w}` as the regularized `∫ θ² E(·, 2w)` over Gamma factors, and the support
formula factors it as `D = \overline{C}² ζ_K(3w − 1) S(w)` (unramified part), with
`S(w) = Σ_a (δ/a)₃² \overline{G̃(a)}² N(a)^{−w}`. The cube frequencies `ν = b³` are principal and give
the pole of `ζ_K(3w − 1)` at `w = 2/3` for every row. The constant term of `θ` is `c y^{2/3}`, so the
renormalized integral has, besides the pole of `E` at `s = 4/3`, the growth pole of `c² y^{4/3}` at the
same point: a double pole, with leading coefficient proportional to `c³ ≠ 0`. Hence the squarefree
part `S` — a finite-order twist of the long columns — has a simple pole at `w = 2/3`: it is coherent,
and its main term is carried by the constant term of `θ`, the principal Fourier mode; the triple
product `∫ θ³` enters the next Laurent coefficient. Below `2/3`, `S = D/(\overline{C}² ζ_K(3w − 1))`
meets the zeros of `ζ_K`: a zero `ρ` with `Re ρ > ½` is a possible pole of `S` at `(ρ + 1)/3`.

**What the budget reads [D].** FCT's floor-bin curve `θ(R₀) = ((6R₀ − 1)n − 8)/((6R₀ − 1)(n − 1))`
(`signedGramSymmetricTheta`, defined for `R₀ ≥ ½ + 1/n`) with the half-plane `½ + (1 − 1/n)θ/2`
gives at `n = 6`: `R₀ = 1 ↦ 13/15`, `R₀ = 5/6 ↦ 5/6` (the free floor), `R₀ = 2/3 ↦ 7/9`. The endpoint
`R_crit(n) = ½ + 1/n` of the curve is the Kubota exponent of Gauss sums of order `n`, and the row root
numbers are Gauss sums of order `n` (Lean at `n = 6`): an evaluation of the long columns lands the
floor bin on the endpoint of its curve, `7/9` as the floor bin's own limit. A bound by squares stops
at `R₀ = 5/6`: the cubic large sieve `(Q + N + (QN)^{2/3})(QN)^ε` of Heath-Brown gives `5/6` and no
more, and its term `(QN)^{2/3}` comes from the cubes among the reflected frequencies, the principal
subfamily of the reflected Gram — the coherent direction that the evaluation extracts as a main term.
What is missing is the sextic Kubota series uniformly in the column index, with the remainder below
`U^{2/3}`. The corpus has the cubic Eisenstein series, its residue and the cubic theta coefficients
(MMD); it has neither the sextic metaplectic Eisenstein series nor a sextic large sieve.

**Parity of the order.** The sign law gives the Möbius sign at odd order only; the large sieve over
`ℤ[ω]` is sharp at order two (`sieveNorm_sharp`) and open at odd order. The families that carry
the sign are exactly those whose mean squares are not known to cancel completely. In the rows the
sign is not a separate coefficient: it is the cube of the theta coefficient, and the root numbers
are its squares.

## 8. Traps

| Trap | Truth |
|---|---|
| A mean square over twists that contains the principal twists is an input | it is the half-plane itself |
| A cleverer row sieve, word, unitary change of basis or more row variables crosses `5/6` | every one is a square: `θ ≥ (n − 2)/(n − 1)` |
| `7/8` is a floor of the probe | a vertex of three estimates; the floors are `13/15` and `5/6` |
| The order `n` of the budget is the order of the Gauss-sum power | it is the order of the row twists; the source is always the cube identity |
| Dividing the correction out removes the wall | it moves to the direct side (exponent `max(a₁, 2/3)`); the joint sixth power of the completed theta index and the frequency produces it in every row |
| The wall bites on every row | only at the signal (`z = 1/6`); on the floor contours the phase factor converges absolutely |
| The triangle bound `R = 1` of the floor bin is a loss | it is sharp for the average row, which is harmless; the question is the rest |
| The floor bin, being selected by zeros, cannot be summed with signs | the complement is counted by detector moments; selection is a cost, not an obstruction |
| The target is read by the whole row family | it lives in the mode `ρ⁻¹`, which averages to zero: only the principal row reads it |
| The Möbius value and the angular character in the row root numbers are a twist that removes the metaplectic main term | they are the cube of the theta coefficient: the root number is `G(u) γ₂(u)²`, a sextic Gauss sum, coherent at `½ + 1/6` [C] |
| The pole-cleared frame `(s − 1)L(s, ψ)` | a false premise as soon as the family has a nonprincipal character |
| Even order carries the Möbius sign | at even order the sign is the parity `χ(−1)` |

## 9. Position in the corpus

| Programme | Relation |
|---|---|
| FamilyContinuationTheory | the frame, the budget, the corrections, the Poisson arithmetic of the probe; CRF is its signed layer |
| MetaplecticMobiusDescent | the cube identity, cubic reciprocity, the cubic Eisenstein series and its residue |
| HTGeometry | Poisson summation on affine lattices, lattice weights |
| SelectiveArithmetic | the ladder and the rungs that read the half-plane |
| FloorFreeArithmetic | the floor census: every large-sieve budget has a floor |
| summary §2.11 (reciprocity calculus without squares), §2.18 (route MC/JAS) | the same objects with an elementary reflection; the stages `7/8 → 13/15 → 5/6 → 2/3 → 3/5`, of which CRF owns `13/15 → 5/6 → 7/9` (the floor bin to the endpoint of its curve) and the wall |

## 10. Success criteria

1. B175 answered for the actual coefficients: an estimate `R₀ < 1` or `s > 0`, or a theorem that they
   saturate along named directions.
2. The coherent directions of the row family classified.
3. The signed Gram of a pair evaluated as a completed sum with its reflection.
4. The tower of corrections closed or shown not to close, with its common abscissa.
5. Every statement calibrated on matched phases, on `μ²` and on even order.

## 11. What a contribution must be

- H1 It evaluates before Cauchy–Schwarz.
- H2 It saturates on matched phases and on the principal twists.
- H3 It fails for `μ²` and for even order.
- H4 Its exponents are stated in the twist exponent, against `1/12`, `1/6`, `1/3`.
- H5 It treats the correction of a family as a member of the theory.
- H6 Unconditional in Lean; an implication counts only when the implication is the content (a frame,
  a transport law), and its premise is named as open.
- H7 It moves a limit of §1 or answers a question of §6.

## 12. Open research topics

1. The long columns of the floor bin: the first moment of the row root numbers `G(u) γ₂(u)²` against
   the dual columns, i.e. the sextic Kubota series uniformly in the column index, its main term (the
   sextic theta coefficients) and a remainder below `U^{2/3}`; the identification of `γ₂` with the
   Fourier coefficients of the cubic theta function of MMD; the Rankin–Selberg square `∫ θ² E` on the
   cubic cover (unfolding over `ℍ³`, the double pole at `s = 4/3`, its leading coefficient from the
   constant term of `θ`, the main term of each finite-order twist of the long columns).
2. The long range of the Gram: the reflected Gram of the amplitudes `α(u)Φ(u)` against the dual
   columns with the bicharacter `r`, summed without the weighted Cauchy–Schwarz inequality; the
   weight `f̂` couples the two rows through `u₁u₂`, and its separation is the step where the
   principal (sixth-power) frequencies produce the large-sieve term `(QN)^{2/3}`.
3. The common abscissa of the tower `ψ₆^k η`: a half-plane uniform in the infinity type.
4. Coherence exponents of Gauss-sum families against a column (Q6); the theta coefficients as the
   coherent directions; for row twists of order `n`, the endpoint `½ + 1/n` of the budget curve as the
   Kubota exponent of the row root numbers.
5. A source outside the cubic probe whose correction converges on `Re s > ½` while keeping a
   reflection: within the cubic probe completion is necessary for the one and excludes the other.
6. The function-field analogue (Q8): over `𝔽_q[T]`, `q ≡ 1 mod 6`, Hasse–Davenport gives the same
   root numbers `G γ₂²`, the Kubota series are rational functions in `q^{−s}` and the theta
   coefficients are explicit [C], so the long columns of a function-field probe can be evaluated
   exactly; the analogue tests whether the floor bin reaches the endpoint `½ + 1/n` of its curve.
