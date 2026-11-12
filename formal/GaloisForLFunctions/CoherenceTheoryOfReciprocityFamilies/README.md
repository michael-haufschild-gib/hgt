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
   `χ_c(4) g_c^{(1)} g_c^{(2)} = μ(c) c g_c^{(3)}`: the cross factors of the sextic, cubic and
   quadratic Gauss sums cancel (`X·X² = X³`), and each prime contributes `−π`.

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
| the short sextic Gram is diagonal: distinct squarefree rows give a pair column of mean zero (`g_c^{(j)}(0) = 0`), so their Gram entry is `O((μ√(2/(3N(u₁u₂))))^{−M})` | `norm_gramEntry_le`, `sum_pairColumn_eq_zero`, `sexticGaussPow_zero_prod` | Q7 |
| the root number of a row: `g̃⁽¹⁾ = μ(c)·(c/|c|)·χ̄_c(4)·g̃⁽³⁾·\overline{g̃⁽²⁾}`, with `|g⁽ʲ⁾_c| = |c|` | `rowRootNumber_eq_angularTwist`, `normSq_sexticGaussPow_prod` | Q1, Q2 |
| the wall is the price of completion: the local series on cube-free indices is `R`-free, every `R`-term is a joint sixth power of index and frequency, and the uncompleted correction has no wall on `Re s > ½` | `hasSum_localTerm_uncompleted`, `rowLocalSum_sub_uncompleted`, `exists_uncompletedCorrection_cutoff` | Q4 |

## 6. Questions

| # | Question | State |
|---|---|---|
| Q1 (B175) | For the actual floor bin: is `R₀ < 1`, is there `s > 0` before Cauchy–Schwarz, or do the amplitudes saturate? | reduced, §7 |
| Q2 | Which directions of amplitude space are coherent besides the principal twists? | the principal twists (mode 0) are target-free; short columns are incoherent; only long columns can be coherent |
| Q3 | Is the signed Gram of two rows a completed sum with its own reflection? | yes: a sum over the dual frequencies `h mod u₁u₂` of the products of the two rows' Gauss sums, twisted by the reciprocity factor, at dual length `N(u₁u₂)` over the row scale (Lean) |
| Q4 (B184) | Do the families `ψ₆^k η` close under correction; their common abscissa; a form whose correction converges on `Re s > ½`? | closure `k ↦ 6k + 1` and the continuation of the tower `L`-functions (FCT); the wall is the zero abscissa of `L(·, ψ₆η⁶)` at `6s − 3` (here), and it is real: the continued correction has infinitely many zeros in `7/12 ≤ Re s < 2/3` and no nonvanishing continuation below `7/12` (FCT, `no_nonvanishing_continuation_of_probeCorrection_below_seven_twelfths`); without completion there is no wall, and completion is what the reflection needs; the common abscissa is a half-plane for the tower uniform in the infinity type: open |
| Q5 | What does the frame prove below the wall? | a transport of zeros into the phase `L`-function |
| Q6 | The coherence exponent of normalized Gauss sums of odd order against a column | open; the Kubota–Patterson residue `½ + 1/n₀` [C] |
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
| long columns | the dual side of `L(w, χ_•(u))`, weighted by the root number `μ(u)·(u/|u|)·\overline{g̃₃(u)}·(unimodular factors of bounded conductor)`: a Möbius-signed family of conjugate cubic Gauss sums twisted by an angular character of infinity type one | identity in Lean; size open |

The binding part is the last one. A twist of infinity type one removes the metaplectic main term
(the arguments of cubic Gauss sums are equidistributed [C]), so the long columns are expected to be
incoherent; their bound is a Type I/Type II problem for cubic Gauss sums (theta function at
nonpolar points; the cubic large sieve over `ℤ[ω]`, not in the corpus).

**What the classical tools give [C]/[D].** The cubic large sieve
`Σ_{N(c) ≤ Q} |Σ_{N(n) ≤ N} a_n (n/c)_3|² ≪ (Q + N + (QN)^{2/3})(QN)^ε ‖a‖²` (Heath-Brown) bounds the
Type II part, and the cubic theta function the Type I part, by `U^{5/6+ε}`: the exponent of sums of
cubic Gauss sums over primes. In the budget of FCT the floor-bin row exponent `R₀ = 5/6` is exactly
the point where the floor reaches the free floor `θ = (n − 2)/(n − 1)`, the half-plane `5/6`. So
with classical tools the floor bin moves from `13/15` to the free floor and no further, and a
saving `s > 0` before Cauchy–Schwarz on the floor bin amounts to improving the term `(QN)^{2/3}`
of the cubic large sieve (Heath-Brown's conjecture `Q + N`): the part of B175 below `5/6` is a named
problem.

**Two floors in the order [C]/[A].** At cubic order four readings of `5/6` meet: the bias exponent
`½ + 1/3` of normalized cubic Gauss sums (the residue of the cubic Kubota series), Heath-Brown's
exponent for cubic Gauss sums over primes, the low boundary of the balanced probe, and the free floor
`1 − 1/6` of the squares. The last coincidence is special to `n₀ = 3`: for a probe built on Gauss sums
of odd order `n₀` with row twists of order `n = 2n₀`, the floor of the squares is `1 − 1/(2n₀)`, rising
to the edge, while the coherence exponent of the Gauss sums is `½ + 1/n₀`, falling to the line. Only
estimates that are not squares can use the second; the higher the order, the larger the gap that
coherence theory has to cover.

**Parity of the order.** The sign law gives the Möbius sign at odd order only; the large sieve over
`ℤ[ω]` is sharp at order two (`sieveNorm_sharp`) and open at odd order. The families that carry
the sign are exactly those whose mean squares are not known to cancel completely.

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
| The sextic root numbers are coherent like cubic Gauss sums (bias `U^{5/6}`) | they are cubic Gauss sums twisted by `μ` and an angular character of infinity type one |
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
| summary §2.11 (reciprocity calculus without squares), §2.18 (route MC/JAS) | the same objects with an elementary reflection; the stages `7/8 → 13/15 → 5/6 → 2/3 → 3/5`, of which CRF owns `13/15 → 5/6` and the wall |

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

1. The long columns of the floor bin: Type I and Type II bounds for Möbius-signed conjugate cubic
   Gauss sums twisted by an angular character of infinity type one; the cubic large sieve over `ℤ[ω]`.
2. The long range of the Gram: the products `g_{u₁}^{(1)}(−h) g_{u₂}^{(5)}(−h)` at the nonzero dual
   frequencies, summed with the amplitudes and the reciprocity bicharacter, without the weighted
   Cauchy–Schwarz inequality.
3. The common abscissa of the tower `ψ₆^k η`: a half-plane uniform in the infinity type.
4. Coherence exponents of Gauss-sum families against a column (Q6); the theta coefficients as the
   coherent directions of untwisted families; the order dependence of the two floors.
5. A source outside the cubic probe whose correction converges on `Re s > ½` while keeping a
   reflection: within the cubic probe completion is necessary for the one and excludes the other.
6. The function-field analogue (Q8): over `𝔽_q[T]` there is no angular character of infinite order,
   so the twist that removes the metaplectic main term from the long columns is absent.
