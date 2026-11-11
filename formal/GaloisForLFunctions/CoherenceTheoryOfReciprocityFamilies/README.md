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
in Lean: every Cauchy–Schwarz row sieve, every reflection–summation word, every unitary
re-expansion stops at the twist exponent `(n − 2)/(n − 1)` (half-plane `5/6` at `n = 6`), and
matched phases saturate the signed Gram of the rows. What none of the 136 programme folders contains
is **an estimate of a family that is not a square**: an evaluation of the phases between the
amplitudes of a family of rows and the columns of a reciprocity kernel.

CRF is the theory of those phases. It asks when arithmetic amplitudes **align** with a column
(coherence; saturation of the Gram form) and when they **cancel** (incoherence), it evaluates
signed Gram forms exactly instead of bounding them, and it treats the correction of a family as a
second family of the same theory, so that the families that correct one another form a tower.

## 2. Objects

| Object | Meaning |
|---|---|
| reciprocity family | rows `u` (sixth-power-free elements of `ℤ[ω]` prime to `6`), each with a residue character `χ_u`; the kernel of the family is a pairing `Φ(u, m)` built from `χ_u(m)` and additive characters |
| column shell | the averaging variable `m` in a box of size `M`, with weights `b(m)` (the Möbius weights in the probe) |
| amplitude | the coefficient `α(u)` of a row: in the probe, a value built from cubic and sextic Gauss sums of the reflected rows |
| bilinear floor sum | `Σ_u α(u) Σ_m b(m) Φ(u, m)` |
| signed Gram | `Q_M(α) = Σ_m ‖Σ_u α(u) Φ(u, m)‖² = diag + Re Σ_{u₁≠u₂} α(u₁) conj α(u₂) G_M(u₁, u₂)`, with `G_M(u₁, u₂) = Σ_m Φ(u₁, m) conj Φ(u₂, m)` |
| coherence of `α` with a column `m₀` | `‖Σ_u α(u) Φ(u, m₀)‖`; its exponent in the size of the family |
| coherent direction | an amplitude vector whose signed Gram is of the order of `‖α‖₁²` (the trivial bound): saturation |
| principal subfamily | the rows that are `n`-th powers (the principal twists); always coherent; it contains the target |
| exceptional frequencies | pairs of rows whose quotient is an `n`-th power: the off-diagonal terms that add without cancellation |
| row exponent `R₀` | the exponent of the floor-bin sum relative to one row: `½` is square-root cancellation, `1` the triangle inequality |
| saving before Cauchy–Schwarz `s` | the gain of a bilinear estimate over its squared form, in the twist exponent |
| correction `H_η` | the Euler product by which the principal row of the probe differs from `L(s, η)⁻¹` |
| phase `L`-function | `L_A(w) = Π_P (1 − A_P N(P)^{−w})⁻¹` for unimodular phases `A_P`; for the probe `A_P = κ_P⁶`, `κ_P = (π̄/|π|) η(π)` |
| tower | the targets `ψ₆^k η`, `ψ₆(π) = (π̄/|π|)⁶`, whose corrections contain one another |
| wall of the frame | the abscissa left of which the correction of the target has zeros |

## 3. Language

- **Coherent / incoherent.** A family is coherent along `α` if its signed Gram is of the size of
  the triangle bound; incoherent if the off-diagonal cancels the diagonal to a positive power.
- **Saturation.** `R₀ = 1`: the amplitudes align with one column.
- **Evaluation before Cauchy–Schwarz.** A statement about `Q_M(α)` or the bilinear sum itself,
  not about `‖α‖² ‖Φ‖²`.
- **Reflection of a pair.** Poisson summation in the column of the product of two rows, followed by
  reciprocity: the off-diagonal entry becomes a completed sum with its own dual length.
- **Correction, tower, wall.** The correction is the factor between the principal row and the
  reciprocal of the target; if it is an `L`-function of a second family, the families form a tower;
  the wall is where the frame stops reading the target alone.
- **The twist exponent** `θ`: the common ruler. The half-plane is `½ + (1 − 1/n)θ/2`; the
  thresholds `s = 1/12, 1/6, 1/3` (at `n = 6`) are `¾`, the wall `2/3`, and the line.

## 4. Mechanisms

**Built (FCT, MMD).**
1. *The frame.* Two estimates for one sum compared with the signal of `exp((s − c)²) H_η(s)/L(s, η)`
   give the half-plane, whenever `H_η` is holomorphic and nonvanishing right of the boundary.
2. *The source identity.* The cube of the composite cubic Gauss sum is the ideal Möbius value times
   a phase; at every odd order `n > 2` the `n`-th power of a Gauss sum is `−card F` modulo `(μ − 1)²`,
   at even order the sign is the parity `χ(−1)`.
3. *The signed Gram identity.* Interchanging the row and column sums before absolute values bounds
   the bilinear sum by the column energy times the exact signed Gram form of the rows.
4. *Saturation.* Matched phases `α(u) = A₀ conj Φ(u, m₀)` give `Q_M(α) ≥ |B₀|² A₀²`.
5. *The separation of a pair.* With the two Möbius signs, the mixed Gauss factor of two disjoint
   prime sets is a quadratic symbol of their residues modulo `4` times one column factor per set: the
   pair is a sum over residue classes of separated pairs.
6. *The budget.* A calculus of exponents, not of sums: the vertex `7/8`, the floors `13/15` and
   `5/6`, the curve in `R₀`, the escape law `1 − 1/n − s`.
7. *The correction.* Its local factor is
   `(1 − Q⁻²)(1 − Q⁻¹(A Q^{3−6s} − η Q^{−s})/(1 − η Q^{−s}))/(1 − A Q^{3−6s})`; it is within
   `14 Q^{−e}` of one for `e ≤ min(6σ − 3, 1 + σ, 2)`.

**To build here.**
8. *The wall as an `L`-function.* The factor `(1 − A Q^{3−6s})⁻¹` is the local factor of a phase
   `L`-function at `w = 6s − 3`; the rest converges on `Re s > ½`.
9. *Transport below the wall.* With `H_η` only holomorphic, the frame proves that the zeros of
   `L(s, η)` right of the boundary are zeros of `H_η`.
10. *Coherence by reciprocity.* Poisson in the column of a pair of rows and reciprocity for products
    of residue symbols turn the signed Gram into a form in dual sums of Gauss sums over the modulus;
    their size is the coherence exponent of the family.

## 5. Pillar theorems

**From FCT and MMD (the base of the field).**

| Theorem | Lean |
|---|---|
| frame with reciprocal kernels and corrections | `zetaZeroAbscissa_le_of_two_reciprocal_estimates`, `exists_cutoff_zetaZeroAbscissa_le_of_probe_estimates` |
| pole-cleared kernels give a false premise for a nonprincipal character | `heckePoleCleared_one_of_ne_one` |
| the cube identity; the sign law at odd and even order | `compositeCubicGauss_cube`; `exists_gaussSum_pow_orderOf_eq_of_odd`, `…_of_even` |
| signed Gram identity and bound; saturation | `sum_norm_sq_eq_diag_add_offDiag`, `norm_sq_bilinearFloorSum_le_mul_signedGram`, `exists_matched_phase_saturation` |
| the floor-bin curve in `R₀`; the phase transition at `½ + 1/n` | `signedGramSymmetricTheta`, `signedGramBrokenTheta`, `endpointExponentOrder_signedGram_pos_of_lt` |
| every Cauchy–Schwarz row sieve, word and unitary re-expansion: `θ ≥ (n − 2)/(n − 1)`; escape needs `s > 0` | `free_floor_le_probeThetaHybridFree`, `escape_below_free_floor_bound` |
| the law of a twist family | `principalTwistGenericSet_gaussianKernel`, `positiveSquarefreeTwistGenericSet_eq` |
| the correction close to one right of `2/3` (principal) and `7/8` (probe) | `exists_principalCorrection_cutoff`, `exists_probeCorrection_cutoff` |
| separation of the pair of the second Poisson reflection | `secondActualPair_eq_separated` |
| the quadratic large sieve over `ℤ[ω]` at exponent one | `sieveNorm_sharp` |

**Of this programme.** Filled as the theorems are proved (§6 lists what they answer).

## 6. Questions

| # | Question | Status |
|---|---|---|
| Q1 (B175) | For the actual amplitudes and Möbius columns of the probe: is `R₀ < 1`? is there `s > 0` before Cauchy–Schwarz? or do the amplitudes saturate along a column? | open |
| Q2 | Which directions of amplitude space are coherent for the sextic kernel besides the principal twists? | open |
| Q3 | Is the signed Gram of two rows a completed sum with its own reflection, and what is its dual length? | open |
| Q4 (B184) | Do the families `ψ₆^k η` close under correction? What is their common abscissa? Is there a form of the probe whose correction converges on `Re s > ½`? | open |
| Q5 | Below the wall, what does the frame prove: a transport of zeros, and between which `L`-functions? | open |
| Q6 | What is the coherence exponent of normalized Gauss sums of odd order `n₀` against a column, and is it the residue exponent `½ + 1/n₀` of the theta function of the `n₀`-fold cover? | open |
| Q7 | Where the mean square is followed by Cauchy–Schwarz the boundary stays above `½`: which reciprocity families have cancellation inside the mean square? | open |
| Q8 | What is the analogue of each statement over `𝔽_q[T]`, where Weil's bound replaces the large sieve? | open |

**Expected answers [A].** Two outcomes decide the field. *Incoherence:* off the principal twists
the actual amplitudes cancel, `R₀ < 1` and `s > 0`; then the probe crosses `13/15` and `5/6`, and
the thresholds `1/12, 1/6, 1/3` measure the rest. *Coherence through the theta function:* the
coherent directions of a Gauss-sum family are spanned by the Fourier coefficients of the residue of
the metaplectic Eisenstein series, the coherence exponent of normalized cubic Gauss sums is
`½ + 1/3 = 5/6` (Patterson's bias [C]); then the floor `5/6` of the squares is not a loss of the
method but the size of the coherent part, and the producer ends at `5/6` unless the coherent part
cancels against the Möbius columns.

## 7. Tools to develop

- Poisson summation in the column of a pair of rows; the Chinese remainder theorem for products of
  residue symbols and the reciprocity phase as a bicharacter.
- Completed sums in two row variables; reflection of a pair.
- Exact evaluation of local coherence: sums of Gauss sums against a column at one prime.
- The phase `L`-functions of unimodular Euler data and their abscissae; Hecke characters of
  infinite order of `ℚ(ω)`.
- The budget calculus with a signed term: a coherence exponent placed on the scale before work.

## 8. Traps

| Trap | Truth |
|---|---|
| A mean square over twists that contains the principal twists is an input | it is the half-plane itself (`principalTwistGenericSet_gaussianKernel`) |
| Positive weights in place of `μ` | not generic below `n/(n − 1)` (`positiveSquarefreeTwistGenericSet_eq`) |
| A cleverer row sieve, word, unitary change of basis or more row variables crosses `5/6` | every one is a square: `θ ≥ (n − 2)/(n − 1)` |
| Reflected rows through the same twists | return the zero `β`: circular |
| `7/8` is a floor of the probe | it is a vertex of three estimates; the floors are `13/15` and `5/6` |
| The order `n` of the budget is the order of the Gauss-sum power | it is the order of the row twists (principal frequencies `a⁶`); the source is always the cube identity |
| Dividing the correction out removes the wall | it moves to the direct side: the trivial bound has exponent `max(a₁, 2/3)` |
| The pole-cleared frame `(s − 1)L(s, ψ)` | a false premise as soon as the family has a nonprincipal character |
| Coherence is a property of the kernel | it is a property of the pair (kernel, amplitudes): the same kernel is saturated by matched phases and orthogonal on a full character group |
| Even order carries the Möbius sign | at even order the sign of a Gauss-sum power is the parity `χ(−1)` |

## 9. Position in the corpus

| Programme | Relation |
|---|---|
| FamilyContinuationTheory | the frame, the budget, the corrections and the Poisson arithmetic of the probe: CRF is its signed layer |
| MetaplecticMobiusDescent | the cube identity, cubic reciprocity, the cubic Eisenstein series and its residue: the global object whose coefficients are the coherent directions |
| SelectiveArithmetic | the ladder and the rungs that read the half-plane |
| FloorFreeArithmetic | the floor census (§4 of the summary): every large-sieve budget has a floor; CRF is the one place where a family estimate may be not a square |
| the summary's §2.11 field (reciprocity calculus without squares) | the same objects with the reflection required elementary |
| the summary's §2.18 programme (route MC/JAS) | the stages `7/8 → 13/15 → 5/6 → 2/3 → 3/5`; CRF owns stages 2 and 3 |

## 10. Success criteria

The field is developed when:
1. B175 has an answer for the actual coefficients: an estimate `R₀ < 1` or `s > 0`, or a theorem that
   they saturate along named directions.
2. The coherent directions of the sextic kernel are classified.
3. The signed Gram of a pair of rows is evaluated as a completed sum with its reflection.
4. The tower of corrections is closed or shown not to close, with its common abscissa or the
   transport statement that replaces it below the wall.
5. Each statement is calibrated on matched phases, on `μ²` and on even order.

## 11. What a contribution must be

- H1 It evaluates before Cauchy–Schwarz.
- H2 It saturates on matched phases and on the principal twists.
- H3 It fails for `μ²` and for even order, where the sign is the parity of the character.
- H4 Its exponents are stated in the twist exponent, against the thresholds `1/12`, `1/6`, `1/3`.
- H5 It treats the correction of a family as a member of the theory, not as a constant.
- H6 Unconditional in Lean, with no hypothesis that hides an estimate; an implication counts only
  when the implication is the content (a frame, a transport law), and its premise is named as open.
- H7 It moves a limit of §1 or answers a question of §6; a restatement of a corpus bound does not.

## 12. Open research topics

1. The phase `L`-function of the probe and its zeros in `½ < Re s < 2/3`.
2. The frame for targets of infinite order; the first member `ψ₆ η⁶` of the tower.
3. Exact local coherence of Gauss-sum amplitudes at one prime; Gauss periods as the local coherent
   directions.
4. The pair of rows after Poisson in the column, without the weighted Cauchy–Schwarz inequality.
5. The theta coefficients as coherent directions; the bias exponent against the free floor.
6. A source whose correction converges on `Re s > ½`: the four conditions of §2.9 (odd order;
   the target with multiplicity; a reflection; a correction convergent on the half-plane).
