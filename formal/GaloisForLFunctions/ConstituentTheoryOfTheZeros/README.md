# Constituent Theory of the Zeros (CTZ)

Namespace `GaloisForLFunctions.ConstituentTheoryOfTheZeros`; umbrella
`ConstituentTheoryOfTheZeros.lean`; 16 modules. Specification: §2.11 of
[the review-1011 report](../../../docs/reports/review-1011/obstacles-summary.md).

*What the zero set of `ξ` does not contain.*

## 1. Motivation

Over a finite field the zeta function of a curve is `P(q^{−s})` divided by two trivial factors:
a Dirichlet polynomial in one base whose zeros are exactly the zeros of the completed zeta
function. The numerator is an arithmetic object with a finite expansion that shares all its zeros
with the function. It is a **constituent**, and every proof of the Riemann hypothesis for curves
works on it.

Over `ℤ` no object of this kind is known. When positivity, forms and operators are excluded, the
theorems that remain are statements about objects of this kind: they locate no zero of `ξ`, they
say which functions can share zeros with it. CTZ makes this a field. It asks which functions with
an expansion `Σ c(q) q^s` can share zeros with `ξ` — all of them, those in a half-plane, those in
a strip, those in a box, those of a limit — and it proves the answers pointwise, with no sign of a
form and no operator.

Two facts about `ℤ` do the work. The zeros of `ζ` off the critical line have density zero. The
fractional part jumps at every integer.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Scale | `Scale`, `Scale.cpow`, `Scale.log`, `Scale.ofLog` | a positive real `q`; `q^s` |
| Expansion | `expansion c`, `WSummable σ₁ σ₂ c`, `stripWeight` | `F(s) = Σ_q c(q) q^s` with `Σ ‖c(q)‖ max(q^σ₁, q^σ₂) < ∞`: absolutely convergent on the closed strip `σ₁ ≤ Re s ≤ σ₂`; an almost periodic function with an absolutely convergent Bohr–Fourier series |
| Dirichlet series | `dirichletCoeff`, `invNat` | the expansion on the scales `1/n` |
| Exponential polynomial | `expCoeff`, `expSum` | the expansion on the scales `e^{λ_k}`, real frequencies |
| Dirichlet polynomial of length `N` | `polyCoeff v` | coefficients on `1, …, N` |
| Wiener algebra of a strip | `StripWiener σ₁ σ₂`, `pointMass`, `isometryLp` | the expansions on a closed strip, a commutative Banach algebra isometric to `ℓ¹` of the scales |
| Constituent on a set `U` | hypothesis `∀ s ∈ U, F s = 0 → xi s = 0` | `F ≢ 0` whose zeros in `U` are zeros of `ξ`; `U` a half-plane, a strip about the line, a box, a band |
| Series of fractional parts | `InfiniteRankPurityTheory.fractSeries` | `Σ_i b_i {a_i u}`; its Mellin transform at `−s` is `−(ζ(s)/s) Σ b_i a_i^s` |
| Merged weight at a scale | `∑' i, if a i = t then b i else 0` | the weight an expansion carries at the scale `t` |
| Polar part | `InfiniteRankPurityTheory.polarPart`, `polarSeries` | `Σ_p r_p u^p` for simple poles on the line, finitely many or with `Σ ‖r_p‖ < ∞` |
| Carry | `carry`, `carrySeries` | `{x} + {y} − {x + y} ∈ {0, 1}` and `Σ_i b_i κ(a_i u, a_i v)` |
| Zero shifts | `RHTower.zetaZeroShiftSet` | the heights that carry a zero of `ζ` into a disc about a point |
| Splitting, defect in a disc | `encard_xi_zeros_le_of_splitting` | `ξ = E + E^♯` on a disc; the defect is the zeros of `E` in it |
| Turán's constant | `turanConstant N M` | `2eN (6(N+1)(M+2N+2))^N` |

## 3. Language

- **Constituent** on a half-plane, in a strip, in a box: as in §2. **Pure**: its zeros there lie on
  the critical line. **Trivial**: it has no zero there.
- **Wiener class** of a strip: absolutely convergent expansion on the closed strip. **Bounded
  class** of a half-plane: bounded holomorphic with a Dirichlet series far to the right.
- **Bohr strip**: between the abscissa of boundedness and the abscissa of absolute convergence.
- **Recurrence**: an almost period carries a zero to a zero nearby. **Density**: the heights at
  which `ζ` has a zero near a point off the line have density zero.
- **Jump**: the discontinuity of a series of fractional parts at `u₀`, minus the weight of the
  indices with `a_i u₀ ∈ ℤ`.
- **Scale**: the positive real `q` of a term; scales `≤ 1` decay to the right, scales `≥ 1` to the
  left.
- **Good height**: a height at which `F` is bounded below across the strip.
- **Exceptional zero**: a zero of `F` that is not a zero of `ξ`.
- **Sign-free**: no nonnegativity of a form, a kernel, a measure or a coefficient, and no operator,
  enters the proof.

## 4. Mechanisms

1. **Recurrence against density.** A zero of an almost periodic function recurs along a relatively
   dense thick set of heights. Off the line the zero shifts of `ζ` have density zero. So a
   constituent is pure, and remains pure when finitely many zeros are exceptional.
2. **The fractional part carries `ζ`.** `∫_0^∞ {u} u^{−s−1} du = −ζ(s)/s` on `0 < Re s < 1`.
3. **Gluing across a strip of any width.** The affine map `s ↦ 2η s + ½ − η` fixes the critical
   line and carries the unit strip onto the strip of half-width `η`; on the functions it is
   `g(u) ↦ (2η)⁻¹ v^{−(½−η)/2η} g(v^{1/2η})`. Two functions with one transform agree.
4. **The jump law and Möbius inversion at every scale.** Equal series of fractional parts have
   equal jumps; the jumps at the points `1/(kt)` and Möbius inversion over `k` give equal merged
   weights at the scale `t`, for arbitrary positive scales on both sides. Simple poles on the
   line with summable residues add a continuous polar part and change no jump.
5. **Wiener inversion on a strip.** A character of the Wiener algebra of a strip has one real
   exponent in `[σ₁, σ₂]` (an additive function between two multiples of the logarithm is one
   multiple) and a unimodular phase, which Kronecker's theorem approximates by `q ↦ q^{it}` on
   finite sets. So a character is a limit of point evaluations on the strip.
6. **A twist is a limit of translates.** `Σ c(q) ω(q) q^s` is a uniform limit of vertical
   translates of `F`; a zero of the twist would plant a zero of a translate. So zero-free on an
   open strip implies invertible on closed substrips, with zeros allowed on both sides.
7. **The analytic quotient.** `−ζ F'/(sF)` is holomorphic where `ζ` vanishes at the zeros of `F`;
   exceptional zeros are divided out and put back as principal parts; between good heights the
   maximum principle bounds it, and a zero of `F` is at distance at least `μ/(M + 1)` from where
   `‖F‖ ≥ μ`.
8. **The order argument.** If `F' = H F` with `H` holomorphic, `F` has no zero.
9. **Compactness in bounded length.** The unit sphere of the coefficient vectors of length `N` is
   compact, and the limit of a sequence of box constituents is a strip constituent.
10. **Two-term factors.** `m^{−s} − ((m+1)/m)^ρ (m+1)^{−s}` vanishes exactly on
    `ρ + 2πi ℤ / log((m+1)/m)`; the step exceeds `2πm`.
11. **Bohr mean values.** The mean of `F(σ + it) n^{it}` is carried between vertical lines by
    Cauchy's theorem on rectangles; Bessel's inequality; Cauchy–Schwarz over the support.
12. **Schur functions in a disc.** `E'/E` times the Blaschke product of the disc at the zeros of
    `E` is a Schur function; it meets a Blaschke product of degree `κ` in at most `κ` points.
13. **Power sums.** Along a vertical progression a polynomial of `N` terms is a power sum with
    unimodular nodes; Turán's bound needs no separation of the nodes.

## 5. Pillar theorems

**Inherited** (`InfiniteRankPurityTheory`, `RHTower`).

| Theorem | Lean |
|---|---|
| A bounded Dirichlet series whose zeros in `Re s > x` are zeros of `ξ` has them on the line | `re_eq_half_of_zeros_subset_xi` |
| Two functions with one Mellin transform on the two sides of the line agree (unit strip) | `eq_of_mellin_eq_two_sided` |
| The zeros of `ξ` contain no vertical progression | `not_forall_xi_progression` |
| Zero shifts of `ζ` off the line have density zero | `exists_zetaZeroShiftSet_density_zero` |
| A Schur function meets a Blaschke product of degree `κ` in at most `κ` points | `encard_agreements_le` |

**Theorems of CTZ.**

| Theorem | Lean |
|---|---|
| The jump law on a strip of any width with arbitrary scales; equal merged weights at every scale | `tsum_jump_eq_of_strip`, `mergedWeight_eq_of_strip` |
| `ζ` cancels no pole of a two-sided expansion: the expansions on the two sides of the line are one expansion, convergent on the closed strip | `eq_riemannZeta_div_mul_tsum_of_strip` |
| The same up to uncancelled poles on the line with summable residues | `fractSeries_sub_eq_polarSeries_of_strip`, `eq_of_strip_of_summable_poles`; finitely many: `eq_of_strip_of_poles` |
| The Wiener algebra of a strip is a commutative Banach algebra; coefficients are unique | `StripWiener`, `isometryLp`, `eq_zero_of_expansion_eq_zero` |
| Wiener's lemma on a strip | `StripWiener.isUnit_of_le_norm_eval`, `exists_inverse_expansion` |
| A zero-free expansion is invertible on closed substrips; its logarithmic derivative expands | `exists_inverse_expansion_of_zeroFree`, `exists_logDeriv_expansion` |
| **No absolutely convergent expansion is a constituent with a zero, in a strip about the line** | `expansion_ne_zero_of_strip_zeros_subset_xi` |
| — for Dirichlet series, on a half-plane and in a strip | `LSeries_ne_zero_of_zeros_subset_xi`, `LSeries_ne_zero_of_strip_zeros_subset_xi` |
| — for exponential polynomials with real frequencies | `expSum_ne_zero_of_strip_zeros_subset_xi` |
| **If such a function has a zero in the strip, infinitely many of its zeros there are not zeros of `ξ`** | `infinite_zeros_not_xi_zeros_of_expansion`, `…_of_LSeries`, `…_of_expSum` |
| Approximants that converge in the norm of absolute convergence and are constituents in growing boxes have, eventually, no zero near the line | `eventually_LSeries_ne_zero_of_box_zeros_subset_xi` |
| A height `H₀(N)` beyond which no Dirichlet polynomial of length `≤ N` with a zero near the line is a box constituent | `exists_height_forall_dirichletPolynomial` |
| Every band `\|Im s\| ≤ H` has a Dirichlet polynomial with exactly the zeros of `ξ`; its length is unbounded in `H` | `exists_dirichletPolynomial_zeros_eq_xi`, `exists_height_forall_not_zeros_eq_xi` |
| Bohr's inequality over a thin support: bounded on `Re s > x` and `Σ_{supp} n^{−2δ} < ∞` give absolute convergence on `Re s > x + δ` | `lSeriesSummable_of_bounded_of_support` |
| A bounded constituent with a zero has `x + δ ≥ ½` for every such `δ`; in particular `x ≥ 0` and infinitely many primes | `ne_zero_of_bounded_of_support_of_zeros_subset_xi`, `ne_zero_of_bounded_of_zeros_subset_xi`, `ne_zero_of_bounded_of_smooth_of_zeros_subset_xi` |
| The index law in a disc: `‖E'‖ ≤ ‖E‖` on the circle bounds the zeros of `E − E'` inside by those of `E` | `encard_zeros_le_of_norm_le_on_sphere`, `encard_xi_zeros_le_of_splitting` |
| A polynomial of `N` terms is detected on `N` consecutive points of a vertical progression; `N` consecutive zeros force a zero on the progression that is not a zero of `ξ` | `exists_le_norm_expSum_progression`, `expSum_eq_zero_on_progression`, `exists_zero_expSum_not_xi_zero_on_progression` |
| The jump law is the law of the carry | `carrySeries_eq_of_strip`, `fractSeries_eq_of_carrySeries_eq` |

## 6. Questions and answers

| Question (§2.11) | Answer |
|---|---|
| Do the zeros carry an almost periodic constituent (B153)? | No in the Wiener class: no almost periodic function with an absolutely convergent expansion on a strip about the line, with scales of both sizes and real frequencies, has a zero there and all its zeros there among those of `ξ`; infinitely many of its zeros are exceptional. No in the bounded class when `x + δ < ½` (`x < 0`; thin support; finitely many primes). Open in the Bohr strip (§10.1) |
| Up to which height can a Dirichlet polynomial of length `N` share zeros with `ξ`? | Up to a height `H₀(N, ω', ω)` that depends on the length and the strips only. No explicit value: the inverse in the Wiener algebra is not effective (§10.2) |
| Can a sequence of approximants share zeros in growing boxes? | Yes without control of the norm: for every height a Dirichlet polynomial has exactly the zeros of `ξ` below it, and its length tends to infinity. No if the approximants converge in the norm of absolute convergence: eventually they have no zero near the line |
| Which splittings have a defect certified by sizes in a height window? | All of them: the comparison `‖E^♯‖ ≤ ‖E‖` on one circle bounds the zeros of `ξ` in the disc by the zeros of `E` in it; no half-plane and no winding number |
| What replaces the carry-free digit calculus when the carry is a nonzero class? | The carry itself: two expansions of one function have the same carry series, and equal carry series imply equal series of fractional parts. The jump law is the law of the carry |

| Milestone | State |
|---|---|
| M1 polynomials | `InfiniteRankPurityTheory.infinite_zeros_not_xi_zeros`; here in every strip about the line and with detection on progressions |
| M2 series on a half-plane | the Wiener class, in the strong form; the bounded class outside the Bohr strip |
| M3 approximate constituents in boxes | both sides: existence in every band, and loss of the zeros under norm convergence or bounded length |
| M4 a sign-free statement about `ξ` itself | the zero set of `ξ` in a strip about the line contains the zeros of no absolutely convergent expansion that vanishes there, not even up to finitely many points. No mechanism here locates a zero of `ξ` (§10.7) |

## 7. Tools

| Tool (§2.11) | Lean |
|---|---|
| Recurrence against density | `exists_thick_zero_shifts_on_strip`, `isStripAlmostPeriodicOn_expansion`, `re_eq_half_of_expansion_strip_zeros_subset_xi`, `re_eq_half_of_strip_zeros_subset_xi_off_finite` |
| Two-sided constant terms | `eq_of_mellin_eq_on_strip`, `fractSeries_eq_of_strip`, `tsum_jump_eq_of_strip`, `tsum_one_eq_of_tsum_dvd_eq`, `mergedWeight_eq_of_jump`, `eq_of_strip`, `hasSum_mellin_topPart_polarSeries`, `tsum_jump_eq_of_strip_of_summable_poles`, `eq_of_strip_of_summable_poles`, `eq_of_strip_of_poles` |
| Inverse expansions | `Scale.exists_eq_mul_log`, `Scale.exists_height_approx`, `exists_height_expansion_approx`, `StripWiener.exists_exponent_phase`, `exists_inverse_expansion_of_zeroFree`, `exists_logDeriv_expansion`, `deriv_expansion` |
| The analytic quotient | `exists_good_heights`, `exists_quotient_sub_principalParts`, `div_le_norm_sub_of_zero`, `ne_zero_of_deriv_eq_mul`, `logDeriv_expansion_eq_off_finset` |
| The index law | `encard_agreements_unitDisc_le`, `encard_zeros_le_of_norm_le_on_sphere`, `ne_zero_of_norm_le_on_sphere` |
| Turán's power sums | `HTGeometry.exists_norm_weightedPowerSum_ge`; `expSum_progression`, `exists_le_norm_expSum_progression` |
| The digit calculus | `carry_cocycle`, `carry_natCast_div`, `carrySeries_eq`, `eq_zero_of_additive_of_bound` |
| Bohr's theory of bounded series | `bohrCoefficient_line_of_bounded`, `sum_norm_sq_le_of_bounded`, `norm_coeff_le_of_bounded`, `eq_LSeries_of_summable_right` |
| Prescribed zeros in a band | `LSeries_twoTermCoeff_eq_zero_iff`, `exists_dirichletPolynomial_zeros_eq` |

## 8. Calibration

| Model | Reading |
|---|---|
| Curve over `𝔽_q` (classical) | `P(q^{−s})` is an exact pure constituent of its own completed zeta function. The counting function of `𝔽_q[T]` jumps only at the powers of `q`; the theorems here use the jumps of the fractional part at every integer |
| `1 − 2^{½−s}` | zeros `½ + 2πik/log 2`, a vertical progression on the line: not a constituent in any strip (`expSum_ne_zero_of_strip_zeros_subset_xi`, `not_forall_xi_progression`) |
| Two-term products | `exists_dirichletPolynomial_zeros_eq_xi`: sharing zeros in a box costs length and nothing else |
| Finitely many primes | boundedness is absolute convergence (`lSeriesSummable_of_bounded_of_smooth`): the Bohr strip is empty |
| Non-tempered pair `ξ(s + a) ξ(s − a)` | has every structure of `ξ` and its zeros off the line; the theorems here do not hold for it, because they use the density of the zeros of `ζ` off the line and the fractional part of `ℤ` |

## 9. Traps

| Trap | Truth |
|---|---|
| The expansion left of the line must have scales `≥ 1` | Möbius inversion works at every scale; any absolutely convergent expansion on a left line will do |
| A series has no highest frequency, so no expansion of `F'/F` left of the line | Wiener's lemma on a strip gives a two-sided expansion over the group of scales |
| Wiener's lemma needs a lower bound on a half-plane | a lower bound on the strip suffices; zeros on both sides are allowed |
| Sharing zeros in a box is restrictive | not without a bound on the length or on the norm (`exists_dirichletPolynomial_zeros_eq_xi`) |
| Positions of zeros can exclude a constituent on the line | the gaps of the zeros of `ξ` tend to zero (classical): every pattern on the line is approximated by zeros; the exclusion is arithmetic, by the jump law |
| Finitely many exceptional zeros can rescue a constituent | they are poles with a continuous polar part; the jump law does not see them |
| Purity of a constituent says where zeros of `ξ` are | it says where the zeros of the constituent are |
| A bounded Dirichlet series is close to an absolutely convergent one | its coefficients are square summable only; the sums of the left expansion over the progressions of scales converge absolutely exactly for exponents `> ½` |

## 10. Open research topics

1. **The Bohr strip (B153, the open case).** `F` bounded on `Re s > x` with `0 ≤ x < ½`, support of
   exponent at least `1 − 2x`, series absolutely convergent at no point left of the line. The
   expansions of `F'/F` near the line have square summable coefficients, and the jump law needs
   absolutely convergent sums over the progressions `{kt}` of scales. Davenport's classical
   identity `Σ μ(n) n^{−1} {nu} = −sin(2πu)/π` (not in Lean) is a conditionally convergent series
   of fractional parts with weight `1` at the scale `1` and no jump: for square summable weights
   the jumps do not determine the merged weights. The boundedness of `F'/F` must enter beyond its
   coefficients.
2. **Effective heights.** An explicit `H₀(N)`: an effective inverse in the Wiener algebra of a
   strip, Turán's bound for the good heights, and an effective density of the zero shifts.
3. **Natural approximants.** Which families of growing length (sections of `ζ`, Riemann–Siegel
   sums) can be box constituents, and with which growth of the norm.
4. **Natural splittings.** The defect in a window of the splittings of `ξ` that arise from the
   approximate functional equation.
5. **Other `L`-functions.** The jump law for fractional parts twisted by a character.
6. **Summable exceptional zeros.** The jump law holds with countably many poles of summable
   residues. For a pure expansion `F` with a zero the residues of `−ζ F'/(sF)` are
   `m_ρ ζ(ρ)/ρ` at the zeros `ρ` of `F`; whether `Σ_ρ m_ρ ‖ζ(ρ)/ρ‖` must diverge is the statement
   this suggests. The analytic quotient with infinitely many principal parts is not in Lean.
7. **A sign-free mechanism that acts on `ξ` itself.** None is known. Every mechanism of this
   programme acts on a function that shares zeros with `ξ`.

## 11. Context

| Neighbour | Interface |
|---|---|
| InfiniteRankPurityTheory | series of fractional parts, the gluing theorem on the unit strip, polar parts, the analytic quotient, the half-plane index law; CTZ carries them to strips of any width, arbitrary scales, infinite series and windows, and contains its theorem on exponential polynomials strip by strip |
| HTGeometry | strip almost periodicity, Bohr mean values, Kronecker's theorem, uniqueness of exponential series, sphere domination, Turán's power sums |
| RHTower | `ξ`, the Mellin transform of the fractional part, zero shifts and their density, finiteness of zeros in bands |
| ArithmeticOrientationTheory | the Wiener algebra of a half-plane; CTZ needs a strip and a group of scales |
| SignFreePurityMechanisms | the priced producers and the digit calculus in characteristic `p`; CTZ supplies the carry over `ℤ` |
| AbsoluteGeometryOfSpecZ | the carry as a cocycle that is not a coboundary |

## 12. Success criteria and contributions

CTZ succeeds when each question of §6 has a theorem-level answer: a theorem, or a sharp boundary
with the exact statement that remains. That is the state for the five questions; the remaining
statement is §10.1.

A **contribution** is unconditional and pointwise; uses no sign of a form and no operator; is
consistent with curve zeta functions, whose constituents are themselves; fails for the
non-tempered pair; states which class of functions it excludes or constructs; and moves one of
the boundaries of §6 or §10. A restatement of a pillar theorem, a finite case of an infinite
question, or a sharper constant is not a contribution.

## 13. Big picture

The constraint "no positivity, no operator" leaves pointwise mechanisms, and they act on
constituents. Inside the Wiener class the answer is complete: the zero set of `ξ` near the line
contains the zeros of no almost periodic function with an absolutely convergent expansion, not
even up to finitely many points; boxes alone constrain nothing; length and norm do. What remains
is one strip of width at most `½`: bounded series that converge absolutely nowhere left of the
line. There the fractional part still jumps at every integer, but the weights are only square
summable, and the main conjecture — no bounded almost periodic function has a zero and all its
zeros among those of `ξ` — is open exactly there.
