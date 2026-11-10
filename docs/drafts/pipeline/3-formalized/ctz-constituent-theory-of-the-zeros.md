# Constituent theory of the zeros (CTZ)

- **ID:** CTZ
- **Stage:** 3-formalized
- **Type:** programme; THEOREM (Lean) for every section P1–P13
- **Source:** `docs/reports/review-1011/obstacles-summary.md` §2.11 (questions), §2.6 (B153), §1.5
- **Statement:** which functions with an expansion `Σ c(q) q^s` over positive real scales can share
  zeros with `ξ`: on a half-plane, in a strip, in a box, in the limit.

## Goal
Answer the five questions of §2.11 and reach its milestones M1–M4. Every statement is pointwise
and sign-free. Nothing here locates a zero of `ξ`.

## Lean
Folder `formal/GaloisForLFunctions/ConstituentTheoryOfTheZeros/`, umbrella
`ConstituentTheoryOfTheZeros.lean`, README in the folder. Every module checks with
`lake --old env lean` without output.

| Module | Proof | Declarations |
|---|---|---|
| TheJumpLawHoldsOnEveryStripAboutTheLine | P1, P2 | `rescale`, `mellin_rescale`, `eq_of_mellin_eq_on_strip`, `fractSeries_eq_of_strip`, `tsum_jump_eq_of_strip`, `tsum_one_eq_of_tsum_dvd_eq`, `mergedWeight_eq_of_jump`, `mergedWeight_eq_of_strip`, `eq_of_strip`, `eq_riemannZeta_div_mul_tsum_of_strip` |
| TheJumpLawOnAStripSurvivesFinitelyManyPoles | P2′ | `fractSeries_sub_eq_polarPart_of_strip`, `tsum_jump_eq_of_strip_of_poles`, `mergedWeight_eq_of_strip_of_poles`, `eq_of_strip_of_poles` |
| TheWienerAlgebraOfAStrip | P3 (a), (b) | `Scale`, `stripWeight`, `WSummable`, `expansion`, `eq_zero_of_expansion_eq_zero`, `convolve`, `expansion_convolve`, `wsummable_convolve`, `StripWiener`, `isometryLp`, `pointMass`, `hasSum_pointMass` |
| WienersLemmaOnAStrip | P3 (c)–(e) | `Scale.exists_eq_mul_log`, `Scale.norm_sub_zpow_le`, `Scale.norm_sub_prod_le`, `Scale.exists_height_approx`, `exists_height_expansion_approx`, `StripWiener.exists_exponent_phase`, `exists_apply_eq_expansion_twist`, `isUnit_of_le_norm_eval`, `exists_inverse_expansion` |
| TheLogarithmicDerivativeExpandsInAZeroFreeStrip | P3′ | `deriv_expansion`, `WSummable.log_mul`, `StripWiener.isUnit_ofCoeff_of_zeroFree`, `exists_inverse_expansion_of_zeroFree`, `exists_logDeriv_expansion` |
| DirichletSeriesAreExpansionsOnTheScalesOneOverN | — | `dirichletCoeff`, `wsummable_dirichletCoeff`, `expansion_dirichletCoeff` |
| NoAbsolutelyConvergentDirichletSeriesIsAConstituent | P4 | `exists_good_heights`, `exists_quotient_sub_principalParts`, `div_le_norm_sub_of_zero`, `ne_zero_of_deriv_eq_mul`, `logDeriv_expansion_eq_off_finset`, `expansion_ne_zero_of_zeros_cancelled_off_finset`, `expansion_ne_zero_of_zeros_cancelled`, `re_eq_half_of_strip_zeros_subset_xi`, `LSeries_ne_zero_of_strip_zeros_subset_xi`, `LSeries_ne_zero_of_zeros_subset_xi` |
| NoAbsolutelyConvergentExpansionIsAConstituentInAStrip | P4 | `isStripAlmostPeriodicOn_expansion`, `exists_thick_zero_shifts_on_strip`, `re_eq_half_of_expansion_strip_zeros_subset_xi`, `expansion_ne_zero_of_strip_zeros_subset_xi`, `expCoeff`, `expansion_expCoeff`, `expSum_ne_zero_of_strip_zeros_subset_xi` |
| InfinitelyManyZerosOfAnExpansionAreNotZerosOfXi | P5 | `re_eq_half_of_strip_zeros_subset_xi_off_finite`, `infinite_zeros_not_xi_zeros_of_expansion`, `infinite_zeros_not_xi_zeros_of_LSeries`, `infinite_zeros_not_xi_zeros_of_expSum` |
| ApproximantsThatShareZerosInGrowingBoxesLoseTheirZeros | P6 | `exists_le_norm_LSeries_of_strip_zeroFree`, `xi_eq_zero_of_limit_of_box_zeros`, `eventually_LSeries_ne_zero_of_box_zeros_subset_xi`, `polyCoeff`, `exists_height_forall_dirichletPolynomial` |
| EveryBoxHasADirichletPolynomialWithExactlyTheZerosOfXi | P7 | `twoTermCoeff`, `LSeries_twoTermCoeff_eq_zero_iff`, `eq_of_exp_stepLog_eq_one`, `exists_dirichletPolynomial_zeros_eq`, `exists_dirichletPolynomial_zeros_eq_xi`, `exists_height_forall_not_zeros_eq_xi` |
| ABoundedConstituentLivesInTheBohrStrip | P8 | `bohrCoefficient_line_of_bounded`, `sum_norm_sq_le_of_bounded`, `lSeriesSummable_of_bounded_of_support`, `lSeriesSummable_of_bounded`, `eq_LSeries_of_summable_right`, `ne_zero_of_bounded_of_support_of_zeros_subset_xi`, `ne_zero_of_bounded_of_zeros_subset_xi`, `norm_coeff_le_of_bounded`, `lSeriesSummable_of_bounded_of_smooth`, `ne_zero_of_bounded_of_smooth_of_zeros_subset_xi` |
| SizesOnACircleCertifyTheDefectInside | P9 | `isBlaschke_disc`, `encard_agreements_unitDisc_le`, `encard_zeros_le_of_norm_le_on_sphere`, `ne_zero_of_norm_le_on_sphere`, `encard_xi_zeros_le_of_splitting` |
| ConsecutivePointsOfAProgressionDetectAPolynomial | P10 | `turanConstant`, `expSum_progression`, `exists_le_norm_expSum_progression`, `expSum_eq_zero_on_progression`, `exists_zero_expSum_not_xi_zero_on_progression`, `xi_eq_zero_on_progression_of_consecutive` |
| TheJumpLawIsTheLawOfTheCarry | P11 | `carry`, `carry_cocycle`, `carry_natCast_div`, `carrySeries_eq`, `carrySeries_eq_of_strip`, `eq_zero_of_additive_of_bound`, `fractSeries_eq_of_carrySeries_eq` |

## Paper proofs

Notation: `{u}` fractional part; `K(s) = −ζ(s)/s = ∫_0^∞ {u} u^{−s−1} du` for `0 < Re s < 1`;
`g_{b,a}(u) = Σ_i b_i {a_i u}` (`fractSeries`); scales are positive reals.

### P1. The jump law on a strip of any width, any scales
Let `0 < η ≤ ½`, families `(b_i, a_i)`, `(c_j, q_j)` with positive scales,
`Σ ‖b_i‖ a_i^σ < ∞` for `σ ∈ (½, ½+η]`, `Σ ‖c_j‖ q_j^σ < ∞` for `σ ∈ [½−η, ½)`. Let `Φ` be
holomorphic on `|Re s − ½| < η`, bounded on `|Re s − ½| ≤ η/2`, with `Φ = K Σ b_i a_i^s` right of
the line and `Φ = K Σ c_j q_j^s` left of it. Then `g_{b,a} = g_{c,q}` on `(0, ∞)` and for every
`u₀ > 0`: `Σ_{a_i u₀ ∈ ℤ} b_i = Σ_{q_j u₀ ∈ ℤ} c_j`.

*Proof.* Put `κ = 2η`, `c₀ = ½ − η`, `g̃(v) = κ^{−1} v^{−c₀/κ} g(v^{1/κ})`. Then
`M[g̃](−s') = M[g](−(κ s' + c₀))`, a bound `O(u^σ)` becomes `O(v^{(σ − c₀)/κ})`, and
`σ ↦ (σ − c₀)/κ` maps `(½, ½+η]` onto `(½, 1]` and `[½−η, ½)` onto `[0, ½)`. The gluing theorem on
the unit strip (`eq_of_mellin_eq_two_sided`) applies to the rescaled functions and
`Φ(κ s' + c₀)`: the two series agree at the points of continuity `≠ 1` of their difference. Both
are right continuous and the exceptional set is countable, so they agree everywhere; the left
limits agree, and the jump of `g_{b,a}` at `u₀` is `−Σ_{a_i u₀ ∈ ℤ} b_i`. ∎

### P2. Merged weights agree; one expansion across the line
Under P1, for every `t > 0`: `Σ_{a_i = t} b_i = Σ_{q_j = t} c_j`. If both families are indexed by
one set with injective scales, `b = c`, the expansion converges absolutely on the closed strip and
`Φ = K Σ b_i a_i^s` on the open strip. The index set may be uncountable.

*Proof.* Fix `t`. Restrict both families to the indices whose scale is `t` times a natural number,
with the scales divided by `t`; the restricted families are summable and summable against
`scale^{1/4}`. The jump law at `u₀ = 1/(kt)` says that the total weight on the scales divisible by
`k` is the same on both sides, for every `k ≥ 1`. Möbius inversion on the disjoint union
(`tsum_one_eq_of_tsum_dvd_eq`) gives equal weights at the scale `1`. For injective scales the
merged weight is the coefficient. Summability on the closed strip follows from
`t^σ ≤ t^{σ₁} + t^{σ₂}`, and the identity theorem carries `Φ = K H` from the right half to the
strip. An absolutely summable family has countable support; the general case is the case of the
union of the two supports. ∎

### P2′. Finitely many poles on the line
Let `Φ` be as in P1 except that `Φ = K Σ b_i a_i^s − Σ_{p ∈ P} r_p/(s − p)` on both sides, `P` a
finite set on the line. Then `g_{b,a} − g_{c,q} = Σ_p r_p u^p`, the jumps agree, the merged
weights agree, and `b = c` for injective common scales.

*Proof.* `u^p` cut off above `1` has the transform `1/(s − p)` right of the line and, cut off
below `1`, the transform `−1/(s − p)` left of it. The corrected functions
`g_{b,a} − (u^p)_{>1}`-sum and `g_{c,q} + (u^p)_{≤1}`-sum have one transform, with bounds
`O(u^σ)` on the two sides because `|u^p| = u^{½}`; P1's gluing applies. The polar part is
continuous, so jumps and left limits are unchanged. ∎

### P3. Wiener's lemma on a strip
For `σ₁ ≤ σ₂` let `𝒲[σ₁, σ₂]` be the functions `f(s) = Σ_q c(q) q^s` on the closed strip with
`‖f‖ = Σ ‖c(q)‖ w(q) < ∞`, `w(q) = max(q^{σ₁}, q^{σ₂})`, `q` over the positive reals.

(a) *Uniqueness.* The support of `c` is countable; on the line `Re s = σ₁` the function is an
absolutely convergent series of exponentials with distinct frequencies `log q`, and the Bohr mean
recovers each coefficient.

(b) *Banach algebra.* `w(qr) ≤ w(q) w(r)`; the product is the convolution over the group; the
coefficient map is an isometry onto `ℓ¹`.

(c) *Exponent of a character.* `χ(q) = φ(δ_q)` is a homomorphism with `‖χ(q)‖ ≤ w(q)`, so
`f = log ‖χ‖` is additive with `σ₁ log q ≤ f(q) ≤ σ₂ log q` for `q ≥ 1`. Put `σ = f(2)/log 2`.
For `q` and `b ≥ 1` the element `q^b 2^{−a}`, `a = ⌊b log q/log 2⌋`, has logarithm in
`[0, log 2)`, and `f` of it is `b (f(q) − σ log q)` plus a bounded term: `f(q) = σ log q`.

(d) *Phase of a character.* `ω = χ/|χ|` is a unimodular homomorphism. For a finite set `T` of
scales choose a rationally independent subfamily of `{log q : q ∈ T}` with the same rational
span, a common denominator `D` of the coordinates, and the scales `β_x = e^{x/D}`. Each `q ∈ T`
is a product of integer powers of the `β_x`; Kronecker's theorem (`kronecker_approx`) gives `t`
with `β_x^{it}` within `δ` of `ω(β_x)`, and the distance of two unimodular homomorphisms is
subadditive under products and powers.

(e) *Wiener's lemma.* So `φ(f)` is a limit of values of `f` on the strip; if `‖f‖ ≥ δ` on the
strip, no character vanishes on `f`, and `f` is a unit (Gelfand). ∎

### P3′. Zero-free on an open strip
If `Σ c(q) q^s` converges absolutely on `τ₁ ≤ Re s ≤ τ₂` and has no zero in the open strip, it is
a unit of `𝒲[σ₁, σ₂]` for `τ₁ < σ₁ ≤ σ₂ < τ₂`, and `F'/F = Σ g(q) q^s` on the open strip,
absolutely on closed substrips.

*Proof.* A character is the value at a real `σ` of the twist `Σ c(q) ω(q) q^s`, a uniform limit
on the closed strip of translates of `F` (Kronecker on a finite set carrying all but `ε` of the
weighted coefficients). A zero of the twist is isolated (uniqueness of coefficients), and a
translate within a third of the minimum on a small circle has a zero in the disc (sphere
domination), against zero-freeness. One family represents `1/F` on every closed substrip (the
inverses agree on a common line), and `F'` has the coefficients `c(q) log q`. ∎

### P4. No absolutely convergent expansion is a constituent with a zero
Let `Σ ‖c(q)‖ max(q^{½−ω}, q^{½+ω}) < ∞`, `0 < ω ≤ ½`, `F = Σ c(q) q^s ≢ 0`. If every zero of `F`
in `|Re s − ½| < ω` is a zero of `ξ`, `F` has no zero there. For Dirichlet series also on a
half-plane `Re s > x` of absolute convergence.

*Proof.* `F` is almost periodic on closed substrips (uniform limit of its finite parts). A zero
off the line recurs on a relatively dense thick set of heights, inside the strip; these are zero
shifts of `ζ`, which have density zero: the zeros lie on the line. Left and right of the line
`F'/F` has absolutely convergent expansions `g_L`, `g_R` (P3′). `Φ = K F'/F` is holomorphic on the
strip (`ζ` vanishes at the zeros of `F`) and bounded near the line: on two vertical lines by the
norms of `g_L`, `g_R`, at heights where `F` is bounded below across the strip (they recur, by
almost periodicity) by `8 ‖F'‖/μ`, and in between by the maximum principle. P2 gives
`g_L = g_R =: g`, convergent on the closed strip; `F' = H F` with `H = Σ g(q) q^s` right of the
line, hence on the strip; at a zero of order `k + 1` the orders `k` of `F'` and `≥ k + 1` of
`H F` differ. ∎

### P5. Infinitely many exceptional zeros
In P4, if `F` has a zero in the strip, infinitely many of its zeros there are not zeros of `ξ`.

*Proof.* Suppose only finitely many, the set `E`. Purity: a zero `ρ₀` off the line recurs on a
thick relatively dense set; above the heights of `E` the recurrences are zeros of `ζ`; the thick
set lies in the zero shifts of `ζ` union a bounded set, and positive lower density contradicts
density zero. On the line, with `P = E`: `K ∏_{p ∈ P}(s − p)` vanishes at every zero of `F`, so
`K ∏ F'/F` is holomorphic, and dividing by the product and subtracting principal parts gives a
holomorphic `Φ = K F'/F − Σ_p r_p/(s − p)`. On the two vertical lines `‖s − p‖ ≥ η/2`; at a
height where `‖F‖ ≥ μ` the mean value inequality gives `‖s − p‖ ≥ μ/(‖F'‖_∞ + 1)`. So `Φ` is
bounded near the line, P2′ gives `g_L = g_R`, and the order argument of P4 excludes every zero,
those of `P` included. ∎

### P6. Approximants in growing boxes; bounded length
(a) Let `F_k → F ≢ 0` in the norm of absolute convergence at `x`, the strip `|Re s − ½| < ω`
right of `x`, `H_k → ∞`, and every zero of `F_k` with `|Re s − ½| < ω`, `|Im s| ≤ H_k` a zero of
`ξ`. Then for `ω' < ω`, eventually `F_k` has no zero with `|Re s − ½| ≤ ω'`.

*Proof.* A zero of `F` in the strip is a limit of zeros of the `F_k` (sphere domination), which
lie in the boxes; so `F` is a strip constituent, has no zero (P4), is a unit of the Wiener
algebra of the closed substrip (P3′), hence bounded below by `m`, and `‖F_k − F‖ < m` there. ∎

(b) For `N` and `ω' < ω ≤ ½` there is `H₀` such that every nonzero Dirichlet polynomial of length
`≤ N` whose zeros in the box of height `H₀` are zeros of `ξ` has no zero with
`|Re s − ½| ≤ ω'`.

*Proof.* Otherwise normalize counterexamples for `H₀ = k`; a subsequence of the coefficient
vectors converges on the unit sphere of `ℂ^N`, and (a) applies. ∎

### P7. Every band has a Dirichlet polynomial with exactly the zeros of `ξ`
For every `H` there is a nonzero Dirichlet polynomial whose zeros with `|Im s| ≤ H` are exactly
the zeros of `ξ` there. For every `N` there is `H₀` such that no Dirichlet polynomial of length
`≤ N` has this property for `H₀`.

*Proof.* `m^{−s} − ((m+1)/m)^ρ (m+1)^{−s} = m^{−s}(1 − e^{(ρ − s) L})`, `L = log((m+1)/m) ≤ 1/m`,
vanishes exactly at `ρ + 2πi n/L`; for `m > H/π` and `|Im ρ|, |Im s| ≤ H` only `n = 0` occurs.
The zeros of `ξ` in the band are finitely many; the product of the factors is a Dirichlet
polynomial (Dirichlet convolution of finitely supported coefficients). For the second statement
take a zero `ρ` of `ξ`, the height of P6 (b) for `ω' = |Re ρ − ½|`, `ω = ½`, and its maximum with
`|Im ρ|`. ∎

### P8. Bohr's inequality over a thin support; the Bohr strip
Let `F` be bounded by `M` and holomorphic on `Re s > x`, equal to `Σ a_n n^{−s}` where that
converges absolutely. Then `Σ ‖a_n‖² n^{−2σ} ≤ M²` for `σ > x`. If `Σ_{a_n ≠ 0} n^{−2δ} < ∞`, the
series converges absolutely on `Re s > x + δ`; if moreover `0 ≤ δ`, `x + δ < ½`, `F ≢ 0` and the
zeros of `F` in `Re s > x` are zeros of `ξ`, `F` has no zero. Cases: `δ > ½` (all `n`), hence
`x < 0`; every `δ > 0` for coefficients on the integers composed of finitely many primes, hence
every `x`.

*Proof.* The mean of `F(σ + it) n^{σ + it}` over `[−T, T]` tends to `a_n`: on a line of absolute
convergence termwise, and two vertical means differ by the horizontal sides of a rectangle,
`O(1/T)`. Bessel's inequality for the finite sections gives the square sum; Cauchy–Schwarz over
the support gives the absolute sum at `y = σ₀ + δ'`, `x < σ₀`, `δ ≤ δ'`. The zeros lie on the line
(`re_eq_half_of_zeros_subset_xi`), `F` is its series right of a point `y < ½` of absolute
convergence, and P4 applies. For finitely many primes `‖a_n‖ n^{−σ} ≤ M` and
`Σ_{n smooth} n^{−ε} < ∞` (Euler product). ∎

### P9. The index law in a disc
Let `E = ∏_{w ∈ W}(z − w) E₁` with `W` in the open disc, `E₁` zero-free on the closed disc, and
`‖E'‖ ≤ ‖E‖` on the circle. Then `E − E' ≡ 0` on the disc or it has at most `card W` zeros there.
For `ξ = E + E^♯` on the disc with `‖E^♯‖ ≤ ‖E‖` on the circle, `ξ` has at most `card W` zeros in
the disc.

*Proof.* Carry the disc to the unit disc and the unit disc to `Re s > ½` by `s ↦ (s − 1)/s`.
`E'/E` times the Blaschke product of the disc at `W` is holomorphic and bounded by `1` on the
circle, hence a Schur function; the zeros of `E − E'` are its agreements with a Blaschke product
of degree `card W`, at most `card W` (`encard_agreements_le`). `ξ` is not identically zero on a
disc: its zeros in a compact set are finitely many. ∎

### P10. Detection on consecutive points of a progression
Let `F = Σ_{k<N} a_k e^{λ_k s}`, `λ_k` real, `N ≥ 1`. For `s₀`, real `d` and `M ≥ 0` there is
`ν ∈ [M+1, M+N]` with `‖F(s₀ + iνd)‖ ≥ ‖F(s₀)‖ / (2eN (6(N+1)(M+2N+2))^N)`. If `F` vanishes at `N`
consecutive points of a vertical progression, it vanishes on the whole progression, and one of
these zeros is not a zero of `ξ`.

*Proof.* `F(s₀ + iνd) = Σ_k (a_k e^{λ_k s₀}) (e^{iλ_k d})^ν`, a power sum with unimodular nodes
and total weight `F(s₀)`; Turán's theorem with coefficients
(`exists_norm_weightedPowerSum_ge`). For the rigidity take a base point before the window with
step `d`, or after it with step `−d`. The zeros of `ξ` contain no vertical progression
(`not_forall_xi_progression`). ∎

### P11. The law of the carry
`κ(x, y) = {x} + {y} − {x + y} ∈ {0, 1}` is a cocycle, and
`Σ_i b_i κ(a_i u, a_i v) = g(u) + g(v) − g(u + v)` for `g = g_{b,a}`. Under P1 the two expansions
have the same carry series. Conversely, equal carry series and the bounds `O(u^σ)`, `σ < 1`,
imply `g_{b,a} = g_{c,q}`: the difference is additive and `o(u)`.

*Proof.* The difference `h` of the two series is additive on `(0, ∞)`, so `h(nu) = n h(u)`, and
`‖h(nu)‖ ≤ C (nu)^σ` with `σ < 1` forces `h(u) = 0`. ∎

## Open
- B153 in the Bohr strip: `F` bounded on `Re s > x`, `0 ≤ x < ½`, support of exponent at least
  `1 − 2x`, no absolute convergence left of the line. The expansions of `F'/F` near the line have
  square summable coefficients; the sums over the progressions of scales that the jump law needs
  converge absolutely exactly for exponents `> ½`.
- An explicit height in P6 (b): needs an effective inverse in the Wiener algebra of a strip.

## Log
- 2026-11-10 — created in 1-in-progress
- 2026-11-10 — formalized; moved to 3-formalized
